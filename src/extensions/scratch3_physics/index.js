// https://cdn.jsdelivr.net/gh/physics/physics.github.io/testExtension.js
const CATEGORY_WALLS = 0x0001;
const CATEGORY_NOT_WALLS = 0x0002;
const CATEGORY_STAGE_WALLS = 0x0004;

const zoom = 50;

const LINEAR_DAMPING = 0;
const ANGULAR_DAMPING = 0;
const MAX_VELOCITY = 200;
const MIN_VELOCITY = 0.1;
// Masks
const MASK_WALLS = CATEGORY_WALLS | CATEGORY_NOT_WALLS | CATEGORY_STAGE_WALLS; // WALLS collide with everything
const MASK_NOT_WALLS = CATEGORY_WALLS | CATEGORY_STAGE_WALLS; // NOT_WALLS should be affected by WALLS

const ArgumentType = require("../../extension-support/argument-type");
const BlockType = require("../../extension-support/block-type");

const Cast = require("../../util/cast");
const Runtime = require("../../engine/runtime");
const RenderedTarget = require("../../sprites/rendered-target");
const formatMessage = require("format-message");

const Box2D = require("./box2d_es6");

const b2World = Box2D.Dynamics.b2World;
const b2Vec2 = Box2D.Common.Math.b2Vec2;
const b2AABB = Box2D.Collision.b2AABB;
const b2BodyDef = Box2D.Dynamics.b2BodyDef;
const b2Body = Box2D.Dynamics.b2Body;
const b2FixtureDef = Box2D.Dynamics.b2FixtureDef;

const b2Contact = Box2D.Dynamics.Contacts.b2Contact;

const b2PolygonShape = Box2D.Collision.Shapes.b2PolygonShape;
const b2Math = Box2D.Common.Math.b2Math;

const fixDef = new b2FixtureDef();
const bodyDef = new b2BodyDef();

const prevPos = {};
let world;

const bodies = {};
const stageBodies = [];
const toRad = Math.PI / 180;

const SPACE_TYPE_OPTIONS = {
    WORLD: "world",
    STAGE: "stage",
    RELATIVE: "relative",
};

const WHERE_TYPE_OPTIONS = {
    ANY: "any",
    FEET: "feet",
};

const SHAPE_TYPE_OPTIONS = {
    COSTUME: "costume",
    CIRCLE: "circle",
    SVG_POLYGON: "svg",
    ALL: "all",
};

const _definePolyFromHull = function (hullPoints) {
    if (hullPoints.length < 3) {
        hullPoints = [
            { x: 0, y: 0 },
            { x: 0, y: 10 },
            { x: 10, y: 0 },
        ];
    }
    fixDef.shape = new b2PolygonShape();

    const vertices = [];

    let prev = null;
    for (let i = hullPoints.length - 1; i >= 0; i--) {
        // for (let i = 0; i < hullPoints.length; i++) {
        const b2Vec = new b2Vec2(
            hullPoints[i].x / zoom,
            hullPoints[i].y / zoom
        );
        if (
            prev !== null &&
            b2Math.SubtractVV(b2Vec, prev).LengthSquared() > Number.MIN_VALUE
        ) {
            vertices.push(b2Vec);
        }
        prev = b2Vec;
    }

    fixDef.shape.SetAsArray(vertices);
};

const _placeBody = function (id, x, y, dir) {
    if (bodies[id]) {
        world.DestroyBody(bodies[id]);
    }

    bodyDef.position.x = x / zoom;
    bodyDef.position.y = y / zoom;
    bodyDef.angle = (90 - dir) * toRad;

    const body = world.CreateBody(bodyDef);
    body.uid = id;
    body.CreateFixture(fixDef);
    bodies[id] = body;
    return body;
};

const _applyForce = function (id, ftype, x, y, dir, pow) {
    const body = bodies[id];
    if (!body) {
        return;
    }

    dir = (90 - dir) * toRad;

    if (ftype === "Impulse") {
        const center = body.GetLocalCenter(); // get the mass data from you body

        body.ApplyImpulse(
            { x: pow * Math.cos(dir), y: pow * Math.sin(dir) },
            body.GetWorldPoint({
                x: x / zoom + center.x,
                y: y / zoom + center.y,
            })
        );
    } else if (ftype === "World Impulse") {
        body.ApplyForce(
            { x: pow * Math.cos(dir), y: pow * Math.sin(dir) },
            { x: x / zoom, y: y / zoom }
        );
    }
};

/**
 * Set the X and Y coordinates (No Fencing)
 * @param {!RenderedTarget} rt the renderedTarget.
 * @param {!number} x New X coordinate, in Scratch coordinates.
 * @param {!number} y New Y coordinate, in Scratch coordinates.
 * @param {?boolean} force Force setting X/Y, in case of dragging
 */
const _setXY = function (rt, x, y, force) {
    if (rt.isStage) return;
    if (rt.dragging && !force) return;
    const oldX = rt.x;
    const oldY = rt.y;
    if (rt.renderer) {
        //   const position = rt.renderer.getFencedPositionOfDrawable(rt.drawableID, [x, y]);
        rt.x = x; // position[0];
        rt.y = y; // position[1];

        rt.renderer.updateDrawableProperties(rt.drawableID, {
            position: [x, y],
        });
        if (rt.visible) {
            rt.emit(RenderedTarget.EVENT_TARGET_VISUAL_CHANGE, rt);
            rt.runtime.requestRedraw();
        }
    } else {
        rt.x = x;
        rt.y = y;
    }

    rt.emit(RenderedTarget.EVENT_TARGET_MOVED, rt, oldX, oldY, force);
    rt.runtime.requestTargetsUpdate(rt);
};

const createStageBody = function () {
    const body = world.CreateBody(bodyDef);
    body.isStage = true;
    body.CreateFixture(fixDef);

    // Set the correct category bits for stage walls
    let categoryBits = CATEGORY_STAGE_WALLS;
    let maskBits = MASK_WALLS; // This will only allow collision with types that should collide with stage walls

    // Loop through all fixtures of the body and update their filter data
    for (
        let fixture = body.GetFixtureList();
        fixture;
        fixture = fixture.GetNext()
    ) {
        let filter = fixture.GetFilterData();
        filter.categoryBits = categoryBits;
        filter.maskBits = maskBits;
        fixture.SetFilterData(filter);
    }
    stageBodies.push(body);
};

const setupStage = function () {
    // Clear down previous stage
    if (stageBodies.length > 0) {
        for (const stageBodyID in stageBodies) {
            world.DestroyBody(stageBodies[stageBodyID]);
            delete stageBodies[stageBodyID];
        }
    }

    // Build up new stage
    bodyDef.type = b2Body.b2_staticBody;
    fixDef.shape = new b2PolygonShape();
    bodyDef.angle = 0;

    let left = -240 / zoom;
    let right = 240 / zoom;
    let top = 180 / zoom;
    let bottom = -180 / zoom;
    let boxWidth = 1000 / zoom;
    let boxHeight = 1000 / zoom;
    let screenWidth = 480 / zoom;
    let screenHeight = 360 / zoom;

    fixDef.shape.SetAsBox(boxWidth, screenHeight);
    bodyDef.position.Set(left - boxWidth, 0);
    createStageBody();
    bodyDef.position.Set(right + boxWidth, 0);
    createStageBody();
    fixDef.shape.SetAsBox(screenWidth, boxHeight);
    bodyDef.position.Set(0, top + boxHeight);
    createStageBody();
    bodyDef.position.Set(0, bottom - boxHeight);
    createStageBody();

    bodyDef.type = b2Body.b2_dynamicBody;

    for (const bodyID in bodies) {
        bodies[bodyID].SetAwake(true);
    }
};

/**
 * Icon svg to be displayed at the left edge of each extension block, encoded as a data URI.
 * @type {string}
 */
// eslint-disable-next-line max-len
const blockIconURI =
    "data:image/svg+xml;base64,PHN2ZyB2ZXJzaW9uPSIxLjEiDQoJIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgeG1sbnM6eGxpbms9Imh0dHA6Ly93d3cudzMub3JnLzE5OTkveGxpbmsiIHhtbG5zOmE9Imh0dHA6Ly9ucy5hZG9iZS5jb20vQWRvYmVTVkdWaWV3ZXJFeHRlbnNpb25zLzMuMC8iDQoJIHg9IjBweCIgeT0iMHB4IiB3aWR0aD0iNDBweCIgaGVpZ2h0PSI0MHB4IiB2aWV3Qm94PSItMy43IC0zLjcgNDAgNDAiIGVuYWJsZS1iYWNrZ3JvdW5kPSJuZXcgLTMuNyAtMy43IDQwIDQwIg0KCSB4bWw6c3BhY2U9InByZXNlcnZlIj4NCjxkZWZzPg0KPC9kZWZzPg0KPHJlY3QgeD0iOC45IiB5PSIxLjUiIGZpbGw9IiNGRkZGRkYiIHN0cm9rZT0iIzE2OUZCMCIgc3Ryb2tlLXdpZHRoPSIzIiB3aWR0aD0iMTQuOCIgaGVpZ2h0PSIxNC44Ii8+DQo8cmVjdCB4PSIxLjUiIHk9IjE2LjMiIGZpbGw9IiNGRkZGRkYiIHN0cm9rZT0iIzE2OUZCMCIgc3Ryb2tlLXdpZHRoPSIzIiB3aWR0aD0iMTQuOCIgaGVpZ2h0PSIxNC44Ii8+DQo8cmVjdCB4PSIxNi4zIiB5PSIxNi4zIiBmaWxsPSIjRkZGRkZGIiBzdHJva2U9IiMxNjlGQjAiIHN0cm9rZS13aWR0aD0iMyIgd2lkdGg9IjE0LjgiIGhlaWdodD0iMTQuOCIvPg0KPC9zdmc+";

/**
 * Icon svg to be displayed in the category menu, encoded as a data URI.
 * @type {string}
 */
// eslint-disable-next-line max-len
const menuIconURI =
    "data:image/svg+xml;base64,PHN2ZyB2ZXJzaW9uPSIxLjEiDQoJIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgeG1sbnM6eGxpbms9Imh0dHA6Ly93d3cudzMub3JnLzE5OTkveGxpbmsiIHhtbG5zOmE9Imh0dHA6Ly9ucy5hZG9iZS5jb20vQWRvYmVTVkdWaWV3ZXJFeHRlbnNpb25zLzMuMC8iDQoJIHg9IjBweCIgeT0iMHB4IiB3aWR0aD0iNDBweCIgaGVpZ2h0PSI0MHB4IiB2aWV3Qm94PSItMy43IC0zLjcgNDAgNDAiIGVuYWJsZS1iYWNrZ3JvdW5kPSJuZXcgLTMuNyAtMy43IDQwIDQwIg0KCSB4bWw6c3BhY2U9InByZXNlcnZlIj4NCjxkZWZzPg0KPC9kZWZzPg0KPHJlY3QgeD0iOC45IiB5PSIxLjUiIGZpbGw9IiNGRkZGRkYiIHN0cm9rZT0iIzE2OUZCMCIgc3Ryb2tlLXdpZHRoPSIzIiB3aWR0aD0iMTQuOCIgaGVpZ2h0PSIxNC44Ii8+DQo8cmVjdCB4PSIxLjUiIHk9IjE2LjMiIGZpbGw9IiNGRkZGRkYiIHN0cm9rZT0iIzE2OUZCMCIgc3Ryb2tlLXdpZHRoPSIzIiB3aWR0aD0iMTQuOCIgaGVpZ2h0PSIxNC44Ii8+DQo8cmVjdCB4PSIxNi4zIiB5PSIxNi4zIiBmaWxsPSIjRkZGRkZGIiBzdHJva2U9IiMxNjlGQjAiIHN0cm9rZS13aWR0aD0iMyIgd2lkdGg9IjE0LjgiIGhlaWdodD0iMTQuOCIvPg0KPC9zdmc+";

class Scratch3Physics {
    constructor(runtime) {
        /**
         * The runtime instantiating this block package.
         * @type {Runtime}
         */
        this.runtime = runtime;
        this.activeTargetCollisions = new Set(); // e.g. "spriteA|spriteB"

        // Clear target motion state values when the project starts.
        this.runtime.on(Runtime.PROJECT_START, this.reset.bind(this));

        world = new b2World(
            new b2Vec2(0, 0), // gravity (0)
            true // allow sleep
        );
        this.contactListener = new MyContactListener(runtime);
        world.SetContactListener(this.contactListener);
        const b2ContactFilter = new MyContactFilter();
        world.SetContactFilter(b2ContactFilter);
        this.runtime.stepPhysics = this.doTick.bind(this);
        this.runtime.savePhysics = this.saveSnapshot.bind(this);
        this.runtime.loadPhysics = this.loadSnapshot.bind(this);
        this.runtime.setScreenwrap = this.setAllowScreenwrap.bind(this);
        this.runtime.setKicker = this.setKicker.bind(this);

        this.runtime.physicsData = {
            world: world,
            bodies: bodies,
            stageBodies: stageBodies,
        };

        this.map = {};

        fixDef.density = 1.0; // 1.0
        fixDef.friction = 0.5; // 0.5
        fixDef.restitution = 0; // 0.2

        setupStage();
    }

    reset() {
        for (const body in bodies) {
            world.DestroyBody(bodies[body]);
            delete bodies[body];
            delete prevPos[body];
        }
        //delete all stage bodies
        for (const stageBodyID in stageBodies) {
            world.DestroyBody(stageBodies[stageBodyID]);
            delete stageBodies[stageBodyID];
        }

        // todo: delete joins?
        setupStage();
    }

    static get STATE_KEY() {
        return "Scratch.physics";
    }

    /**
     * @returns {object} metadata for this extension and its blocks.
     */
    getInfo() {
        return {
            id: "physics",
            name: formatMessage({
                id: "physics.categoryName",
                default: "Physics",
                description: "Label for the physics extension category",
            }),
            menuIconURI: menuIconURI,
            blockIconURI: blockIconURI,
            blocks: [
                {
                    opcode: "whenCollide",
                    blockType: BlockType.HAT,
                    text: "when I collide with [sprite]",
                    isEdgeActivated: false,
                    arguments: {
                        sprite: {
                            type: ArgumentType.STRING,
                            menu: "SpriteMenu",
                            defaultValue: "any",
                        },
                    },
                },

                {
                    opcode: "setPhysics",
                    blockType: BlockType.COMMAND,
                    text: formatMessage({
                        id: "physics.setPhysics",
                        default: "enable for [shape] mode [mode]",
                        description: "Enable Physics for this Sprite",
                    }),
                    arguments: {
                        shape: {
                            type: ArgumentType.STRING,
                            menu: "ShapeTypes",
                            defaultValue: "costume",
                        },
                        mode: {
                            type: ArgumentType.STRING,
                            menu: "EnableModeTypes",
                            defaultValue: "normal",
                        },
                    },
                },
                {
                    opcode: "setKickStrength",
                    blockType: BlockType.COMMAND,
                    text: formatMessage({
                        id: "physics.setKickStrength",
                        default: "set kick strength to [strength]",
                        description: "Set the strength of the kick",
                    }),
                    arguments: {
                        strength: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 10,
                        },
                    },
                },
                {
                    opcode: "setBounciness",
                    blockType: BlockType.COMMAND,
                    text: formatMessage({
                        id: "physics.setBounciness",
                        default: "set bounciness to [BOUNCINESS]",
                        description: "Set the bounciness for this object",
                    }),
                    arguments: {
                        BOUNCINESS: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 0.5, // Default bounciness
                        },
                    },
                },
                "---",

                {
                    opcode: "doTick",
                    blockType: BlockType.COMMAND,
                    text: formatMessage({
                        id: "physics.doTick",
                        default: "step simulation",
                        description:
                            "Run a single tick of the physics simulation",
                    }),
                },

                "---",

                // applyForce (target, ftype, x, y, dir, pow) {
                // applyAngForce (target, pow) {

                {
                    opcode: "setVelocity",
                    blockType: BlockType.COMMAND,
                    text: formatMessage({
                        id: "physics.setVelocity",
                        default: "set velocity to sx: [sx] sy: [sy]",
                        description: "Set Velocity",
                    }),
                    arguments: {
                        sx: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 0,
                        },
                        sy: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 0,
                        },
                    },
                },
                {
                    opcode: "changeVelocity",
                    blockType: BlockType.COMMAND,
                    text: formatMessage({
                        id: "physics.changeVelocity",
                        default: "change velocity by sx: [sx] sy: [sy]",
                        description: "Change Velocity",
                    }),
                    arguments: {
                        sx: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 0,
                        },
                        sy: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 0,
                        },
                    },
                },
                {
                    opcode: "getKickStrength",
                    text: formatMessage({
                        id: "physics.getKickStrength",
                        default: "kick strength",
                        description: "get the kick strength",
                    }),
                    blockType: BlockType.REPORTER,
                },
                {
                    opcode: "getFriction",
                    text: formatMessage({
                        id: "physics.getFriction",
                        default: "friction",
                        description: "get the friction",
                    }),
                    blockType: BlockType.REPORTER,
                },
                {
                    opcode: "getMass",
                    text: formatMessage({
                        id: "physics.getMass",
                        default: "mass",
                        description: "get the mass",
                    }),
                    blockType: BlockType.REPORTER,
                },
                {
                    opcode: "getBounciness",
                    text: formatMessage({
                        id: "physics.getBounciness",
                        default: "bounciness",
                        description: "get the bounciness",
                    }),
                    blockType: BlockType.REPORTER,
                },
                {
                    opcode: "getVelocityX",
                    text: formatMessage({
                        id: "physics.getVelocityX",
                        default: "x velocity",
                        description: "get the x velocity",
                    }),
                    blockType: BlockType.REPORTER,
                },
                {
                    opcode: "getVelocityY",
                    text: formatMessage({
                        id: "physics.getVelocityY",
                        default: "y velocity",
                        description: "get the y velocity",
                    }),
                    blockType: BlockType.REPORTER,
                },

                "---",

                {
                    opcode: "applyForce",
                    blockType: BlockType.COMMAND,
                    text: formatMessage({
                        id: "physics.applyForce",
                        default: "push with force [force] in direction [dir]",
                        description: "Push this object in a given direction",
                    }),
                    arguments: {
                        force: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 25,
                        },
                        dir: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 0,
                        },
                    },
                },
                {
                    opcode: "applyAngForce",
                    blockType: BlockType.COMMAND,
                    text: formatMessage({
                        id: "physics.applyAngForce",
                        default: "spin with force [force]",
                        description: "Push this object in a given direction",
                    }),
                    arguments: {
                        force: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 500,
                        },
                    },
                },

                "---",

                {
                    opcode: "setStatic",
                    blockType: BlockType.COMMAND,
                    text: formatMessage({
                        id: "physics.setStatic",
                        default: "set fixed [static]",
                        description:
                            "Sets whether this block is static or dynamic",
                    }),
                    arguments: {
                        static: {
                            type: ArgumentType.STRING,
                            menu: "StaticTypes",
                            defaultValue: "static",
                        },
                    },
                },
                {
                    opcode: "setIsWall",
                    blockType: BlockType.COMMAND,
                    text: formatMessage({
                        id: "physics.setIsWall",
                        default: "set is wall [isWall]",
                        description: "Sets whether this block is a wall",
                    }),
                    arguments: {
                        isWall: {
                            type: ArgumentType.STRING,
                            menu: "WallTypes",
                            defaultValue: "wall",
                        },
                    },
                },
                {
                    opcode: "setScreenwrap",
                    blockType: BlockType.COMMAND,
                    text: formatMessage({
                        id: "physics.setScreenwrap",
                        default: "set screenwrap [screenwrap]",
                        description: "Sets whether this piece can screenwrap",
                    }),
                    arguments: {
                        screenwrap: {
                            type: ArgumentType.STRING,
                            menu: "ScreenwrapTypes",
                            defaultValue: "allowed",
                        },
                    },
                },
                {
                    opcode: "setLinearDamping",
                    blockType: BlockType.COMMAND,
                    text: formatMessage({
                        id: "physics.setLinearDamping",
                        default: "set friction to [damping]",
                        description: "Set the linear damping of the object",
                    }),
                    arguments: {
                        damping: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 1,
                        },
                    },
                },
                {
                    opcode: "setProperties",
                    blockType: BlockType.COMMAND,
                    text: formatMessage({
                        id: "physics.setProperties",
                        default:
                            "set density [density] roughness [friction] bounce [restitution]",
                        description: "Set the density of the object",
                    }),
                    arguments: {
                        density: {
                            type: ArgumentType.NUMBER,
                            menu: "DensityTypes",
                            defaultValue: 100,
                        },
                        friction: {
                            type: ArgumentType.NUMBER,
                            menu: "FrictionTypes",
                            defaultValue: 50,
                        },
                        restitution: {
                            type: ArgumentType.NUMBER,
                            menu: "RestitutionTypes",
                            defaultValue: 20,
                        },
                    },
                },
                {
                    opcode: "getTouching",
                    text: formatMessage({
                        id: "physics.getTouching",
                        default: "touching [where]",
                        description:
                            "get the name of any sprites we are touching",
                    }),
                    blockType: BlockType.REPORTER,
                    arguments: {
                        where: {
                            type: ArgumentType.STRING,
                            menu: "WhereTypes",
                            defaultValue: "any",
                        },
                    },
                },
                {
                    opcode: "getStatic",
                    text: formatMessage({
                        id: "physics.getStatic",
                        default: "is static?",
                        description: "get whether this sprite is static",
                    }),
                    blockType: BlockType.REPORTER,
                },
                {
                    opcode: "getIsWall",
                    text: formatMessage({
                        id: "physics.getIsWall",
                        default: "is wall?",
                        description: "get whether this sprite is static",
                    }),
                    blockType: BlockType.REPORTER,
                },
            ],

            menus: {
                SpriteMenu: this.SPRITE_MENU,

                SpaceTypes: this.SPACE_TYPE_MENU,
                WhereTypes: this.WHERE_TYPE_MENU,
                ShapeTypes: this.SHAPE_TYPE_MENU,
                EnableModeTypes: this.ENABLE_TYPES_TYPE_MENU,
                StaticTypes: this.STATIC_TYPE_MENU,
                WallTypes: this.WALL_TYPE_MENU,
                ScreenwrapTypes: this.SCREENWRAP_TYPE_MENU,
                FrictionTypes: this.FRICTION_TYPE_MENU,
                RestitutionTypes: this.RESTITUTION_TYPE_MENU,
                DensityTypes: this.DENSITY_TYPE_MENU,
            },
        };
    }

    get SPACE_TYPE_MENU() {
        return [
            { text: "in world", value: SPACE_TYPE_OPTIONS.WORLD },
            { text: "on stage", value: SPACE_TYPE_OPTIONS.STAGE },
            { text: "relative", value: SPACE_TYPE_OPTIONS.RELATIVE },
        ];
    }
    get SPRITE_MENU() {
        const targets = this.runtime.targets;
        const options = targets
            .filter((t) => !t.isStage)
            .map((t) => ({ text: t.sprite.name, value: t.sprite.name }));
        options.unshift({ text: "any", value: "any" });
        return options;
    }

    get WHERE_TYPE_MENU() {
        return [
            { text: "any", value: WHERE_TYPE_OPTIONS.ANY },
            { text: "feet", value: WHERE_TYPE_OPTIONS.FEET },
        ];
    }

    get SHAPE_TYPE_MENU() {
        return [
            { text: "this costume", value: SHAPE_TYPE_OPTIONS.COSTUME },
            { text: "this circle", value: SHAPE_TYPE_OPTIONS.CIRCLE },
            { text: "this polygon", value: SHAPE_TYPE_OPTIONS.SVG_POLYGON },
            { text: "all sprites", value: SHAPE_TYPE_OPTIONS.ALL },
        ];
    }

    get ENABLE_TYPES_TYPE_MENU() {
        return [
            { text: "normal", value: "normal" },
            { text: "precision", value: "bullet" },
        ];
    }

    get STATIC_TYPE_MENU() {
        return [
            { text: "free", value: "free" },
            { text: "static", value: "static" },
        ];
    }

    get WALL_TYPE_MENU() {
        return [
            { text: "wall", value: "wall" },
            { text: "not wall", value: "not wall" },
        ];
    }

    get SCREENWRAP_TYPE_MENU() {
        return [
            { text: "allowed", value: "allowed" },
            { text: "not allowed", value: "not allowed" },
        ];
    }
    get DENSITY_TYPE_MENU() {
        return [
            { text: "very light", value: "25" },
            { text: "light", value: "50" },
            { text: "normal", value: "100" },
            { text: "heavy", value: "200" },
            { text: "very heavy", value: "400" },
        ];
    }

    get FRICTION_TYPE_MENU() {
        return [
            { text: "none", value: "0" },
            { text: "smooth", value: "20" },
            { text: "normal", value: "50" },
            { text: "rough", value: "75" },
            { text: "extremely rough", value: "100" },
        ];
    }

    get RESTITUTION_TYPE_MENU() {
        return [
            { text: "none", value: "0" },
            { text: "little", value: "10" },
            { text: "normal", value: "20" },
            { text: "quite bouncy", value: "40" },
            { text: "very bouncy", value: "70" },
            { text: "unstable", value: "100" },
        ];
    }

    /**
     * Play a drum sound for some number of beats.
     * @property {number} x - x offset.
     * @property {number} y - y offset.
     */
    doTick() {
        this._checkMoved();

        world.Step(1 / 30, 20, 20);
        world.ClearForces();

        for (const targetID in bodies) {
            let body = bodies[targetID];
            previousPosition = prevPos[targetID]
                ? prevPos[targetID]
                : { x: 0, y: 0 };

            const target = this.runtime.getTargetById(targetID);
            if (!target) {
                world.DestroyBody(body);
                delete bodies[targetID];
                delete prevPos[targetID];
                continue;
            }

            const position = body.GetPosition();
            //   if (!body.isStatic) {
            _setXY(target, position.x * zoom, position.y * zoom);
            //   }

            //TODO:  Does this make sense?  Who gets to decide the rotation?  Physics or Scratch?  When?
            if (
                target.rotationStyle ===
                RenderedTarget.ROTATION_STYLE_ALL_AROUND
            ) {
                target.setDirection(90 - body.GetAngle() / toRad);
            }

            prevPos[targetID] = {
                x: target.x,
                y: target.y,
                dir: target.direction,
            };

            if (!body.allowScreenwrap && body.isStatic) {
                const hasConvexHullPoints =
                    target.renderer._allDrawables[target.drawableID]
                        .convexHullPoints &&
                    target.renderer._allDrawables[target.drawableID]
                        .convexHullPoints.length > 1 &&
                    target.renderer._allDrawables[target.drawableID]
                        .convexHullPoints[0];
                if (!hasConvexHullPoints) {
                    target.updateAllDrawableProperties();
                    const size = target.size;
                    target.setSize(size + 1);
                    target.setSize(size);
                    target.updateAllDrawableProperties();
                    continue;
                }
                const bounds = target.getBounds();
                if (bounds.right >= 245) {
                    const delta = bounds.right - 245;
                    target.x -= delta;
                    // reverse the x velocity
                    const vel = body.GetLinearVelocity();
                    body.SetLinearVelocity(new b2Vec2(-vel.x, vel.y));
                } else if (bounds.left <= -245) {
                    const delta = bounds.left + 245;
                    target.x -= delta;
                    const vel = body.GetLinearVelocity();
                    body.SetLinearVelocity(new b2Vec2(-vel.x, vel.y));
                }

                if (bounds.bottom <= -185) {
                    const delta = bounds.bottom + 185;
                    target.y -= delta;
                    const vel = body.GetLinearVelocity();
                    body.SetLinearVelocity(new b2Vec2(vel.x, -vel.y));
                }
                if (bounds.top >= 185) {
                    const delta = bounds.top - 185;
                    target.y -= delta;
                    const vel = body.GetLinearVelocity();
                    body.SetLinearVelocity(new b2Vec2(vel.x, -vel.y));
                }
            }

            if (body.isStatic) {
                continue;
            }
            const appliedGlitchesList = Object.values(target.variables).find(
                (v) => v.name === "$applied_glitches" && v.type === "list"
            );
            if (appliedGlitchesList) {
                const hasGravity = appliedGlitchesList.value.find(
                    (v) => v === "gravity"
                );
                const oldVelocity = body.GetLinearVelocity();
                // if body.friction is undefined, set it to 1
                if (body.friction === undefined) {
                    body.friction = 1;
                }
                let friction = body.friction;
                if (hasGravity) {
                    // only apply friction ot the x velocity
                    const newVelocity = new b2Vec2(
                        oldVelocity.x * (1 - friction),
                        oldVelocity.y
                    );

                    body.SetLinearVelocity(newVelocity);
                } else {
                    // apply friction to both x and y velocity
                    const newVelocity = new b2Vec2(
                        oldVelocity.x * (1 - friction),
                        oldVelocity.y * (1 - friction)
                    );
                    body.SetLinearVelocity(newVelocity);
                }
            }
        }
        this.contactListener.finalizeCollisions();
    }

    _checkMoved() {
        for (const targetID in bodies) {
            let body = bodies[targetID];
            let target = this.runtime.getTargetById(targetID);
            let pos = body.GetPosition();
            if (!target) {
                // Drop target from simulation
                world.DestroyBody(body);
                delete bodies[targetID];
                delete prevPos[targetID];
                continue;
            }

            const prev = prevPos[targetID];
            const fixedRotation = true;
            if (
                (target.physicsCostumeName !== "hitbox" &&
                    target.physicsCostumeName !==
                        target.getCurrentCostume().name) ||
                target.size !== target.physicsSize ||
                !body ||
                body.isStatic
            ) {
                const cachedVelocity = body.GetLinearVelocity();
                body = this.setPhysicsFor(target);
                if (!body || !body.SetLinearVelocity) {
                    continue;
                }
                body.SetLinearVelocity(cachedVelocity);
            }

            target.physicsSize = target.size;
            if (!target.visible && !body.isHidden) {
                this.setHidden(target, true);
            } else if (target.visible && body.isHidden) {
                this.setHidden(target, false);
            }
            const newPos = new b2Vec2(target.x / zoom, target.y / zoom);
            if (newPos.x !== pos.x || newPos.y !== pos.y) {
                body.SetPosition(newPos);
            }
            const newDir = (90 - target.direction) * toRad;
            const angle = body.GetAngle();
            if (angle !== newDir) {
                body.SetAngle(newDir);
            }
            body.SetAwake(true);
            const velocityMagnitude = body.GetLinearVelocity().Length();
            if (velocityMagnitude > MAX_VELOCITY) {
                const velocity = body.GetLinearVelocity();
                velocity.Normalize();
                velocity.Multiply(MAX_VELOCITY);
                body.SetLinearVelocity(velocity);
            }
            if (velocityMagnitude < MIN_VELOCITY) {
                body.SetLinearVelocity(new b2Vec2(0, 0));
            }
        }
    }

    setPhysicsAll() {
        const allTargets = this.runtime.targets;
        if (allTargets === null) return;
        for (let i = 0; i < allTargets.length; i++) {
            const target = allTargets[i];
            if (!target.isStage && !bodies[target.id]) {
                this.setPhysicsFor(target);
            }
        }
    }

    /**
     * Play a drum sound for some number of beats.
     * @param {object} args - the block arguments.
     * @param {object} util - utility object provided by the runtime.
     * @property {string} shape - the shape
     */
    setPhysics(args, util) {
        if (args.shape === SHAPE_TYPE_OPTIONS.ALL) {
            this.setPhysicsAll();
            return;
        }

        const target = util.target;
        const body = this.setPhysicsFor(target);
    }

    setHidden(target, isHidden) {
        let body = bodies[target.id];
        if (!body) {
            body = this.setPhysicsFor(target);
        }
        if (isHidden) {
            this.setCollisionFilter(target, "not wall");
        } else {
            this.setCollisionFilter(target, body.isWall ? "wall" : "not wall");
        }
        body.isHidden = isHidden;
    }

    setAllowScreenwrap(target, allowScreenwrap) {
        if (target.isStage) {
            return; // Ignore if it's the stage itself
        }

        let body = bodies[target.id];
        if (!body) {
            body = this.setPhysicsFor(target); // Ensure the body exists
        }
        if (allowScreenwrap === body.allowScreenwrap) {
            return; // Ignore if the setting hasn't changed
        }
        body.allowScreenwrap = allowScreenwrap; // Track screenwrap setting

        body.SetAwake(true); // Make sure the body is active so changes take effect immediately

        // Flag all contacts for re-evaluation to update collision behavior
        let contactEdge = body.GetContactList();
        while (contactEdge) {
            let contact = contactEdge.contact;
            contact.FlagForFiltering();
            contactEdge = contactEdge.next;
        }
    }

    setCollisionFilter(target, type) {
        let body = bodies[target.id];
        if (!body) {
            body = this.setPhysicsFor(target); // Ensure the body exists
        }
        let categoryBits, maskBits;
        if (type === "wall") {
            categoryBits = CATEGORY_WALLS;
            maskBits = MASK_WALLS; // WALLS should collide with NOT_WALLS and other WALLS
        } else {
            categoryBits = CATEGORY_NOT_WALLS;
            maskBits = MASK_NOT_WALLS; // NOT_WALLS should be stopped by WALLS
        }
        updateCollisionFilter(body, categoryBits, maskBits);
    }

    setPhysicsFor(target, props) {
        let isWall = false,
            kickStrength = 0,
            isStatic = false,
            allowScreenwrap = false;
        friction = 1;
        isHidden = false;
        if (props) {
            if (props.isWall === "wall" || props.isWall === true) {
                props.isWall = true;
            } else {
                props.isWall = false;
            }
            isWall = props.isWall;
            kickStrength = props.kickStrength;
            isStatic = props.isStatic;
            allowScreenwrap = props.allowScreenwrap;
            isHidden = props.isHidden;
            friction = props.friction;
        } else {
            let oldBody = bodies[target.id];
            if (!oldBody) {
                if (!target.isOriginal) {
                    const originalId = target.sprite.clones[0].id;
                    oldBody = bodies[originalId];
                }
            }
            if (oldBody) {
                isWall = oldBody.isWall;
                isStatic = oldBody.isStatic;
                allowScreenwrap = oldBody.allowScreenwrap;
                kickStrength = oldBody.kickStrength;
                isHidden = oldBody.isHidden;
                friction = oldBody.friction;
            }
        }

        const r = this.runtime.renderer;

        if (target.visible === false) {
            target.setVisible(true);
            isHidden = true;
        } else {
            isHidden = false;
        }
        const drawable = r._allDrawables[target.drawableID];

        // Check for a 'hitbox' costume

        const hitboxCostumeIndex = target.getCostumeIndexByName("hitbox"); // Method to get a costume by name
        let hitboxCostume = null;
        if (hitboxCostumeIndex !== -1) {
            hitboxCostume = target.getCostumes()[hitboxCostumeIndex];
        }
        const currentCostume = target.getCurrentCostume(); // Method to get the current costume
        const currentCostumeIndex = target.getCostumeIndexByName(
            currentCostume.name
        ); // Method to get a costume by name
        let costumeToUse = hitboxCostume || currentCostume; // Use 'hitbox' costume if available, otherwise current costume
        target.physicsCostumeName = costumeToUse.name;
        target.physicsCostumeSize = target.size;
        const costumeToUseIndex = target.getCostumeIndexByName(
            costumeToUse.name
        ); // Method to get a costume by name
        // Set the costume to the one we've determined to use
        target.setCostume(costumeToUseIndex);

        // Update convex hull points for the costume in use
        if (drawable.needsConvexHullPoints()) {
            const points = r._getConvexHullPointsForDrawable(target.drawableID);
            drawable.setConvexHullPoints(points);
        }

        const points = drawable._convexHullPoints;
        const scaleX = drawable.scale[0] / 100;
        const scaleY = drawable.scale[1] / -100; // Flip Y for hulls
        const offset = drawable.skin.rotationCenter;
        let allHulls = null;

        const hullPoints = [];
        for (const i in points) {
            if (!points[i] || points[i].length < 2) {
                if (bodies[target.id]) {
                    return bodies[target.id];
                } else {
                    return null;
                }
            } else {
                hullPoints.push({
                    x: (points[i][0] - offset[0]) * scaleX,
                    y: (points[i][1] - offset[1]) * scaleY,
                });
            }
        }

        _definePolyFromHull(hullPoints);

        const body = _placeBody(
            target.id,
            target.x,
            target.y,
            target.direction
        );
        body.friction = friction;
        //set to dynamic
        if (isStatic) {
            body.SetType(b2Body.b2_staticBody);
            body.isStatic = true;
        } else {
            body.SetType(b2Body.b2_dynamicBody);
            body.isStatic = false;
        }
        this.setCollisionFilter(target, isWall ? "wall" : "not wall");
        body.SetLinearDamping(LINEAR_DAMPING);
        body.SetAngularDamping(ANGULAR_DAMPING);
        body.SetPosition(new b2Vec2(target.x / zoom, target.y / zoom));
        body.SetFixedRotation(true);
        body.isWall = isWall;

        if (allHulls) {
            for (let i = 1; i < allHulls.length; i++) {
                _definePolyFromHull(allHulls[i]);
                body.CreateFixture(fixDef);
            }
        }

        // Restore the original costume if we used the 'hitbox' costume
        if (hitboxCostume) {
            target.setCostume(currentCostumeIndex);
        }

        this.setAllowScreenwrap(target, allowScreenwrap);

        body.kickStrength = kickStrength;
        if (isHidden) {
            target.setVisible(false);
        }
        this.setHidden(target, isHidden);

        //set friction to 0 for all fixtures
        for (
            let fixture = body.GetFixtureList();
            fixture;
            fixture = fixture.GetNext()
        ) {
            fixture.SetFriction(0);
        }
        body.targetId = target.id;
        return body;
    }

    setKickStrength(args, util) {
        const target = util.target;
        let body = bodies[target.id];
        if (!body) {
            body = this.setPhysicsFor(target);
        }
        body.kickStrength = args.strength;
    }

    setBounciness(args, util) {
        const bounciness = Cast.toNumber(args.BOUNCINESS);
        let body = bodies[util.target.id];
        if (!body) {
            body = this.setPhysicsFor(util.target);
        }
        const fixtures = body.GetFixtureList();
        for (
            let fixture = body.GetFixtureList();
            fixture;
            fixture = fixture.GetNext()
        ) {
            fixture.SetRestitution(bounciness);
        }
    }

    applyForce(args, util) {
        _applyForce(
            util.target.id,
            "Impulse",
            0,
            0,
            Cast.toNumber(args.dir),
            Cast.toNumber(args.force)
        );
    }

    applyAngForce(args, util) {
        let body = bodies[util.target.id];
        if (!body) {
            body = this.setPhysicsFor(util.target);
        }

        body.ApplyTorque(-Cast.toNumber(args.force));
    }

    setDensity(args, util) {
        let body = bodies[util.target.id];
        if (!body) {
            body = this.setPhysicsFor(util.target);
        }

        body.GetFixtureList().SetDensity(Cast.toNumber(args.density));
        body.ResetMassData();
    }

    setProperties(args, util) {
        let body = bodies[util.target.id];
        if (!body) {
            body = this.setPhysicsFor(util.target);
        }

        body.GetFixtureList().SetDensity(Cast.toNumber(args.density) / 100.0);
        body.GetFixtureList().SetFriction(Cast.toNumber(args.friction) / 100.0);
        body.GetFixtureList().SetRestitution(
            Cast.toNumber(args.restitution) / 100.0
        );
        body.ResetMassData();
    }

    setVelocity(args, util) {
        this.runtime.requestRedraw();
        this.runtime.requestTargetsUpdate(util.target);
        let body = bodies[util.target.id];
        if (!body) {
            body = this.setPhysicsFor(util.target);
        }

        body.SetAwake(true);

        const x = Cast.toNumber(args.sx);
        const y = Cast.toNumber(args.sy);
        const force = new b2Vec2(x, y);
        force.Multiply(30 / zoom);
        body.SetLinearVelocity(force);
    }

    changeVelocity(args, util) {
        this.runtime.requestRedraw();
        this.runtime.requestTargetsUpdate(util.target);
        let body = bodies[util.target.id];
        if (!body) {
            body = this.setPhysicsFor(util.target);
        }

        body.SetAwake(true);

        const x = Cast.toNumber(args.sx);
        const y = Cast.toNumber(args.sy);
        const force = new b2Vec2(x, y);
        force.Multiply(30 / zoom);
        force.Add(body.GetLinearVelocity());
        body.SetLinearVelocity(force);
    }

    getStatic(args, util) {
        const body = bodies[util.target.id];
        if (!body) {
            return false;
        }

        return body.isStatic;
    }

    getIsWall(args, util) {
        const body = bodies[util.target.id];
        if (!body) {
            return false;
        }

        return body.isWall;
    }

    getMass(args, util) {
        const body = bodies[util.target.id];
        if (!body) {
            return 0;
        }
        return body.GetMass();
    }

    getBounciness(args, util) {
        const body = bodies[util.target.id];
        if (!body) {
            return 0;
        }
        const fixture = body.GetFixtureList();
        return fixture.GetRestitution();
    }

    getFriction(args, util) {
        const body = bodies[util.target.id];
        if (!body) {
            return 0;
        }
        // get linear damping
        return body.friction;
    }

    getKickStrength(args, util) {
        const body = bodies[util.target.id];
        if (!body) {
            return 0;
        }
        return body.kickStrength;
    }

    getVelocityX(args, util) {
        const body = bodies[util.target.id];
        if (!body) {
            return 0;
        }
        const x = body.GetLinearVelocity().x;
        return (x * zoom) / 30;
    }

    getVelocityY(args, util) {
        const body = bodies[util.target.id];
        if (!body) {
            return 0;
        }
        const y = body.GetLinearVelocity().y;
        return (y * zoom) / 30;
    }

    setScreenwrap(args, util) {
        this.setAllowScreenwrap(util.target, args.screenwrap === "allowed");
    }

    setIsWall(args, util) {
        const body = bodies[util.target.id];
        if (!body) {
            return;
        }
        let isWall = false;

        if (args.isWall === "wall" || args.isWall === true) {
            isWall = true;
        } else {
            isWall = false;
        }

        body.isWall = isWall;
        const isWallString = isWall ? "wall" : "not wall";
        this.setCollisionFilter(util.target, isWallString);
    }

    setLinearDamping(args, util) {
        const body = bodies[util.target.id];
        if (!body) {
            return;
        }
        //        body.SetLinearDamping(args.damping);
        body.friction = args.damping;
    }

    setStatic(args, util) {
        const target = util.target;
        let body = bodies[util.target.id];
        if (!body) {
            body = this.setPhysicsFor(target);
        }
        const argsStatic = args.static === "static" ? true : false;
        if (body.isStatic === argsStatic) {
            return;
        }
        body.SetLinearVelocity(new b2Vec2(0, 0));
        body.SetAngularVelocity(0);
        switch (args.static) {
            case "free":
                body.SetType(b2Body.b2_dynamicBody);
                break;
            case "static":
                body.SetType(b2Body.b2_staticBody);
                break;
        }
        body.isStatic = args.static === "static";
        const pos = new b2Vec2(target.x / zoom, target.y / zoom);
        body.SetPositionAndAngle(pos, (90 - target.direction) * toRad);
    }

    getTouching(args, util) {
        const target = util.target;
        const body = bodies[target.id];
        if (!body) {
            return "";
        }
        const where = args.where;
        let touching = "";
        const contacts = body.GetContactList();
        for (let ce = contacts; ce; ce = ce.next) {
            // noinspection JSBitwiseOperatorUsage
            if (ce.contact.m_flags & b2Contact.e_islandFlag) {
                continue;
            }
            if (
                ce.contact.IsSensor() === true ||
                ce.contact.IsEnabled() === false ||
                ce.contact.IsTouching() === false
            ) {
                continue;
            }
            const contact = ce.contact;
            const fixtureA = contact.GetFixtureA();
            const fixtureB = contact.GetFixtureB();
            const bodyA = fixtureA.GetBody();
            const bodyB = fixtureB.GetBody();

            // const myFix = touchingB ? fixtureA : fixtureB;

            const touchingB = bodyA === body;
            if (where !== "any") {
                const man = new Box2D.Collision.b2WorldManifold();
                contact.GetWorldManifold(man);

                if (where === "feet") {
                    const fixture = body.GetFixtureList();
                    const y = man.m_points[0].y;
                    if (
                        y >
                        fixture.m_aabb.lowerBound.y * 0.75 +
                            fixture.m_aabb.upperBound.y * 0.25
                    ) {
                        continue;
                    }
                }
            }

            const other = touchingB ? bodyB : bodyA;
            const uid = other.uid;
            const target2 = uid
                ? this.runtime.getTargetById(uid)
                : this.runtime.getTargetForStage();
            if (target2) {
                const name = target2.sprite.name;
                if (touching.length === 0) {
                    touching = name;
                } else {
                    touching += `,${name}`;
                }
            }
        }
        return touching;
    }

    loadSnapshot(snapshot) {
        this.reset();
        if (!snapshot || !snapshot.bodies) {
            return;
        }
        const _bodies = snapshot.bodies;

        const _stageBodies = snapshot.stageBodies;

        this.runtime.targets.forEach((target) => {
            const body = _bodies[target.id];
            if (body) {
                this.setPhysicsFor(target, {
                    isStatic: body.isStatic,
                    isWall: body.isWall,
                    allowScreenwrap: body.allowScreenwrap,
                    kickStrength: body.kickStrength,
                    isHidden: body.isHidden,
                });
                const b = bodies[target.id];
                if (!b) {
                    return;
                }
                b.SetPosition(body.position);
                b.SetAngle(body.angle);
                b.SetLinearVelocity(body.linearVelocity);
                b.SetAngularVelocity(body.angularVelocity);
                b.SetFixedRotation(body.fixedRotation);
                b.SetType(body.type);
            }
        });

        _stageBodies.forEach((body) => {
            const b = _placeBody(
                null,
                body.position.x,
                body.position.y,
                body.angle
            );
            stageBodies.push(b);
        });
    }

    saveSnapshot() {
        this._checkMoved();
        const _bodies = serializeBodies(bodies);
        const _stageBodies = serializeStageBodies(stageBodies);
        return {
            bodies: _bodies,
            stageBodies: _stageBodies,
        };
    }

    setKicker(target, strength) {
        const body = bodies[target.id];
        if (body) {
            body.kickStrength = strength;
        }
    }
}

function serializeBodies(bodies) {
    const _bodies = {};
    for (const key in bodies) {
        const body = bodies[key];
        _bodies[key] = {
            position: body.GetPosition(),
            angle: body.GetAngle(),
            linearVelocity: body.GetLinearVelocity(),
            angularVelocity: body.GetAngularVelocity(),
            fixedRotation: body.IsFixedRotation(),
            type: body.GetType(),
            isHidden: body.isHidden,
            friction: body.friction,
            isStatic: body.isStatic,
            isWall: body.isWall,
            allowScreenwrap: body.allowScreenwrap,
            kickStrength: body.kickStrength,
        };
    }
    return _bodies;
}

function serializeStageBodies(stageBodies) {
    const _stageBodies = [];
    for (const key in stageBodies) {
        const body = stageBodies[key];
        _stageBodies.push({
            position: body.GetPosition(),
            angle: body.GetAngle(),
        });
    }
    return _stageBodies;
}
class MyContactFilter extends Box2D.Dynamics.b2ContactFilter {
    ShouldCollide(fixtureA, fixtureB) {
        const bodyA = fixtureA.GetBody();
        const bodyB = fixtureB.GetBody();

        if (bodyA.allowScreenwrap && bodyB.isStage) {
            return false;
        }
        if (bodyB.allowScreenwrap && bodyA.isStage) {
            return false;
        }
        return super.ShouldCollide(fixtureA, fixtureB);
    }

    whenCollide(args, util) {
        const target = util.target;
        const otherName = args.sprite;

        const { TARGET, OTHER } = util.stackFrame;
        if (TARGET !== target.id) return false;

        if (otherName === "any") return true;

        const otherTarget = this.runtime.getTargetById(OTHER);
        return otherTarget && otherTarget.sprite.name === otherName;
    }
}

class MyContactListener extends Box2D.Dynamics.b2ContactListener {
    constructor(runtime) {
        super();
        this.runtime = runtime;
        this.frameCollisions = new Set(); // collisions found this frame
        this.activeCollisions = new Set(); // collisions currently active
    }

    _getPairKey(idA, idB) {
        return idA < idB ? `${idA}|${idB}` : `${idB}|${idA}`;
    }

    // Called during physics step; store active collisions found this frame
    BeginContact(contact) {
        const bodyA = contact.GetFixtureA().GetBody();
        const bodyB = contact.GetFixtureB().GetBody();
        if (!bodyA || !bodyB) return;

        const idA = bodyA.targetId;
        const idB = bodyB.targetId;
        if (!idA || !idB) return;

        const key = this._getPairKey(idA, idB);
        this.frameCollisions.add(key);
    }

    // Should be called once per frame after Step()
    finalizeCollisions() {
        // Add newly detected collisions
        for (const key of this.frameCollisions) {
            if (!this.activeCollisions.has(key)) {
                this.activeCollisions.add(key);

                const [idA, idB] = key.split("|");
                const targetA = this.runtime.getTargetById(idA);
                const targetB = this.runtime.getTargetById(idB);
                if (!targetA || !targetB) continue;

                if (this.runtime.triggerCollisionSound) {
                    this.runtime.triggerCollisionSound(targetA, targetB);
                }

                this.runtime.startHats("physics_whenCollide", {
                    TARGET: targetA.id,
                    OTHER: targetB.id,
                });
                this.runtime.startHats("physics_whenCollide", {
                    TARGET: targetB.id,
                    OTHER: targetA.id,
                });
            }
        }

        // Remove collisions no longer present
        for (const key of this.activeCollisions) {
            if (!this.frameCollisions.has(key)) {
                this.activeCollisions.delete(key);
            }
        }

        // Clear for next frame
        this.frameCollisions.clear();
    }

    PostSolve(contact, impulse) {
        const bodyA = contact.GetFixtureA().GetBody();
        const bodyB = contact.GetFixtureB().GetBody();
        if (!bodyA || !bodyB) return;

        const worldManifold = new Box2D.Collision.b2WorldManifold();
        contact.GetWorldManifold(worldManifold);
        const normal = worldManifold.m_normal;

        if (bodyA.kickStrength > 0) {
            const kickDir = new Box2D.Common.Math.b2Vec2(normal.x, normal.y);
            this.applyKick(bodyB, bodyA.kickStrength, kickDir);
        }
        if (bodyB.kickStrength > 0) {
            const kickDir = new Box2D.Common.Math.b2Vec2(-normal.x, -normal.y);
            this.applyKick(bodyA, bodyB.kickStrength, kickDir);
        }
    }

    applyKick(body, strength, direction) {
        direction.Normalize();
        const vel = body.GetLinearVelocity();
        const newVel = new Box2D.Common.Math.b2Vec2(
            vel.x + direction.x * strength,
            vel.y + direction.y * strength
        );
        body.SetLinearVelocity(newVel);
    }
}

function updateCollisionFilter(body, categoryBits, maskBits) {
    for (
        let fixture = body.GetFixtureList();
        fixture;
        fixture = fixture.GetNext()
    ) {
        let filter = fixture.GetFilterData();
        filter.categoryBits = categoryBits;
        filter.maskBits = maskBits;
        fixture.SetFilterData(filter);
    }

    let contactEdge = body.GetContactList();
    while (contactEdge) {
        let contact = contactEdge.contact;
        contact.FlagForFiltering();
        contactEdge = contactEdge.next;
    }
}

function scratchPositionToBox2DPosition(position) {
    if (!position) {
        return null;
    }
    const { x, y } = position;
    return new b2Vec2(x / zoom, y / zoom);
}

module.exports = Scratch3Physics;
