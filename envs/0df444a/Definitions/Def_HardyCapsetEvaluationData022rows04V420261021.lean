-- Prove2me | Definitions.Def_HardyCapsetEvaluationData022rows04V420261021
-- name    : HardyCapsetEvaluationData022rows04V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T01:57:38.548108+00:00
-- url     : https://prove2.me/theorems/9d02dc74-9b77-40a3-b308-42131009d6c9
-- title:
--   HardyCapsetEvaluationData022rows04V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er022_256 : Row := { vars := #[164, 586, 384, 599], coeff := #[1, 1, 1, 1], bound := 1, weight := 592486, edges := #[⟨0, 1, 312⟩, ⟨0, 2, 510⟩, ⟨0, 3, 321⟩, ⟨1, 2, 153⟩, ⟨1, 3, 501⟩, ⟨2, 3, 163⟩], triples := #[] }
def er022_257 : Row := { vars := #[165, 389, 376, 594], coeff := #[1, 1, 1, 1], bound := 1, weight := 382347, edges := #[⟨0, 1, 503⟩, ⟨0, 2, 494⟩, ⟨0, 3, 327⟩, ⟨1, 2, 318⟩, ⟨1, 3, 164⟩, ⟨2, 3, 154⟩], triples := #[] }
def er022_258 : Row := { vars := #[166, 392, 564, 398], coeff := #[1, 1, 1, 1], bound := 1, weight := 16714, edges := #[⟨0, 1, 472⟩, ⟨0, 2, 336⟩, ⟨0, 3, 470⟩, ⟨1, 2, 146⟩, ⟨1, 3, 347⟩, ⟨2, 3, 166⟩], triples := #[] }
def er022_259 : Row := { vars := #[166, 302, 431], coeff := #[1, 1, 1], bound := 1, weight := 607077, edges := #[⟨0, 1, 363⟩, ⟨0, 2, 247⟩, ⟨1, 2, 163⟩], triples := #[] }
def er022_260 : Row := { vars := #[166, 584, 384, 597], coeff := #[1, 1, 1, 1], bound := 1, weight := 334080, edges := #[⟨0, 1, 312⟩, ⟨0, 2, 506⟩, ⟨0, 3, 321⟩, ⟨1, 2, 156⟩, ⟨1, 3, 497⟩, ⟨2, 3, 166⟩], triples := #[] }
def er022_261 : Row := { vars := #[167, 430, 302], coeff := #[1, 1, 1], bound := 1, weight := 108467, edges := #[⟨0, 1, 247⟩, ⟨0, 2, 361⟩, ⟨1, 2, 164⟩], triples := #[] }
def er022_262 : Row := { vars := #[167, 234, 381], coeff := #[1, 1, 1], bound := 1, weight := 459118, edges := #[⟨0, 1, 406⟩, ⟨0, 2, 493⟩, ⟨1, 2, 281⟩], triples := #[] }
def er022_263 : Row := { vars := #[167, 238, 494], coeff := #[1, 1, 1], bound := 1, weight := 144237, edges := #[⟨0, 1, 407⟩, ⟨0, 2, 201⟩, ⟨1, 2, 164⟩], triples := #[] }
def er022_264 : Row := { vars := #[168, 176, 196, 214], coeff := #[1, 1, 1, 1], bound := 1, weight := 427153, edges := #[⟨0, 1, 178⟩, ⟨0, 2, 145⟩, ⟨0, 3, 152⟩, ⟨1, 2, 165⟩, ⟨1, 3, 134⟩, ⟨2, 3, 184⟩], triples := #[] }
def er022_265 : Row := { vars := #[169, 433, 282], coeff := #[1, 1, 1], bound := 1, weight := 151451, edges := #[⟨0, 1, 291⟩, ⟨0, 2, 407⟩, ⟨1, 2, 32⟩], triples := #[] }
def er022_266 : Row := { vars := #[169, 177, 294, 474], coeff := #[1, 1, 1, 1], bound := 1, weight := 670708, edges := #[⟨0, 1, 179⟩, ⟨0, 2, 408⟩, ⟨0, 3, 247⟩, ⟨1, 2, 406⟩, ⟨1, 3, 251⟩, ⟨2, 3, 52⟩], triples := #[] }
def er022_267 : Row := { vars := #[169, 241, 474], coeff := #[1, 1, 1], bound := 1, weight := 177843, edges := #[⟨0, 1, 451⟩, ⟨0, 2, 247⟩, ⟨1, 2, 32⟩], triples := #[] }
def er022_268 : Row := { vars := #[170, 184, 390, 588], coeff := #[1, 1, 1, 1], bound := 1, weight := 588859, edges := #[⟨0, 1, 172⟩, ⟨0, 2, 460⟩, ⟨0, 3, 305⟩, ⟨1, 2, 462⟩, ⟨1, 3, 301⟩, ⟨2, 3, 190⟩], triples := #[] }
def er022_269 : Row := { vars := #[172, 257, 490], coeff := #[1, 1, 1], bound := 1, weight := 38711, edges := #[⟨0, 1, 440⟩, ⟨0, 2, 248⟩, ⟨1, 2, 33⟩], triples := #[] }
def er022_270 : Row := { vars := #[172, 287, 421], coeff := #[1, 1, 1], bound := 1, weight := 300154, edges := #[⟨0, 1, 406⟩, ⟨0, 2, 278⟩, ⟨1, 2, 13⟩], triples := #[] }
def er022_271 : Row := { vars := #[172, 552, 352, 341], coeff := #[1, 1, 1, 1], bound := 1, weight := 313218, edges := #[⟨0, 1, 350⟩, ⟨0, 2, 360⟩, ⟨0, 3, 352⟩, ⟨1, 2, 5⟩, ⟨1, 3, 30⟩, ⟨2, 3, 286⟩], triples := #[] }
def er022_272 : Row := { vars := #[172, 478, 72], coeff := #[1, 1, 1], bound := 1, weight := 184205, edges := #[⟨0, 1, 247⟩, ⟨0, 2, 71⟩, ⟨1, 2, 323⟩], triples := #[] }
def er022_273 : Row := { vars := #[173, 418, 304], coeff := #[1, 1, 1], bound := 1, weight := 22172, edges := #[⟨0, 1, 279⟩, ⟨0, 2, 397⟩, ⟨1, 2, 144⟩], triples := #[] }
def er022_274 : Row := { vars := #[173, 316, 450], coeff := #[1, 1, 1], bound := 1, weight := 378933, edges := #[⟨0, 1, 398⟩, ⟨0, 2, 280⟩, ⟨1, 2, 167⟩], triples := #[] }
def er022_275 : Row := { vars := #[174, 530, 536, 366], coeff := #[1, 1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 196⟩, ⟨0, 2, 212⟩, ⟨0, 3, 496⟩, ⟨1, 2, 452⟩, ⟨1, 3, 23⟩, ⟨2, 3, 10⟩], triples := #[] }
def er022_276 : Row := { vars := #[174, 531, 488], coeff := #[1, 1, 1], bound := 1, weight := 600833, edges := #[⟨0, 1, 192⟩, ⟨0, 2, 248⟩, ⟨1, 2, 495⟩], triples := #[] }
def er022_277 : Row := { vars := #[175, 303, 414], coeff := #[1, 1, 1], bound := 1, weight := 557546, edges := #[⟨0, 1, 396⟩, ⟨0, 2, 278⟩, ⟨1, 2, 139⟩], triples := #[] }
def er022_278 : Row := { vars := #[175, 234, 500], coeff := #[1, 1, 1], bound := 1, weight := 271847, edges := #[⟨0, 1, 449⟩, ⟨0, 2, 241⟩, ⟨1, 2, 154⟩], triples := #[] }
def er022_279 : Row := { vars := #[176, 218, 493], coeff := #[1, 1, 1], bound := 1, weight := 340350, edges := #[⟨0, 1, 457⟩, ⟨0, 2, 241⟩, ⟨1, 2, 145⟩], triples := #[] }
def er022_280 : Row := { vars := #[178, 230, 499], coeff := #[1, 1, 1], bound := 1, weight := 483879, edges := #[⟨0, 1, 453⟩, ⟨0, 2, 238⟩, ⟨1, 2, 162⟩], triples := #[] }
def er022_281 : Row := { vars := #[180, 287, 453], coeff := #[1, 1, 1], bound := 1, weight := 8319, edges := #[⟨0, 1, 411⟩, ⟨0, 2, 278⟩, ⟨1, 2, 23⟩], triples := #[] }
def er022_282 : Row := { vars := #[180, 341, 352, 546], coeff := #[1, 1, 1, 1], bound := 1, weight := 20468, edges := #[⟨0, 1, 372⟩, ⟨0, 2, 356⟩, ⟨0, 3, 350⟩, ⟨1, 2, 286⟩, ⟨1, 3, 2⟩, ⟨2, 3, 20⟩], triples := #[] }
def er022_283 : Row := { vars := #[181, 422, 317], coeff := #[1, 1, 1], bound := 1, weight := 557835, edges := #[⟨0, 1, 289⟩, ⟨0, 2, 396⟩, ⟨1, 2, 157⟩], triples := #[] }
def er022_284 : Row := { vars := #[181, 341, 352, 457], coeff := #[1, 1, 1, 1], bound := 1, weight := 271557, edges := #[⟨0, 1, 375⟩, ⟨0, 2, 359⟩, ⟨0, 3, 275⟩, ⟨1, 2, 286⟩, ⟨1, 3, 136⟩, ⟨2, 3, 154⟩], triples := #[] }
def er022_285 : Row := { vars := #[182, 339, 546, 350], coeff := #[1, 1, 1, 1], bound := 1, weight := 28786, edges := #[⟨0, 1, 372⟩, ⟨0, 2, 346⟩, ⟨0, 3, 356⟩, ⟨1, 2, 10⟩, ⟨1, 3, 282⟩, ⟨2, 3, 23⟩], triples := #[] }
def er022_286 : Row := { vars := #[183, 531, 271, 537], coeff := #[1, 1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 215⟩, ⟨0, 2, 421⟩, ⟨0, 3, 203⟩, ⟨1, 2, 167⟩, ⟨1, 3, 452⟩, ⟨2, 3, 157⟩], triples := #[] }
def er022_287 : Row := { vars := #[183, 339, 457, 350], coeff := #[1, 1, 1, 1], bound := 1, weight := 580531, edges := #[⟨0, 1, 375⟩, ⟨0, 2, 271⟩, ⟨0, 3, 359⟩, ⟨1, 2, 144⟩, ⟨1, 3, 282⟩, ⟨2, 3, 157⟩], triples := #[] }
def er022_288 : Row := { vars := #[188, 532, 545, 366], coeff := #[1, 1, 1, 1], bound := 1, weight := 69728, edges := #[⟨0, 1, 200⟩, ⟨0, 2, 212⟩, ⟨0, 3, 510⟩, ⟨1, 2, 446⟩, ⟨1, 3, 20⟩, ⟨2, 3, 30⟩], triples := #[] }
def er022_289 : Row := { vars := #[188, 538, 539, 366], coeff := #[1, 1, 1, 1], bound := 1, weight := 531106, edges := #[⟨0, 1, 192⟩, ⟨0, 2, 196⟩, ⟨0, 3, 510⟩, ⟨1, 2, 446⟩, ⟨1, 3, 2⟩, ⟨2, 3, 5⟩], triples := #[] }
def er022_290 : Row := { vars := #[188, 340, 353, 558], coeff := #[1, 1, 1, 1], bound := 1, weight := 240675, edges := #[⟨0, 1, 360⟩, ⟨0, 2, 372⟩, ⟨0, 3, 350⟩, ⟨1, 2, 286⟩, ⟨1, 3, 20⟩, ⟨2, 3, 30⟩], triples := #[] }
def er022_291 : Row := { vars := #[189, 532, 538, 265], coeff := #[1, 1, 1, 1], bound := 1, weight := 176261, edges := #[⟨0, 1, 203⟩, ⟨0, 2, 195⟩, ⟨0, 3, 425⟩, ⟨1, 2, 456⟩, ⟨1, 3, 139⟩, ⟨2, 3, 164⟩], triples := #[] }
def er022_292 : Row := { vars := #[189, 340, 353, 469], coeff := #[1, 1, 1, 1], bound := 1, weight := 117353, edges := #[⟨0, 1, 363⟩, ⟨0, 2, 375⟩, ⟨0, 3, 275⟩, ⟨1, 2, 286⟩, ⟨1, 3, 154⟩, ⟨2, 3, 164⟩], triples := #[] }
def er022_293 : Row := { vars := #[190, 290, 445], coeff := #[1, 1, 1], bound := 1, weight := 620138, edges := #[⟨0, 1, 406⟩, ⟨0, 2, 289⟩, ⟨1, 2, 5⟩], triples := #[] }
def er022_294 : Row := { vars := #[191, 530, 507], coeff := #[1, 1, 1], bound := 1, weight := 276924, edges := #[⟨0, 1, 203⟩, ⟨0, 2, 241⟩, ⟨1, 2, 420⟩], triples := #[] }
def er022_295 : Row := { vars := #[191, 338, 351, 469], coeff := #[1, 1, 1, 1], bound := 1, weight := 57226, edges := #[⟨0, 1, 363⟩, ⟨0, 2, 375⟩, ⟨0, 3, 271⟩, ⟨1, 2, 282⟩, ⟨1, 3, 157⟩, ⟨2, 3, 167⟩], triples := #[] }
def er022_296 : Row := { vars := #[192, 200, 372, 576], coeff := #[1, 1, 1, 1], bound := 1, weight := 634083, edges := #[⟨0, 1, 190⟩, ⟨0, 2, 461⟩, ⟨0, 3, 302⟩, ⟨1, 2, 465⟩, ⟨1, 3, 300⟩, ⟨2, 3, 172⟩], triples := #[] }
def er022_297 : Row := { vars := #[193, 201, 135, 121], coeff := #[1, 1, 1, 1], bound := 1, weight := 190820, edges := #[⟨0, 1, 191⟩, ⟨0, 2, 61⟩, ⟨0, 3, 43⟩, ⟨1, 2, 48⟩, ⟨1, 3, 68⟩, ⟨2, 3, 125⟩], triples := #[] }
def er022_298 : Row := { vars := #[193, 201, 8, 26], coeff := #[1, 1, 1, 1], bound := 1, weight := 101815, edges := #[⟨0, 1, 191⟩, ⟨0, 2, 77⟩, ⟨0, 3, 95⟩, ⟨1, 2, 102⟩, ⟨1, 3, 82⟩, ⟨2, 3, 16⟩], triples := #[] }
def er022_299 : Row := { vars := #[193, 433, 6], coeff := #[1, 1, 1], bound := 1, weight := 80585, edges := #[⟨0, 1, 271⟩, ⟨0, 2, 85⟩, ⟨1, 2, 241⟩], triples := #[] }
def er022_300 : Row := { vars := #[193, 211, 135, 137], coeff := #[1, 1, 1, 1], bound := 1, weight := 242141, edges := #[⟨0, 1, 185⟩, ⟨0, 2, 61⟩, ⟨0, 3, 58⟩, ⟨1, 2, 71⟩, ⟨1, 3, 68⟩, ⟨2, 3, 131⟩], triples := #[] }
def er022_301 : Row := { vars := #[195, 209, 510, 324], coeff := #[1, 1, 1, 1], bound := 1, weight := 506266, edges := #[⟨0, 1, 185⟩, ⟨0, 2, 194⟩, ⟨0, 3, 374⟩, ⟨1, 2, 202⟩, ⟨1, 3, 358⟩, ⟨2, 3, 118⟩], triples := #[] }
def er022_302 : Row := { vars := #[196, 280, 449], coeff := #[1, 1, 1], bound := 1, weight := 152930, edges := #[⟨0, 1, 408⟩, ⟨0, 2, 258⟩, ⟨1, 2, 69⟩], triples := #[] }
def er022_303 : Row := { vars := #[196, 461, 229], coeff := #[1, 1, 1], bound := 1, weight := 276924, edges := #[⟨0, 1, 246⟩, ⟨0, 2, 416⟩, ⟨1, 2, 49⟩], triples := #[] }
def er022_304 : Row := { vars := #[196, 466, 241], coeff := #[1, 1, 1], bound := 1, weight := 142994, edges := #[⟨0, 1, 251⟩, ⟨0, 2, 427⟩, ⟨1, 2, 59⟩], triples := #[] }
def er022_305 : Row := { vars := #[198, 512, 464], coeff := #[1, 1, 1], bound := 1, weight := 681370, edges := #[⟨0, 1, 198⟩, ⟨0, 2, 251⟩, ⟨1, 2, 485⟩], triples := #[] }
def er022_306 : Row := { vars := #[198, 513, 524, 361], coeff := #[1, 1, 1, 1], bound := 1, weight := 100001, edges := #[⟨0, 1, 194⟩, ⟨0, 2, 202⟩, ⟨0, 3, 483⟩, ⟨1, 2, 419⟩, ⟨1, 3, 69⟩, ⟨2, 3, 49⟩], triples := #[] }
def er022_307 : Row := { vars := #[202, 200, 312, 504], coeff := #[1, 1, 1, 1], bound := 1, weight := 360830, edges := #[⟨0, 1, 184⟩, ⟨0, 2, 387⟩, ⟨0, 3, 227⟩, ⟨1, 2, 386⟩, ⟨1, 3, 226⟩, ⟨2, 3, 100⟩], triples := #[] }
def er022_308 : Row := { vars := #[204, 515, 361, 521], coeff := #[1, 1, 1, 1], bound := 1, weight := 198577, edges := #[⟨0, 1, 214⟩, ⟨0, 2, 477⟩, ⟨0, 3, 202⟩, ⟨1, 2, 66⟩, ⟨1, 3, 433⟩, ⟨2, 3, 56⟩], triples := #[] }
def er022_309 : Row := { vars := #[204, 269, 453], coeff := #[1, 1, 1], bound := 1, weight := 285111, edges := #[⟨0, 1, 411⟩, ⟨0, 2, 256⟩, ⟨1, 2, 59⟩], triples := #[] }
def er022_310 : Row := { vars := #[204, 526, 527, 361], coeff := #[1, 1, 1, 1], bound := 1, weight := 297684, edges := #[⟨0, 1, 198⟩, ⟨0, 2, 194⟩, ⟨0, 3, 477⟩, ⟨1, 2, 433⟩, ⟨1, 3, 41⟩, ⟨2, 3, 38⟩], triples := #[] }
def er022_311 : Row := { vars := #[205, 323, 481, 329], coeff := #[1, 1, 1, 1], bound := 1, weight := 215735, edges := #[⟨0, 1, 373⟩, ⟨0, 2, 285⟩, ⟨0, 3, 361⟩, ⟨1, 2, 163⟩, ⟨1, 3, 273⟩, ⟨2, 3, 153⟩], triples := #[] }
def er022_312 : Row := { vars := #[206, 513, 361, 519], coeff := #[1, 1, 1, 1], bound := 1, weight := 403740, edges := #[⟨0, 1, 214⟩, ⟨0, 2, 473⟩, ⟨0, 3, 202⟩, ⟨1, 2, 69⟩, ⟨1, 3, 429⟩, ⟨2, 3, 59⟩], triples := #[] }
def er022_313 : Row := { vars := #[206, 278, 429], coeff := #[1, 1, 1], bound := 1, weight := 517445, edges := #[⟨0, 1, 407⟩, ⟨0, 2, 258⟩, ⟨1, 2, 38⟩], triples := #[] }
def er022_314 : Row := { vars := #[206, 321, 553, 327], coeff := #[1, 1, 1, 1], bound := 1, weight := 78816, edges := #[⟨0, 1, 374⟩, ⟨0, 2, 313⟩, ⟨0, 3, 362⟩, ⟨1, 2, 69⟩, ⟨1, 3, 269⟩, ⟨2, 3, 59⟩], triples := #[] }
def er022_315 : Row := { vars := #[208, 210, 517, 325], coeff := #[1, 1, 1, 1], bound := 1, weight := 404214, edges := #[⟨0, 1, 190⟩, ⟨0, 2, 197⟩, ⟨0, 3, 357⟩, ⟨1, 2, 193⟩, ⟨1, 3, 353⟩, ⟨2, 3, 113⟩], triples := #[] }
def er022_316 : Row := { vars := #[208, 210, 498, 306], coeff := #[1, 1, 1, 1], bound := 1, weight := 76676, edges := #[⟨0, 1, 190⟩, ⟨0, 2, 227⟩, ⟨0, 3, 387⟩, ⟨1, 2, 226⟩, ⟨1, 3, 386⟩, ⟨2, 3, 88⟩], triples := #[] }
def er022_317 : Row := { vars := #[209, 229, 6], coeff := #[1, 1, 1], bound := 1, weight := 120516, edges := #[⟨0, 1, 421⟩, ⟨0, 2, 95⟩, ⟨1, 2, 396⟩], triples := #[] }
def er022_318 : Row := { vars := #[212, 322, 328, 547], coeff := #[1, 1, 1, 1], bound := 1, weight := 353029, edges := #[⟨0, 1, 362⟩, ⟨0, 2, 354⟩, ⟨0, 3, 317⟩, ⟨1, 2, 273⟩, ⟨1, 3, 41⟩, ⟨2, 3, 66⟩], triples := #[] }
def er022_319 : Row := { vars := #[214, 512, 518, 355], coeff := #[1, 1, 1, 1], bound := 1, weight := 142123, edges := #[⟨0, 1, 202⟩, ⟨0, 2, 194⟩, ⟨0, 3, 473⟩, ⟨1, 2, 429⟩, ⟨1, 3, 49⟩, ⟨2, 3, 69⟩], triples := #[] }
end HardyCapset20261020.Cert


