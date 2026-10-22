-- Prove2me | Definitions.Def_HardyCapsetEvaluationData010rows04V420261021
-- name    : HardyCapsetEvaluationData010rows04V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T01:26:04.669526+00:00
-- url     : https://prove2.me/theorems/5ef21c45-4c41-4eeb-956a-5d336a4eb09b
-- title:
--   HardyCapsetEvaluationData010rows04V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er010_256 : Row := { vars := #[107, 290, 121, 494], coeff := #[1, 1, 1, 1], bound := 1, weight := 220760, edges := #[⟨0, 1, 425⟩, ⟨0, 2, 21⟩, ⟨0, 3, 265⟩, ⟨1, 2, 366⟩, ⟨1, 3, 95⟩, ⟨2, 3, 206⟩], triples := #[] }
def er010_257 : Row := { vars := #[107, 117, 519, 325], coeff := #[1, 1, 1, 1], bound := 1, weight := 389251, edges := #[⟨0, 1, 123⟩, ⟨0, 2, 290⟩, ⟨0, 3, 454⟩, ⟨1, 2, 284⟩, ⟨1, 3, 448⟩, ⟨2, 3, 120⟩], triples := #[] }
def er010_258 : Row := { vars := #[109, 143, 293, 570], coeff := #[1, 1, 1, 1], bound := 1, weight := 201222, edges := #[⟨0, 1, 31⟩, ⟨0, 2, 431⟩, ⟨0, 3, 205⟩, ⟨1, 2, 382⟩, ⟨1, 3, 340⟩, ⟨2, 3, 61⟩], triples := #[] }
def er010_259 : Row := { vars := #[109, 404, 437], coeff := #[1, 1, 1], bound := 1, weight := 44537, edges := #[⟨0, 1, 318⟩, ⟨0, 2, 327⟩, ⟨1, 2, 366⟩], triples := #[] }
def er010_260 : Row := { vars := #[109, 412, 441], coeff := #[1, 1, 1], bound := 1, weight := 198964, edges := #[⟨0, 1, 314⟩, ⟨0, 2, 323⟩, ⟨1, 2, 370⟩], triples := #[] }
def er010_261 : Row := { vars := #[109, 413, 440], coeff := #[1, 1, 1], bound := 1, weight := 366442, edges := #[⟨0, 1, 313⟩, ⟨0, 2, 324⟩, ⟨1, 2, 370⟩], triples := #[] }
def er010_262 : Row := { vars := #[110, 419, 578], coeff := #[1, 1, 1], bound := 1, weight := 403793, edges := #[⟨0, 1, 316⟩, ⟨0, 2, 216⟩, ⟨1, 2, 445⟩], triples := #[] }
def er010_263 : Row := { vars := #[110, 439, 352], coeff := #[1, 1, 1], bound := 1, weight := 94941, edges := #[⟨0, 1, 326⟩, ⟨0, 2, 393⟩, ⟨1, 2, 103⟩], triples := #[] }
def er010_264 : Row := { vars := #[111, 408, 280], coeff := #[1, 1, 1], bound := 1, weight := 490600, edges := #[⟨0, 1, 320⟩, ⟨0, 2, 423⟩, ⟨1, 2, 135⟩], triples := #[] }
def er010_265 : Row := { vars := #[111, 232, 363], coeff := #[1, 1, 1], bound := 1, weight := 396822, edges := #[⟨0, 1, 486⟩, ⟨0, 2, 371⟩, ⟨1, 2, 283⟩], triples := #[] }
def er010_266 : Row := { vars := #[112, 405, 435], coeff := #[1, 1, 1], bound := 1, weight := 456807, edges := #[⟨0, 1, 315⟩, ⟨0, 2, 328⟩, ⟨1, 2, 369⟩], triples := #[] }
def er010_267 : Row := { vars := #[113, 396, 282], coeff := #[1, 1, 1], bound := 1, weight := 203765, edges := #[⟨0, 1, 318⟩, ⟨0, 2, 421⟩, ⟨1, 2, 144⟩], triples := #[] }
def er010_268 : Row := { vars := #[113, 404, 278], coeff := #[1, 1, 1], bound := 1, weight := 257145, edges := #[⟨0, 1, 314⟩, ⟨0, 2, 425⟩, ⟨1, 2, 144⟩], triples := #[] }
def er010_269 : Row := { vars := #[113, 278, 125, 565], coeff := #[1, 1, 1, 1], bound := 1, weight := 181415, edges := #[⟨0, 1, 425⟩, ⟨0, 2, 3⟩, ⟨0, 3, 205⟩, ⟨1, 2, 382⟩, ⟨1, 3, 51⟩, ⟨2, 3, 346⟩], triples := #[] }
def er010_270 : Row := { vars := #[113, 282, 121, 486], coeff := #[1, 1, 1, 1], bound := 1, weight := 141686, edges := #[⟨0, 1, 421⟩, ⟨0, 2, 11⟩, ⟨0, 3, 261⟩, ⟨1, 2, 382⟩, ⟨1, 3, 74⟩, ⟨2, 3, 222⟩], triples := #[] }
def er010_271 : Row := { vars := #[115, 256, 133, 460], coeff := #[1, 1, 1, 1], bound := 1, weight := 350841, edges := #[⟨0, 1, 466⟩, ⟨0, 2, 34⟩, ⟨0, 3, 306⟩, ⟨1, 2, 457⟩, ⟨1, 3, 32⟩, ⟨2, 3, 297⟩], triples := #[] }
def er010_272 : Row := { vars := #[115, 228, 363], coeff := #[1, 1, 1], bound := 1, weight := 273937, edges := #[⟨0, 1, 486⟩, ⟨0, 2, 367⟩, ⟨1, 2, 287⟩], triples := #[] }
def er010_273 : Row := { vars := #[117, 293, 135, 570], coeff := #[1, 1, 1, 1], bound := 1, weight := 305621, edges := #[⟨0, 1, 435⟩, ⟨0, 2, 31⟩, ⟨0, 3, 209⟩, ⟨1, 2, 378⟩, ⟨1, 3, 61⟩, ⟨2, 3, 336⟩], triples := #[] }
def er010_274 : Row := { vars := #[118, 403, 578], coeff := #[1, 1, 1], bound := 1, weight := 243033, edges := #[⟨0, 1, 316⟩, ⟨0, 2, 220⟩, ⟨1, 2, 441⟩], triples := #[] }
def er010_275 : Row := { vars := #[118, 231, 471], coeff := #[1, 1, 1], bound := 1, weight := 361431, edges := #[⟨0, 1, 482⟩, ⟨0, 2, 341⟩, ⟨1, 2, 21⟩], triples := #[] }
def er010_276 : Row := { vars := #[119, 455, 123, 251], coeff := #[1, 1, 1, 1], bound := 1, weight := 90613, edges := #[⟨0, 1, 304⟩, ⟨0, 2, 6⟩, ⟨0, 3, 464⟩, ⟨1, 2, 293⟩, ⟨1, 3, 15⟩, ⟨2, 3, 453⟩], triples := #[] }
def er010_277 : Row := { vars := #[119, 455, 123, 327], coeff := #[1, 1, 1, 1], bound := 1, weight := 152361, edges := #[⟨0, 1, 304⟩, ⟨0, 2, 6⟩, ⟨0, 3, 445⟩, ⟨1, 2, 293⟩, ⟨1, 3, 142⟩, ⟨2, 3, 392⟩], triples := #[] }
def er010_278 : Row := { vars := #[120, 138, 262, 466], coeff := #[1, 1, 1, 1], bound := 1, weight := 175024, edges := #[⟨0, 1, 140⟩, ⟨0, 2, 433⟩, ⟨0, 3, 273⟩, ⟨1, 2, 419⟩, ⟨1, 3, 259⟩, ⟨2, 3, 36⟩], triples := #[] }
def er010_279 : Row := { vars := #[120, 590, 367], coeff := #[1, 1, 1], bound := 1, weight := 373018, edges := #[⟨0, 1, 324⟩, ⟨0, 2, 504⟩, ⟨1, 2, 147⟩], triples := #[] }
def er010_280 : Row := { vars := #[121, 388, 569], coeff := #[1, 1, 1], bound := 1, weight := 33729, edges := #[⟨0, 1, 482⟩, ⟨0, 2, 347⟩, ⟨1, 2, 146⟩], triples := #[] }
def er010_281 : Row := { vars := #[121, 388, 490], coeff := #[1, 1, 1], bound := 1, weight := 298185, edges := #[⟨0, 1, 482⟩, ⟨0, 2, 218⟩, ⟨1, 2, 10⟩], triples := #[] }
def er010_282 : Row := { vars := #[121, 392, 494], coeff := #[1, 1, 1], bound := 1, weight := 305642, edges := #[⟨0, 1, 476⟩, ⟨0, 2, 206⟩, ⟨1, 2, 23⟩], triples := #[] }
def er010_283 : Row := { vars := #[122, 140, 488, 306], coeff := #[1, 1, 1, 1], bound := 1, weight := 320194, edges := #[⟨0, 1, 132⟩, ⟨0, 2, 218⟩, ⟨0, 3, 402⟩, ⟨1, 2, 210⟩, ⟨1, 3, 400⟩, ⟨2, 3, 122⟩], triples := #[] }
def er010_284 : Row := { vars := #[122, 271, 574], coeff := #[1, 1, 1], bound := 1, weight := 43605, edges := #[⟨0, 1, 424⟩, ⟨0, 2, 341⟩, ⟨1, 2, 94⟩], triples := #[] }
def er010_285 : Row := { vars := #[123, 588, 360], coeff := #[1, 1, 1], bound := 1, weight := 36389, edges := #[⟨0, 1, 328⟩, ⟨0, 2, 508⟩, ⟨1, 2, 135⟩], triples := #[] }
def er010_286 : Row := { vars := #[123, 588, 247], coeff := #[1, 1, 1], bound := 1, weight := 48565, edges := #[⟨0, 1, 328⟩, ⟨0, 2, 457⟩, ⟨1, 2, 78⟩], triples := #[] }
def er010_287 : Row := { vars := #[124, 195, 370], coeff := #[1, 1, 1], bound := 1, weight := 94790, edges := #[⟨0, 1, 413⟩, ⟨0, 2, 498⟩, ⟨1, 2, 295⟩], triples := #[] }
def er010_288 : Row := { vars := #[125, 135, 584, 380], coeff := #[1, 1, 1, 1], bound := 1, weight := 591559, edges := #[⟨0, 1, 141⟩, ⟨0, 2, 323⟩, ⟨0, 3, 483⟩, ⟨1, 2, 317⟩, ⟨1, 3, 477⟩, ⟨2, 3, 180⟩], triples := #[] }
def er010_289 : Row := { vars := #[125, 587, 355], coeff := #[1, 1, 1], bound := 1, weight := 227027, edges := #[⟨0, 1, 322⟩, ⟨0, 2, 511⟩, ⟨1, 2, 146⟩], triples := #[] }
def er010_290 : Row := { vars := #[127, 384, 447], coeff := #[1, 1, 1], bound := 1, weight := 440564, edges := #[⟨0, 1, 484⟩, ⟨0, 2, 297⟩, ⟨1, 2, 86⟩], triples := #[] }
def er010_291 : Row := { vars := #[127, 133, 485, 281], coeff := #[1, 1, 1, 1], bound := 1, weight := 378934, edges := #[⟨0, 1, 141⟩, ⟨0, 2, 219⟩, ⟨0, 3, 379⟩, ⟨1, 2, 211⟩, ⟨1, 3, 371⟩, ⟨2, 3, 73⟩], triples := #[] }
def er010_292 : Row := { vars := #[127, 137, 360, 559], coeff := #[1, 1, 1, 1], bound := 1, weight := 19565, edges := #[⟨0, 1, 133⟩, ⟨0, 2, 504⟩, ⟨0, 3, 348⟩, ⟨1, 2, 498⟩, ⟨1, 3, 342⟩, ⟨2, 3, 171⟩], triples := #[] }
def er010_293 : Row := { vars := #[128, 431, 561], coeff := #[1, 1, 1], bound := 1, weight := 675418, edges := #[⟨0, 1, 250⟩, ⟨0, 2, 344⟩, ⟨1, 2, 451⟩], triples := #[] }
def er010_294 : Row := { vars := #[129, 143, 452, 240], coeff := #[1, 1, 1, 1], bound := 1, weight := 366820, edges := #[⟨0, 1, 141⟩, ⟨0, 2, 296⟩, ⟨0, 3, 452⟩, ⟨1, 2, 286⟩, ⟨1, 3, 442⟩, ⟨2, 3, 0⟩], triples := #[] }
def er010_295 : Row := { vars := #[129, 286, 582], coeff := #[1, 1, 1], bound := 1, weight := 281939, edges := #[⟨0, 1, 382⟩, ⟨0, 2, 322⟩, ⟨1, 2, 2⟩], triples := #[] }
def er010_296 : Row := { vars := #[131, 392, 456], coeff := #[1, 1, 1], bound := 1, weight := 694359, edges := #[⟨0, 1, 478⟩, ⟨0, 2, 283⟩, ⟨1, 2, 93⟩], triples := #[] }
def er010_297 : Row := { vars := #[131, 596, 252], coeff := #[1, 1, 1], bound := 1, weight := 205399, edges := #[⟨0, 1, 318⟩, ⟨0, 2, 443⟩, ⟨1, 2, 93⟩], triples := #[] }
def er010_298 : Row := { vars := #[132, 262, 466, 126], coeff := #[1, 1, 1, 1], bound := 1, weight := 6845, edges := #[⟨0, 1, 426⟩, ⟨0, 2, 266⟩, ⟨0, 3, 140⟩, ⟨1, 2, 36⟩, ⟨1, 3, 428⟩, ⟨2, 3, 268⟩], triples := #[] }
def er010_299 : Row := { vars := #[132, 264, 77, 505], coeff := #[1, 1, 1, 1], bound := 1, weight := 266254, edges := #[⟨0, 1, 424⟩, ⟨0, 2, 47⟩, ⟨0, 3, 240⟩, ⟨1, 2, 466⟩, ⟨1, 3, 137⟩, ⟨2, 3, 271⟩], triples := #[] }
def er010_300 : Row := { vars := #[132, 394, 362], coeff := #[1, 1, 1], bound := 1, weight := 646518, edges := #[⟨0, 1, 489⟩, ⟨0, 2, 501⟩, ⟨1, 2, 303⟩], triples := #[] }
def er010_301 : Row := { vars := #[132, 571, 599], coeff := #[1, 1, 1], bound := 1, weight := 80385, edges := #[⟨0, 1, 337⟩, ⟨0, 2, 325⟩, ⟨1, 2, 464⟩], triples := #[] }
def er010_302 : Row := { vars := #[133, 578, 592], coeff := #[1, 1, 1], bound := 1, weight := 270227, edges := #[⟨0, 1, 345⟩, ⟨0, 2, 314⟩, ⟨1, 2, 464⟩], triples := #[] }
def er010_303 : Row := { vars := #[134, 439, 567], coeff := #[1, 1, 1], bound := 1, weight := 505872, edges := #[⟨0, 1, 253⟩, ⟨0, 2, 342⟩, ⟨1, 2, 441⟩], triples := #[] }
def er010_304 : Row := { vars := #[134, 496, 373], coeff := #[1, 1, 1], bound := 1, weight := 169606, edges := #[⟨0, 1, 223⟩, ⟨0, 2, 508⟩, ⟨1, 2, 66⟩], triples := #[] }
def er010_305 : Row := { vars := #[135, 389, 237], coeff := #[1, 1, 1], bound := 1, weight := 33729, edges := #[⟨0, 1, 476⟩, ⟨0, 2, 412⟩, ⟨1, 2, 265⟩], triples := #[] }
def er010_306 : Row := { vars := #[137, 393, 362], coeff := #[1, 1, 1], bound := 1, weight := 221108, edges := #[⟨0, 1, 488⟩, ⟨0, 2, 495⟩, ⟨1, 2, 304⟩], triples := #[] }
def er010_307 : Row := { vars := #[137, 587, 242], coeff := #[1, 1, 1], bound := 1, weight := 509762, edges := #[⟨0, 1, 314⟩, ⟨0, 2, 447⟩, ⟨1, 2, 83⟩], triples := #[] }
def er010_308 : Row := { vars := #[138, 231, 363], coeff := #[1, 1, 1], bound := 1, weight := 38244, edges := #[⟨0, 1, 413⟩, ⟨0, 2, 498⟩, ⟨1, 2, 285⟩], triples := #[] }
def er010_309 : Row := { vars := #[139, 292, 597], coeff := #[1, 1, 1], bound := 1, weight := 169606, edges := #[⟨0, 1, 378⟩, ⟨0, 2, 326⟩, ⟨1, 2, 33⟩], triples := #[] }
def er010_310 : Row := { vars := #[139, 433, 588], coeff := #[1, 1, 1], bound := 1, weight := 101600, edges := #[⟨0, 1, 253⟩, ⟨0, 2, 316⟩, ⟨1, 2, 425⟩], triples := #[] }
def er010_311 : Row := { vars := #[141, 571, 597], coeff := #[1, 1, 1], bound := 1, weight := 386681, edges := #[⟨0, 1, 339⟩, ⟨0, 2, 324⟩, ⟨1, 2, 463⟩], triples := #[] }
def er010_312 : Row := { vars := #[144, 290, 428], coeff := #[1, 1, 1], bound := 1, weight := 176257, edges := #[⟨0, 1, 399⟩, ⟨0, 2, 284⟩, ⟨1, 2, 157⟩], triples := #[] }
def er010_313 : Row := { vars := #[144, 424, 244], coeff := #[1, 1, 1], bound := 1, weight := 622016, edges := #[⟨0, 1, 288⟩, ⟨0, 2, 433⟩, ⟨1, 2, 66⟩], triples := #[] }
def er010_314 : Row := { vars := #[145, 431, 345], coeff := #[1, 1, 1], bound := 1, weight := 223716, edges := #[⟨0, 1, 284⟩, ⟨0, 2, 507⟩, ⟨1, 2, 107⟩], triples := #[] }
def er010_315 : Row := { vars := #[145, 323, 223], coeff := #[1, 1, 1], bound := 1, weight := 108895, edges := #[⟨0, 1, 382⟩, ⟨0, 2, 448⟩, ⟨1, 2, 323⟩], triples := #[] }
def er010_316 : Row := { vars := #[146, 160, 360, 564], coeff := #[1, 1, 1, 1], bound := 1, weight := 288987, edges := #[⟨0, 1, 170⟩, ⟨0, 2, 486⟩, ⟨0, 3, 326⟩, ⟨1, 2, 476⟩, ⟨1, 3, 316⟩, ⟨2, 3, 169⟩], triples := #[] }
def er010_317 : Row := { vars := #[147, 161, 585, 381], coeff := #[1, 1, 1, 1], bound := 1, weight := 217936, edges := #[⟨0, 1, 171⟩, ⟨0, 2, 307⟩, ⟨0, 3, 467⟩, ⟨1, 2, 303⟩, ⟨1, 3, 463⟩, ⟨2, 3, 181⟩], triples := #[] }
def er010_318 : Row := { vars := #[147, 418, 431], coeff := #[1, 1, 1], bound := 1, weight := 83221, edges := #[⟨0, 1, 293⟩, ⟨0, 2, 282⟩, ⟨1, 2, 383⟩], triples := #[] }
def er010_319 : Row := { vars := #[148, 158, 360, 564], coeff := #[1, 1, 1, 1], bound := 1, weight := 361696, edges := #[⟨0, 1, 170⟩, ⟨0, 2, 484⟩, ⟨0, 3, 324⟩, ⟨1, 2, 478⟩, ⟨1, 3, 318⟩, ⟨2, 3, 169⟩], triples := #[] }
end HardyCapset20261020.Cert


