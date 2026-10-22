-- Prove2me | Definitions.Def_HardyCapsetEvaluationData010rows05V420261021
-- name    : HardyCapsetEvaluationData010rows05V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T01:26:17.597401+00:00
-- url     : https://prove2.me/theorems/ec19e8aa-848e-4595-829b-7f38c8529a34
-- title:
--   HardyCapsetEvaluationData010rows05V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er010_320 : Row := { vars := #[149, 534, 407], coeff := #[1, 1, 1], bound := 1, weight := 258836, edges := #[⟨0, 1, 210⟩, ⟨0, 2, 290⟩, ⟨1, 2, 487⟩], triples := #[] }
def er010_321 : Row := { vars := #[149, 163, 449, 241], coeff := #[1, 1, 1, 1], bound := 1, weight := 34629, edges := #[⟨0, 1, 169⟩, ⟨0, 2, 271⟩, ⟨0, 3, 435⟩, ⟨1, 2, 261⟩, ⟨1, 3, 425⟩, ⟨2, 3, 9⟩], triples := #[] }
def er010_322 : Row := { vars := #[150, 156, 322, 503], coeff := #[1, 1, 1, 1], bound := 1, weight := 141524, edges := #[⟨0, 1, 170⟩, ⟨0, 2, 379⟩, ⟨0, 3, 232⟩, ⟨1, 2, 371⟩, ⟨1, 3, 230⟩, ⟨2, 3, 73⟩], triples := #[] }
def er010_323 : Row := { vars := #[150, 156, 299, 526], coeff := #[1, 1, 1, 1], bound := 1, weight := 414625, edges := #[⟨0, 1, 170⟩, ⟨0, 2, 392⟩, ⟨0, 3, 219⟩, ⟨1, 2, 390⟩, ⟨1, 3, 211⟩, ⟨2, 3, 73⟩], triples := #[] }
def er010_324 : Row := { vars := #[150, 160, 503, 294], coeff := #[1, 1, 1, 1], bound := 1, weight := 248175, edges := #[⟨0, 1, 168⟩, ⟨0, 2, 232⟩, ⟨0, 3, 393⟩, ⟨1, 2, 229⟩, ⟨1, 3, 390⟩, ⟨2, 3, 110⟩], triples := #[] }
def er010_325 : Row := { vars := #[151, 157, 585, 381], coeff := #[1, 1, 1, 1], bound := 1, weight := 347307, edges := #[⟨0, 1, 171⟩, ⟨0, 2, 306⟩, ⟨0, 3, 466⟩, ⟨1, 2, 304⟩, ⟨1, 3, 464⟩, ⟨2, 3, 181⟩], triples := #[] }
def er010_326 : Row := { vars := #[152, 330, 208], coeff := #[1, 1, 1], bound := 1, weight := 323023, edges := #[⟨0, 1, 365⟩, ⟨0, 2, 454⟩, ⟨1, 2, 325⟩], triples := #[] }
def er010_327 : Row := { vars := #[153, 167, 249, 445], coeff := #[1, 1, 1, 1], bound := 1, weight := 410054, edges := #[⟨0, 1, 171⟩, ⟨0, 2, 435⟩, ⟨0, 3, 271⟩, ⟨1, 2, 425⟩, ⟨1, 3, 261⟩, ⟨2, 3, 1⟩], triples := #[] }
def er010_328 : Row := { vars := #[153, 195, 332], coeff := #[1, 1, 1], bound := 1, weight := 413557, edges := #[⟨0, 1, 450⟩, ⟨0, 2, 370⟩, ⟨1, 2, 323⟩], triples := #[] }
def er010_329 : Row := { vars := #[153, 330, 211], coeff := #[1, 1, 1], bound := 1, weight := 176390, edges := #[⟨0, 1, 366⟩, ⟨0, 2, 454⟩, ⟨1, 2, 323⟩], triples := #[] }
def er010_330 : Row := { vars := #[154, 164, 294, 508], coeff := #[1, 1, 1, 1], bound := 1, weight := 325835, edges := #[⟨0, 1, 170⟩, ⟨0, 2, 392⟩, ⟨0, 3, 233⟩, ⟨1, 2, 389⟩, ⟨1, 3, 230⟩, ⟨2, 3, 108⟩], triples := #[] }
def er010_331 : Row := { vars := #[154, 164, 304, 498], coeff := #[1, 1, 1, 1], bound := 1, weight := 654602, edges := #[⟨0, 1, 170⟩, ⟨0, 2, 393⟩, ⟨0, 3, 232⟩, ⟨1, 2, 390⟩, ⟨1, 3, 229⟩, ⟨2, 3, 108⟩], triples := #[] }
def er010_332 : Row := { vars := #[155, 157, 386, 531], coeff := #[1, 1, 1, 1], bound := 1, weight := 535154, edges := #[⟨0, 1, 169⟩, ⟨0, 2, 467⟩, ⟨0, 3, 220⟩, ⟨1, 2, 463⟩, ⟨1, 3, 204⟩, ⟨2, 3, 44⟩], triples := #[] }
def er010_333 : Row := { vars := #[155, 157, 364, 568], coeff := #[1, 1, 1, 1], bound := 1, weight := 117540, edges := #[⟨0, 1, 169⟩, ⟨0, 2, 486⟩, ⟨0, 3, 326⟩, ⟨1, 2, 476⟩, ⟨1, 3, 316⟩, ⟨2, 3, 170⟩], triples := #[] }
def er010_334 : Row := { vars := #[155, 419, 339], coeff := #[1, 1, 1], bound := 1, weight := 48308, edges := #[⟨0, 1, 296⟩, ⟨0, 2, 505⟩, ⟨1, 2, 78⟩], triples := #[] }
def er010_335 : Row := { vars := #[156, 404, 438], coeff := #[1, 1, 1], bound := 1, weight := 100776, edges := #[⟨0, 1, 286⟩, ⟨0, 2, 295⟩, ⟨1, 2, 364⟩], triples := #[] }
def er010_336 : Row := { vars := #[156, 208, 238], coeff := #[1, 1, 1], bound := 1, weight := 282393, edges := #[⟨0, 1, 442⟩, ⟨0, 2, 451⟩, ⟨1, 2, 208⟩], triples := #[] }
def er010_337 : Row := { vars := #[158, 287, 416], coeff := #[1, 1, 1], bound := 1, weight := 380797, edges := #[⟨0, 1, 399⟩, ⟨0, 2, 284⟩, ⟨1, 2, 147⟩], triples := #[] }
def er010_338 : Row := { vars := #[159, 329, 239], coeff := #[1, 1, 1], bound := 1, weight := 535154, edges := #[⟨0, 1, 366⟩, ⟨0, 2, 450⟩, ⟨1, 2, 317⟩], triples := #[] }
def er010_339 : Row := { vars := #[160, 398, 436], coeff := #[1, 1, 1], bound := 1, weight := 4479, edges := #[⟨0, 1, 285⟩, ⟨0, 2, 292⟩, ⟨1, 2, 368⟩], triples := #[] }
def er010_340 : Row := { vars := #[161, 231, 545], coeff := #[1, 1, 1], bound := 1, weight := 195076, edges := #[⟨0, 1, 456⟩, ⟨0, 2, 338⟩, ⟨1, 2, 97⟩], triples := #[] }
def er010_341 : Row := { vars := #[162, 232, 495], coeff := #[1, 1, 1], bound := 1, weight := 513435, edges := #[⟨0, 1, 450⟩, ⟨0, 2, 243⟩, ⟨1, 2, 167⟩], triples := #[] }
def er010_342 : Row := { vars := #[163, 199, 334], coeff := #[1, 1, 1], bound := 1, weight := 965372, edges := #[⟨0, 1, 448⟩, ⟨0, 2, 378⟩, ⟨1, 2, 317⟩], triples := #[] }
def er010_343 : Row := { vars := #[166, 333, 212], coeff := #[1, 1, 1], bound := 1, weight := 350356, edges := #[⟨0, 1, 377⟩, ⟨0, 2, 448⟩, ⟨1, 2, 315⟩], triples := #[] }
def er010_344 : Row := { vars := #[168, 226, 494], coeff := #[1, 1, 1], bound := 1, weight := 298185, edges := #[⟨0, 1, 422⟩, ⟨0, 2, 229⟩, ⟨1, 2, 156⟩], triples := #[] }
def er010_345 : Row := { vars := #[169, 405, 246], coeff := #[1, 1, 1], bound := 1, weight := 234205, edges := #[⟨0, 1, 272⟩, ⟨0, 2, 413⟩, ⟨1, 2, 38⟩], triples := #[] }
def er010_346 : Row := { vars := #[169, 310, 201], coeff := #[1, 1, 1], bound := 1, weight := 765796, edges := #[⟨0, 1, 371⟩, ⟨0, 2, 432⟩, ⟨1, 2, 346⟩], triples := #[] }
def er010_347 : Row := { vars := #[170, 9, 272, 476], coeff := #[1, 1, 1, 1], bound := 1, weight := 306876, edges := #[⟨0, 1, 93⟩, ⟨0, 2, 443⟩, ⟨0, 3, 283⟩, ⟨1, 2, 368⟩, ⟨1, 3, 208⟩, ⟨2, 3, 61⟩], triples := #[] }
def er010_348 : Row := { vars := #[170, 271, 5, 505], coeff := #[1, 1, 1, 1], bound := 1, weight := 78400, edges := #[⟨0, 1, 447⟩, ⟨0, 2, 96⟩, ⟨0, 3, 222⟩, ⟨1, 2, 364⟩, ⟨1, 3, 162⟩, ⟨2, 3, 325⟩], triples := #[] }
def er010_349 : Row := { vars := #[170, 272, 430], coeff := #[1, 1, 1], bound := 1, weight := 200552, edges := #[⟨0, 1, 443⟩, ⟨0, 2, 259⟩, ⟨1, 2, 24⟩], triples := #[] }
def er010_350 : Row := { vars := #[170, 214, 470], coeff := #[1, 1, 1], bound := 1, weight := 242439, edges := #[⟨0, 1, 429⟩, ⟨0, 2, 290⟩, ⟨1, 2, 10⟩], triples := #[] }
def er010_351 : Row := { vars := #[171, 425, 349], coeff := #[1, 1, 1], bound := 1, weight := 194546, edges := #[⟨0, 1, 263⟩, ⟨0, 2, 479⟩, ⟨1, 2, 94⟩], triples := #[] }
def er010_352 : Row := { vars := #[171, 554, 57, 350], coeff := #[1, 1, 1, 1], bound := 1, weight := 512090, edges := #[⟨0, 1, 315⟩, ⟨0, 2, 20⟩, ⟨0, 3, 475⟩, ⟨1, 2, 210⟩, ⟨1, 3, 155⟩, ⟨2, 3, 370⟩], triples := #[] }
def er010_353 : Row := { vars := #[171, 185, 360, 505], coeff := #[1, 1, 1, 1], bound := 1, weight := 293365, edges := #[⟨0, 1, 183⟩, ⟨0, 2, 467⟩, ⟨0, 3, 220⟩, ⟨1, 2, 463⟩, ⟨1, 3, 204⟩, ⟨2, 3, 0⟩], triples := #[] }
def er010_354 : Row := { vars := #[172, 186, 541, 341], coeff := #[1, 1, 1, 1], bound := 1, weight := 195076, edges := #[⟨0, 1, 180⟩, ⟨0, 2, 327⟩, ⟨0, 3, 483⟩, ⟨1, 2, 317⟩, ⟨1, 3, 473⟩, ⟨2, 3, 141⟩], triples := #[] }
def er010_355 : Row := { vars := #[172, 186, 580, 381], coeff := #[1, 1, 1, 1], bound := 1, weight := 256883, edges := #[⟨0, 1, 180⟩, ⟨0, 2, 351⟩, ⟨0, 3, 507⟩, ⟨1, 2, 341⟩, ⟨1, 3, 497⟩, ⟨2, 3, 183⟩], triples := #[] }
def er010_356 : Row := { vars := #[173, 405, 242], coeff := #[1, 1, 1], bound := 1, weight := 40066, edges := #[⟨0, 1, 268⟩, ⟨0, 2, 413⟩, ⟨1, 2, 46⟩], triples := #[] }
def er010_357 : Row := { vars := #[173, 217, 544], coeff := #[1, 1, 1], bound := 1, weight := 350356, edges := #[⟨0, 1, 426⟩, ⟨0, 2, 324⟩, ⟨1, 2, 106⟩], triples := #[] }
def er010_358 : Row := { vars := #[176, 190, 345, 541], coeff := #[1, 1, 1, 1], bound := 1, weight := 572843, edges := #[⟨0, 1, 182⟩, ⟨0, 2, 487⟩, ⟨0, 3, 323⟩, ⟨1, 2, 477⟩, ⟨1, 3, 313⟩, ⟨2, 3, 133⟩], triples := #[] }
def er010_359 : Row := { vars := #[176, 218, 494], coeff := #[1, 1, 1], bound := 1, weight := 41447, edges := #[⟨0, 1, 422⟩, ⟨0, 2, 230⟩, ⟨1, 2, 153⟩], triples := #[] }
def er010_360 : Row := { vars := #[177, 429, 501], coeff := #[1, 1, 1], bound := 1, weight := 110352, edges := #[⟨0, 1, 266⟩, ⟨0, 2, 219⟩, ⟨1, 2, 506⟩], triples := #[] }
def er010_361 : Row := { vars := #[177, 183, 385, 589], coeff := #[1, 1, 1, 1], bound := 1, weight := 239926, edges := #[⟨0, 1, 181⟩, ⟨0, 2, 511⟩, ⟨0, 3, 351⟩, ⟨1, 2, 497⟩, ⟨1, 3, 337⟩, ⟨2, 3, 182⟩], triples := #[] }
def er010_362 : Row := { vars := #[180, 274, 19, 478], coeff := #[1, 1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 457⟩, ⟨0, 2, 106⟩, ⟨0, 3, 297⟩, ⟨1, 2, 376⟩, ⟨1, 3, 68⟩, ⟨2, 3, 216⟩], triples := #[] }
def er010_363 : Row := { vars := #[181, 413, 440], coeff := #[1, 1, 1], bound := 1, weight := 81694, edges := #[⟨0, 1, 259⟩, ⟨0, 2, 270⟩, ⟨1, 2, 370⟩], triples := #[] }
def er010_364 : Row := { vars := #[181, 548, 209], coeff := #[1, 1, 1], bound := 1, weight := 214331, edges := #[⟨0, 1, 316⟩, ⟨0, 2, 419⟩, ⟨1, 2, 86⟩], triples := #[] }
def er010_365 : Row := { vars := #[181, 550, 209], coeff := #[1, 1, 1], bound := 1, weight := 375617, edges := #[⟨0, 1, 315⟩, ⟨0, 2, 419⟩, ⟨1, 2, 84⟩], triples := #[] }
def er010_366 : Row := { vars := #[181, 441, 344], coeff := #[1, 1, 1], bound := 1, weight := 328361, edges := #[⟨0, 1, 269⟩, ⟨0, 2, 476⟩, ⟨1, 2, 96⟩], triples := #[] }
def er010_367 : Row := { vars := #[182, 518, 418], coeff := #[1, 1, 1], bound := 1, weight := 617310, edges := #[⟨0, 1, 217⟩, ⟨0, 2, 262⟩, ⟨1, 2, 499⟩], triples := #[] }
def er010_368 : Row := { vars := #[182, 287, 418], coeff := #[1, 1, 1], bound := 1, weight := 198618, edges := #[⟨0, 1, 389⟩, ⟨0, 2, 262⟩, ⟨1, 2, 146⟩], triples := #[] }
def er010_369 : Row := { vars := #[182, 438, 262], coeff := #[1, 1, 1], bound := 1, weight := 184074, edges := #[⟨0, 1, 272⟩, ⟨0, 2, 446⟩, ⟨1, 2, 20⟩], triples := #[] }
def er010_370 : Row := { vars := #[183, 256, 437], coeff := #[1, 1, 1], bound := 1, weight := 347606, edges := #[⟨0, 1, 413⟩, ⟨0, 2, 272⟩, ⟨1, 2, 66⟩], triples := #[] }
def er010_371 : Row := { vars := #[186, 517, 402], coeff := #[1, 1, 1], bound := 1, weight := 134353, edges := #[⟨0, 1, 217⟩, ⟨0, 2, 266⟩, ⟨1, 2, 499⟩], triples := #[] }
def er010_372 : Row := { vars := #[187, 298, 233], coeff := #[1, 1, 1], bound := 1, weight := 123020, edges := #[⟨0, 1, 371⟩, ⟨0, 2, 428⟩, ⟨1, 2, 340⟩], triples := #[] }
def er010_373 : Row := { vars := #[190, 442, 502], coeff := #[1, 1, 1], bound := 1, weight := 427158, edges := #[⟨0, 1, 272⟩, ⟨0, 2, 205⟩, ⟨1, 2, 495⟩], triples := #[] }
def er010_374 : Row := { vars := #[191, 512, 433], coeff := #[1, 1, 1], bound := 1, weight := 239973, edges := #[⟨0, 1, 211⟩, ⟨0, 2, 268⟩, ⟨1, 2, 496⟩], triples := #[] }
def er010_375 : Row := { vars := #[191, 312, 213], coeff := #[1, 1, 1], bound := 1, weight := 373018, edges := #[⟨0, 1, 379⟩, ⟨0, 2, 426⟩, ⟨1, 2, 336⟩], triples := #[] }
def er010_376 : Row := { vars := #[192, 9, 371], coeff := #[1, 1, 1], bound := 1, weight := 373018, edges := #[⟨0, 1, 402⟩, ⟨0, 2, 293⟩, ⟨1, 2, 426⟩], triples := #[] }
def er010_377 : Row := { vars := #[197, 175, 547], coeff := #[1, 1, 1], bound := 1, weight := 301157, edges := #[⟨0, 1, 433⟩, ⟨0, 2, 87⟩, ⟨1, 2, 325⟩], triples := #[] }
def er010_378 : Row := { vars := #[201, 76, 445], coeff := #[1, 1, 1], bound := 1, weight := 166534, edges := #[⟨0, 1, 504⟩, ⟨0, 2, 50⟩, ⟨1, 2, 328⟩], triples := #[] }
def er010_379 : Row := { vars := #[206, 393, 91], coeff := #[1, 1, 1], bound := 1, weight := 403490, edges := #[⟨0, 1, 264⟩, ⟨0, 2, 498⟩, ⟨1, 2, 382⟩], triples := #[] }
def er010_380 : Row := { vars := #[212, 179, 217], coeff := #[1, 1, 1], bound := 1, weight := 336580, edges := #[⟨0, 1, 434⟩, ⟨0, 2, 218⟩, ⟨1, 2, 419⟩], triples := #[] }
def er010_381 : Row := { vars := #[218, 388, 81], coeff := #[1, 1, 1], bound := 1, weight := 40193, edges := #[⟨0, 1, 270⟩, ⟨0, 2, 498⟩, ⟨1, 2, 382⟩], triples := #[] }
def er010_382 : Row := { vars := #[226, 81, 378], coeff := #[1, 1, 1], bound := 1, weight := 342580, edges := #[⟨0, 1, 502⟩, ⟨0, 2, 270⟩, ⟨1, 2, 378⟩], triples := #[] }
def er010_383 : Row := { vars := #[230, 188, 479], coeff := #[1, 1, 1], bound := 1, weight := 173134, edges := #[⟨0, 1, 429⟩, ⟨0, 2, 31⟩, ⟨1, 2, 297⟩], triples := #[] }
end HardyCapset20261020.Cert


