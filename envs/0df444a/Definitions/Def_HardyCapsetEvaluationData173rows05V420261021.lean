-- Prove2me | Definitions.Def_HardyCapsetEvaluationData173rows05V420261021
-- name    : HardyCapsetEvaluationData173rows05V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T03:08:28.156987+00:00
-- url     : https://prove2.me/theorems/00361a86-6b21-43c2-b4ed-eb558a3630e5
-- title:
--   HardyCapsetEvaluationData173rows05V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er173_320 : Row := { vars := #[168, 224, 395], coeff := #[1, 1, 1], bound := 1, weight := 410750, edges := #[⟨0, 1, 71⟩, ⟨0, 2, 434⟩, ⟨1, 2, 401⟩], triples := #[] }
def er173_321 : Row := { vars := #[169, 402, 396], coeff := #[1, 1, 1], bound := 1, weight := 330456, edges := #[⟨0, 1, 431⟩, ⟨0, 2, 435⟩, ⟨1, 2, 275⟩], triples := #[] }
def er173_322 : Row := { vars := #[169, 567, 203], coeff := #[1, 1, 1], bound := 1, weight := 552512, edges := #[⟨0, 1, 301⟩, ⟨0, 2, 54⟩, ⟨1, 2, 275⟩], triples := #[] }
def er173_323 : Row := { vars := #[170, 404, 403, 496, 497, 498], coeff := #[1, 1, 1, 1, 1, 1], bound := 1, weight := 187837, edges := #[⟨0, 1, 432⟩, ⟨0, 2, 433⟩, ⟨0, 3, 354⟩, ⟨0, 4, 353⟩, ⟨0, 5, 352⟩, ⟨1, 2, 273⟩, ⟨1, 3, 194⟩, ⟨1, 4, 193⟩, ⟨1, 5, 192⟩, ⟨2, 3, 198⟩, ⟨2, 4, 197⟩, ⟨2, 5, 196⟩, ⟨3, 4, 337⟩, ⟨3, 5, 336⟩, ⟨4, 5, 335⟩], triples := #[] }
def er173_324 : Row := { vars := #[170, 404, 312], coeff := #[1, 1, 1], bound := 1, weight := 273869, edges := #[⟨0, 1, 432⟩, ⟨0, 2, 511⟩, ⟨1, 2, 351⟩], triples := #[] }
def er173_325 : Row := { vars := #[171, 405, 357, 376], coeff := #[1, 1, 1, 1], bound := 1, weight := 496553, edges := #[⟨0, 1, 436⟩, ⟨0, 2, 416⟩, ⟨0, 3, 406⟩, ⟨1, 2, 256⟩, ⟨1, 3, 246⟩, ⟨2, 3, 279⟩], triples := #[] }
def er173_326 : Row := { vars := #[171, 173, 352, 480], coeff := #[1, 1, 1, 1], bound := 1, weight := 55229, edges := #[⟨0, 1, 122⟩, ⟨0, 2, 502⟩, ⟨0, 3, 370⟩, ⟨1, 2, 498⟩, ⟨1, 3, 366⟩, ⟨2, 3, 252⟩], triples := #[] }
def er173_327 : Row := { vars := #[171, 180, 458], coeff := #[1, 1, 1], bound := 1, weight := 448220, edges := #[⟨0, 1, 130⟩, ⟨0, 2, 352⟩, ⟨1, 2, 372⟩], triples := #[] }
def er173_328 : Row := { vars := #[172, 181, 417, 415], coeff := #[1, 1, 1, 1], bound := 1, weight := 412220, edges := #[⟨0, 1, 131⟩, ⟨0, 2, 455⟩, ⟨0, 3, 456⟩, ⟨1, 2, 445⟩, ⟨1, 3, 446⟩, ⟨2, 3, 283⟩], triples := #[] }
def er173_329 : Row := { vars := #[172, 188, 199], coeff := #[1, 1, 1], bound := 1, weight := 482424, edges := #[⟨0, 1, 127⟩, ⟨0, 2, 11⟩, ⟨1, 2, 24⟩], triples := #[] }
def er173_330 : Row := { vars := #[172, 188, 489, 340], coeff := #[1, 1, 1, 1], bound := 1, weight := 105357, edges := #[⟨0, 1, 127⟩, ⟨0, 2, 396⟩, ⟨0, 3, 492⟩, ⟨1, 2, 398⟩, ⟨1, 3, 494⟩, ⟨2, 3, 279⟩], triples := #[] }
def er173_331 : Row := { vars := #[173, 272, 492], coeff := #[1, 1, 1], bound := 1, weight := 526053, edges := #[⟨0, 1, 65⟩, ⟨0, 2, 395⟩, ⟨1, 2, 511⟩], triples := #[] }
def er173_332 : Row := { vars := #[173, 297, 311], coeff := #[1, 1, 1], bound := 1, weight := 181660, edges := #[⟨0, 1, 486⟩, ⟨0, 2, 478⟩, ⟨1, 2, 199⟩], triples := #[] }
def er173_333 : Row := { vars := #[175, 288, 311, 644], coeff := #[1, 1, 1, 1], bound := 1, weight := 61127, edges := #[⟨0, 1, 486⟩, ⟨0, 2, 480⟩, ⟨0, 3, 232⟩, ⟨1, 2, 195⟩, ⟨1, 3, 96⟩, ⟨2, 3, 83⟩], triples := #[] }
def er173_334 : Row := { vars := #[175, 197, 344, 571, 349, 198], coeff := #[1, 1, 1, 1, 1, 1], bound := 1, weight := 424673, edges := #[⟨0, 1, 6⟩, ⟨0, 2, 510⟩, ⟨0, 3, 336⟩, ⟨0, 4, 500⟩, ⟨0, 5, 7⟩, ⟨1, 2, 435⟩, ⟨1, 3, 261⟩, ⟨1, 4, 425⟩, ⟨1, 5, 139⟩, ⟨2, 3, 48⟩, ⟨2, 4, 236⟩, ⟨2, 5, 434⟩, ⟨3, 4, 71⟩, ⟨3, 5, 260⟩, ⟨4, 5, 424⟩], triples := #[] }
def er173_335 : Row := { vars := #[176, 284, 196, 294], coeff := #[1, 1, 1, 1], bound := 1, weight := 30708, edges := #[⟨0, 1, 470⟩, ⟨0, 2, 3⟩, ⟨0, 3, 487⟩, ⟨1, 2, 405⟩, ⟨1, 3, 216⟩, ⟨2, 3, 413⟩], triples := #[] }
def er173_336 : Row := { vars := #[176, 194, 196], coeff := #[1, 1, 1], bound := 1, weight := 139526, edges := #[⟨0, 1, 11⟩, ⟨0, 2, 3⟩, ⟨1, 2, 141⟩], triples := #[] }
def er173_337 : Row := { vars := #[176, 196, 459, 474], coeff := #[1, 1, 1, 1], bound := 1, weight := 438707, edges := #[⟨0, 1, 3⟩, ⟨0, 2, 353⟩, ⟨0, 3, 371⟩, ⟨1, 2, 490⟩, ⟨1, 3, 499⟩, ⟨2, 3, 315⟩], triples := #[] }
def er173_338 : Row := { vars := #[177, 660, 286], coeff := #[1, 1, 1], bound := 1, weight := 9, edges := #[⟨0, 1, 219⟩, ⟨0, 2, 485⟩, ⟨1, 2, 127⟩], triples := #[] }
def er173_339 : Row := { vars := #[177, 537, 449], coeff := #[1, 1, 1], bound := 1, weight := 103114, edges := #[⟨0, 1, 313⟩, ⟨0, 2, 389⟩, ⟨1, 2, 100⟩], triples := #[] }
def er173_340 : Row := { vars := #[177, 55, 201], coeff := #[1, 1, 1], bound := 1, weight := 77333, edges := #[⟨0, 1, 150⟩, ⟨0, 2, 12⟩, ⟨1, 2, 126⟩], triples := #[] }
def er173_341 : Row := { vars := #[177, 201, 483], coeff := #[1, 1, 1], bound := 1, weight := 242787, edges := #[⟨0, 1, 12⟩, ⟨0, 2, 361⟩, ⟨1, 2, 494⟩], triples := #[] }
def er173_342 : Row := { vars := #[177, 201, 342, 200], coeff := #[1, 1, 1, 1], bound := 1, weight := 249050, edges := #[⟨0, 1, 12⟩, ⟨0, 2, 506⟩, ⟨0, 3, 11⟩, ⟨1, 2, 430⟩, ⟨1, 3, 144⟩, ⟨2, 3, 431⟩], triples := #[] }
def er173_343 : Row := { vars := #[178, 662, 286], coeff := #[1, 1, 1], bound := 1, weight := 99405, edges := #[⟨0, 1, 216⟩, ⟨0, 2, 483⟩, ⟨1, 2, 126⟩], triples := #[] }
def er173_344 : Row := { vars := #[178, 482, 526], coeff := #[1, 1, 1], bound := 1, weight := 354381, edges := #[⟨0, 1, 360⟩, ⟨0, 2, 322⟩, ⟨1, 2, 123⟩], triples := #[] }
def er173_345 : Row := { vars := #[179, 412, 476], coeff := #[1, 1, 1], bound := 1, weight := 196991, edges := #[⟨0, 1, 440⟩, ⟨0, 2, 354⟩, ⟨1, 2, 194⟩], triples := #[] }
def er173_346 : Row := { vars := #[181, 281, 426], coeff := #[1, 1, 1], bound := 1, weight := 273963, edges := #[⟨0, 1, 485⟩, ⟨0, 2, 436⟩, ⟨1, 2, 313⟩], triples := #[] }
def er173_347 : Row := { vars := #[181, 443, 214], coeff := #[1, 1, 1], bound := 1, weight := 190162, edges := #[⟨0, 1, 388⟩, ⟨0, 2, 25⟩, ⟨1, 2, 464⟩], triples := #[] }
def er173_348 : Row := { vars := #[181, 101, 506], coeff := #[1, 1, 1], bound := 1, weight := 53529, edges := #[⟨0, 1, 183⟩, ⟨0, 2, 394⟩, ⟨1, 2, 455⟩], triples := #[] }
def er173_349 : Row := { vars := #[182, 414, 274], coeff := #[1, 1, 1], bound := 1, weight := 169037, edges := #[⟨0, 1, 448⟩, ⟨0, 2, 44⟩, ⟨1, 2, 394⟩], triples := #[] }
def er173_350 : Row := { vars := #[182, 289, 418], coeff := #[1, 1, 1], bound := 1, weight := 240962, edges := #[⟨0, 1, 480⟩, ⟨0, 2, 444⟩, ⟨1, 2, 320⟩], triples := #[] }
def er173_351 : Row := { vars := #[182, 49, 54], coeff := #[1, 1, 1], bound := 1, weight := 168265, edges := #[⟨0, 1, 143⟩, ⟨0, 2, 135⟩, ⟨1, 2, 34⟩], triples := #[] }
def er173_352 : Row := { vars := #[182, 588, 205], coeff := #[1, 1, 1], bound := 1, weight := 212680, edges := #[⟨0, 1, 257⟩, ⟨0, 2, 29⟩, ⟨1, 2, 208⟩], triples := #[] }
def er173_353 : Row := { vars := #[183, 225, 49, 371], coeff := #[1, 1, 1, 1], bound := 1, weight := 202709, edges := #[⟨0, 1, 2⟩, ⟨0, 2, 139⟩, ⟨0, 3, 416⟩, ⟨1, 2, 131⟩, ⟨1, 3, 383⟩, ⟨2, 3, 509⟩], triples := #[] }
def er173_354 : Row := { vars := #[183, 420, 332, 469], coeff := #[1, 1, 1, 1], bound := 1, weight := 797292, edges := #[⟨0, 1, 445⟩, ⟨0, 2, 460⟩, ⟨0, 3, 370⟩, ⟨1, 2, 300⟩, ⟨1, 3, 210⟩, ⟨2, 3, 257⟩], triples := #[] }
def er173_355 : Row := { vars := #[184, 421, 419, 478, 430, 479], coeff := #[1, 1, 1, 1, 1, 1], bound := 1, weight := 36659, edges := #[⟨0, 1, 446⟩, ⟨0, 2, 448⟩, ⟨0, 3, 352⟩, ⟨0, 4, 438⟩, ⟨0, 5, 355⟩, ⟨1, 2, 288⟩, ⟨1, 3, 192⟩, ⟨1, 4, 278⟩, ⟨1, 5, 195⟩, ⟨2, 3, 196⟩, ⟨2, 4, 279⟩, ⟨2, 5, 199⟩, ⟨3, 4, 219⟩, ⟨3, 5, 322⟩, ⟨4, 5, 216⟩], triples := #[] }
def er173_356 : Row := { vars := #[184, 421, 360], coeff := #[1, 1, 1], bound := 1, weight := 184163, edges := #[⟨0, 1, 446⟩, ⟨0, 2, 434⟩, ⟨1, 2, 274⟩], triples := #[] }
def er173_357 : Row := { vars := #[184, 421, 341], coeff := #[1, 1, 1], bound := 1, weight := 156593, edges := #[⟨0, 1, 446⟩, ⟨0, 2, 509⟩, ⟨1, 2, 349⟩], triples := #[] }
def er173_358 : Row := { vars := #[185, 422, 388, 509], coeff := #[1, 1, 1, 1], bound := 1, weight := 24528, edges := #[⟨0, 1, 447⟩, ⟨0, 2, 410⟩, ⟨0, 3, 396⟩, ⟨1, 2, 250⟩, ⟨1, 3, 236⟩, ⟨2, 3, 198⟩], triples := #[] }
def er173_359 : Row := { vars := #[185, 422, 411], coeff := #[1, 1, 1], bound := 1, weight := 593792, edges := #[⟨0, 1, 447⟩, ⟨0, 2, 457⟩, ⟨1, 2, 297⟩], triples := #[] }
def er173_360 : Row := { vars := #[185, 51, 222, 351], coeff := #[1, 1, 1, 1], bound := 1, weight := 381682, edges := #[⟨0, 1, 136⟩, ⟨0, 2, 5⟩, ⟨0, 3, 492⟩, ⟨1, 2, 130⟩, ⟨1, 3, 380⟩, ⟨2, 3, 434⟩], triples := #[] }
def er173_361 : Row := { vars := #[186, 660, 352, 52], coeff := #[1, 1, 1, 1], bound := 1, weight := 119502, edges := #[⟨0, 1, 199⟩, ⟨0, 2, 510⟩, ⟨0, 3, 160⟩, ⟨1, 2, 83⟩, ⟨1, 3, 256⟩, ⟨2, 3, 381⟩], triples := #[] }
def er173_362 : Row := { vars := #[186, 423, 464], coeff := #[1, 1, 1], bound := 1, weight := 35332, edges := #[⟨0, 1, 449⟩, ⟨0, 2, 354⟩, ⟨1, 2, 194⟩], triples := #[] }
def er173_363 : Row := { vars := #[186, 423, 343], coeff := #[1, 1, 1], bound := 1, weight := 492926, edges := #[⟨0, 1, 449⟩, ⟨0, 2, 492⟩, ⟨1, 2, 332⟩], triples := #[] }
def er173_364 : Row := { vars := #[189, 431, 307], coeff := #[1, 1, 1], bound := 1, weight := 743677, edges := #[⟨0, 1, 451⟩, ⟨0, 2, 489⟩, ⟨1, 2, 329⟩], triples := #[] }
def er173_365 : Row := { vars := #[190, 669, 205], coeff := #[1, 1, 1], bound := 1, weight := 49340, edges := #[⟨0, 1, 198⟩, ⟨0, 2, 19⟩, ⟨1, 2, 351⟩], triples := #[] }
def er173_366 : Row := { vars := #[190, 426, 432], coeff := #[1, 1, 1], bound := 1, weight := 170773, edges := #[⟨0, 1, 456⟩, ⟨0, 2, 452⟩, ⟨1, 2, 296⟩], triples := #[] }
def er173_367 : Row := { vars := #[190, 432, 307], coeff := #[1, 1, 1], bound := 1, weight := 77398, edges := #[⟨0, 1, 452⟩, ⟨0, 2, 488⟩, ⟨1, 2, 328⟩], triples := #[] }
def er173_368 : Row := { vars := #[190, 564, 210], coeff := #[1, 1, 1], bound := 1, weight := 293502, edges := #[⟨0, 1, 335⟩, ⟨0, 2, 8⟩, ⟨1, 2, 274⟩], triples := #[] }
def er173_369 : Row := { vars := #[191, 207, 212], coeff := #[1, 1, 1], bound := 1, weight := 313265, edges := #[⟨0, 1, 10⟩, ⟨0, 2, 2⟩, ⟨1, 2, 156⟩], triples := #[] }
def er173_370 : Row := { vars := #[192, 435, 434, 466, 465, 467], coeff := #[1, 1, 1, 1, 1, 1], bound := 1, weight := 466516, edges := #[⟨0, 1, 454⟩, ⟨0, 2, 456⟩, ⟨0, 3, 355⟩, ⟨0, 4, 352⟩, ⟨0, 5, 354⟩, ⟨1, 2, 296⟩, ⟨1, 3, 195⟩, ⟨1, 4, 192⟩, ⟨1, 5, 194⟩, ⟨2, 3, 199⟩, ⟨2, 4, 196⟩, ⟨2, 5, 198⟩, ⟨3, 4, 314⟩, ⟨3, 5, 315⟩, ⟨4, 5, 313⟩], triples := #[] }
def er173_371 : Row := { vars := #[193, 436, 357, 407], coeff := #[1, 1, 1, 1], bound := 1, weight := 176514, edges := #[⟨0, 1, 458⟩, ⟨0, 2, 354⟩, ⟨0, 3, 386⟩, ⟨1, 2, 194⟩, ⟨1, 3, 226⟩, ⟨2, 3, 257⟩], triples := #[] }
def er173_372 : Row := { vars := #[193, 436, 497, 498], coeff := #[1, 1, 1, 1], bound := 1, weight := 72497, edges := #[⟨0, 1, 458⟩, ⟨0, 2, 488⟩, ⟨0, 3, 487⟩, ⟨1, 2, 328⟩, ⟨1, 3, 327⟩, ⟨2, 3, 335⟩], triples := #[] }
def er173_373 : Row := { vars := #[193, 436, 465], coeff := #[1, 1, 1], bound := 1, weight := 533485, edges := #[⟨0, 1, 458⟩, ⟨0, 2, 510⟩, ⟨1, 2, 350⟩], triples := #[] }
def er173_374 : Row := { vars := #[193, 436, 370], coeff := #[1, 1, 1], bound := 1, weight := 5306, edges := #[⟨0, 1, 458⟩, ⟨0, 2, 370⟩, ⟨1, 2, 210⟩], triples := #[] }
def er173_375 : Row := { vars := #[193, 209, 498, 345], coeff := #[1, 1, 1, 1], bound := 1, weight := 212200, edges := #[⟨0, 1, 160⟩, ⟨0, 2, 487⟩, ⟨0, 3, 433⟩, ⟨1, 2, 477⟩, ⟨1, 3, 423⟩, ⟨2, 3, 281⟩], triples := #[] }
def er173_376 : Row := { vars := #[194, 437, 496], coeff := #[1, 1, 1], bound := 1, weight := 289252, edges := #[⟨0, 1, 459⟩, ⟨0, 2, 487⟩, ⟨1, 2, 327⟩], triples := #[] }
def er173_377 : Row := { vars := #[194, 196, 326, 467], coeff := #[1, 1, 1, 1], bound := 1, weight := 4627, edges := #[⟨0, 1, 141⟩, ⟨0, 2, 456⟩, ⟨0, 3, 510⟩, ⟨1, 2, 452⟩, ⟨1, 3, 506⟩, ⟨2, 3, 261⟩], triples := #[] }
def er173_378 : Row := { vars := #[194, 196, 496], coeff := #[1, 1, 1], bound := 1, weight := 139751, edges := #[⟨0, 1, 141⟩, ⟨0, 2, 487⟩, ⟨1, 2, 483⟩], triples := #[] }
def er173_379 : Row := { vars := #[194, 196, 466, 467], coeff := #[1, 1, 1, 1], bound := 1, weight := 43633, edges := #[⟨0, 1, 141⟩, ⟨0, 2, 511⟩, ⟨0, 3, 510⟩, ⟨1, 2, 507⟩, ⟨1, 3, 506⟩, ⟨2, 3, 315⟩], triples := #[] }
def er173_380 : Row := { vars := #[194, 197, 198, 210], coeff := #[1, 1, 1, 1], bound := 1, weight := 383214, edges := #[⟨0, 1, 143⟩, ⟨0, 2, 142⟩, ⟨0, 3, 161⟩, ⟨1, 2, 139⟩, ⟨1, 3, 166⟩, ⟨2, 3, 165⟩], triples := #[] }
def er173_381 : Row := { vars := #[195, 659, 670], coeff := #[1, 1, 1], bound := 1, weight := 94047, edges := #[⟨0, 1, 351⟩, ⟨0, 2, 342⟩, ⟨1, 2, 470⟩], triples := #[] }
def er173_382 : Row := { vars := #[195, 218, 491], coeff := #[1, 1, 1], bound := 1, weight := 730676, edges := #[⟨0, 1, 161⟩, ⟨0, 2, 468⟩, ⟨1, 2, 487⟩], triples := #[] }
def er173_383 : Row := { vars := #[198, 463, 571, 473], coeff := #[1, 1, 1, 1], bound := 1, weight := 192115, edges := #[⟨0, 1, 511⟩, ⟨0, 2, 260⟩, ⟨0, 3, 501⟩, ⟨1, 2, 84⟩, ⟨1, 3, 310⟩, ⟨2, 3, 107⟩], triples := #[] }
end HardyCapset20261020.Cert


