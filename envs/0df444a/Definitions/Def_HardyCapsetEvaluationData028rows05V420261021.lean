-- Prove2me | Definitions.Def_HardyCapsetEvaluationData028rows05V420261021
-- name    : HardyCapsetEvaluationData028rows05V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:23:09.30254+00:00
-- url     : https://prove2.me/theorems/272583d3-5270-4f30-8328-5b55999a0d95
-- title:
--   HardyCapsetEvaluationData028rows05V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er028_320 : Row := { vars := #[241, 514, 260], coeff := #[1, 1, 1], bound := 1, weight := 123182, edges := #[⟨0, 1, 59⟩, ⟨0, 2, 267⟩, ⟨1, 2, 40⟩], triples := #[] }
def er028_321 : Row := { vars := #[241, 414, 341], coeff := #[1, 1, 1], bound := 1, weight := 507559, edges := #[⟨0, 1, 142⟩, ⟨0, 2, 232⟩, ⟨1, 2, 106⟩], triples := #[] }
def er028_322 : Row := { vars := #[242, 259, 417, 17], coeff := #[1, 1, 1, 1], bound := 1, weight := 314434, edges := #[⟨0, 1, 272⟩, ⟨0, 2, 163⟩, ⟨0, 3, 481⟩, ⟨1, 2, 153⟩, ⟨1, 3, 472⟩, ⟨2, 3, 209⟩], triples := #[] }
def er028_323 : Row := { vars := #[244, 524, 119], coeff := #[1, 1, 1], bound := 1, weight := 212947, edges := #[⟨0, 1, 10⟩, ⟨0, 2, 407⟩, ⟨1, 2, 197⟩], triples := #[] }
def er028_324 : Row := { vars := #[244, 555, 127], coeff := #[1, 1, 1], bound := 1, weight := 640697, edges := #[⟨0, 1, 23⟩, ⟨0, 2, 411⟩, ⟨1, 2, 197⟩], triples := #[] }
def er028_325 : Row := { vars := #[248, 555, 470], coeff := #[1, 1, 1], bound := 1, weight := 72322, edges := #[⟨0, 1, 7⟩, ⟨0, 2, 107⟩, ⟨1, 2, 360⟩], triples := #[] }
def er028_326 : Row := { vars := #[252, 514, 274], coeff := #[1, 1, 1], bound := 1, weight := 61307, edges := #[⟨0, 1, 49⟩, ⟨0, 2, 256⟩, ⟨1, 2, 68⟩], triples := #[] }
def er028_327 : Row := { vars := #[252, 389, 468], coeff := #[1, 1, 1], bound := 1, weight := 443102, edges := #[⟨0, 1, 202⟩, ⟨0, 2, 106⟩, ⟨1, 2, 68⟩], triples := #[] }
def er028_328 : Row := { vars := #[252, 274, 418], coeff := #[1, 1, 1], bound := 1, weight := 415581, edges := #[⟨0, 1, 256⟩, ⟨0, 2, 145⟩, ⟨1, 2, 163⟩], triples := #[] }
def er028_329 : Row := { vars := #[257, 516, 379], coeff := #[1, 1, 1], bound := 1, weight := 417020, edges := #[⟨0, 1, 32⟩, ⟨0, 2, 221⟩, ⟨1, 2, 135⟩], triples := #[] }
def er028_330 : Row := { vars := #[257, 544, 393], coeff := #[1, 1, 1], bound := 1, weight := 160034, edges := #[⟨0, 1, 7⟩, ⟨0, 2, 209⟩, ⟨1, 2, 135⟩], triples := #[] }
def er028_331 : Row := { vars := #[258, 514, 268], coeff := #[1, 1, 1], bound := 1, weight := 396481, edges := #[⟨0, 1, 41⟩, ⟨0, 2, 256⟩, ⟨1, 2, 71⟩], triples := #[] }
def er028_332 : Row := { vars := #[258, 469, 383], coeff := #[1, 1, 1], bound := 1, weight := 457163, edges := #[⟨0, 1, 102⟩, ⟨0, 2, 202⟩, ⟨1, 2, 70⟩], triples := #[] }
def er028_333 : Row := { vars := #[260, 416, 266], coeff := #[1, 1, 1], bound := 1, weight := 80558, edges := #[⟨0, 1, 153⟩, ⟨0, 2, 257⟩, ⟨1, 2, 142⟩], triples := #[] }
def er028_334 : Row := { vars := #[262, 549, 474], coeff := #[1, 1, 1], bound := 1, weight := 175657, edges := #[⟨0, 1, 35⟩, ⟨0, 2, 96⟩, ⟨1, 2, 364⟩], triples := #[] }
def er028_335 : Row := { vars := #[263, 507, 528], coeff := #[1, 1, 1], bound := 1, weight := 107992, edges := #[⟨0, 1, 102⟩, ⟨0, 2, 20⟩, ⟨1, 2, 370⟩], triples := #[] }
def er028_336 : Row := { vars := #[266, 271, 510], coeff := #[1, 1, 1], bound := 1, weight := 33391, edges := #[⟨0, 1, 267⟩, ⟨0, 2, 59⟩, ⟨1, 2, 58⟩], triples := #[] }
def er028_337 : Row := { vars := #[266, 121, 327], coeff := #[1, 1, 1], bound := 1, weight := 879471, edges := #[⟨0, 1, 408⟩, ⟨0, 2, 229⟩, ⟨1, 2, 356⟩], triples := #[] }
def er028_338 : Row := { vars := #[267, 356, 207], coeff := #[1, 1, 1], bound := 1, weight := 119267, edges := #[⟨0, 1, 232⟩, ⟨0, 2, 357⟩, ⟨1, 2, 460⟩], triples := #[] }
def er028_339 : Row := { vars := #[273, 378, 496], coeff := #[1, 1, 1], bound := 1, weight := 339459, edges := #[⟨0, 1, 208⟩, ⟨0, 2, 104⟩, ⟨1, 2, 58⟩], triples := #[] }
def er028_340 : Row := { vars := #[275, 524, 127], coeff := #[1, 1, 1], bound := 1, weight := 359304, edges := #[⟨0, 1, 23⟩, ⟨0, 2, 407⟩, ⟨1, 2, 213⟩], triples := #[] }
def er028_341 : Row := { vars := #[277, 430, 590], coeff := #[1, 1, 1], bound := 1, weight := 54960, edges := #[⟨0, 1, 85⟩, ⟨0, 2, 59⟩, ⟨1, 2, 367⟩], triples := #[] }
def er028_342 : Row := { vars := #[278, 317, 513], coeff := #[1, 1, 1], bound := 1, weight := 443695, edges := #[⟨0, 1, 280⟩, ⟨0, 2, 33⟩, ⟨1, 2, 7⟩], triples := #[] }
def er028_343 : Row := { vars := #[281, 8, 432], coeff := #[1, 1, 1], bound := 1, weight := 929625, edges := #[⟨0, 1, 460⟩, ⟨0, 2, 78⟩, ⟨1, 2, 310⟩], triples := #[] }
def er028_344 : Row := { vars := #[283, 351, 587], coeff := #[1, 1, 1], bound := 1, weight := 60339, edges := #[⟨0, 1, 215⟩, ⟨0, 2, 59⟩, ⟨1, 2, 134⟩], triples := #[] }
def er028_345 : Row := { vars := #[283, 287, 408], coeff := #[1, 1, 1], bound := 1, weight := 131117, edges := #[⟨0, 1, 279⟩, ⟨0, 2, 144⟩, ⟨1, 2, 134⟩], triples := #[] }
def er028_346 : Row := { vars := #[284, 16, 466], coeff := #[1, 1, 1], bound := 1, weight := 197686, edges := #[⟨0, 1, 465⟩, ⟨0, 2, 96⟩, ⟨1, 2, 311⟩], triples := #[] }
def er028_347 : Row := { vars := #[284, 427, 326], coeff := #[1, 1, 1], bound := 1, weight := 568110, edges := #[⟨0, 1, 77⟩, ⟨0, 2, 192⟩, ⟨1, 2, 14⟩], triples := #[] }
def er028_348 : Row := { vars := #[284, 441, 350], coeff := #[1, 1, 1], bound := 1, weight := 32067, edges := #[⟨0, 1, 102⟩, ⟨0, 2, 222⟩, ⟨1, 2, 20⟩], triples := #[] }
def er028_349 : Row := { vars := #[284, 311, 513], coeff := #[1, 1, 1], bound := 1, weight := 202140, edges := #[⟨0, 1, 280⟩, ⟨0, 2, 30⟩, ⟨1, 2, 15⟩], triples := #[] }
def er028_350 : Row := { vars := #[287, 297, 515], coeff := #[1, 1, 1], bound := 1, weight := 523853, edges := #[⟨0, 1, 289⟩, ⟨0, 2, 20⟩, ⟨1, 2, 12⟩], triples := #[] }
def er028_351 : Row := { vars := #[287, 297, 412], coeff := #[1, 1, 1], bound := 1, weight := 137775, edges := #[⟨0, 1, 289⟩, ⟨0, 2, 152⟩, ⟨1, 2, 144⟩], triples := #[] }
def er028_352 : Row := { vars := #[290, 589, 453], coeff := #[1, 1, 1], bound := 1, weight := 59130, edges := #[⟨0, 1, 48⟩, ⟨0, 2, 93⟩, ⟨1, 2, 358⟩], triples := #[] }
def er028_353 : Row := { vars := #[292, 427, 330], coeff := #[1, 1, 1], bound := 1, weight := 431891, edges := #[⟨0, 1, 105⟩, ⟨0, 2, 218⟩, ⟨1, 2, 10⟩], triples := #[] }
def er028_354 : Row := { vars := #[292, 455, 363], coeff := #[1, 1, 1], bound := 1, weight := 38650, edges := #[⟨0, 1, 85⟩, ⟨0, 2, 192⟩, ⟨1, 2, 31⟩], triples := #[] }
def er028_355 : Row := { vars := #[294, 559, 348], coeff := #[1, 1, 1], bound := 1, weight := 113255, edges := #[⟨0, 1, 69⟩, ⟨0, 2, 203⟩, ⟨1, 2, 162⟩], triples := #[] }
def er028_356 : Row := { vars := #[296, 413, 382], coeff := #[1, 1, 1], bound := 1, weight := 169532, edges := #[⟨0, 1, 144⟩, ⟨0, 2, 239⟩, ⟨1, 2, 85⟩], triples := #[] }
def er028_357 : Row := { vars := #[300, 259, 515], coeff := #[1, 1, 1], bound := 1, weight := 100502, edges := #[⟨0, 1, 250⟩, ⟨0, 2, 7⟩, ⟨1, 2, 38⟩], triples := #[] }
def er028_358 : Row := { vars := #[300, 558, 336], coeff := #[1, 1, 1], bound := 1, weight := 840550, edges := #[⟨0, 1, 68⟩, ⟨0, 2, 221⟩, ⟨1, 2, 136⟩], triples := #[] }
def er028_359 : Row := { vars := #[303, 356, 573], coeff := #[1, 1, 1], bound := 1, weight := 68221, edges := #[⟨0, 1, 199⟩, ⟨0, 2, 56⟩, ⟨1, 2, 142⟩], triples := #[] }
def er028_360 : Row := { vars := #[303, 572, 333], coeff := #[1, 1, 1], bound := 1, weight := 125183, edges := #[⟨0, 1, 58⟩, ⟨0, 2, 221⟩, ⟨1, 2, 164⟩], triples := #[] }
def er028_361 : Row := { vars := #[305, 439, 599], coeff := #[1, 1, 1], bound := 1, weight := 604004, edges := #[⟨0, 1, 92⟩, ⟨0, 2, 66⟩, ⟨1, 2, 371⟩], triples := #[] }
def er028_362 : Row := { vars := #[306, 441, 349], coeff := #[1, 1, 1], bound := 1, weight := 58131, edges := #[⟨0, 1, 82⟩, ⟨0, 2, 196⟩, ⟨1, 2, 21⟩], triples := #[] }
def er028_363 : Row := { vars := #[308, 362, 559], coeff := #[1, 1, 1], bound := 1, weight := 83318, edges := #[⟨0, 1, 215⟩, ⟨0, 2, 59⟩, ⟨1, 2, 152⟩], triples := #[] }
def er028_364 : Row := { vars := #[308, 312, 408], coeff := #[1, 1, 1], bound := 1, weight := 606074, edges := #[⟨0, 1, 289⟩, ⟨0, 2, 157⟩, ⟨1, 2, 152⟩], triples := #[] }
def er028_365 : Row := { vars := #[309, 18, 429], coeff := #[1, 1, 1], bound := 1, weight := 532051, edges := #[⟨0, 1, 461⟩, ⟨0, 2, 93⟩, ⟨1, 2, 321⟩], triples := #[] }
def er028_366 : Row := { vars := #[309, 455, 346], coeff := #[1, 1, 1], bound := 1, weight := 51949, edges := #[⟨0, 1, 105⟩, ⟨0, 2, 192⟩, ⟨1, 2, 6⟩], triples := #[] }
def er028_367 : Row := { vars := #[312, 6, 333], coeff := #[1, 1, 1], bound := 1, weight := 58964, edges := #[⟨0, 1, 462⟩, ⟨0, 2, 210⟩, ⟨1, 2, 417⟩], triples := #[] }
def er028_368 : Row := { vars := #[312, 440, 343], coeff := #[1, 1, 1], bound := 1, weight := 216423, edges := #[⟨0, 1, 76⟩, ⟨0, 2, 196⟩, ⟨1, 2, 25⟩], triples := #[] }
def er028_369 : Row := { vars := #[312, 407, 410], coeff := #[1, 1, 1], bound := 1, weight := 42221, edges := #[⟨0, 1, 243⟩, ⟨0, 2, 134⟩, ⟨1, 2, 79⟩], triples := #[] }
def er028_370 : Row := { vars := #[313, 374, 409], coeff := #[1, 1, 1], bound := 1, weight := 169532, edges := #[⟨0, 1, 240⟩, ⟨0, 2, 154⟩, ⟨1, 2, 77⟩], triples := #[] }
def er028_371 : Row := { vars := #[314, 356, 559], coeff := #[1, 1, 1], bound := 1, weight := 474545, edges := #[⟨0, 1, 215⟩, ⟨0, 2, 56⟩, ⟨1, 2, 155⟩], triples := #[] }
def er028_372 : Row := { vars := #[318, 443, 450], coeff := #[1, 1, 1], bound := 1, weight := 292029, edges := #[⟨0, 1, 71⟩, ⟨0, 2, 66⟩, ⟨1, 2, 418⟩], triples := #[] }
def er028_373 : Row := { vars := #[319, 475, 479], coeff := #[1, 1, 1], bound := 1, weight := 501143, edges := #[⟨0, 1, 12⟩, ⟨0, 2, 2⟩, ⟨1, 2, 439⟩], triples := #[] }
def er028_374 : Row := { vars := #[319, 484, 492], coeff := #[1, 1, 1], bound := 1, weight := 318597, edges := #[⟨0, 1, 33⟩, ⟨0, 2, 32⟩, ⟨1, 2, 440⟩], triples := #[] }
def er028_375 : Row := { vars := #[320, 429, 467], coeff := #[1, 1, 1], bound := 1, weight := 180358, edges := #[⟨0, 1, 71⟩, ⟨0, 2, 41⟩, ⟨1, 2, 418⟩], triples := #[] }
def er028_376 : Row := { vars := #[321, 478, 501], coeff := #[1, 1, 1], bound := 1, weight := 452097, edges := #[⟨0, 1, 32⟩, ⟨0, 2, 13⟩, ⟨1, 2, 440⟩], triples := #[] }
def er028_377 : Row := { vars := #[322, 460, 450], coeff := #[1, 1, 1], bound := 1, weight := 504951, edges := #[⟨0, 1, 71⟩, ⟨0, 2, 41⟩, ⟨1, 2, 416⟩], triples := #[] }
def er028_378 : Row := { vars := #[323, 495, 473], coeff := #[1, 1, 1], bound := 1, weight := 87810, edges := #[⟨0, 1, 4⟩, ⟨0, 2, 23⟩, ⟨1, 2, 449⟩], triples := #[] }
def er028_379 : Row := { vars := #[324, 435, 208], coeff := #[1, 1, 1], bound := 1, weight := 287319, edges := #[⟨0, 1, 7⟩, ⟨0, 2, 462⟩, ⟨1, 2, 207⟩], triples := #[] }
def er028_380 : Row := { vars := #[324, 463, 568], coeff := #[1, 1, 1], bound := 1, weight := 262124, edges := #[⟨0, 1, 22⟩, ⟨0, 2, 138⟩, ⟨1, 2, 369⟩], triples := #[] }
def er028_381 : Row := { vars := #[328, 422, 363], coeff := #[1, 1, 1], bound := 1, weight := 961351, edges := #[⟨0, 1, 70⟩, ⟨0, 2, 312⟩, ⟨1, 2, 43⟩], triples := #[] }
def er028_382 : Row := { vars := #[329, 337, 415], coeff := #[1, 1, 1], bound := 1, weight := 495300, edges := #[⟨0, 1, 311⟩, ⟨0, 2, 83⟩, ⟨1, 2, 74⟩], triples := #[] }
def er028_383 : Row := { vars := #[333, 361, 119, 441], coeff := #[1, 1, 1, 1], bound := 1, weight := 65234, edges := #[⟨0, 1, 320⟩, ⟨0, 2, 356⟩, ⟨0, 3, 30⟩, ⟨1, 2, 360⟩, ⟨1, 3, 2⟩, ⟨2, 3, 253⟩], triples := #[] }
end HardyCapset20261020.Cert


