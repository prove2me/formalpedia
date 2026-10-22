-- Prove2me | Definitions.Def_HardyCapsetEvaluationData022rows06V420261021
-- name    : HardyCapsetEvaluationData022rows06V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T01:57:56.511304+00:00
-- url     : https://prove2.me/theorems/42c9dee3-46ff-43d6-80a0-d62cceab40c2
-- title:
--   HardyCapsetEvaluationData022rows06V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er022_384 : Row := { vars := #[300, 411, 416], coeff := #[1, 1, 1], bound := 1, weight := 191448, edges := #[⟨0, 1, 145⟩, ⟨0, 2, 139⟩, ⟨1, 2, 353⟩], triples := #[] }
def er022_385 : Row := { vars := #[301, 410, 416], coeff := #[1, 1, 1], bound := 1, weight := 290939, edges := #[⟨0, 1, 145⟩, ⟨0, 2, 138⟩, ⟨1, 2, 355⟩], triples := #[] }
def er022_386 : Row := { vars := #[309, 321, 571], coeff := #[1, 1, 1], bound := 1, weight := 97845, edges := #[⟨0, 1, 293⟩, ⟨0, 2, 61⟩, ⟨1, 2, 34⟩], triples := #[] }
def er022_387 : Row := { vars := #[312, 447, 432], coeff := #[1, 1, 1], bound := 1, weight := 639171, edges := #[⟨0, 1, 165⟩, ⟨0, 2, 136⟩, ⟨1, 2, 357⟩], triples := #[] }
def er022_388 : Row := { vars := #[313, 434, 444], coeff := #[1, 1, 1], bound := 1, weight := 636568, edges := #[⟨0, 1, 134⟩, ⟨0, 2, 166⟩, ⟨1, 2, 359⟩], triples := #[] }
def er022_389 : Row := { vars := #[318, 477, 551], coeff := #[1, 1, 1], bound := 1, weight := 920512, edges := #[⟨0, 1, 142⟩, ⟨0, 2, 38⟩, ⟨1, 2, 417⟩], triples := #[] }
def er022_390 : Row := { vars := #[320, 326, 215, 475], coeff := #[1, 1, 1, 1], bound := 1, weight := 242201, edges := #[⟨0, 1, 269⟩, ⟨0, 2, 361⟩, ⟨0, 3, 146⟩, ⟨1, 2, 353⟩, ⟨1, 3, 166⟩, ⟨2, 3, 281⟩], triples := #[] }
def er022_391 : Row := { vars := #[322, 328, 565, 27], coeff := #[1, 1, 1, 1], bound := 1, weight := 409800, edges := #[⟨0, 1, 273⟩, ⟨0, 2, 6⟩, ⟨0, 3, 472⟩, ⟨1, 2, 31⟩, ⟨1, 3, 470⟩, ⟨2, 3, 265⟩], triples := #[] }
def er022_392 : Row := { vars := #[323, 334, 7, 571], coeff := #[1, 1, 1, 1], bound := 1, weight := 21438, edges := #[⟨0, 1, 263⟩, ⟨0, 2, 470⟩, ⟨0, 3, 31⟩, ⟨1, 2, 472⟩, ⟨1, 3, 6⟩, ⟨2, 3, 275⟩], triples := #[] }
def er022_393 : Row := { vars := #[324, 485, 533], coeff := #[1, 1, 1], bound := 1, weight := 279540, edges := #[⟨0, 1, 152⟩, ⟨0, 2, 103⟩, ⟨1, 2, 509⟩], triples := #[] }
def er022_394 : Row := { vars := #[336, 550, 458], coeff := #[1, 1, 1], bound := 1, weight := 185774, edges := #[⟨0, 1, 5⟩, ⟨0, 2, 145⟩, ⟨1, 2, 438⟩], triples := #[] }
def er022_395 : Row := { vars := #[336, 472, 515], coeff := #[1, 1, 1], bound := 1, weight := 18857, edges := #[⟨0, 1, 152⟩, ⟨0, 2, 76⟩, ⟨1, 2, 479⟩], triples := #[] }
def er022_396 : Row := { vars := #[337, 562, 587], coeff := #[1, 1, 1], bound := 1, weight := 74669, edges := #[⟨0, 1, 22⟩, ⟨0, 2, 38⟩, ⟨1, 2, 477⟩], triples := #[] }
def er022_397 : Row := { vars := #[348, 466, 521], coeff := #[1, 1, 1], bound := 1, weight := 163722, edges := #[⟨0, 1, 134⟩, ⟨0, 2, 79⟩, ⟨1, 2, 479⟩], triples := #[] }
def er022_398 : Row := { vars := #[354, 409, 419], coeff := #[1, 1, 1], bound := 1, weight := 62275, edges := #[⟨0, 1, 87⟩, ⟨0, 2, 77⟩, ⟨1, 2, 352⟩], triples := #[] }
def er022_399 : Row := { vars := #[354, 425, 435], coeff := #[1, 1, 1], bound := 1, weight := 365645, edges := #[⟨0, 1, 107⟩, ⟨0, 2, 102⟩, ⟨1, 2, 360⟩], triples := #[] }
def er022_400 : Row := { vars := #[354, 441, 451], coeff := #[1, 1, 1], bound := 1, weight := 526959, edges := #[⟨0, 1, 97⟩, ⟨0, 2, 92⟩, ⟨1, 2, 372⟩], triples := #[] }
def er022_401 : Row := { vars := #[354, 451, 533], coeff := #[1, 1, 1], bound := 1, weight := 521, edges := #[⟨0, 1, 92⟩, ⟨0, 2, 2⟩, ⟨1, 2, 479⟩], triples := #[] }
def er022_402 : Row := { vars := #[355, 520, 418], coeff := #[1, 1, 1], bound := 1, weight := 500747, edges := #[⟨0, 1, 66⟩, ⟨0, 2, 77⟩, ⟨1, 2, 509⟩], triples := #[] }
def er022_403 : Row := { vars := #[355, 409, 418], coeff := #[1, 1, 1], bound := 1, weight := 170261, edges := #[⟨0, 1, 86⟩, ⟨0, 2, 77⟩, ⟨1, 2, 354⟩], triples := #[] }
def er022_404 : Row := { vars := #[355, 414, 421], coeff := #[1, 1, 1], bound := 1, weight := 186871, edges := #[⟨0, 1, 82⟩, ⟨0, 2, 75⟩, ⟨1, 2, 358⟩], triples := #[] }
def er022_405 : Row := { vars := #[356, 398, 529], coeff := #[1, 1, 1], bound := 1, weight := 93561, edges := #[⟨0, 1, 323⟩, ⟨0, 2, 15⟩, ⟨1, 2, 69⟩], triples := #[] }
def er022_406 : Row := { vars := #[356, 121, 411], coeff := #[1, 1, 1], bound := 1, weight := 362173, edges := #[⟨0, 1, 387⟩, ⟨0, 2, 75⟩, ⟨1, 2, 311⟩], triples := #[] }
def er022_407 : Row := { vars := #[360, 415, 453], coeff := #[1, 1, 1], bound := 1, weight := 7946, edges := #[⟨0, 1, 105⟩, ⟨0, 2, 76⟩, ⟨1, 2, 360⟩], triples := #[] }
def er022_408 : Row := { vars := #[360, 423, 445], coeff := #[1, 1, 1], bound := 1, weight := 341473, edges := #[⟨0, 1, 102⟩, ⟨0, 2, 84⟩, ⟨1, 2, 360⟩], triples := #[] }
def er022_409 : Row := { vars := #[360, 429, 451], coeff := #[1, 1, 1], bound := 1, weight := 272989, edges := #[⟨0, 1, 97⟩, ⟨0, 2, 77⟩, ⟨1, 2, 352⟩], triples := #[] }
def er022_410 : Row := { vars := #[360, 443, 437], coeff := #[1, 1, 1], bound := 1, weight := 326930, edges := #[⟨0, 1, 85⟩, ⟨0, 2, 94⟩, ⟨1, 2, 352⟩], triples := #[] }
def er022_411 : Row := { vars := #[364, 135, 455], coeff := #[1, 1, 1], bound := 1, weight := 13336, edges := #[⟨0, 1, 386⟩, ⟨0, 2, 86⟩, ⟨1, 2, 321⟩], triples := #[] }
def er022_412 : Row := { vars := #[364, 119, 435], coeff := #[1, 1, 1], bound := 1, weight := 634356, edges := #[⟨0, 1, 391⟩, ⟨0, 2, 96⟩, ⟨1, 2, 321⟩], triples := #[] }
def er022_413 : Row := { vars := #[367, 418, 429], coeff := #[1, 1, 1], bound := 1, weight := 149469, edges := #[⟨0, 1, 92⟩, ⟨0, 2, 86⟩, ⟨1, 2, 374⟩], triples := #[] }
def er022_414 : Row := { vars := #[367, 430, 417], coeff := #[1, 1, 1], bound := 1, weight := 494385, edges := #[⟨0, 1, 85⟩, ⟨0, 2, 93⟩, ⟨1, 2, 374⟩], triples := #[] }
def er022_415 : Row := { vars := #[372, 484, 500], coeff := #[1, 1, 1], bound := 1, weight := 291893, edges := #[⟨0, 1, 102⟩, ⟨0, 2, 70⟩, ⟨1, 2, 472⟩], triples := #[] }
def er022_416 : Row := { vars := #[374, 380, 137, 474], coeff := #[1, 1, 1, 1], bound := 1, weight := 86822, edges := #[⟨0, 1, 324⟩, ⟨0, 2, 360⟩, ⟨0, 3, 86⟩, ⟨1, 2, 352⟩, ⟨1, 3, 106⟩, ⟨2, 3, 335⟩], triples := #[] }
def er022_417 : Row := { vars := #[378, 491, 598], coeff := #[1, 1, 1], bound := 1, weight := 100058, edges := #[⟨0, 1, 74⟩, ⟨0, 2, 138⟩, ⟨1, 2, 455⟩], triples := #[] }
def er022_418 : Row := { vars := #[379, 513, 9, 524], coeff := #[1, 1, 1, 1], bound := 1, weight := 496260, edges := #[⟨0, 1, 34⟩, ⟨0, 2, 431⟩, ⟨0, 3, 14⟩, ⟨1, 2, 310⟩, ⟨1, 3, 419⟩, ⟨2, 3, 312⟩], triples := #[] }
def er022_419 : Row := { vars := #[379, 509, 477], coeff := #[1, 1, 1], bound := 1, weight := 79489, edges := #[⟨0, 1, 40⟩, ⟨0, 2, 106⟩, ⟨1, 2, 472⟩], triples := #[] }
def er022_420 : Row := { vars := #[379, 495, 491], coeff := #[1, 1, 1], bound := 1, weight := 366055, edges := #[⟨0, 1, 71⟩, ⟨0, 2, 75⟩, ⟨1, 2, 472⟩], triples := #[] }
def er022_421 : Row := { vars := #[381, 380, 523, 28], coeff := #[1, 1, 1, 1], bound := 1, weight := 278624, edges := #[⟨0, 1, 314⟩, ⟨0, 2, 13⟩, ⟨0, 3, 417⟩, ⟨1, 2, 10⟩, ⟨1, 3, 416⟩, ⟨2, 3, 325⟩], triples := #[] }
def er022_422 : Row := { vars := #[384, 483, 496], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 85⟩, ⟨0, 2, 57⟩, ⟨1, 2, 481⟩], triples := #[] }
def er022_423 : Row := { vars := #[384, 484, 593], coeff := #[1, 1, 1], bound := 1, weight := 44793, edges := #[⟨0, 1, 74⟩, ⟨0, 2, 138⟩, ⟨1, 2, 445⟩], triples := #[] }
def er022_424 : Row := { vars := #[397, 507, 461], coeff := #[1, 1, 1], bound := 1, weight := 723077, edges := #[⟨0, 1, 12⟩, ⟨0, 2, 104⟩, ⟨1, 2, 494⟩], triples := #[] }
def er022_425 : Row := { vars := #[402, 566, 471], coeff := #[1, 1, 1], bound := 1, weight := 154192, edges := #[⟨0, 1, 157⟩, ⟨0, 2, 105⟩, ⟨1, 2, 421⟩], triples := #[] }
def er022_426 : Row := { vars := #[402, 466, 575], coeff := #[1, 1, 1], bound := 1, weight := 343880, edges := #[⟨0, 1, 74⟩, ⟨0, 2, 139⟩, ⟨1, 2, 425⟩], triples := #[] }
def er022_427 : Row := { vars := #[403, 464, 509], coeff := #[1, 1, 1], bound := 1, weight := 2108, edges := #[⟨0, 1, 84⟩, ⟨0, 2, 32⟩, ⟨1, 2, 493⟩], triples := #[] }
def er022_428 : Row := { vars := #[411, 283, 416], coeff := #[1, 1, 1], bound := 1, weight := 293833, edges := #[⟨0, 1, 13⟩, ⟨0, 2, 353⟩, ⟨1, 2, 7⟩], triples := #[] }
def er022_429 : Row := { vars := #[427, 295, 452], coeff := #[1, 1, 1], bound := 1, weight := 590410, edges := #[⟨0, 1, 10⟩, ⟨0, 2, 357⟩, ⟨1, 2, 32⟩], triples := #[] }
def er022_430 : Row := { vars := #[427, 433, 282], coeff := #[1, 1, 1], bound := 1, weight := 85682, edges := #[⟨0, 1, 360⟩, ⟨0, 2, 34⟩, ⟨1, 2, 32⟩], triples := #[] }
def er022_431 : Row := { vars := #[433, 568, 282], coeff := #[1, 1, 1], bound := 1, weight := 636568, edges := #[⟨0, 1, 457⟩, ⟨0, 2, 32⟩, ⟨1, 2, 78⟩], triples := #[] }
def er022_432 : Row := { vars := #[441, 8, 567], coeff := #[1, 1, 1], bound := 1, weight := 184899, edges := #[⟨0, 1, 238⟩, ⟨0, 2, 443⟩, ⟨1, 2, 256⟩], triples := #[] }
def er022_433 : Row := { vars := #[476, 331, 557], coeff := #[1, 1, 1], bound := 1, weight := 678581, edges := #[⟨0, 1, 156⟩, ⟨0, 2, 427⟩, ⟨1, 2, 43⟩], triples := #[] }
def er022_434 : Row := { vars := #[478, 548, 319], coeff := #[1, 1, 1], bound := 1, weight := 391854, edges := #[⟨0, 1, 416⟩, ⟨0, 2, 138⟩, ⟨1, 2, 51⟩], triples := #[] }
def er022_435 : Row := { vars := #[482, 331, 563], coeff := #[1, 1, 1], bound := 1, weight := 288078, edges := #[⟨0, 1, 143⟩, ⟨0, 2, 417⟩, ⟨1, 2, 68⟩], triples := #[] }
def er022_436 : Row := { vars := #[485, 548, 331], coeff := #[1, 1, 1], bound := 1, weight := 33343, edges := #[⟨0, 1, 427⟩, ⟨0, 2, 138⟩, ⟨1, 2, 61⟩], triples := #[] }
def er022_437 : Row := { vars := #[519, 518, 385, 29], coeff := #[1, 1, 1, 1], bound := 1, weight := 596261, edges := #[⟨0, 1, 419⟩, ⟨0, 2, 14⟩, ⟨0, 3, 311⟩, ⟨1, 2, 11⟩, ⟨1, 3, 310⟩, ⟨2, 3, 431⟩], triples := #[] }
def er022_438 : Row := { vars := #[521, 520, 385, 27], coeff := #[1, 1, 1, 1], bound := 1, weight := 231218, edges := #[⟨0, 1, 423⟩, ⟨0, 2, 6⟩, ⟨0, 3, 311⟩, ⟨1, 2, 3⟩, ⟨1, 3, 310⟩, ⟨2, 3, 435⟩], triples := #[] }
def er022_439 : Row := { vars := #[560, 319, 567], coeff := #[1, 1, 1], bound := 1, weight := 165180, edges := #[⟨0, 1, 61⟩, ⟨0, 2, 496⟩, ⟨1, 2, 10⟩], triples := #[] }
def er022_440 : Row := { vars := #[13, 124, 153, 135, 137, 150], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 188008, edges := #[⟨3, 4, 131⟩, ⟨3, 5, 11⟩, ⟨4, 5, 3⟩, ⟨0, 3, 146⟩, ⟨2, 3, 14⟩, ⟨0, 4, 138⟩, ⟨2, 4, 6⟩, ⟨0, 5, 124⟩, ⟨2, 5, 149⟩], triples := #[⟨0, 1, 2⟩] }
def er022_441 : Row := { vars := #[13, 239, 485, 257, 480], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 9337, edges := #[⟨3, 4, 7⟩, ⟨1, 3, 192⟩, ⟨2, 3, 10⟩, ⟨0, 4, 201⟩, ⟨1, 4, 24⟩], triples := #[⟨0, 1, 2⟩] }
def er022_442 : Row := { vars := #[13, 239, 485, 26, 225], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 96166, edges := #[⟨3, 4, 398⟩, ⟨0, 3, 14⟩, ⟨2, 3, 197⟩, ⟨1, 4, 212⟩, ⟨2, 4, 33⟩], triples := #[⟨0, 1, 2⟩] }
def er022_443 : Row := { vars := #[13, 239, 485, 225, 486], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 255328, edges := #[⟨3, 4, 22⟩, ⟨1, 3, 212⟩, ⟨2, 3, 33⟩, ⟨0, 4, 197⟩, ⟨1, 4, 14⟩], triples := #[⟨0, 1, 2⟩] }
def er022_444 : Row := { vars := #[13, 293, 431, 137, 356], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 156245, edges := #[⟨3, 4, 388⟩, ⟨0, 3, 138⟩, ⟨2, 3, 311⟩, ⟨1, 4, 267⟩, ⟨2, 4, 103⟩], triples := #[⟨0, 1, 2⟩] }
def er022_445 : Row := { vars := #[13, 293, 431, 137, 150], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 140807, edges := #[⟨3, 4, 3⟩, ⟨0, 3, 138⟩, ⟨2, 3, 311⟩, ⟨0, 4, 124⟩, ⟨1, 4, 420⟩], triples := #[⟨0, 1, 2⟩] }
def er022_446 : Row := { vars := #[13, 293, 431, 289, 448], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 38354, edges := #[⟨3, 4, 7⟩, ⟨0, 3, 360⟩, ⟨2, 3, 23⟩, ⟨1, 4, 11⟩, ⟨2, 4, 353⟩], triples := #[⟨0, 1, 2⟩] }
def er022_447 : Row := { vars := #[13, 381, 521, 295, 213, 520], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 115758, edges := #[⟨3, 4, 455⟩, ⟨3, 5, 135⟩, ⟨4, 5, 193⟩, ⟨0, 3, 356⟩, ⟨2, 3, 138⟩, ⟨0, 4, 86⟩, ⟨2, 4, 197⟩, ⟨0, 5, 314⟩, ⟨2, 5, 423⟩], triples := #[⟨0, 1, 2⟩] }
end HardyCapset20261020.Cert


