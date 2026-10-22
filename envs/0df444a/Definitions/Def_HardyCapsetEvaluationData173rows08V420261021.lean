-- Prove2me | Definitions.Def_HardyCapsetEvaluationData173rows08V420261021
-- name    : HardyCapsetEvaluationData173rows08V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T03:08:59.586102+00:00
-- url     : https://prove2.me/theorems/7414a27e-1eef-442a-899c-c13bda485758
-- title:
--   HardyCapsetEvaluationData173rows08V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er173_512 : Row := { vars := #[373, 674, 675], coeff := #[1, 1, 1], bound := 1, weight := 159636, edges := #[⟨0, 1, 70⟩, ⟨0, 2, 71⟩, ⟨1, 2, 488⟩], triples := #[] }
def er173_513 : Row := { vars := #[374, 525, 593], coeff := #[1, 1, 1], bound := 1, weight := 275838, edges := #[⟨0, 1, 190⟩, ⟨0, 2, 111⟩, ⟨1, 2, 511⟩], triples := #[] }
def er173_514 : Row := { vars := #[374, 144, 489, 619], coeff := #[1, 1, 1, 1], bound := 1, weight := 280658, edges := #[⟨0, 1, 445⟩, ⟨0, 2, 194⟩, ⟨0, 3, 80⟩, ⟨1, 2, 390⟩, ⟨1, 3, 261⟩, ⟨2, 3, 46⟩], triples := #[] }
def er173_515 : Row := { vars := #[374, 593, 597], coeff := #[1, 1, 1], bound := 1, weight := 174731, edges := #[⟨0, 1, 111⟩, ⟨0, 2, 119⟩, ⟨1, 2, 433⟩], triples := #[] }
def er173_516 : Row := { vars := #[375, 643, 135], coeff := #[1, 1, 1], bound := 1, weight := 8614, edges := #[⟨0, 1, 65⟩, ⟨0, 2, 440⟩, ⟨1, 2, 199⟩], triples := #[] }
def er173_517 : Row := { vars := #[375, 135, 550], coeff := #[1, 1, 1], bound := 1, weight := 464569, edges := #[⟨0, 1, 440⟩, ⟨0, 2, 179⟩, ⟨1, 2, 333⟩], triples := #[] }
def er173_518 : Row := { vars := #[381, 633, 575], coeff := #[1, 1, 1], bound := 1, weight := 366663, edges := #[⟨0, 1, 80⟩, ⟨0, 2, 130⟩, ⟨1, 2, 426⟩], triples := #[] }
def er173_519 : Row := { vars := #[382, 544, 636], coeff := #[1, 1, 1], bound := 1, weight := 295384, edges := #[⟨0, 1, 183⟩, ⟨0, 2, 79⟩, ⟨1, 2, 481⟩], triples := #[] }
def er173_520 : Row := { vars := #[384, 633, 569, 572], coeff := #[1, 1, 1, 1], bound := 1, weight := 294113, edges := #[⟨0, 1, 78⟩, ⟨0, 2, 142⟩, ⟨0, 3, 134⟩, ⟨1, 2, 509⟩, ⟨1, 3, 505⟩, ⟨2, 3, 403⟩], triples := #[] }
def er173_521 : Row := { vars := #[389, 646, 668, 630], coeff := #[1, 1, 1, 1], bound := 1, weight := 850560, edges := #[⟨0, 1, 59⟩, ⟨0, 2, 24⟩, ⟨0, 3, 96⟩, ⟨1, 2, 502⟩, ⟨1, 3, 390⟩, ⟨2, 3, 368⟩], triples := #[] }
def er173_522 : Row := { vars := #[389, 628, 568, 669], coeff := #[1, 1, 1, 1], bound := 1, weight := 149441, edges := #[⟨0, 1, 97⟩, ⟨0, 2, 156⟩, ⟨0, 3, 23⟩, ⟨1, 2, 502⟩, ⟨1, 3, 370⟩, ⟨2, 3, 410⟩], triples := #[] }
def er173_523 : Row := { vars := #[392, 575, 624], coeff := #[1, 1, 1], bound := 1, weight := 148109, edges := #[⟨0, 1, 126⟩, ⟨0, 2, 80⟩, ⟨1, 2, 433⟩], triples := #[] }
def er173_524 : Row := { vars := #[396, 578, 629], coeff := #[1, 1, 1], bound := 1, weight := 371417, edges := #[⟨0, 1, 127⟩, ⟨0, 2, 77⟩, ⟨1, 2, 431⟩], triples := #[] }
def er173_525 : Row := { vars := #[396, 402, 56], coeff := #[1, 1, 1], bound := 1, weight := 298129, edges := #[⟨0, 1, 275⟩, ⟨0, 2, 487⟩, ⟨1, 2, 483⟩], triples := #[] }
def er173_526 : Row := { vars := #[401, 654, 560], coeff := #[1, 1, 1], bound := 1, weight := 8141, edges := #[⟨0, 1, 23⟩, ⟨0, 2, 156⟩, ⟨1, 2, 406⟩], triples := #[] }
def er173_527 : Row := { vars := #[404, 675, 676, 652], coeff := #[1, 1, 1, 1], bound := 1, weight := 276726, edges := #[⟨0, 1, 34⟩, ⟨0, 2, 33⟩, ⟨0, 3, 69⟩, ⟨1, 2, 489⟩, ⟨1, 3, 511⟩, ⟨2, 3, 510⟩], triples := #[] }
def er173_528 : Row := { vars := #[405, 531, 618], coeff := #[1, 1, 1], bound := 1, weight := 166590, edges := #[⟨0, 1, 174⟩, ⟨0, 2, 123⟩, ⟨1, 2, 480⟩], triples := #[] }
def er173_529 : Row := { vars := #[405, 682, 525], coeff := #[1, 1, 1], bound := 1, weight := 291532, edges := #[⟨0, 1, 45⟩, ⟨0, 2, 178⟩, ⟨1, 2, 433⟩], triples := #[] }
def er173_530 : Row := { vars := #[405, 594, 458, 143], coeff := #[1, 1, 1, 1], bound := 1, weight := 45327, edges := #[⟨0, 1, 81⟩, ⟨0, 2, 192⟩, ⟨0, 3, 425⟩, ⟨1, 2, 10⟩, ⟨1, 3, 281⟩, ⟨2, 3, 400⟩], triples := #[] }
def er173_531 : Row := { vars := #[406, 531, 593], coeff := #[1, 1, 1], bound := 1, weight := 275346, edges := #[⟨0, 1, 175⟩, ⟨0, 2, 80⟩, ⟨1, 2, 502⟩], triples := #[] }
def er173_532 : Row := { vars := #[406, 684, 680], coeff := #[1, 1, 1], bound := 1, weight := 206928, edges := #[⟨0, 1, 64⟩, ⟨0, 2, 44⟩, ⟨1, 2, 509⟩], triples := #[] }
def er173_533 : Row := { vars := #[406, 565, 680], coeff := #[1, 1, 1], bound := 1, weight := 174383, edges := #[⟨0, 1, 191⟩, ⟨0, 2, 44⟩, ⟨1, 2, 455⟩], triples := #[] }
def er173_534 : Row := { vars := #[406, 457, 100, 680], coeff := #[1, 1, 1, 1], bound := 1, weight := 89885, edges := #[⟨0, 1, 195⟩, ⟨0, 2, 500⟩, ⟨0, 3, 44⟩, ⟨1, 2, 410⟩, ⟨1, 3, 144⟩, ⟨2, 3, 283⟩], triples := #[] }
def er173_535 : Row := { vars := #[407, 56, 595, 456], coeff := #[1, 1, 1, 1], bound := 1, weight := 202433, edges := #[⟨0, 1, 464⟩, ⟨0, 2, 83⟩, ⟨0, 3, 192⟩, ⟨1, 2, 313⟩, ⟨1, 3, 424⟩, ⟨2, 3, 9⟩], triples := #[] }
def er173_536 : Row := { vars := #[409, 495, 52], coeff := #[1, 1, 1], bound := 1, weight := 137833, edges := #[⟨0, 1, 242⟩, ⟨0, 2, 463⟩, ⟨1, 2, 405⟩], triples := #[] }
def er173_537 : Row := { vars := #[409, 495, 253], coeff := #[1, 1, 1], bound := 1, weight := 350037, edges := #[⟨0, 1, 242⟩, ⟨0, 2, 365⟩, ⟨1, 2, 459⟩], triples := #[] }
def er173_538 : Row := { vars := #[413, 224, 477], coeff := #[1, 1, 1], bound := 1, weight := 187632, edges := #[⟨0, 1, 385⟩, ⟨0, 2, 196⟩, ⟨1, 2, 503⟩], triples := #[] }
def er173_539 : Row := { vars := #[415, 609, 554, 557], coeff := #[1, 1, 1, 1], bound := 1, weight := 237451, edges := #[⟨0, 1, 79⟩, ⟨0, 2, 142⟩, ⟨0, 3, 134⟩, ⟨1, 2, 489⟩, ⟨1, 3, 485⟩, ⟨2, 3, 393⟩], triples := #[] }
def er173_540 : Row := { vars := #[416, 696, 650, 647], coeff := #[1, 1, 1, 1], bound := 1, weight := 633479, edges := #[⟨0, 1, 41⟩, ⟨0, 2, 4⟩, ⟨0, 3, 12⟩, ⟨1, 2, 483⟩, ⟨1, 3, 487⟩, ⟨2, 3, 467⟩], triples := #[] }
def er173_541 : Row := { vars := #[421, 645, 692, 606], coeff := #[1, 1, 1, 1], bound := 1, weight := 622586, edges := #[⟨0, 1, 23⟩, ⟨0, 2, 60⟩, ⟨0, 3, 97⟩, ⟨1, 2, 480⟩, ⟨1, 3, 400⟩, ⟨2, 3, 368⟩], triples := #[] }
def er173_542 : Row := { vars := #[425, 519, 605], coeff := #[1, 1, 1], bound := 1, weight := 24528, edges := #[⟨0, 1, 174⟩, ⟨0, 2, 77⟩, ⟨1, 2, 507⟩], triples := #[] }
def er173_543 : Row := { vars := #[425, 552, 592], coeff := #[1, 1, 1], bound := 1, weight := 594520, edges := #[⟨0, 1, 137⟩, ⟨0, 2, 91⟩, ⟨1, 2, 484⟩], triples := #[] }
def er173_544 : Row := { vars := #[425, 143, 431], coeff := #[1, 1, 1], bound := 1, weight := 256324, edges := #[⟨0, 1, 434⟩, ⟨0, 2, 295⟩, ⟨1, 2, 430⟩], triples := #[] }
def er173_545 : Row := { vars := #[427, 548, 646], coeff := #[1, 1, 1], bound := 1, weight := 149441, edges := #[⟨0, 1, 151⟩, ⟨0, 2, 7⟩, ⟨1, 2, 453⟩], triples := #[] }
def er173_546 : Row := { vars := #[427, 691, 563], coeff := #[1, 1, 1], bound := 1, weight := 289266, edges := #[⟨0, 1, 43⟩, ⟨0, 2, 186⟩, ⟨1, 2, 453⟩], triples := #[] }
def er173_547 : Row := { vars := #[428, 685, 600, 689], coeff := #[1, 1, 1, 1], bound := 1, weight := 174731, edges := #[⟨0, 1, 48⟩, ⟨0, 2, 79⟩, ⟨0, 3, 40⟩, ⟨1, 2, 368⟩, ⟨1, 3, 500⟩, ⟨2, 3, 364⟩], triples := #[] }
def er173_548 : Row := { vars := #[429, 687, 603, 599], coeff := #[1, 1, 1, 1], bound := 1, weight := 670680, edges := #[⟨0, 1, 41⟩, ⟨0, 2, 74⟩, ⟨0, 3, 82⟩, ⟨1, 2, 367⟩, ⟨1, 3, 371⟩, ⟨2, 3, 425⟩], triples := #[] }
def er173_549 : Row := { vars := #[435, 651, 699, 700], coeff := #[1, 1, 1, 1], bound := 1, weight := 533485, edges := #[⟨0, 1, 33⟩, ⟨0, 2, 70⟩, ⟨0, 3, 69⟩, ⟨1, 2, 488⟩, ⟨1, 3, 487⟩, ⟨2, 3, 509⟩], triples := #[] }
def er173_550 : Row := { vars := #[437, 525, 656], coeff := #[1, 1, 1], bound := 1, weight := 167456, edges := #[⟨0, 1, 100⟩, ⟨0, 2, 182⟩, ⟨1, 2, 457⟩], triples := #[] }
def er173_551 : Row := { vars := #[437, 531, 682], coeff := #[1, 1, 1], bound := 1, weight := 58203, edges := #[⟨0, 1, 90⟩, ⟨0, 2, 171⟩, ⟨1, 2, 426⟩], triples := #[] }
def er173_552 : Row := { vars := #[437, 695, 682], coeff := #[1, 1, 1], bound := 1, weight := 210520, edges := #[⟨0, 1, 175⟩, ⟨0, 2, 171⟩, ⟨1, 2, 502⟩], triples := #[] }
def er173_553 : Row := { vars := #[442, 530, 450], coeff := #[1, 1, 1], bound := 1, weight := 61490, edges := #[⟨0, 1, 95⟩, ⟨0, 2, 300⟩, ⟨1, 2, 82⟩], triples := #[] }
def er173_554 : Row := { vars := #[444, 540, 449], coeff := #[1, 1, 1], bound := 1, weight := 13218, edges := #[⟨0, 1, 82⟩, ⟨0, 2, 300⟩, ⟨1, 2, 105⟩], triples := #[] }
def er173_555 : Row := { vars := #[444, 221, 252], coeff := #[1, 1, 1], bound := 1, weight := 103114, edges := #[⟨0, 1, 460⟩, ⟨0, 2, 490⟩, ⟨1, 2, 190⟩], triples := #[] }
def er173_556 : Row := { vars := #[454, 635, 636], coeff := #[1, 1, 1], bound := 1, weight := 10510, edges := #[⟨0, 1, 33⟩, ⟨0, 2, 35⟩, ⟨1, 2, 456⟩], triples := #[] }
def er173_557 : Row := { vars := #[455, 525, 681], coeff := #[1, 1, 1], bound := 1, weight := 174731, edges := #[⟨0, 1, 130⟩, ⟨0, 2, 140⟩, ⟨1, 2, 434⟩], triples := #[] }
def er173_558 : Row := { vars := #[455, 608, 593], coeff := #[1, 1, 1], bound := 1, weight := 274087, edges := #[⟨0, 1, 18⟩, ⟨0, 2, 8⟩, ⟨1, 2, 426⟩], triples := #[] }
def er173_559 : Row := { vars := #[462, 545, 581], coeff := #[1, 1, 1], bound := 1, weight := 655275, edges := #[⟨0, 1, 119⟩, ⟨0, 2, 59⟩, ⟨1, 2, 510⟩], triples := #[] }
def er173_560 : Row := { vars := #[463, 473, 91], coeff := #[1, 1, 1], bound := 1, weight := 346901, edges := #[⟨0, 1, 310⟩, ⟨0, 2, 406⟩, ⟨1, 2, 411⟩], triples := #[] }
def er173_561 : Row := { vars := #[466, 609, 584, 587], coeff := #[1, 1, 1, 1], bound := 1, weight := 489853, edges := #[⟨0, 1, 6⟩, ⟨0, 2, 48⟩, ⟨0, 3, 40⟩, ⟨1, 2, 457⟩, ⟨1, 3, 453⟩, ⟨2, 3, 413⟩], triples := #[] }
def er173_562 : Row := { vars := #[471, 691, 606, 567], coeff := #[1, 1, 1, 1], bound := 1, weight := 130665, edges := #[⟨0, 1, 157⟩, ⟨0, 2, 24⟩, ⟨0, 3, 96⟩, ⟨1, 2, 370⟩, ⟨1, 3, 448⟩, ⟨2, 3, 464⟩], triples := #[] }
def er173_563 : Row := { vars := #[475, 481, 56], coeff := #[1, 1, 1], bound := 1, weight := 240054, edges := #[⟨0, 1, 327⟩, ⟨0, 2, 435⟩, ⟨1, 2, 431⟩], triples := #[] }
def er173_564 : Row := { vars := #[477, 641, 692], coeff := #[1, 1, 1], bound := 1, weight := 157675, edges := #[⟨0, 1, 187⟩, ⟨0, 2, 137⟩, ⟨1, 2, 485⟩], triples := #[] }
def er173_565 : Row := { vars := #[477, 679, 568], coeff := #[1, 1, 1], bound := 1, weight := 461074, edges := #[⟨0, 1, 150⟩, ⟨0, 2, 77⟩, ⟨1, 2, 452⟩], triples := #[] }
def er173_566 : Row := { vars := #[478, 598, 602, 687], coeff := #[1, 1, 1, 1], bound := 1, weight := 217923, edges := #[⟨0, 1, 12⟩, ⟨0, 2, 4⟩, ⟨0, 3, 138⟩, ⟨1, 2, 424⟩, ⟨1, 3, 369⟩, ⟨2, 3, 365⟩], triples := #[] }
def er173_567 : Row := { vars := #[481, 591, 561], coeff := #[1, 1, 1], bound := 1, weight := 198654, edges := #[⟨0, 1, 24⟩, ⟨0, 2, 96⟩, ⟨1, 2, 460⟩], triples := #[] }
def er173_568 : Row := { vars := #[482, 675, 559], coeff := #[1, 1, 1], bound := 1, weight := 328111, edges := #[⟨0, 1, 178⟩, ⟨0, 2, 118⟩, ⟨1, 2, 435⟩], triples := #[] }
def er173_569 : Row := { vars := #[485, 612, 613, 589], coeff := #[1, 1, 1, 1], bound := 1, weight := 349735, edges := #[⟨0, 1, 33⟩, ⟨0, 2, 34⟩, ⟨0, 3, 70⟩, ⟨1, 2, 435⟩, ⟨1, 3, 456⟩, ⟨2, 3, 457⟩], triples := #[] }
def er173_570 : Row := { vars := #[486, 643, 92], coeff := #[1, 1, 1], bound := 1, weight := 464094, edges := #[⟨0, 1, 178⟩, ⟨0, 2, 440⟩, ⟨1, 2, 257⟩], triples := #[] }
def er173_571 : Row := { vars := #[486, 695, 682], coeff := #[1, 1, 1], bound := 1, weight := 317985, edges := #[⟨0, 1, 187⟩, ⟨0, 2, 183⟩, ⟨1, 2, 502⟩], triples := #[] }
def er173_572 : Row := { vars := #[487, 531, 657], coeff := #[1, 1, 1], bound := 1, weight := 411448, edges := #[⟨0, 1, 115⟩, ⟨0, 2, 140⟩, ⟨1, 2, 448⟩], triples := #[] }
def er173_573 : Row := { vars := #[487, 671, 657], coeff := #[1, 1, 1], bound := 1, weight := 254114, edges := #[⟨0, 1, 150⟩, ⟨0, 2, 140⟩, ⟨1, 2, 480⟩], triples := #[] }
def er173_574 : Row := { vars := #[496, 672, 554, 557], coeff := #[1, 1, 1, 1], bound := 1, weight := 147196, edges := #[⟨0, 1, 139⟩, ⟨0, 2, 82⟩, ⟨0, 3, 74⟩, ⟨1, 2, 435⟩, ⟨1, 3, 431⟩, ⟨2, 3, 393⟩], triples := #[] }
def er173_575 : Row := { vars := #[501, 667, 57], coeff := #[1, 1, 1], bound := 1, weight := 490088, edges := #[⟨0, 1, 157⟩, ⟨0, 2, 405⟩, ⟨1, 2, 257⟩], triples := #[] }
end HardyCapset20261020.Cert


