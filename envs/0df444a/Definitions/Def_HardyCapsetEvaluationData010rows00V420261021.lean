-- Prove2me | Definitions.Def_HardyCapsetEvaluationData010rows00V420261021
-- name    : HardyCapsetEvaluationData010rows00V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T01:25:24.691878+00:00
-- url     : https://prove2.me/theorems/9763c046-a5b9-4bc7-86ab-afb56a9f8278
-- title:
--   HardyCapsetEvaluationData010rows00V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er010_000 : Row := { vars := #[199, 551], coeff := #[1, 1], bound := 1, weight := 15065, edges := #[⟨0, 1, 78⟩], triples := #[] }
def er010_001 : Row := { vars := #[201, 542], coeff := #[1, 1], bound := 1, weight := 67671, edges := #[⟨0, 1, 84⟩], triples := #[] }
def er010_002 : Row := { vars := #[218, 323], coeff := #[1, 1], bound := 1, weight := 211862, edges := #[⟨0, 1, 328⟩], triples := #[] }
def er010_003 : Row := { vars := #[330, 589], coeff := #[1, 1], bound := 1, weight := 27578, edges := #[⟨0, 1, 67⟩], triples := #[] }
def er010_004 : Row := { vars := #[351, 439], coeff := #[1, 1], bound := 1, weight := 232371, edges := #[⟨0, 1, 106⟩], triples := #[] }
def er010_005 : Row := { vars := #[396, 442], coeff := #[1, 1], bound := 1, weight := 85306, edges := #[⟨0, 1, 364⟩], triples := #[] }
def er010_006 : Row := { vars := #[396, 535], coeff := #[1, 1], bound := 1, weight := 14682, edges := #[⟨0, 1, 489⟩], triples := #[] }
def er010_007 : Row := { vars := #[402, 535], coeff := #[1, 1], bound := 1, weight := 505960, edges := #[⟨0, 1, 486⟩], triples := #[] }
def er010_008 : Row := { vars := #[415, 594], coeff := #[1, 1], bound := 1, weight := 413036, edges := #[⟨0, 1, 429⟩], triples := #[] }
def er010_009 : Row := { vars := #[0, 18, 545, 341], coeff := #[1, 1, 1, 1], bound := 1, weight := 804925, edges := #[⟨0, 1, 8⟩, ⟨0, 2, 296⟩, ⟨0, 3, 456⟩, ⟨1, 2, 282⟩, ⟨1, 3, 442⟩, ⟨2, 3, 133⟩], triples := #[] }
def er010_010 : Row := { vars := #[0, 310, 563], coeff := #[1, 1, 1], bound := 1, weight := 195076, edges := #[⟨0, 1, 480⟩, ⟨0, 2, 273⟩, ⟨1, 2, 31⟩], triples := #[] }
def er010_011 : Row := { vars := #[1, 268, 571], coeff := #[1, 1, 1], bound := 1, weight := 203443, edges := #[⟨0, 1, 376⟩, ⟨0, 2, 268⟩, ⟨1, 2, 84⟩], triples := #[] }
def er010_012 : Row := { vars := #[1, 412, 575], coeff := #[1, 1, 1], bound := 1, weight := 739853, edges := #[⟨0, 1, 242⟩, ⟨0, 2, 262⟩, ⟨1, 2, 457⟩], triples := #[] }
def er010_013 : Row := { vars := #[2, 512, 347], coeff := #[1, 1, 1], bound := 1, weight := 301157, edges := #[⟨0, 1, 324⟩, ⟨0, 2, 451⟩, ⟨1, 2, 50⟩], triples := #[] }
def er010_014 : Row := { vars := #[2, 547, 114, 343], coeff := #[1, 1, 1, 1], bound := 1, weight := 698844, edges := #[⟨0, 1, 295⟩, ⟨0, 2, 146⟩, ⟨0, 3, 455⟩, ⟨1, 2, 229⟩, ⟨1, 3, 137⟩, ⟨2, 3, 389⟩], triples := #[] }
def er010_015 : Row := { vars := #[3, 283, 186, 487], coeff := #[1, 1, 1, 1], bound := 1, weight := 231487, edges := #[⟨0, 1, 509⟩, ⟨0, 2, 86⟩, ⟨0, 3, 349⟩, ⟨1, 2, 389⟩, ⟨1, 3, 77⟩, ⟨2, 3, 229⟩], triples := #[] }
def er010_016 : Row := { vars := #[3, 290, 176, 591], coeff := #[1, 1, 1, 1], bound := 1, weight := 251744, edges := #[⟨0, 1, 495⟩, ⟨0, 2, 93⟩, ⟨0, 3, 252⟩, ⟨1, 2, 390⟩, ⟨1, 3, 35⟩, ⟨2, 3, 350⟩], triples := #[] }
def er010_017 : Row := { vars := #[3, 371, 508], coeff := #[1, 1, 1], bound := 1, weight := 448470, edges := #[⟨0, 1, 419⟩, ⟨0, 2, 322⟩, ⟨1, 2, 33⟩], triples := #[] }
def er010_018 : Row := { vars := #[4, 513, 271], coeff := #[1, 1, 1], bound := 1, weight := 49847, edges := #[⟨0, 1, 320⟩, ⟨0, 2, 365⟩, ⟨1, 2, 157⟩], triples := #[] }
def er010_019 : Row := { vars := #[4, 14, 359, 563], coeff := #[1, 1, 1, 1], bound := 1, weight := 451710, edges := #[⟨0, 1, 8⟩, ⟨0, 2, 429⟩, ⟨0, 3, 269⟩, ⟨1, 2, 423⟩, ⟨1, 3, 263⟩, ⟨2, 3, 168⟩], triples := #[] }
def er010_020 : Row := { vars := #[4, 271, 102, 474], coeff := #[1, 1, 1, 1], bound := 1, weight := 187971, edges := #[⟨0, 1, 365⟩, ⟨0, 2, 153⟩, ⟨0, 3, 209⟩, ⟨1, 2, 496⟩, ⟨1, 3, 61⟩, ⟨2, 3, 340⟩], triples := #[] }
def er010_021 : Row := { vars := #[4, 18, 499, 300], coeff := #[1, 1, 1, 1], bound := 1, weight := 140132, edges := #[⟨0, 1, 0⟩, ⟨0, 2, 329⟩, ⟨0, 3, 485⟩, ⟨1, 2, 319⟩, ⟨1, 3, 475⟩, ⟨2, 3, 111⟩], triples := #[] }
def er010_022 : Row := { vars := #[4, 425, 501], coeff := #[1, 1, 1], bound := 1, weight := 170342, edges := #[⟨0, 1, 239⟩, ⟨0, 2, 326⟩, ⟨1, 2, 510⟩], triples := #[] }
def er010_023 : Row := { vars := #[6, 514, 562], coeff := #[1, 1, 1], bound := 1, weight := 640658, edges := #[⟨0, 1, 314⟩, ⟨0, 2, 274⟩, ⟨1, 2, 393⟩], triples := #[] }
def er010_024 : Row := { vars := #[6, 553, 96, 349], coeff := #[1, 1, 1, 1], bound := 1, weight := 185666, edges := #[⟨0, 1, 281⟩, ⟨0, 2, 156⟩, ⟨0, 3, 441⟩, ⟨1, 2, 230⟩, ⟨1, 3, 152⟩, ⟨2, 3, 390⟩], triples := #[] }
def er010_025 : Row := { vars := #[6, 349, 96, 526], coeff := #[1, 1, 1, 1], bound := 1, weight := 173677, edges := #[⟨0, 1, 441⟩, ⟨0, 2, 156⟩, ⟨0, 3, 306⟩, ⟨1, 2, 390⟩, ⟨1, 3, 32⟩, ⟨2, 3, 297⟩], triples := #[] }
def er010_026 : Row := { vars := #[7, 288, 172, 493], coeff := #[1, 1, 1, 1], bound := 1, weight := 548042, edges := #[⟨0, 1, 499⟩, ⟨0, 2, 93⟩, ⟨0, 3, 335⟩, ⟨1, 2, 390⟩, ⟨1, 3, 95⟩, ⟨2, 3, 229⟩], triples := #[] }
def er010_027 : Row := { vars := #[7, 567, 294], coeff := #[1, 1, 1], bound := 1, weight := 219860, edges := #[⟨0, 1, 269⟩, ⟨0, 2, 486⟩, ⟨1, 2, 10⟩], triples := #[] }
def er010_028 : Row := { vars := #[8, 268, 116, 464], coeff := #[1, 1, 1, 1], bound := 1, weight := 796558, edges := #[⟨0, 1, 381⟩, ⟨0, 2, 143⟩, ⟨0, 3, 217⟩, ⟨1, 2, 500⟩, ⟨1, 3, 40⟩, ⟨2, 3, 336⟩], triples := #[] }
def er010_029 : Row := { vars := #[8, 22, 541, 345], coeff := #[1, 1, 1, 1], bound := 1, weight := 203443, edges := #[⟨0, 1, 8⟩, ⟨0, 2, 292⟩, ⟨0, 3, 456⟩, ⟨1, 2, 282⟩, ⟨1, 3, 446⟩, ⟨2, 3, 133⟩], triples := #[] }
def er010_030 : Row := { vars := #[10, 512, 339], coeff := #[1, 1, 1], bound := 1, weight := 241849, edges := #[⟨0, 1, 328⟩, ⟨0, 2, 451⟩, ⟨1, 2, 42⟩], triples := #[] }
def er010_031 : Row := { vars := #[10, 12, 364, 568], coeff := #[1, 1, 1, 1], bound := 1, weight := 405686, edges := #[⟨0, 1, 0⟩, ⟨0, 2, 432⟩, ⟨0, 3, 272⟩, ⟨1, 2, 422⟩, ⟨1, 3, 262⟩, ⟨2, 3, 170⟩], triples := #[] }
def er010_032 : Row := { vars := #[10, 554, 104, 348], coeff := #[1, 1, 1, 1], bound := 1, weight := 188109, edges := #[⟨0, 1, 285⟩, ⟨0, 2, 156⟩, ⟨0, 3, 441⟩, ⟨1, 2, 230⟩, ⟨1, 3, 152⟩, ⟨2, 3, 389⟩], triples := #[] }
def er010_033 : Row := { vars := #[11, 13, 489, 285], coeff := #[1, 1, 1, 1], bound := 1, weight := 567848, edges := #[⟨0, 1, 1⟩, ⟨0, 2, 348⟩, ⟨0, 3, 508⟩, ⟨1, 2, 338⟩, ⟨1, 3, 498⟩, ⟨2, 3, 81⟩], triples := #[] }
def er010_034 : Row := { vars := #[11, 21, 387, 463], coeff := #[1, 1, 1, 1], bound := 1, weight := 92053, edges := #[⟨0, 1, 9⟩, ⟨0, 2, 413⟩, ⟨0, 3, 217⟩, ⟨1, 2, 410⟩, ⟨1, 3, 205⟩, ⟨2, 3, 121⟩], triples := #[] }
def er010_035 : Row := { vars := #[11, 21, 294, 508], coeff := #[1, 1, 1, 1], bound := 1, weight := 206133, edges := #[⟨0, 1, 9⟩, ⟨0, 2, 482⟩, ⟨0, 3, 326⟩, ⟨1, 2, 476⟩, ⟨1, 3, 320⟩, ⟨2, 3, 108⟩], triples := #[] }
def er010_036 : Row := { vars := #[11, 288, 176, 494], coeff := #[1, 1, 1, 1], bound := 1, weight := 133969, edges := #[⟨0, 1, 495⟩, ⟨0, 2, 96⟩, ⟨0, 3, 339⟩, ⟨1, 2, 389⟩, ⟨1, 3, 92⟩, ⟨2, 3, 230⟩], triples := #[] }
def er010_037 : Row := { vars := #[12, 307, 374], coeff := #[1, 1, 1], bound := 1, weight := 594315, edges := #[⟨0, 1, 474⟩, ⟨0, 2, 430⟩, ⟨1, 2, 230⟩], triples := #[] }
def er010_038 : Row := { vars := #[13, 304, 571], coeff := #[1, 1, 1], bound := 1, weight := 187723, edges := #[⟨0, 1, 476⟩, ⟨0, 2, 259⟩, ⟨1, 2, 13⟩], triples := #[] }
def er010_039 : Row := { vars := #[13, 373, 503], coeff := #[1, 1, 1], bound := 1, weight := 244431, edges := #[⟨0, 1, 433⟩, ⟨0, 2, 320⟩, ⟨1, 2, 20⟩], triples := #[] }
def er010_040 : Row := { vars := #[14, 303, 233], coeff := #[1, 1, 1], bound := 1, weight := 409871, edges := #[⟨0, 1, 480⟩, ⟨0, 2, 403⟩, ⟨1, 2, 336⟩], triples := #[] }
def er010_041 : Row := { vars := #[14, 568, 314], coeff := #[1, 1, 1], bound := 1, weight := 123561, edges := #[⟨0, 1, 259⟩, ⟨0, 2, 482⟩, ⟨1, 2, 24⟩], triples := #[] }
def er010_042 : Row := { vars := #[15, 5, 299, 503], coeff := #[1, 1, 1, 1], bound := 1, weight := 365871, edges := #[⟨0, 1, 9⟩, ⟨0, 2, 478⟩, ⟨0, 3, 318⟩, ⟨1, 2, 484⟩, ⟨1, 3, 324⟩, ⟨2, 3, 108⟩], triples := #[] }
def er010_043 : Row := { vars := #[15, 269, 178, 473], coeff := #[1, 1, 1, 1], bound := 1, weight := 26997, edges := #[⟨0, 1, 364⟩, ⟨0, 2, 78⟩, ⟨0, 3, 204⟩, ⟨1, 2, 457⟩, ⟨1, 3, 51⟩, ⟨2, 3, 297⟩], triples := #[] }
def er010_044 : Row := { vars := #[15, 269, 572], coeff := #[1, 1, 1], bound := 1, weight := 245113, edges := #[⟨0, 1, 364⟩, ⟨0, 2, 262⟩, ⟨1, 2, 87⟩], triples := #[] }
def er010_045 : Row := { vars := #[15, 306, 479, 188], coeff := #[1, 1, 1, 1], bound := 1, weight := 362021, edges := #[⟨0, 1, 475⟩, ⟨0, 2, 216⟩, ⟨0, 3, 103⟩, ⟨1, 2, 155⟩, ⟨1, 3, 370⟩, ⟨2, 3, 297⟩], triples := #[] }
def er010_046 : Row := { vars := #[16, 517, 561], coeff := #[1, 1, 1], bound := 1, weight := 303539, edges := #[⟨0, 1, 324⟩, ⟨0, 2, 264⟩, ⟨1, 2, 390⟩], triples := #[] }
def er010_047 : Row := { vars := #[16, 517, 351], coeff := #[1, 1, 1], bound := 1, weight := 221858, edges := #[⟨0, 1, 324⟩, ⟨0, 2, 455⟩, ⟨1, 2, 70⟩], triples := #[] }
def er010_048 : Row := { vars := #[16, 542, 100, 342], coeff := #[1, 1, 1, 1], bound := 1, weight := 14795, edges := #[⟨0, 1, 285⟩, ⟨0, 2, 135⟩, ⟨0, 3, 441⟩, ⟨1, 2, 233⟩, ⟨1, 3, 142⟩, ⟨2, 3, 392⟩], triples := #[] }
def er010_049 : Row := { vars := #[16, 546, 96, 342], coeff := #[1, 1, 1, 1], bound := 1, weight := 331207, edges := #[⟨0, 1, 281⟩, ⟨0, 2, 143⟩, ⟨0, 3, 441⟩, ⟨1, 2, 233⟩, ⟨1, 3, 134⟩, ⟨2, 3, 393⟩], triples := #[] }
def er010_050 : Row := { vars := #[17, 516, 566], coeff := #[1, 1, 1], bound := 1, weight := 875876, edges := #[⟨0, 1, 327⟩, ⟨0, 2, 259⟩, ⟨1, 2, 390⟩], triples := #[] }
def er010_051 : Row := { vars := #[17, 357, 486], coeff := #[1, 1, 1], bound := 1, weight := 124125, edges := #[⟨0, 1, 423⟩, ⟨0, 2, 335⟩, ⟨1, 2, 46⟩], triples := #[] }
def er010_052 : Row := { vars := #[20, 542, 307], coeff := #[1, 1, 1], bound := 1, weight := 405686, edges := #[⟨0, 1, 281⟩, ⟨0, 2, 478⟩, ⟨1, 2, 39⟩], triples := #[] }
def er010_053 : Row := { vars := #[20, 550, 96, 327], coeff := #[1, 1, 1, 1], bound := 1, weight := 139178, edges := #[⟨0, 1, 285⟩, ⟨0, 2, 135⟩, ⟨0, 3, 464⟩, ⟨1, 2, 232⟩, ⟨1, 3, 15⟩, ⟨2, 3, 453⟩], triples := #[] }
def er010_054 : Row := { vars := #[20, 550, 104, 338], coeff := #[1, 1, 1, 1], bound := 1, weight := 224143, edges := #[⟨0, 1, 285⟩, ⟨0, 2, 143⟩, ⟨0, 3, 441⟩, ⟨1, 2, 233⟩, ⟨1, 3, 134⟩, ⟨2, 3, 392⟩], triples := #[] }
def er010_055 : Row := { vars := #[20, 314, 357], coeff := #[1, 1, 1], bound := 1, weight := 208947, edges := #[⟨0, 1, 488⟩, ⟨0, 2, 420⟩, ⟨1, 2, 229⟩], triples := #[] }
def er010_056 : Row := { vars := #[21, 286, 168, 490], coeff := #[1, 1, 1, 1], bound := 1, weight := 701816, edges := #[⟨0, 1, 499⟩, ⟨0, 2, 75⟩, ⟨0, 3, 339⟩, ⟨1, 2, 392⟩, ⟨1, 3, 82⟩, ⟨2, 3, 232⟩], triples := #[] }
def er010_057 : Row := { vars := #[22, 298, 473], coeff := #[1, 1, 1], bound := 1, weight := 74662, edges := #[⟨0, 1, 476⟩, ⟨0, 2, 209⟩, ⟨1, 2, 139⟩], triples := #[] }
def er010_058 : Row := { vars := #[22, 308, 558], coeff := #[1, 1, 1], bound := 1, weight := 288094, edges := #[⟨0, 1, 480⟩, ⟨0, 2, 259⟩, ⟨1, 2, 3⟩], triples := #[] }
def er010_059 : Row := { vars := #[22, 314, 558], coeff := #[1, 1, 1], bound := 1, weight := 54504, edges := #[⟨0, 1, 486⟩, ⟨0, 2, 259⟩, ⟨1, 2, 21⟩], triples := #[] }
def er010_060 : Row := { vars := #[22, 465, 106, 366], coeff := #[1, 1, 1, 1], bound := 1, weight := 178628, edges := #[⟨0, 1, 205⟩, ⟨0, 2, 146⟩, ⟨0, 3, 425⟩, ⟨1, 2, 346⟩, ⟨1, 3, 74⟩, ⟨2, 3, 382⟩], triples := #[] }
def er010_061 : Row := { vars := #[24, 42, 584, 380], coeff := #[1, 1, 1, 1], bound := 1, weight := 115636, edges := #[⟨0, 1, 44⟩, ⟨0, 2, 296⟩, ⟨0, 3, 456⟩, ⟨1, 2, 282⟩, ⟨1, 3, 442⟩, ⟨2, 3, 180⟩], triples := #[] }
def er010_062 : Row := { vars := #[24, 454, 328], coeff := #[1, 1, 1], bound := 1, weight := 102766, edges := #[⟨0, 1, 217⟩, ⟨0, 2, 504⟩, ⟨1, 2, 143⟩], triples := #[] }
def er010_063 : Row := { vars := #[24, 454, 250, 92], coeff := #[1, 1, 1, 1], bound := 1, weight := 128625, edges := #[⟨0, 1, 217⟩, ⟨0, 2, 377⟩, ⟨0, 3, 136⟩, ⟨1, 2, 12⟩, ⟨1, 3, 317⟩, ⟨2, 3, 477⟩], triples := #[] }
end HardyCapset20261020.Cert


