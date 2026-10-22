-- Prove2me | Definitions.Def_HardyCapsetEvaluationData173rows00V420261021
-- name    : HardyCapsetEvaluationData173rows00V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T03:07:33.623337+00:00
-- url     : https://prove2.me/theorems/aa78e59d-5895-4118-8208-4d4924ad2971
-- title:
--   HardyCapsetEvaluationData173rows00V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er173_000 : Row := { vars := #[0, 146, 108], coeff := #[1, 1, 1], bound := 1, weight := 191336, edges := #[⟨0, 1, 139⟩, ⟨0, 2, 166⟩, ⟨1, 2, 91⟩], triples := #[] }
def er173_001 : Row := { vars := #[0, 285, 427], coeff := #[1, 1, 1], bound := 1, weight := 561294, edges := #[⟨0, 1, 360⟩, ⟨0, 2, 470⟩, ⟨1, 2, 310⟩], triples := #[] }
def er173_002 : Row := { vars := #[0, 180, 508], coeff := #[1, 1, 1], bound := 1, weight := 247371, edges := #[⟨0, 1, 175⟩, ⟨0, 2, 416⟩, ⟨1, 2, 395⟩], triples := #[] }
def er173_003 : Row := { vars := #[1, 534, 326, 159], coeff := #[1, 1, 1, 1], bound := 1, weight := 316365, edges := #[⟨0, 1, 196⟩, ⟨0, 2, 400⟩, ⟨0, 3, 186⟩, ⟨1, 2, 47⟩, ⟨1, 3, 332⟩, ⟨2, 3, 479⟩], triples := #[] }
def er173_004 : Row := { vars := #[1, 195, 233], coeff := #[1, 1, 1], bound := 1, weight := 57537, edges := #[⟨0, 1, 106⟩, ⟨0, 2, 79⟩, ⟨1, 2, 151⟩], triples := #[] }
def er173_005 : Row := { vars := #[1, 81, 99], coeff := #[1, 1, 1], bound := 1, weight := 135877, edges := #[⟨0, 1, 25⟩, ⟨0, 2, 12⟩, ⟨1, 2, 38⟩], triples := #[] }
def er173_006 : Row := { vars := #[1, 211, 229], coeff := #[1, 1, 1], bound := 1, weight := 490222, edges := #[⟨0, 1, 97⟩, ⟨0, 2, 84⟩, ⟨1, 2, 134⟩], triples := #[] }
def er173_007 : Row := { vars := #[2, 158, 476], coeff := #[1, 1, 1], bound := 1, weight := 410750, edges := #[⟨0, 1, 187⟩, ⟨0, 2, 438⟩, ⟨1, 2, 385⟩], triples := #[] }
def er173_008 : Row := { vars := #[2, 287, 395], coeff := #[1, 1, 1], bound := 1, weight := 589251, edges := #[⟨0, 1, 362⟩, ⟨0, 2, 492⟩, ⟨1, 2, 332⟩], triples := #[] }
def er173_009 : Row := { vars := #[3, 288, 475], coeff := #[1, 1, 1], bound := 1, weight := 759947, edges := #[⟨0, 1, 363⟩, ⟨0, 2, 438⟩, ⟨1, 2, 278⟩], triples := #[] }
def er173_010 : Row := { vars := #[3, 245, 394], coeff := #[1, 1, 1], bound := 1, weight := 240054, edges := #[⟨0, 1, 127⟩, ⟨0, 2, 492⟩, ⟨1, 2, 384⟩], triples := #[] }
def er173_011 : Row := { vars := #[4, 50, 166], coeff := #[1, 1, 1], bound := 1, weight := 255463, edges := #[⟨0, 1, 48⟩, ⟨0, 2, 183⟩, ⟨1, 2, 179⟩], triples := #[] }
def er173_012 : Row := { vars := #[4, 134, 137], coeff := #[1, 1, 1], bound := 1, weight := 35332, edges := #[⟨0, 1, 142⟩, ⟨0, 2, 141⟩, ⟨1, 2, 101⟩], triples := #[] }
def er173_013 : Row := { vars := #[4, 221, 274], coeff := #[1, 1, 1], bound := 1, weight := 148119, edges := #[⟨0, 1, 82⟩, ⟨0, 2, 110⟩, ⟨1, 2, 178⟩], triples := #[] }
def er173_014 : Row := { vars := #[4, 222, 227], coeff := #[1, 1, 1], bound := 1, weight := 10993, edges := #[⟨0, 1, 84⟩, ⟨0, 2, 76⟩, ⟨1, 2, 166⟩], triples := #[] }
def er173_015 : Row := { vars := #[4, 324, 328], coeff := #[1, 1, 1], bound := 1, weight := 435224, edges := #[⟨0, 1, 400⟩, ⟨0, 2, 399⟩, ⟨1, 2, 230⟩], triples := #[] }
def er173_016 : Row := { vars := #[4, 334, 55], coeff := #[1, 1, 1], bound := 1, weight := 114871, edges := #[⟨0, 1, 396⟩, ⟨0, 2, 40⟩, ⟨1, 2, 391⟩], triples := #[] }
def er173_017 : Row := { vars := #[5, 290, 298], coeff := #[1, 1, 1], bound := 1, weight := 328111, edges := #[⟨0, 1, 368⟩, ⟨0, 2, 364⟩, ⟨1, 2, 208⟩], triples := #[] }
def er173_018 : Row := { vars := #[5, 297, 298], coeff := #[1, 1, 1], bound := 1, weight := 69796, edges := #[⟨0, 1, 370⟩, ⟨0, 2, 364⟩, ⟨1, 2, 210⟩], triples := #[] }
def er173_019 : Row := { vars := #[5, 48, 53], coeff := #[1, 1, 1], bound := 1, weight := 602094, edges := #[⟨0, 1, 46⟩, ⟨0, 2, 38⟩, ⟨1, 2, 33⟩], triples := #[] }
def er173_020 : Row := { vars := #[6, 32, 573], coeff := #[1, 1, 1], bound := 1, weight := 246273, edges := #[⟨0, 1, 64⟩, ⟨0, 2, 227⟩, ⟨1, 2, 209⟩], triples := #[] }
def er173_021 : Row := { vars := #[6, 289, 299], coeff := #[1, 1, 1], bound := 1, weight := 557836, edges := #[⟨0, 1, 368⟩, ⟨0, 2, 365⟩, ⟨1, 2, 208⟩], triples := #[] }
def er173_022 : Row := { vars := #[6, 291, 36], coeff := #[1, 1, 1], bound := 1, weight := 195893, edges := #[⟨0, 1, 369⟩, ⟨0, 2, 61⟩, ⟨1, 2, 398⟩], triples := #[] }
def er173_023 : Row := { vars := #[7, 652, 73], coeff := #[1, 1, 1], bound := 1, weight := 219308, edges := #[⟨0, 1, 247⟩, ⟨0, 2, 29⟩, ⟨1, 2, 266⟩], triples := #[] }
def er173_024 : Row := { vars := #[7, 300, 292], coeff := #[1, 1, 1], bound := 1, weight := 780693, edges := #[⟨0, 1, 366⟩, ⟨0, 2, 370⟩, ⟨1, 2, 210⟩], triples := #[] }
def er173_025 : Row := { vars := #[8, 293, 301], coeff := #[1, 1, 1], bound := 1, weight := 471743, edges := #[⟨0, 1, 369⟩, ⟨0, 2, 367⟩, ⟨1, 2, 209⟩], triples := #[] }
def er173_026 : Row := { vars := #[8, 223, 228], coeff := #[1, 1, 1], bound := 1, weight := 528258, edges := #[⟨0, 1, 84⟩, ⟨0, 2, 76⟩, ⟨1, 2, 167⟩], triples := #[] }
def er173_027 : Row := { vars := #[9, 65, 410], coeff := #[1, 1, 1], bound := 1, weight := 650266, edges := #[⟨0, 1, 29⟩, ⟨0, 2, 488⟩, ⟨1, 2, 490⟩], triples := #[] }
def er173_028 : Row := { vars := #[9, 390, 500], coeff := #[1, 1, 1], bound := 1, weight := 237060, edges := #[⟨0, 1, 500⟩, ⟨0, 2, 426⟩, ⟨1, 2, 209⟩], triples := #[] }
def er173_029 : Row := { vars := #[9, 419, 470], coeff := #[1, 1, 1], bound := 1, weight := 88149, edges := #[⟨0, 1, 480⟩, ⟨0, 2, 447⟩, ⟨1, 2, 208⟩], triples := #[] }
def er173_030 : Row := { vars := #[9, 461, 472], coeff := #[1, 1, 1], bound := 1, weight := 24528, edges := #[⟨0, 1, 455⟩, ⟨0, 2, 445⟩, ⟨1, 2, 329⟩], triples := #[] }
def er173_031 : Row := { vars := #[10, 662, 509, 187], coeff := #[1, 1, 1, 1], bound := 1, weight := 528258, edges := #[⟨0, 1, 279⟩, ⟨0, 2, 435⟩, ⟨0, 3, 179⟩, ⟨1, 2, 143⟩, ⟨1, 3, 193⟩, ⟨2, 3, 403⟩], triples := #[] }
def er173_032 : Row := { vars := #[10, 303, 495], coeff := #[1, 1, 1], bound := 1, weight := 471743, edges := #[⟨0, 1, 372⟩, ⟨0, 2, 416⟩, ⟨1, 2, 256⟩], triples := #[] }
def er173_033 : Row := { vars := #[11, 274, 44], coeff := #[1, 1, 1], bound := 1, weight := 270141, edges := #[⟨0, 1, 119⟩, ⟨0, 2, 46⟩, ⟨1, 2, 80⟩], triples := #[] }
def er173_034 : Row := { vars := #[11, 23, 218], coeff := #[1, 1, 1], bound := 1, weight := 184951, edges := #[⟨0, 1, 60⟩, ⟨0, 2, 79⟩, ⟨1, 2, 131⟩], triples := #[] }
def er173_035 : Row := { vars := #[11, 304, 414], coeff := #[1, 1, 1], bound := 1, weight := 544909, edges := #[⟨0, 1, 373⟩, ⟨0, 2, 470⟩, ⟨1, 2, 310⟩], triples := #[] }
def er173_036 : Row := { vars := #[12, 275, 598, 479], coeff := #[1, 1, 1, 1], bound := 1, weight := 782078, edges := #[⟨0, 1, 118⟩, ⟨0, 2, 333⟩, ⟨0, 3, 457⟩, ⟨1, 2, 192⟩, ⟨1, 3, 467⟩, ⟨2, 3, 10⟩], triples := #[] }
def er173_037 : Row := { vars := #[12, 305, 296], coeff := #[1, 1, 1], bound := 1, weight := 217923, edges := #[⟨0, 1, 374⟩, ⟨0, 2, 354⟩, ⟨1, 2, 194⟩], triples := #[] }
def er173_038 : Row := { vars := #[13, 129, 140], coeff := #[1, 1, 1], bound := 1, weight := 271476, edges := #[⟨0, 1, 142⟩, ⟨0, 2, 165⟩, ⟨1, 2, 75⟩], triples := #[] }
def er173_039 : Row := { vars := #[13, 306, 295], coeff := #[1, 1, 1], bound := 1, weight := 183751, edges := #[⟨0, 1, 375⟩, ⟨0, 2, 354⟩, ⟨1, 2, 194⟩], triples := #[] }
def er173_040 : Row := { vars := #[13, 306, 383], coeff := #[1, 1, 1], bound := 1, weight := 289432, edges := #[⟨0, 1, 375⟩, ⟨0, 2, 492⟩, ⟨1, 2, 332⟩], triples := #[] }
def er173_041 : Row := { vars := #[13, 188, 297], coeff := #[1, 1, 1], bound := 1, weight := 9890, edges := #[⟨0, 1, 178⟩, ⟨0, 2, 355⟩, ⟨1, 2, 468⟩], triples := #[] }
def er173_042 : Row := { vars := #[13, 196, 90], coeff := #[1, 1, 1], bound := 1, weight := 109476, edges := #[⟨0, 1, 97⟩, ⟨0, 2, 5⟩, ⟨1, 2, 118⟩], triples := #[] }
def er173_043 : Row := { vars := #[13, 621, 397, 252], coeff := #[1, 1, 1, 1], bound := 1, weight := 135978, edges := #[⟨0, 1, 311⟩, ⟨0, 2, 509⟩, ⟨0, 3, 131⟩, ⟨1, 2, 84⟩, ⟨1, 3, 194⟩, ⟨2, 3, 393⟩], triples := #[] }
def er173_044 : Row := { vars := #[14, 78, 268], coeff := #[1, 1, 1], bound := 1, weight := 259411, edges := #[⟨0, 1, 12⟩, ⟨0, 2, 111⟩, ⟨1, 2, 127⟩], triples := #[] }
def er173_045 : Row := { vars := #[14, 80, 508], coeff := #[1, 1, 1], bound := 1, weight := 253821, edges := #[⟨0, 1, 8⟩, ⟨0, 2, 433⟩, ⟨1, 2, 436⟩], triples := #[] }
def er173_046 : Row := { vars := #[14, 126, 348], coeff := #[1, 1, 1], bound := 1, weight := 274570, edges := #[⟨0, 1, 135⟩, ⟨0, 2, 386⟩, ⟨1, 2, 472⟩], triples := #[] }
def er173_047 : Row := { vars := #[14, 206, 37], coeff := #[1, 1, 1], bound := 1, weight := 5123, edges := #[⟨0, 1, 82⟩, ⟨0, 2, 44⟩, ⟨1, 2, 127⟩], triples := #[] }
def er173_048 : Row := { vars := #[14, 206, 159], coeff := #[1, 1, 1], bound := 1, weight := 207077, edges := #[⟨0, 1, 82⟩, ⟨0, 2, 183⟩, ⟨1, 2, 55⟩], triples := #[] }
def er173_049 : Row := { vars := #[15, 410, 152], coeff := #[1, 1, 1], bound := 1, weight := 349735, edges := #[⟨0, 1, 480⟩, ⟨0, 2, 187⟩, ⟨1, 2, 405⟩], triples := #[] }
def er173_050 : Row := { vars := #[15, 460, 195], coeff := #[1, 1, 1], bound := 1, weight := 117742, edges := #[⟨0, 1, 448⟩, ⟨0, 2, 91⟩, ⟨1, 2, 491⟩], triples := #[] }
def er173_051 : Row := { vars := #[15, 460, 151], coeff := #[1, 1, 1], bound := 1, weight := 532524, edges := #[⟨0, 1, 448⟩, ⟨0, 2, 186⟩, ⟨1, 2, 385⟩], triples := #[] }
def er173_052 : Row := { vars := #[16, 313, 327, 403], coeff := #[1, 1, 1, 1], bound := 1, weight := 349180, edges := #[⟨0, 1, 380⟩, ⟨0, 2, 396⟩, ⟨0, 3, 510⟩, ⟨1, 2, 236⟩, ⟨1, 3, 350⟩, ⟨2, 3, 311⟩], triples := #[] }
def er173_053 : Row := { vars := #[16, 313, 434, 346], coeff := #[1, 1, 1, 1], bound := 1, weight := 533485, edges := #[⟨0, 1, 380⟩, ⟨0, 2, 487⟩, ⟨0, 3, 386⟩, ⟨1, 2, 327⟩, ⟨1, 3, 226⟩, ⟨2, 3, 333⟩], triples := #[] }
def er173_054 : Row := { vars := #[16, 76, 384, 122], coeff := #[1, 1, 1, 1], bound := 1, weight := 117336, edges := #[⟨0, 1, 5⟩, ⟨0, 2, 492⟩, ⟨0, 3, 136⟩, ⟨1, 2, 464⟩, ⟨1, 3, 175⟩, ⟨2, 3, 447⟩], triples := #[] }
def er173_055 : Row := { vars := #[17, 141, 678], coeff := #[1, 1, 1], bound := 1, weight := 533485, edges := #[⟨0, 1, 160⟩, ⟨0, 2, 261⟩, ⟨1, 2, 230⟩], triples := #[] }
def er173_056 : Row := { vars := #[17, 31, 46], coeff := #[1, 1, 1], bound := 1, weight := 466516, edges := #[⟨0, 1, 60⟩, ⟨0, 2, 47⟩, ⟨1, 2, 34⟩], triples := #[] }
def er173_057 : Row := { vars := #[18, 315, 365, 403], coeff := #[1, 1, 1, 1], bound := 1, weight := 462984, edges := #[⟨0, 1, 382⟩, ⟨0, 2, 460⟩, ⟨0, 3, 509⟩, ⟨1, 2, 300⟩, ⟨1, 3, 349⟩, ⟨2, 3, 279⟩], triples := #[] }
def er173_058 : Row := { vars := #[18, 315, 283], coeff := #[1, 1, 1], bound := 1, weight := 537017, edges := #[⟨0, 1, 382⟩, ⟨0, 2, 370⟩, ⟨1, 2, 210⟩], triples := #[] }
def er173_059 : Row := { vars := #[19, 53, 614], coeff := #[1, 1, 1], bound := 1, weight := 24528, edges := #[⟨0, 1, 65⟩, ⟨0, 2, 313⟩, ⟨1, 2, 304⟩], triples := #[] }
def er173_060 : Row := { vars := #[19, 316, 461], coeff := #[1, 1, 1], bound := 1, weight := 975473, edges := #[⟨0, 1, 383⟩, ⟨0, 2, 448⟩, ⟨1, 2, 288⟩], triples := #[] }
def er173_061 : Row := { vars := #[20, 22, 467, 446], coeff := #[1, 1, 1, 1], bound := 1, weight := 349735, edges := #[⟨0, 1, 8⟩, ⟨0, 2, 435⟩, ⟨0, 3, 456⟩, ⟨1, 2, 431⟩, ⟨1, 3, 452⟩, ⟨2, 3, 336⟩], triples := #[] }
def er173_062 : Row := { vars := #[20, 51, 358], coeff := #[1, 1, 1], bound := 1, weight := 117884, edges := #[⟨0, 1, 18⟩, ⟨0, 2, 492⟩, ⟨1, 2, 494⟩], triples := #[] }
def er173_063 : Row := { vars := #[20, 51, 430, 452], coeff := #[1, 1, 1, 1], bound := 1, weight := 371747, edges := #[⟨0, 1, 18⟩, ⟨0, 2, 464⟩, ⟨0, 3, 448⟩, ⟨1, 2, 467⟩, ⟨1, 3, 454⟩, ⟨2, 3, 232⟩], triples := #[] }
end HardyCapset20261020.Cert


