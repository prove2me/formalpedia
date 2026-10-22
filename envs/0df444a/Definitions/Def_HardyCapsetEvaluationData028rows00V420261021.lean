-- Prove2me | Definitions.Def_HardyCapsetEvaluationData028rows00V420261021
-- name    : HardyCapsetEvaluationData028rows00V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:22:16.743755+00:00
-- url     : https://prove2.me/theorems/d1cae837-10ec-43af-9bea-4aeaddf2b1f1
-- title:
--   HardyCapsetEvaluationData028rows00V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er028_000 : Row := { vars := #[115, 351], coeff := #[1, 1], bound := 1, weight := 9608, edges := #[⟨0, 1, 376⟩], triples := #[] }
def er028_001 : Row := { vars := #[162, 289], coeff := #[1, 1], bound := 1, weight := 58571, edges := #[⟨0, 1, 389⟩], triples := #[] }
def er028_002 : Row := { vars := #[256, 391], coeff := #[1, 1], bound := 1, weight := 202346, edges := #[⟨0, 1, 210⟩], triples := #[] }
def er028_003 : Row := { vars := #[273, 289], coeff := #[1, 1], bound := 1, weight := 34853, edges := #[⟨0, 1, 250⟩], triples := #[] }
def er028_004 : Row := { vars := #[283, 446], coeff := #[1, 1], bound := 1, weight := 3124, edges := #[⟨0, 1, 102⟩], triples := #[] }
def er028_005 : Row := { vars := #[311, 348], coeff := #[1, 1], bound := 1, weight := 15879, edges := #[⟨0, 1, 195⟩], triples := #[] }
def er028_006 : Row := { vars := #[317, 342], coeff := #[1, 1], bound := 1, weight := 353284, edges := #[⟨0, 1, 195⟩], triples := #[] }
def er028_007 : Row := { vars := #[317, 450], coeff := #[1, 1], bound := 1, weight := 165726, edges := #[⟨0, 1, 84⟩], triples := #[] }
def er028_008 : Row := { vars := #[0, 7, 208, 19], coeff := #[1, 1, 1, 1], bound := 1, weight := 513351, edges := #[⟨0, 1, 13⟩, ⟨0, 2, 91⟩, ⟨0, 3, 30⟩, ⟨1, 2, 96⟩, ⟨1, 3, 27⟩, ⟨2, 3, 75⟩], triples := #[] }
def er028_009 : Row := { vars := #[0, 415, 160, 225], coeff := #[1, 1, 1, 1], bound := 1, weight := 317119, edges := #[⟨0, 1, 196⟩, ⟨0, 2, 126⟩, ⟨0, 3, 372⟩, ⟨1, 2, 258⟩, ⟨1, 3, 63⟩, ⟨2, 3, 416⟩], triples := #[] }
def er028_010 : Row := { vars := #[1, 391, 411], coeff := #[1, 1, 1], bound := 1, weight := 33792, edges := #[⟨0, 1, 412⟩, ⟨0, 2, 231⟩, ⟨1, 2, 92⟩], triples := #[] }
def er028_011 : Row := { vars := #[1, 14, 128, 126], coeff := #[1, 1, 1, 1], bound := 1, weight := 245074, edges := #[⟨0, 1, 26⟩, ⟨0, 2, 163⟩, ⟨0, 3, 166⟩, ⟨1, 2, 153⟩, ⟨1, 3, 156⟩, ⟨2, 3, 126⟩], triples := #[] }
def er028_012 : Row := { vars := #[1, 14, 573, 381], coeff := #[1, 1, 1, 1], bound := 1, weight := 345555, edges := #[⟨0, 1, 26⟩, ⟨0, 2, 251⟩, ⟨0, 3, 411⟩, ⟨1, 2, 248⟩, ⟨1, 3, 408⟩, ⟨2, 3, 187⟩], triples := #[] }
def er028_013 : Row := { vars := #[1, 14, 422, 230], coeff := #[1, 1, 1, 1], bound := 1, weight := 38650, edges := #[⟨0, 1, 26⟩, ⟨0, 2, 343⟩, ⟨0, 3, 503⟩, ⟨1, 2, 334⟩, ⟨1, 3, 494⟩, ⟨2, 3, 90⟩], triples := #[] }
def er028_014 : Row := { vars := #[1, 14, 17, 19], coeff := #[1, 1, 1, 1], bound := 1, weight := 336931, edges := #[⟨0, 1, 26⟩, ⟨0, 2, 35⟩, ⟨0, 3, 32⟩, ⟨1, 2, 25⟩, ⟨1, 3, 22⟩, ⟨2, 3, 19⟩], triples := #[] }
def er028_015 : Row := { vars := #[2, 15, 291, 483], coeff := #[1, 1, 1, 1], bound := 1, weight := 487381, edges := #[⟨0, 1, 27⟩, ⟨0, 2, 465⟩, ⟨0, 3, 305⟩, ⟨1, 2, 462⟩, ⟨1, 3, 302⟩, ⟨2, 3, 127⟩], triples := #[] }
def er028_016 : Row := { vars := #[2, 22, 512, 318], coeff := #[1, 1, 1, 1], bound := 1, weight := 165665, edges := #[⟨0, 1, 19⟩, ⟨0, 2, 289⟩, ⟨0, 3, 439⟩, ⟨1, 2, 278⟩, ⟨1, 3, 440⟩, ⟨2, 3, 158⟩], triples := #[] }
def er028_017 : Row := { vars := #[2, 22, 408, 218], coeff := #[1, 1, 1, 1], bound := 1, weight := 262811, edges := #[⟨0, 1, 19⟩, ⟨0, 2, 227⟩, ⟨0, 3, 391⟩, ⟨1, 2, 228⟩, ⟨1, 3, 386⟩, ⟨2, 3, 26⟩], triples := #[] }
def er028_018 : Row := { vars := #[3, 7, 200, 29], coeff := #[1, 1, 1, 1], bound := 1, weight := 59656, edges := #[⟨0, 1, 10⟩, ⟨0, 2, 99⟩, ⟨0, 3, 20⟩, ⟨1, 2, 106⟩, ⟨1, 3, 19⟩, ⟨2, 3, 78⟩], triples := #[] }
def er028_019 : Row := { vars := #[3, 26, 414, 347], coeff := #[1, 1, 1, 1], bound := 1, weight := 57211, edges := #[⟨0, 1, 24⟩, ⟨0, 2, 193⟩, ⟨0, 3, 428⟩, ⟨1, 2, 208⟩, ⟨1, 3, 417⟩, ⟨2, 3, 103⟩], triples := #[] }
def er028_020 : Row := { vars := #[3, 28, 550, 226], coeff := #[1, 1, 1, 1], bound := 1, weight := 58964, edges := #[⟨0, 1, 21⟩, ⟨0, 2, 266⟩, ⟨0, 3, 361⟩, ⟨1, 2, 267⟩, ⟨1, 3, 376⟩, ⟨2, 3, 106⟩], triples := #[] }
def er028_021 : Row := { vars := #[3, 550, 137, 263], coeff := #[1, 1, 1, 1], bound := 1, weight := 151978, edges := #[⟨0, 1, 266⟩, ⟨0, 2, 153⟩, ⟨0, 3, 472⟩, ⟨1, 2, 212⟩, ⟨1, 3, 33⟩, ⟨2, 3, 412⟩], triples := #[] }
def er028_022 : Row := { vars := #[3, 448, 353, 197], coeff := #[1, 1, 1, 1], bound := 1, weight := 89180, edges := #[⟨0, 1, 322⟩, ⟨0, 2, 418⟩, ⟨0, 3, 83⟩, ⟨1, 2, 6⟩, ⟨1, 3, 213⟩, ⟨2, 3, 464⟩], triples := #[] }
def er028_023 : Row := { vars := #[3, 448, 325, 213], coeff := #[1, 1, 1, 1], bound := 1, weight := 122345, edges := #[⟨0, 1, 322⟩, ⟨0, 2, 416⟩, ⟨0, 3, 96⟩, ⟨1, 2, 31⟩, ⟨1, 3, 197⟩, ⟨2, 3, 464⟩], triples := #[] }
def er028_024 : Row := { vars := #[4, 24, 213, 215], coeff := #[1, 1, 1, 1], bound := 1, weight := 338258, edges := #[⟨0, 1, 18⟩, ⟨0, 2, 95⟩, ⟨0, 3, 92⟩, ⟨1, 2, 105⟩, ⟨1, 3, 102⟩, ⟨2, 3, 189⟩], triples := #[] }
def er028_025 : Row := { vars := #[4, 574, 9], coeff := #[1, 1, 1], bound := 1, weight := 146906, edges := #[⟨0, 1, 253⟩, ⟨0, 2, 4⟩, ⟨1, 2, 251⟩], triples := #[] }
def er028_026 : Row := { vars := #[4, 574, 217], coeff := #[1, 1, 1], bound := 1, weight := 11167, edges := #[⟨0, 1, 253⟩, ⟨0, 2, 386⟩, ⟨1, 2, 105⟩], triples := #[] }
def er028_027 : Row := { vars := #[5, 12, 514, 318], coeff := #[1, 1, 1, 1], bound := 1, weight := 419032, edges := #[⟨0, 1, 27⟩, ⟨0, 2, 280⟩, ⟨0, 3, 438⟩, ⟨1, 2, 279⟩, ⟨1, 3, 449⟩, ⟨2, 3, 150⟩], triples := #[] }
def er028_028 : Row := { vars := #[5, 12, 412, 216], coeff := #[1, 1, 1, 1], bound := 1, weight := 274703, edges := #[⟨0, 1, 27⟩, ⟨0, 2, 228⟩, ⟨0, 3, 386⟩, ⟨1, 2, 227⟩, ⟨1, 3, 391⟩, ⟨2, 3, 18⟩], triples := #[] }
def er028_029 : Row := { vars := #[20, 129, 358, 441], coeff := #[1, 1, 1, 1], bound := 1, weight := 757857, edges := #[⟨0, 1, 135⟩, ⟨0, 2, 432⟩, ⟨0, 3, 310⟩, ⟨1, 2, 356⟩, ⟨1, 3, 249⟩, ⟨2, 3, 13⟩], triples := #[] }
def er028_030 : Row := { vars := #[20, 8, 224, 519], coeff := #[1, 1, 1, 1], bound := 1, weight := 70376, edges := #[⟨0, 1, 21⟩, ⟨0, 2, 353⟩, ⟨0, 3, 266⟩, ⟨1, 2, 376⟩, ⟨1, 3, 257⟩, ⟨2, 3, 106⟩], triples := #[] }
def er028_031 : Row := { vars := #[20, 19, 428, 223], coeff := #[1, 1, 1, 1], bound := 1, weight := 102371, edges := #[⟨0, 1, 2⟩, ⟨0, 2, 320⟩, ⟨0, 3, 360⟩, ⟨1, 2, 321⟩, ⟨1, 3, 377⟩, ⟨2, 3, 146⟩], triples := #[] }
def er028_032 : Row := { vars := #[20, 62, 205, 199], coeff := #[1, 1, 1, 1], bound := 1, weight := 69398, edges := #[⟨0, 1, 186⟩, ⟨0, 2, 83⟩, ⟨0, 3, 93⟩, ⟨1, 2, 33⟩, ⟨1, 3, 5⟩, ⟨2, 3, 189⟩], triples := #[] }
def er028_033 : Row := { vars := #[21, 24, 205, 207], coeff := #[1, 1, 1, 1], bound := 1, weight := 146906, edges := #[⟨0, 1, 26⟩, ⟨0, 2, 82⟩, ⟨0, 3, 74⟩, ⟨1, 2, 85⟩, ⟨1, 3, 77⟩, ⟨2, 3, 187⟩], triples := #[] }
def er028_034 : Row := { vars := #[22, 507, 16], coeff := #[1, 1, 1], bound := 1, weight := 73790, edges := #[⟨0, 1, 306⟩, ⟨0, 2, 12⟩, ⟨1, 2, 301⟩], triples := #[] }
def er028_035 : Row := { vars := #[22, 470, 216], coeff := #[1, 1, 1], bound := 1, weight := 497735, edges := #[⟨0, 1, 304⟩, ⟨0, 2, 388⟩, ⟨1, 2, 145⟩], triples := #[] }
def er028_036 : Row := { vars := #[25, 473, 220], coeff := #[1, 1, 1], bound := 1, weight := 721592, edges := #[⟨0, 1, 304⟩, ⟨0, 2, 391⟩, ⟨1, 2, 155⟩], triples := #[] }
def er028_037 : Row := { vars := #[26, 301, 438], coeff := #[1, 1, 1], bound := 1, weight := 98453, edges := #[⟨0, 1, 460⟩, ⟨0, 2, 312⟩, ⟨1, 2, 106⟩], triples := #[] }
def er028_038 : Row := { vars := #[26, 493, 246], coeff := #[1, 1, 1], bound := 1, weight := 626691, edges := #[⟨0, 1, 300⟩, ⟨0, 2, 472⟩, ⟨1, 2, 106⟩], triples := #[] }
def er028_039 : Row := { vars := #[27, 9, 117, 123], coeff := #[1, 1, 1, 1], bound := 1, weight := 622744, edges := #[⟨0, 1, 19⟩, ⟨0, 2, 155⟩, ⟨0, 3, 145⟩, ⟨1, 2, 134⟩, ⟨1, 3, 162⟩, ⟨2, 3, 129⟩], triples := #[] }
def er028_040 : Row := { vars := #[27, 273, 377], coeff := #[1, 1, 1], bound := 1, weight := 377257, edges := #[⟨0, 1, 481⟩, ⟨0, 2, 408⟩, ⟨1, 2, 210⟩], triples := #[] }
def er028_041 : Row := { vars := #[28, 6, 195, 201], coeff := #[1, 1, 1, 1], bound := 1, weight := 941037, edges := #[⟨0, 1, 18⟩, ⟨0, 2, 92⟩, ⟨0, 3, 77⟩, ⟨1, 2, 82⟩, ⟨1, 3, 105⟩, ⟨2, 3, 189⟩], triples := #[] }
def er028_042 : Row := { vars := #[29, 267, 239, 419], coeff := #[1, 1, 1, 1], bound := 1, weight := 495781, edges := #[⟨0, 1, 481⟩, ⟨0, 2, 472⟩, ⟨0, 3, 217⟩, ⟨1, 2, 262⟩, ⟨1, 3, 166⟩, ⟨2, 3, 156⟩], triples := #[] }
def er028_043 : Row := { vars := #[29, 549, 382], coeff := #[1, 1, 1], bound := 1, weight := 444564, edges := #[⟨0, 1, 267⟩, ⟨0, 2, 407⟩, ⟨1, 2, 135⟩], triples := #[] }
def er028_044 : Row := { vars := #[30, 50, 517, 339], coeff := #[1, 1, 1, 1], bound := 1, weight := 875372, edges := #[⟨0, 1, 54⟩, ⟨0, 2, 247⟩, ⟨0, 3, 411⟩, ⟨1, 2, 248⟩, ⟨1, 3, 406⟩, ⟨2, 3, 177⟩], triples := #[] }
def er028_045 : Row := { vars := #[31, 458, 222], coeff := #[1, 1, 1], bound := 1, weight := 272440, edges := #[⟨0, 1, 304⟩, ⟨0, 2, 397⟩, ⟨1, 2, 155⟩], triples := #[] }
def er028_046 : Row := { vars := #[31, 458, 38], coeff := #[1, 1, 1], bound := 1, weight := 532982, edges := #[⟨0, 1, 304⟩, ⟨0, 2, 43⟩, ⟨1, 2, 302⟩], triples := #[] }
def er028_047 : Row := { vars := #[31, 80, 172, 182], coeff := #[1, 1, 1, 1], bound := 1, weight := 194579, edges := #[⟨0, 1, 175⟩, ⟨0, 2, 87⟩, ⟨0, 3, 104⟩, ⟨1, 2, 59⟩, ⟨1, 3, 38⟩, ⟨2, 3, 176⟩], triples := #[] }
def er028_048 : Row := { vars := #[33, 40, 96, 110], coeff := #[1, 1, 1, 1], bound := 1, weight := 177906, edges := #[⟨0, 1, 62⟩, ⟨0, 2, 136⟩, ⟨0, 3, 157⟩, ⟨1, 2, 164⟩, ⟨1, 3, 147⟩, ⟨2, 3, 114⟩], triples := #[] }
def er028_049 : Row := { vars := #[33, 53, 545, 353], coeff := #[1, 1, 1, 1], bound := 1, weight := 676497, edges := #[⟨0, 1, 54⟩, ⟨0, 2, 248⟩, ⟨0, 3, 408⟩, ⟨1, 2, 251⟩, ⟨1, 3, 411⟩, ⟨2, 3, 177⟩], triples := #[] }
def er028_050 : Row := { vars := #[33, 342, 415], coeff := #[1, 1, 1], bound := 1, weight := 145599, edges := #[⟨0, 1, 413⟩, ⟨0, 2, 236⟩, ⟨1, 2, 105⟩], triples := #[] }
def er028_051 : Row := { vars := #[34, 467, 56], coeff := #[1, 1, 1], bound := 1, weight := 63155, edges := #[⟨0, 1, 303⟩, ⟨0, 2, 61⟩, ⟨1, 2, 305⟩], triples := #[] }
def er028_052 : Row := { vars := #[34, 54, 455, 263], coeff := #[1, 1, 1, 1], bound := 1, weight := 326537, edges := #[⟨0, 1, 55⟩, ⟨0, 2, 302⟩, ⟨0, 3, 462⟩, ⟨1, 2, 305⟩, ⟨1, 3, 465⟩, ⟨2, 3, 117⟩], triples := #[] }
def er028_053 : Row := { vars := #[34, 54, 188, 190], coeff := #[1, 1, 1, 1], bound := 1, weight := 194729, edges := #[⟨0, 1, 55⟩, ⟨0, 2, 97⟩, ⟨0, 3, 94⟩, ⟨1, 2, 107⟩, ⟨1, 3, 104⟩, ⟨2, 3, 176⟩], triples := #[] }
def er028_054 : Row := { vars := #[35, 401, 113, 497], coeff := #[1, 1, 1, 1], bound := 1, weight := 19245, edges := #[⟨0, 1, 448⟩, ⟨0, 2, 154⟩, ⟨0, 3, 334⟩, ⟨1, 2, 374⟩, ⟨1, 3, 69⟩, ⟨2, 3, 252⟩], triples := #[] }
def er028_055 : Row := { vars := #[35, 293, 587, 175], coeff := #[1, 1, 1, 1], bound := 1, weight := 361735, edges := #[⟨0, 1, 508⟩, ⟨0, 2, 280⟩, ⟨0, 3, 76⟩, ⟨1, 2, 50⟩, ⟨1, 3, 375⟩, ⟨2, 3, 303⟩], triples := #[] }
def er028_056 : Row := { vars := #[36, 286, 436], coeff := #[1, 1, 1], bound := 1, weight := 962704, edges := #[⟨0, 1, 493⟩, ⟨0, 2, 301⟩, ⟨1, 2, 84⟩], triples := #[] }
def er028_057 : Row := { vars := #[36, 289, 439], coeff := #[1, 1, 1], bound := 1, weight := 36082, edges := #[⟨0, 1, 492⟩, ⟨0, 2, 300⟩, ⟨1, 2, 87⟩], triples := #[] }
def er028_058 : Row := { vars := #[36, 568, 464], coeff := #[1, 1, 1], bound := 1, weight := 1216, edges := #[⟨0, 1, 279⟩, ⟨0, 2, 302⟩, ⟨1, 2, 371⟩], triples := #[] }
def er028_059 : Row := { vars := #[37, 413, 288, 299], coeff := #[1, 1, 1, 1], bound := 1, weight := 830469, edges := #[⟨0, 1, 209⟩, ⟨0, 2, 492⟩, ⟨0, 3, 503⟩, ⟨1, 2, 154⟩, ⟨1, 3, 139⟩, ⟨2, 3, 294⟩], triples := #[] }
def er028_060 : Row := { vars := #[37, 49, 107, 91], coeff := #[1, 1, 1, 1], bound := 1, weight := 44904, edges := #[⟨0, 1, 63⟩, ⟨0, 2, 155⟩, ⟨0, 3, 145⟩, ⟨1, 2, 134⟩, ⟨1, 3, 162⟩, ⟨2, 3, 115⟩], triples := #[] }
def er028_061 : Row := { vars := #[37, 334, 50], coeff := #[1, 1, 1], bound := 1, weight := 124629, edges := #[⟨0, 1, 407⟩, ⟨0, 2, 61⟩, ⟨1, 2, 409⟩], triples := #[] }
def er028_062 : Row := { vars := #[38, 430, 590], coeff := #[1, 1, 1], bound := 1, weight := 53701, edges := #[⟨0, 1, 301⟩, ⟨0, 2, 280⟩, ⟨1, 2, 367⟩], triples := #[] }
def er028_063 : Row := { vars := #[38, 472, 238], coeff := #[1, 1, 1], bound := 1, weight := 374779, edges := #[⟨0, 1, 333⟩, ⟨0, 2, 461⟩, ⟨1, 2, 76⟩], triples := #[] }
end HardyCapset20261020.Cert


