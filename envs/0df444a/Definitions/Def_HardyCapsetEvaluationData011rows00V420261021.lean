-- Prove2me | Definitions.Def_HardyCapsetEvaluationData011rows00V420261021
-- name    : HardyCapsetEvaluationData011rows00V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T01:44:00.55067+00:00
-- url     : https://prove2.me/theorems/73361b60-9053-4adf-9e5b-d5ac449de886
-- title:
--   HardyCapsetEvaluationData011rows00V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er011_000 : Row := { vars := #[24, 223], coeff := #[1, 1], bound := 1, weight := 136333, edges := #[⟨0, 1, 386⟩], triples := #[] }
def er011_001 : Row := { vars := #[54, 98], coeff := #[1, 1], bound := 1, weight := 203385, edges := #[⟨0, 1, 175⟩], triples := #[] }
def er011_002 : Row := { vars := #[55, 394], coeff := #[1, 1], bound := 1, weight := 81902, edges := #[⟨0, 1, 257⟩], triples := #[] }
def er011_003 : Row := { vars := #[61, 343], coeff := #[1, 1], bound := 1, weight := 52591, edges := #[⟨0, 1, 194⟩], triples := #[] }
def er011_004 : Row := { vars := #[85, 318], coeff := #[1, 1], bound := 1, weight := 218314, edges := #[⟨0, 1, 301⟩], triples := #[] }
def er011_005 : Row := { vars := #[85, 394], coeff := #[1, 1], bound := 1, weight := 132834, edges := #[⟨0, 1, 197⟩], triples := #[] }
def er011_006 : Row := { vars := #[90, 369], coeff := #[1, 1], bound := 1, weight := 273122, edges := #[⟨0, 1, 280⟩], triples := #[] }
def er011_007 : Row := { vars := #[116, 250], coeff := #[1, 1], bound := 1, weight := 35777, edges := #[⟨0, 1, 414⟩], triples := #[] }
def er011_008 : Row := { vars := #[143, 378], coeff := #[1, 1], bound := 1, weight := 44024, edges := #[⟨0, 1, 227⟩], triples := #[] }
def er011_009 : Row := { vars := #[151, 254], coeff := #[1, 1], bound := 1, weight := 34115, edges := #[⟨0, 1, 398⟩], triples := #[] }
def er011_010 : Row := { vars := #[158, 244], coeff := #[1, 1], bound := 1, weight := 648823, edges := #[⟨0, 1, 372⟩], triples := #[] }
def er011_011 : Row := { vars := #[183, 415], coeff := #[1, 1], bound := 1, weight := 158543, edges := #[⟨0, 1, 331⟩], triples := #[] }
def er011_012 : Row := { vars := #[196, 359], coeff := #[1, 1], bound := 1, weight := 71993, edges := #[⟨0, 1, 231⟩], triples := #[] }
def er011_013 : Row := { vars := #[205, 342], coeff := #[1, 1], bound := 1, weight := 539439, edges := #[⟨0, 1, 53⟩], triples := #[] }
def er011_014 : Row := { vars := #[207, 394], coeff := #[1, 1], bound := 1, weight := 86700, edges := #[⟨0, 1, 101⟩], triples := #[] }
def er011_015 : Row := { vars := #[217, 267], coeff := #[1, 1], bound := 1, weight := 181223, edges := #[⟨0, 1, 311⟩], triples := #[] }
def er011_016 : Row := { vars := #[229, 425], coeff := #[1, 1], bound := 1, weight := 188387, edges := #[⟨0, 1, 125⟩], triples := #[] }
def er011_017 : Row := { vars := #[236, 389], coeff := #[1, 1], bound := 1, weight := 392066, edges := #[⟨0, 1, 188⟩], triples := #[] }
def er011_018 : Row := { vars := #[241, 342], coeff := #[1, 1], bound := 1, weight := 161599, edges := #[⟨0, 1, 185⟩], triples := #[] }
def er011_019 : Row := { vars := #[242, 341], coeff := #[1, 1], bound := 1, weight := 417843, edges := #[⟨0, 1, 184⟩], triples := #[] }
def er011_020 : Row := { vars := #[251, 339], coeff := #[1, 1], bound := 1, weight := 14256, edges := #[⟨0, 1, 176⟩], triples := #[] }
def er011_021 : Row := { vars := #[277, 343], coeff := #[1, 1], bound := 1, weight := 55262, edges := #[⟨0, 1, 124⟩], triples := #[] }
def er011_022 : Row := { vars := #[295, 365], coeff := #[1, 1], bound := 1, weight := 110714, edges := #[⟨0, 1, 18⟩], triples := #[] }
def er011_023 : Row := { vars := #[309, 345], coeff := #[1, 1], bound := 1, weight := 103936, edges := #[⟨0, 1, 125⟩], triples := #[] }
def er011_024 : Row := { vars := #[315, 425], coeff := #[1, 1], bound := 1, weight := 28011, edges := #[⟨0, 1, 418⟩], triples := #[] }
def er011_025 : Row := { vars := #[325, 389], coeff := #[1, 1], bound := 1, weight := 26314, edges := #[⟨0, 1, 470⟩], triples := #[] }
def er011_026 : Row := { vars := #[7, 206, 331], coeff := #[1, 1, 1], bound := 2, weight := 231215, edges := #[], triples := #[⟨0, 1, 2⟩] }
def er011_027 : Row := { vars := #[7, 304, 374], coeff := #[1, 1, 1], bound := 2, weight := 331970, edges := #[], triples := #[⟨0, 1, 2⟩] }
def er011_028 : Row := { vars := #[49, 59, 65], coeff := #[1, 1, 1], bound := 2, weight := 17573, edges := #[], triples := #[⟨0, 1, 2⟩] }
def er011_029 : Row := { vars := #[117, 265, 389], coeff := #[1, 1, 1], bound := 2, weight := 125534, edges := #[], triples := #[⟨0, 1, 2⟩] }
def er011_030 : Row := { vars := #[24, 416, 152, 114], coeff := #[1, 1, 1, 1], bound := 1, weight := 148185, edges := #[⟨0, 1, 247⟩, ⟨0, 2, 128⟩, ⟨0, 3, 173⟩, ⟨1, 2, 327⟩, ⟨1, 3, 209⟩, ⟨2, 3, 47⟩], triples := #[] }
def er011_031 : Row := { vars := #[25, 356, 302], coeff := #[1, 1, 1], bound := 1, weight := 421890, edges := #[⟨0, 1, 333⟩, ⟨0, 2, 407⟩, ⟨1, 2, 13⟩], triples := #[] }
def er011_032 : Row := { vars := #[26, 203, 348], coeff := #[1, 1, 1], bound := 1, weight := 31994, edges := #[⟨0, 1, 397⟩, ⟨0, 2, 198⟩, ⟨1, 2, 14⟩], triples := #[] }
def er011_033 : Row := { vars := #[28, 328, 234], coeff := #[1, 1, 1], bound := 1, weight := 143971, edges := #[⟨0, 1, 238⟩, ⟨0, 2, 363⟩, ⟨1, 2, 23⟩], triples := #[] }
def er011_034 : Row := { vars := #[35, 236, 336], coeff := #[1, 1, 1], bound := 1, weight := 101199, edges := #[⟨0, 1, 375⟩, ⟨0, 2, 241⟩, ⟨1, 2, 33⟩], triples := #[] }
def er011_035 : Row := { vars := #[37, 228, 378], coeff := #[1, 1, 1], bound := 1, weight := 176159, edges := #[⟨0, 1, 391⟩, ⟨0, 2, 302⟩, ⟨1, 2, 155⟩], triples := #[] }
def er011_036 : Row := { vars := #[52, 338, 222], coeff := #[1, 1, 1], bound := 1, weight := 279294, edges := #[⟨0, 1, 197⟩, ⟨0, 2, 357⟩, ⟨1, 2, 9⟩], triples := #[] }
def er011_037 : Row := { vars := #[55, 198, 338], coeff := #[1, 1, 1], bound := 1, weight := 142119, edges := #[⟨0, 1, 385⟩, ⟨0, 2, 193⟩, ⟨1, 2, 50⟩], triples := #[] }
def er011_038 : Row := { vars := #[57, 292, 358], coeff := #[1, 1, 1], bound := 1, weight := 546748, edges := #[⟨0, 1, 408⟩, ⟨0, 2, 312⟩, ⟨1, 2, 59⟩], triples := #[] }
def er011_039 : Row := { vars := #[58, 226, 342], coeff := #[1, 1, 1], bound := 1, weight := 106135, edges := #[⟨0, 1, 360⟩, ⟨0, 2, 200⟩, ⟨1, 2, 25⟩], triples := #[] }
def er011_040 : Row := { vars := #[58, 334, 222], coeff := #[1, 1, 1], bound := 1, weight := 209378, edges := #[⟨0, 1, 225⟩, ⟨0, 2, 373⟩, ⟨1, 2, 60⟩], triples := #[] }
def er011_041 : Row := { vars := #[59, 350, 285], coeff := #[1, 1, 1], bound := 1, weight := 119623, edges := #[⟨0, 1, 238⟩, ⟨0, 2, 411⟩, ⟨1, 2, 105⟩], triples := #[] }
def er011_042 : Row := { vars := #[59, 401, 234], coeff := #[1, 1, 1], bound := 1, weight := 15153, edges := #[⟨0, 1, 251⟩, ⟨0, 2, 398⟩, ⟨1, 2, 105⟩], triples := #[] }
def er011_043 : Row := { vars := #[59, 285, 129, 153], coeff := #[1, 1, 1, 1], bound := 1, weight := 157068, edges := #[⟨0, 1, 411⟩, ⟨0, 2, 185⟩, ⟨0, 3, 114⟩, ⟨1, 2, 381⟩, ⟨1, 3, 510⟩, ⟨2, 3, 24⟩], triples := #[] }
def er011_044 : Row := { vars := #[64, 360, 297], coeff := #[1, 1, 1], bound := 1, weight := 648823, edges := #[⟨0, 1, 321⟩, ⟨0, 2, 411⟩, ⟨1, 2, 69⟩], triples := #[] }
def er011_045 : Row := { vars := #[86, 109, 128], coeff := #[1, 1, 1], bound := 1, weight := 9085, edges := #[⟨0, 1, 126⟩, ⟨0, 2, 112⟩, ⟨1, 2, 95⟩], triples := #[] }
def er011_046 : Row := { vars := #[88, 396, 210], coeff := #[1, 1, 1], bound := 1, weight := 359133, edges := #[⟨0, 1, 201⟩, ⟨0, 2, 462⟩, ⟨1, 2, 97⟩], triples := #[] }
def er011_047 : Row := { vars := #[94, 193, 41], coeff := #[1, 1, 1], bound := 1, weight := 57335, edges := #[⟨0, 1, 29⟩, ⟨0, 2, 188⟩, ⟨1, 2, 106⟩], triples := #[] }
def er011_048 : Row := { vars := #[144, 223, 379], coeff := #[1, 1, 1], bound := 1, weight := 171678, edges := #[⟨0, 1, 438⟩, ⟨0, 2, 226⟩, ⟨1, 2, 143⟩], triples := #[] }
def er011_049 : Row := { vars := #[144, 355, 239], coeff := #[1, 1, 1], bound := 1, weight := 561660, edges := #[⟨0, 1, 194⟩, ⟨0, 2, 354⟩, ⟨1, 2, 82⟩], triples := #[] }
def er011_050 : Row := { vars := #[148, 415, 286], coeff := #[1, 1, 1], bound := 1, weight := 108737, edges := #[⟨0, 1, 310⟩, ⟨0, 2, 491⟩, ⟨1, 2, 147⟩], triples := #[] }
def er011_051 : Row := { vars := #[149, 280, 396], coeff := #[1, 1, 1], bound := 1, weight := 147450, edges := #[⟨0, 1, 462⟩, ⟨0, 2, 302⟩, ⟨1, 2, 155⟩], triples := #[] }
def er011_052 : Row := { vars := #[158, 352, 259], coeff := #[1, 1, 1], bound := 1, weight := 120651, edges := #[⟨0, 1, 267⟩, ⟨0, 2, 401⟩, ⟨1, 2, 167⟩], triples := #[] }
def er011_053 : Row := { vars := #[205, 32, 408], coeff := #[1, 1, 1], bound := 1, weight := 12221, edges := #[⟨0, 1, 398⟩, ⟨0, 2, 124⟩, ⟨1, 2, 266⟩], triples := #[] }
def er011_054 : Row := { vars := #[208, 199, 89], coeff := #[1, 1, 1], bound := 1, weight := 394694, edges := #[⟨0, 1, 215⟩, ⟨0, 2, 462⟩, ⟨1, 2, 467⟩], triples := #[] }
def er011_055 : Row := { vars := #[215, 201, 353], coeff := #[1, 1, 1], bound := 1, weight := 589000, edges := #[⟨0, 1, 201⟩, ⟨0, 2, 150⟩, ⟨1, 2, 143⟩], triples := #[] }
def er011_056 : Row := { vars := #[216, 98, 375], coeff := #[1, 1, 1], bound := 1, weight := 324844, edges := #[⟨0, 1, 465⟩, ⟨0, 2, 191⟩, ⟨1, 2, 294⟩], triples := #[] }
def er011_057 : Row := { vars := #[225, 259, 286], coeff := #[1, 1, 1], bound := 1, weight := 879350, edges := #[⟨0, 1, 310⟩, ⟨0, 2, 267⟩, ⟨1, 2, 230⟩], triples := #[] }
def er011_058 : Row := { vars := #[227, 399, 249], coeff := #[1, 1, 1], bound := 1, weight := 492038, edges := #[⟨0, 1, 114⟩, ⟨0, 2, 312⟩, ⟨1, 2, 11⟩], triples := #[] }
def er011_059 : Row := { vars := #[233, 263, 414], coeff := #[1, 1, 1], bound := 1, weight := 589317, edges := #[⟨0, 1, 343⟩, ⟨0, 2, 128⟩, ⟨1, 2, 50⟩], triples := #[] }
def er011_060 : Row := { vars := #[233, 274, 301], coeff := #[1, 1, 1], bound := 1, weight := 224898, edges := #[⟨0, 1, 332⟩, ⟨0, 2, 289⟩, ⟨1, 2, 240⟩], triples := #[] }
def er011_061 : Row := { vars := #[235, 302, 376], coeff := #[1, 1, 1], bound := 1, weight := 395044, edges := #[⟨0, 1, 280⟩, ⟨0, 2, 186⟩, ⟨1, 2, 46⟩], triples := #[] }
def er011_062 : Row := { vars := #[247, 389, 67, 109, 62], coeff := #[1, 1, 1, 1, 1], bound := 1, weight := 29582, edges := #[⟨0, 1, 89⟩, ⟨0, 2, 464⟩, ⟨0, 3, 434⟩, ⟨0, 4, 467⟩, ⟨1, 2, 343⟩, ⟨1, 3, 244⟩, ⟨1, 4, 333⟩, ⟨2, 3, 144⟩, ⟨2, 4, 44⟩, ⟨3, 4, 157⟩], triples := #[] }
def er011_063 : Row := { vars := #[247, 41, 368, 193, 191], coeff := #[1, 1, 1, 1, 1], bound := 1, weight := 12685, edges := #[⟨0, 1, 479⟩, ⟨0, 2, 119⟩, ⟨0, 3, 370⟩, ⟨0, 4, 382⟩, ⟨1, 2, 309⟩, ⟨1, 3, 106⟩, ⟨1, 4, 86⟩, ⟨2, 3, 192⟩, ⟨2, 4, 200⟩, ⟨3, 4, 182⟩], triples := #[] }
end HardyCapset20261020.Cert


