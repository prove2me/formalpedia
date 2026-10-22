-- Prove2me | Definitions.Def_HardyCapsetEvaluationData185rows00V420261021
-- name    : HardyCapsetEvaluationData185rows00V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T03:48:31.636008+00:00
-- url     : https://prove2.me/theorems/dc4b142c-d62e-43fd-9202-8943ac9beffe
-- title:
--   HardyCapsetEvaluationData185rows00V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er185_000 : Row := { vars := #[3, 257], coeff := #[1, 1], bound := 1, weight := 428572, edges := #[⟨0, 1, 257⟩], triples := #[] }
def er185_001 : Row := { vars := #[5, 197], coeff := #[1, 1], bound := 1, weight := 303572, edges := #[⟨0, 1, 195⟩], triples := #[] }
def er185_002 : Row := { vars := #[5, 275], coeff := #[1, 1], bound := 1, weight := 232143, edges := #[⟨0, 1, 246⟩], triples := #[] }
def er185_003 : Row := { vars := #[7, 161], coeff := #[1, 1], bound := 1, weight := 17858, edges := #[⟨0, 1, 236⟩], triples := #[] }
def er185_004 : Row := { vars := #[8, 13], coeff := #[1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 32⟩], triples := #[] }
def er185_005 : Row := { vars := #[10, 52], coeff := #[1, 1], bound := 1, weight := 339286, edges := #[⟨0, 1, 131⟩], triples := #[] }
def er185_006 : Row := { vars := #[14, 34], coeff := #[1, 1], bound := 1, weight := 732143, edges := #[⟨0, 1, 172⟩], triples := #[] }
def er185_007 : Row := { vars := #[19, 161], coeff := #[1, 1], bound := 1, weight := 982143, edges := #[⟨0, 1, 226⟩], triples := #[] }
def er185_008 : Row := { vars := #[21, 141], coeff := #[1, 1], bound := 1, weight := 214286, edges := #[⟨0, 1, 431⟩], triples := #[] }
def er185_009 : Row := { vars := #[26, 203], coeff := #[1, 1], bound := 1, weight := 660715, edges := #[⟨0, 1, 246⟩], triples := #[] }
def er185_010 : Row := { vars := #[33, 197], coeff := #[1, 1], bound := 1, weight := 321429, edges := #[⟨0, 1, 317⟩], triples := #[] }
def er185_011 : Row := { vars := #[35, 207], coeff := #[1, 1], bound := 1, weight := 339286, edges := #[⟨0, 1, 251⟩], triples := #[] }
def er185_012 : Row := { vars := #[42, 270], coeff := #[1, 1], bound := 1, weight := 196429, edges := #[⟨0, 1, 203⟩], triples := #[] }
def er185_013 : Row := { vars := #[49, 249], coeff := #[1, 1], bound := 1, weight := 642858, edges := #[⟨0, 1, 300⟩], triples := #[] }
def er185_014 : Row := { vars := #[50, 123], coeff := #[1, 1], bound := 1, weight := 17858, edges := #[⟨0, 1, 395⟩], triples := #[] }
def er185_015 : Row := { vars := #[53, 107], coeff := #[1, 1], bound := 1, weight := 571429, edges := #[⟨0, 1, 430⟩], triples := #[] }
def er185_016 : Row := { vars := #[56, 179], coeff := #[1, 1], bound := 1, weight := 321429, edges := #[⟨0, 1, 251⟩], triples := #[] }
def er185_017 : Row := { vars := #[64, 197], coeff := #[1, 1], bound := 1, weight := 357143, edges := #[⟨0, 1, 287⟩], triples := #[] }
def er185_018 : Row := { vars := #[70, 126], coeff := #[1, 1], bound := 1, weight := 303572, edges := #[⟨0, 1, 341⟩], triples := #[] }
def er185_019 : Row := { vars := #[70, 132], coeff := #[1, 1], bound := 1, weight := 696429, edges := #[⟨0, 1, 318⟩], triples := #[] }
def er185_020 : Row := { vars := #[80, 132], coeff := #[1, 1], bound := 1, weight := 303572, edges := #[⟨0, 1, 328⟩], triples := #[] }
def er185_021 : Row := { vars := #[80, 150], coeff := #[1, 1], bound := 1, weight := 696429, edges := #[⟨0, 1, 296⟩], triples := #[] }
def er185_022 : Row := { vars := #[81, 139], coeff := #[1, 1], bound := 1, weight := 303572, edges := #[⟨0, 1, 247⟩], triples := #[] }
def er185_023 : Row := { vars := #[82, 193], coeff := #[1, 1], bound := 1, weight := 89286, edges := #[⟨0, 1, 64⟩], triples := #[] }
def er185_024 : Row := { vars := #[83, 204], coeff := #[1, 1], bound := 1, weight := 535715, edges := #[⟨0, 1, 149⟩], triples := #[] }
def er185_025 : Row := { vars := #[88, 247], coeff := #[1, 1], bound := 1, weight := 71429, edges := #[⟨0, 1, 156⟩], triples := #[] }
def er185_026 : Row := { vars := #[89, 208], coeff := #[1, 1], bound := 1, weight := 339286, edges := #[⟨0, 1, 184⟩], triples := #[] }
def er185_027 : Row := { vars := #[96, 180], coeff := #[1, 1], bound := 1, weight := 446429, edges := #[⟨0, 1, 64⟩], triples := #[] }
def er185_028 : Row := { vars := #[99, 157], coeff := #[1, 1], bound := 1, weight := 321429, edges := #[⟨0, 1, 9⟩], triples := #[] }
def er185_029 : Row := { vars := #[117, 183], coeff := #[1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 161⟩], triples := #[] }
def er185_030 : Row := { vars := #[126, 230], coeff := #[1, 1], bound := 1, weight := 696429, edges := #[⟨0, 1, 89⟩], triples := #[] }
def er185_031 : Row := { vars := #[139, 173], coeff := #[1, 1], bound := 1, weight := 35715, edges := #[⟨0, 1, 80⟩], triples := #[] }
def er185_032 : Row := { vars := #[144, 190], coeff := #[1, 1], bound := 1, weight := 303572, edges := #[⟨0, 1, 125⟩], triples := #[] }
def er185_033 : Row := { vars := #[176, 224], coeff := #[1, 1], bound := 1, weight := 535715, edges := #[⟨0, 1, 507⟩], triples := #[] }
def er185_034 : Row := { vars := #[176, 243], coeff := #[1, 1], bound := 1, weight := 464286, edges := #[⟨0, 1, 484⟩], triples := #[] }
def er185_035 : Row := { vars := #[179, 220], coeff := #[1, 1], bound := 1, weight := 660715, edges := #[⟨0, 1, 493⟩], triples := #[] }
def er185_036 : Row := { vars := #[254, 291], coeff := #[1, 1], bound := 1, weight := 732143, edges := #[⟨0, 1, 486⟩], triples := #[] }
def er185_037 : Row := { vars := #[0, 12, 252], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 49⟩, ⟨0, 2, 247⟩, ⟨1, 2, 289⟩], triples := #[] }
def er185_038 : Row := { vars := #[1, 256, 246], coeff := #[1, 1, 1], bound := 1, weight := 303572, edges := #[⟨0, 1, 280⟩, ⟨0, 2, 328⟩, ⟨1, 2, 361⟩], triples := #[] }
def er185_039 : Row := { vars := #[2, 7, 263], coeff := #[1, 1, 1], bound := 1, weight := 982143, edges := #[⟨0, 1, 4⟩, ⟨0, 2, 271⟩, ⟨1, 2, 275⟩], triples := #[] }
def er185_040 : Row := { vars := #[10, 256, 223], coeff := #[1, 1, 1], bound := 1, weight := 357143, edges := #[⟨0, 1, 263⟩, ⟨0, 2, 327⟩, ⟨1, 2, 389⟩], triples := #[] }
def er185_041 : Row := { vars := #[14, 196, 235], coeff := #[1, 1, 1], bound := 1, weight := 267858, edges := #[⟨0, 1, 236⟩, ⟨0, 2, 345⟩, ⟨1, 2, 505⟩], triples := #[] }
def er185_042 : Row := { vars := #[18, 280, 94], coeff := #[1, 1, 1], bound := 1, weight := 17858, edges := #[⟨0, 1, 297⟩, ⟨0, 2, 369⟩, ⟨1, 2, 81⟩], triples := #[] }
def er185_043 : Row := { vars := #[26, 29, 237], coeff := #[1, 1, 1], bound := 1, weight := 339286, edges := #[⟨0, 1, 74⟩, ⟨0, 2, 270⟩, ⟨1, 2, 274⟩], triples := #[] }
def er185_044 : Row := { vars := #[31, 118, 218], coeff := #[1, 1, 1], bound := 1, weight := 142858, edges := #[⟨0, 1, 410⟩, ⟨0, 2, 297⟩, ⟨1, 2, 122⟩], triples := #[] }
def er185_045 : Row := { vars := #[40, 113, 178], coeff := #[1, 1, 1], bound := 1, weight := 339286, edges := #[⟨0, 1, 442⟩, ⟨0, 2, 351⟩, ⟨1, 2, 150⟩], triples := #[] }
def er185_046 : Row := { vars := #[41, 164, 93], coeff := #[1, 1, 1], bound := 1, weight := 285715, edges := #[⟨0, 1, 341⟩, ⟨0, 2, 484⟩, ⟨1, 2, 54⟩], triples := #[] }
def er185_047 : Row := { vars := #[41, 165, 94], coeff := #[1, 1, 1], bound := 1, weight := 714286, edges := #[⟨0, 1, 340⟩, ⟨0, 2, 483⟩, ⟨1, 2, 55⟩], triples := #[] }
def er185_048 : Row := { vars := #[45, 162, 105], coeff := #[1, 1, 1], bound := 1, weight := 250001, edges := #[⟨0, 1, 318⟩, ⟨0, 2, 507⟩, ⟨1, 2, 18⟩], triples := #[] }
def er185_049 : Row := { vars := #[46, 248, 261], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 300⟩, ⟨0, 2, 346⟩, ⟨1, 2, 506⟩], triples := #[] }
def er185_050 : Row := { vars := #[61, 164, 93], coeff := #[1, 1, 1], bound := 1, weight := 714286, edges := #[⟨0, 1, 287⟩, ⟨0, 2, 430⟩, ⟨1, 2, 54⟩], triples := #[] }
def er185_051 : Row := { vars := #[65, 167, 186], coeff := #[1, 1, 1], bound := 1, weight := 250000, edges := #[⟨0, 1, 261⟩, ⟨0, 2, 271⟩, ⟨1, 2, 369⟩], triples := #[] }
def er185_052 : Row := { vars := #[66, 71, 194], coeff := #[1, 1, 1], bound := 1, weight := 571429, edges := #[⟨0, 1, 216⟩, ⟨0, 2, 57⟩, ⟨1, 2, 42⟩], triples := #[] }
def er185_053 : Row := { vars := #[83, 230, 287], coeff := #[1, 1, 1], bound := 1, weight := 303572, edges := #[⟨0, 1, 173⟩, ⟨0, 2, 119⟩, ⟨1, 2, 399⟩], triples := #[] }
def er185_054 : Row := { vars := #[89, 277, 56], coeff := #[1, 1, 1], bound := 1, weight := 660715, edges := #[⟨0, 1, 81⟩, ⟨0, 2, 448⟩, ⟨1, 2, 317⟩], triples := #[] }
def er185_055 : Row := { vars := #[97, 259, 218], coeff := #[1, 1, 1], bound := 1, weight := 535715, edges := #[⟨0, 1, 75⟩, ⟨0, 2, 162⟩, ⟨1, 2, 393⟩], triples := #[] }
def er185_056 : Row := { vars := #[100, 37, 215], coeff := #[1, 1, 1], bound := 1, weight := 410715, edges := #[⟨0, 1, 480⟩, ⟨0, 2, 140⟩, ⟨1, 2, 287⟩], triples := #[] }
def er185_057 : Row := { vars := #[100, 11, 287], coeff := #[1, 1, 1], bound := 1, weight := 160715, edges := #[⟨0, 1, 368⟩, ⟨0, 2, 126⟩, ⟨1, 2, 251⟩], triples := #[] }
def er185_058 : Row := { vars := #[101, 260, 226], coeff := #[1, 1, 1], bound := 1, weight := 571429, edges := #[⟨0, 1, 80⟩, ⟨0, 2, 157⟩, ⟨1, 2, 390⟩], triples := #[] }
def er185_059 : Row := { vars := #[106, 170, 264, 236], coeff := #[1, 1, 1, 1], bound := 1, weight := 160715, edges := #[⟨0, 1, 5⟩, ⟨0, 2, 87⟩, ⟨0, 3, 183⟩, ⟨1, 2, 443⟩, ⟨1, 3, 476⟩, ⟨2, 3, 368⟩], triples := #[] }
def er185_060 : Row := { vars := #[108, 162, 178], coeff := #[1, 1, 1], bound := 1, weight := 339286, edges := #[⟨0, 1, 17⟩, ⟨0, 2, 28⟩, ⟨1, 2, 366⟩], triples := #[] }
def er185_061 : Row := { vars := #[113, 178, 160], coeff := #[1, 1, 1], bound := 1, weight := 107143, edges := #[⟨0, 1, 150⟩, ⟨0, 2, 134⟩, ⟨1, 2, 369⟩], triples := #[] }
def er185_062 : Row := { vars := #[113, 119, 182], coeff := #[1, 1, 1], bound := 1, weight := 107143, edges := #[⟨0, 1, 250⟩, ⟨0, 2, 149⟩, ⟨1, 2, 160⟩], triples := #[] }
def er185_063 : Row := { vars := #[118, 137, 201], coeff := #[1, 1, 1], bound := 1, weight := 321429, edges := #[⟨0, 1, 210⟩, ⟨0, 2, 179⟩, ⟨1, 2, 113⟩], triples := #[] }
end HardyCapset20261020.Cert


