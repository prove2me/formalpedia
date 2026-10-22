-- Prove2me | Definitions.Def_HardyCapsetEvaluationData059rows00V420261021
-- name    : HardyCapsetEvaluationData059rows00V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:35:15.14218+00:00
-- url     : https://prove2.me/theorems/b3e1c710-71ba-4595-a1ff-2b2a9d3611ba
-- title:
--   HardyCapsetEvaluationData059rows00V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er059_000 : Row := { vars := #[5, 140], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 483⟩], triples := #[] }
def er059_001 : Row := { vars := #[6, 175], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 430⟩], triples := #[] }
def er059_002 : Row := { vars := #[9, 142], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 487⟩], triples := #[] }
def er059_003 : Row := { vars := #[24, 282], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 247⟩], triples := #[] }
def er059_004 : Row := { vars := #[26, 103], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 384⟩], triples := #[] }
def er059_005 : Row := { vars := #[27, 245], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 301⟩], triples := #[] }
def er059_006 : Row := { vars := #[29, 206], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 225⟩], triples := #[] }
def er059_007 : Row := { vars := #[32, 56], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 171⟩], triples := #[] }
def er059_008 : Row := { vars := #[38, 138], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 464⟩], triples := #[] }
def er059_009 : Row := { vars := #[45, 247], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 276⟩], triples := #[] }
def er059_010 : Row := { vars := #[46, 192], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 385⟩], triples := #[] }
def er059_011 : Row := { vars := #[55, 307], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 224⟩], triples := #[] }
def er059_012 : Row := { vars := #[57, 101], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 463⟩], triples := #[] }
def er059_013 : Row := { vars := #[60, 208], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 304⟩], triples := #[] }
def er059_014 : Row := { vars := #[62, 302], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 225⟩], triples := #[] }
def er059_015 : Row := { vars := #[68, 262], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 276⟩], triples := #[] }
def er059_016 : Row := { vars := #[92, 128], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 407⟩], triples := #[] }
def er059_017 : Row := { vars := #[97, 104], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 430⟩], triples := #[] }
def er059_018 : Row := { vars := #[106, 177], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 293⟩], triples := #[] }
def er059_019 : Row := { vars := #[110, 272], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 171⟩], triples := #[] }
def er059_020 : Row := { vars := #[111, 129], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 231⟩], triples := #[] }
def er059_021 : Row := { vars := #[118, 267], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 171⟩], triples := #[] }
def er059_022 : Row := { vars := #[121, 230], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 60⟩], triples := #[] }
def er059_023 : Row := { vars := #[127, 299], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 120⟩], triples := #[] }
def er059_024 : Row := { vars := #[137, 280], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 52⟩], triples := #[] }
def er059_025 : Row := { vars := #[139, 145], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 269⟩], triples := #[] }
def er059_026 : Row := { vars := #[141, 153], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 266⟩], triples := #[] }
def er059_027 : Row := { vars := #[147, 222], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 180⟩], triples := #[] }
def er059_028 : Row := { vars := #[157, 162], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 292⟩], triples := #[] }
def er059_029 : Row := { vars := #[159, 164], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 296⟩], triples := #[] }
def er059_030 : Row := { vars := #[172, 214], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 72⟩], triples := #[] }
def er059_031 : Row := { vars := #[173, 281], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 169⟩], triples := #[] }
def er059_032 : Row := { vars := #[174, 181], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 324⟩], triples := #[] }
def er059_033 : Row := { vars := #[176, 278], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 169⟩], triples := #[] }
def er059_034 : Row := { vars := #[194, 232], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 120⟩], triples := #[] }
def er059_035 : Row := { vars := #[217, 233], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 391⟩], triples := #[] }
def er059_036 : Row := { vars := #[234, 273], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 499⟩], triples := #[] }
def er059_037 : Row := { vars := #[244, 250], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 429⟩], triples := #[] }
def er059_038 : Row := { vars := #[246, 252], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 433⟩], triples := #[] }
def er059_039 : Row := { vars := #[264, 269], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 456⟩], triples := #[] }
def er059_040 : Row := { vars := #[279, 286], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 484⟩], triples := #[] }
def er059_041 : Row := { vars := #[297, 303], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 507⟩], triples := #[] }
def er059_042 : Row := { vars := #[0, 1, 2], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }
def er059_043 : Row := { vars := #[0, 123, 228], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }
def er059_044 : Row := { vars := #[7, 17, 96], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 5⟩, ⟨0, 2, 99⟩, ⟨1, 2, 89⟩], triples := #[] }
def er059_045 : Row := { vars := #[8, 18, 74], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 6⟩, ⟨0, 2, 129⟩, ⟨1, 2, 125⟩], triples := #[] }
def er059_046 : Row := { vars := #[11, 21, 43], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 13⟩, ⟨0, 2, 189⟩, ⟨1, 2, 185⟩], triples := #[] }
def er059_047 : Row := { vars := #[12, 22, 67], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 14⟩, ⟨0, 2, 159⟩, ⟨1, 2, 149⟩], triples := #[] }
def er059_048 : Row := { vars := #[28, 52, 59], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 176⟩, ⟨0, 2, 172⟩, ⟨1, 2, 79⟩], triples := #[] }
def er059_049 : Row := { vars := #[31, 124, 207], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 379⟩, ⟨0, 2, 232⟩, ⟨1, 2, 43⟩], triples := #[] }
def er059_050 : Row := { vars := #[33, 39, 190], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 39⟩, ⟨0, 2, 456⟩, ⟨1, 2, 448⟩], triples := #[] }
def er059_051 : Row := { vars := #[35, 41, 260], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 46⟩, ⟨0, 2, 347⟩, ⟨1, 2, 338⟩], triples := #[] }
def er059_052 : Row := { vars := #[36, 42, 134], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 47⟩, ⟨0, 2, 484⟩, ⟨1, 2, 476⟩], triples := #[] }
def er059_053 : Row := { vars := #[37, 298, 158], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 281⟩, ⟨0, 2, 495⟩, ⟨1, 2, 43⟩], triples := #[] }
def er059_054 : Row := { vars := #[48, 54, 61], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 106⟩, ⟨0, 2, 96⟩, ⟨1, 2, 83⟩], triples := #[] }
def er059_055 : Row := { vars := #[51, 58, 243], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 75⟩, ⟨0, 2, 296⟩, ⟨1, 2, 288⟩], triples := #[] }
def er059_056 : Row := { vars := #[63, 83, 90], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 62⟩, ⟨0, 2, 52⟩, ⟨1, 2, 147⟩], triples := #[] }
def er059_057 : Row := { vars := #[64, 80, 87], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 62⟩, ⟨0, 2, 52⟩, ⟨1, 2, 139⟩], triples := #[] }
def er059_058 : Row := { vars := #[71, 196, 201], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 488⟩, ⟨0, 2, 480⟩, ⟨1, 2, 332⟩], triples := #[] }
def er059_059 : Row := { vars := #[72, 195, 265], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 469⟩, ⟨0, 2, 224⟩, ⟨1, 2, 51⟩], triples := #[] }
def er059_060 : Row := { vars := #[73, 79, 86], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 163⟩, ⟨0, 2, 153⟩, ⟨1, 2, 135⟩], triples := #[] }
def er059_061 : Row := { vars := #[76, 82, 89], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 166⟩, ⟨0, 2, 156⟩, ⟨1, 2, 143⟩], triples := #[] }
def er059_062 : Row := { vars := #[91, 212, 220], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 296⟩, ⟨0, 2, 288⟩, ⟨1, 2, 352⟩], triples := #[] }
def er059_063 : Row := { vars := #[95, 213, 221], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 273⟩, ⟨0, 2, 266⟩, ⟨1, 2, 353⟩], triples := #[] }
end HardyCapset20261020.Cert


