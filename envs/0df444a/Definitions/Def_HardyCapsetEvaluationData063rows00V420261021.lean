-- Prove2me | Definitions.Def_HardyCapsetEvaluationData063rows00V420261021
-- name    : HardyCapsetEvaluationData063rows00V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:39:12.949514+00:00
-- url     : https://prove2.me/theorems/0070fa76-3774-4fa8-8e04-0e4c43869395
-- title:
--   HardyCapsetEvaluationData063rows00V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er063_000 : Row := { vars := #[5, 59], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 146⟩], triples := #[] }
def er063_001 : Row := { vars := #[7, 10], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 11⟩], triples := #[] }
def er063_002 : Row := { vars := #[9, 250], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 197⟩], triples := #[] }
def er063_003 : Row := { vars := #[18, 83], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 144⟩], triples := #[] }
def er063_004 : Row := { vars := #[34, 211], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 407⟩], triples := #[] }
def er063_005 : Row := { vars := #[38, 219], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 449⟩], triples := #[] }
def er063_006 : Row := { vars := #[41, 116], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 86⟩], triples := #[] }
def er063_007 : Row := { vars := #[42, 114], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 96⟩], triples := #[] }
def er063_008 : Row := { vars := #[50, 63], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 96⟩], triples := #[] }
def er063_009 : Row := { vars := #[52, 77], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 110⟩], triples := #[] }
def er063_010 : Row := { vars := #[52, 113], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 44⟩], triples := #[] }
def er063_011 : Row := { vars := #[53, 112], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 44⟩], triples := #[] }
def er063_012 : Row := { vars := #[70, 291], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 238⟩], triples := #[] }
def er063_013 : Row := { vars := #[71, 162], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 437⟩], triples := #[] }
def er063_014 : Row := { vars := #[88, 95], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 167⟩], triples := #[] }
def er063_015 : Row := { vars := #[93, 139], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 406⟩], triples := #[] }
def er063_016 : Row := { vars := #[97, 271], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 237⟩], triples := #[] }
def er063_017 : Row := { vars := #[127, 143], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 236⟩], triples := #[] }
def er063_018 : Row := { vars := #[132, 264], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 185⟩], triples := #[] }
def er063_019 : Row := { vars := #[137, 282], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 176⟩], triples := #[] }
def er063_020 : Row := { vars := #[144, 313], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 99⟩], triples := #[] }
def er063_021 : Row := { vars := #[145, 256], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 191⟩], triples := #[] }
def er063_022 : Row := { vars := #[190, 234], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 90⟩], triples := #[] }
def er063_023 : Row := { vars := #[192, 235], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 88⟩], triples := #[] }
def er063_024 : Row := { vars := #[198, 203], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 334⟩], triples := #[] }
def er063_025 : Row := { vars := #[290, 296], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 503⟩], triples := #[] }
def er063_026 : Row := { vars := #[294, 295], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 467⟩], triples := #[] }
def er063_027 : Row := { vars := #[12, 14, 15], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }
def er063_028 : Row := { vars := #[12, 19, 23], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }
def er063_029 : Row := { vars := #[3, 136, 31], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 353⟩, ⟨0, 2, 17⟩, ⟨1, 2, 384⟩], triples := #[] }
def er063_030 : Row := { vars := #[3, 25, 125], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 29⟩, ⟨0, 2, 373⟩, ⟨1, 2, 384⟩], triples := #[] }
def er063_031 : Row := { vars := #[4, 98, 8], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 91⟩, ⟨0, 2, 64⟩, ⟨1, 2, 131⟩], triples := #[] }
def er063_032 : Row := { vars := #[6, 105, 20], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 99⟩, ⟨0, 2, 64⟩, ⟨1, 2, 131⟩], triples := #[] }
def er063_033 : Row := { vars := #[11, 17, 245, 149], coeff := #[1, 1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 34⟩, ⟨0, 2, 232⟩, ⟨0, 3, 392⟩, ⟨1, 2, 230⟩, ⟨1, 3, 390⟩, ⟨2, 3, 20⟩], triples := #[] }
def er063_034 : Row := { vars := #[16, 270, 57], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 308⟩, ⟨0, 2, 184⟩, ⟨1, 2, 278⟩], triples := #[] }
def er063_035 : Row := { vars := #[21, 130, 247], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 396⟩, ⟨0, 2, 233⟩, ⟨1, 2, 44⟩], triples := #[] }
def er063_036 : Row := { vars := #[32, 156, 314], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 399⟩, ⟨0, 2, 285⟩, ⟨1, 2, 127⟩], triples := #[] }
def er063_037 : Row := { vars := #[33, 56, 79], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 174⟩, ⟨0, 2, 185⟩, ⟨1, 2, 114⟩], triples := #[] }
def er063_038 : Row := { vars := #[39, 220, 251], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 455⟩, ⟨0, 2, 239⟩, ⟨1, 2, 127⟩], triples := #[] }
def er063_039 : Row := { vars := #[40, 44, 247, 151], coeff := #[1, 1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 174⟩, ⟨0, 2, 223⟩, ⟨0, 3, 383⟩, ⟨1, 2, 339⟩, ⟨1, 3, 499⟩, ⟨2, 3, 30⟩], triples := #[] }
def er063_040 : Row := { vars := #[58, 133, 252], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 464⟩, ⟨0, 2, 313⟩, ⟨1, 2, 16⟩], triples := #[] }
def er063_041 : Row := { vars := #[64, 154, 236], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 473⟩, ⟨0, 2, 307⟩, ⟨1, 2, 16⟩], triples := #[] }
def er063_042 : Row := { vars := #[69, 78, 84], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 89⟩, ⟨0, 2, 62⟩, ⟨1, 2, 26⟩], triples := #[] }
def er063_043 : Row := { vars := #[73, 82, 85], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 101⟩, ⟨0, 2, 54⟩, ⟨1, 2, 18⟩], triples := #[] }
def er063_044 : Row := { vars := #[75, 196, 195], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 392⟩, ⟨0, 2, 393⟩, ⟨1, 2, 304⟩], triples := #[] }
def er063_045 : Row := { vars := #[92, 146, 242, 99], coeff := #[1, 1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 457⟩, ⟨0, 2, 297⟩, ⟨0, 3, 156⟩, ⟨1, 2, 2⟩, ⟨1, 3, 453⟩, ⟨2, 3, 293⟩], triples := #[] }
def er063_046 : Row := { vars := #[96, 147, 243, 108], coeff := #[1, 1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 457⟩, ⟨0, 2, 297⟩, ⟨0, 3, 143⟩, ⟨1, 2, 5⟩, ⟨1, 3, 443⟩, ⟨2, 3, 283⟩], triples := #[] }
def er063_047 : Row := { vars := #[101, 225, 120], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 244⟩, ⟨0, 2, 188⟩, ⟨1, 2, 278⟩], triples := #[] }
def er063_048 : Row := { vars := #[102, 118, 37], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 189⟩, ⟨0, 2, 118⟩, ⟨1, 2, 100⟩], triples := #[] }
def er063_049 : Row := { vars := #[103, 259, 158], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 223⟩, ⟨0, 2, 431⟩, ⟨1, 2, 178⟩], triples := #[] }
def er063_050 : Row := { vars := #[123, 43, 263], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 27⟩, ⟨0, 2, 213⟩, ⟨1, 2, 277⟩], triples := #[] }
def er063_051 : Row := { vars := #[124, 168, 62], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 353⟩, ⟨0, 2, 27⟩, ⟨1, 2, 437⟩], triples := #[] }
def er063_052 : Row := { vars := #[129, 165, 265], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 343⟩, ⟨0, 2, 187⟩, ⟨1, 2, 118⟩], triples := #[] }
def er063_053 : Row := { vars := #[131, 239, 286], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 62⟩, ⟨0, 2, 98⟩, ⟨1, 2, 437⟩], triples := #[] }
def er063_054 : Row := { vars := #[150, 216, 315], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 248⟩, ⟨0, 2, 99⟩, ⟨1, 2, 184⟩], triples := #[] }
def er063_055 : Row := { vars := #[153, 161, 251], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 326⟩, ⟨0, 2, 40⟩, ⟨1, 2, 178⟩], triples := #[] }
def er063_056 : Row := { vars := #[155, 121, 251], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 438⟩, ⟨0, 2, 50⟩, ⟨1, 2, 278⟩], triples := #[] }
def er063_057 : Row := { vars := #[156, 257, 249], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 172⟩, ⟨0, 2, 68⟩, ⟨1, 2, 486⟩], triples := #[] }
def er063_058 : Row := { vars := #[160, 260, 276], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 129⟩, ⟨0, 2, 116⟩, ⟨1, 2, 404⟩], triples := #[] }
def er063_059 : Row := { vars := #[160, 312, 241], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 27⟩, ⟨0, 2, 191⟩, ⟨1, 2, 406⟩], triples := #[] }
def er063_060 : Row := { vars := #[164, 258, 180], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 127⟩, ⟨0, 2, 244⟩, ⟨1, 2, 114⟩], triples := #[] }
def er063_061 : Row := { vars := #[166, 216, 278], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 199⟩, ⟨0, 2, 99⟩, ⟨1, 2, 64⟩], triples := #[] }
def er063_062 : Row := { vars := #[187, 200, 254], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 210⟩, ⟨0, 2, 191⟩, ⟨1, 2, 92⟩], triples := #[] }
def er063_063 : Row := { vars := #[205, 261, 288], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 29⟩, ⟨0, 2, 189⟩, ⟨1, 2, 397⟩], triples := #[] }
end HardyCapset20261020.Cert


