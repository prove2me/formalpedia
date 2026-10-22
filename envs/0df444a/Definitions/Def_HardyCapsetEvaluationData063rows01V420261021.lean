-- Prove2me | Definitions.Def_HardyCapsetEvaluationData063rows01V420261021
-- name    : HardyCapsetEvaluationData063rows01V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:39:19.545417+00:00
-- url     : https://prove2.me/theorems/1832a4a1-7e40-472c-ac5d-e94ecebced6b
-- title:
--   HardyCapsetEvaluationData063rows01V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er063_064 : Row := { vars := #[221, 261, 169], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 493⟩, ⟨0, 2, 189⟩, ⟨1, 2, 118⟩], triples := #[] }
def er063_065 : Row := { vars := #[223, 175, 261], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 187⟩, ⟨0, 2, 492⟩, ⟨1, 2, 112⟩], triples := #[] }
def er063_066 : Row := { vars := #[1, 138, 231, 140], coeff := #[1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨0, 3, 365⟩, ⟨1, 3, 222⟩], triples := #[⟨0, 1, 2⟩] }
def er063_067 : Row := { vars := #[1, 142, 227, 229], coeff := #[1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨0, 3, 217⟩, ⟨2, 3, 370⟩], triples := #[⟨0, 1, 2⟩] }
def er063_068 : Row := { vars := #[1, 217, 275, 218], coeff := #[1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨0, 3, 431⟩, ⟨1, 3, 340⟩], triples := #[⟨0, 1, 2⟩] }
def er063_069 : Row := { vars := #[12, 135, 255, 2], coeff := #[1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨0, 3, 44⟩, ⟨1, 3, 382⟩], triples := #[⟨0, 1, 2⟩] }
def er063_070 : Row := { vars := #[24, 55, 110, 27], coeff := #[1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨0, 3, 46⟩, ⟨2, 3, 77⟩], triples := #[⟨0, 1, 2⟩] }
def er063_071 : Row := { vars := #[26, 68, 87, 110, 111], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨3, 4, 169⟩, ⟨0, 3, 73⟩, ⟨2, 3, 181⟩, ⟨0, 4, 72⟩, ⟨1, 4, 0⟩], triples := #[⟨0, 1, 2⟩] }
def er063_072 : Row := { vars := #[45, 47, 49, 46], coeff := #[1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨1, 3, 77⟩, ⟨2, 3, 74⟩], triples := #[⟨0, 1, 2⟩] }
def er063_073 : Row := { vars := #[45, 183, 272, 75, 182], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨3, 4, 457⟩, ⟨0, 3, 109⟩, ⟨1, 3, 453⟩, ⟨0, 4, 434⟩, ⟨1, 4, 285⟩], triples := #[⟨0, 1, 2⟩] }
def er063_074 : Row := { vars := #[45, 188, 266, 186, 75], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨3, 4, 447⟩, ⟨0, 3, 424⟩, ⟨1, 3, 295⟩, ⟨0, 4, 109⟩, ⟨1, 4, 443⟩], triples := #[⟨0, 1, 2⟩] }
def er063_075 : Row := { vars := #[45, 199, 230, 0, 228], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨3, 4, 220⟩, ⟨0, 3, 132⟩, ⟨2, 3, 216⟩, ⟨0, 4, 307⟩, ⟨2, 4, 371⟩], triples := #[⟨0, 1, 2⟩] }
def er063_076 : Row := { vars := #[87, 89, 91, 86], coeff := #[1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨1, 3, 137⟩, ⟨2, 3, 134⟩], triples := #[⟨0, 1, 2⟩] }
def er063_077 : Row := { vars := #[87, 100, 109, 76], coeff := #[1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨1, 3, 32⟩, ⟨2, 3, 22⟩], triples := #[⟨0, 1, 2⟩] }
def er063_078 : Row := { vars := #[110, 209, 307, 310], coeff := #[1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨0, 3, 313⟩, ⟨2, 3, 489⟩], triples := #[⟨0, 1, 2⟩] }
def er063_079 : Row := { vars := #[110, 215, 301, 303], coeff := #[1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨0, 3, 323⟩, ⟨2, 3, 479⟩], triples := #[⟨0, 1, 2⟩] }
def er063_080 : Row := { vars := #[13], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_081 : Row := { vars := #[22], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_082 : Row := { vars := #[28], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_083 : Row := { vars := #[29], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_084 : Row := { vars := #[30], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_085 : Row := { vars := #[35], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_086 : Row := { vars := #[36], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_087 : Row := { vars := #[48], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_088 : Row := { vars := #[51], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_089 : Row := { vars := #[54], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_090 : Row := { vars := #[60], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_091 : Row := { vars := #[61], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_092 : Row := { vars := #[65], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_093 : Row := { vars := #[66], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_094 : Row := { vars := #[67], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_095 : Row := { vars := #[72], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_096 : Row := { vars := #[74], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_097 : Row := { vars := #[80], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_098 : Row := { vars := #[81], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_099 : Row := { vars := #[90], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_100 : Row := { vars := #[94], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_101 : Row := { vars := #[104], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_102 : Row := { vars := #[106], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_103 : Row := { vars := #[107], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_104 : Row := { vars := #[115], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_105 : Row := { vars := #[117], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_106 : Row := { vars := #[119], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_107 : Row := { vars := #[122], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_108 : Row := { vars := #[126], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_109 : Row := { vars := #[128], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_110 : Row := { vars := #[134], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_111 : Row := { vars := #[141], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_112 : Row := { vars := #[148], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_113 : Row := { vars := #[152], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_114 : Row := { vars := #[157], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_115 : Row := { vars := #[159], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_116 : Row := { vars := #[163], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_117 : Row := { vars := #[167], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_118 : Row := { vars := #[170], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_119 : Row := { vars := #[171], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_120 : Row := { vars := #[172], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_121 : Row := { vars := #[173], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_122 : Row := { vars := #[174], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_123 : Row := { vars := #[176], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_124 : Row := { vars := #[177], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_125 : Row := { vars := #[178], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_126 : Row := { vars := #[179], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er063_127 : Row := { vars := #[181], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
end HardyCapset20261020.Cert


