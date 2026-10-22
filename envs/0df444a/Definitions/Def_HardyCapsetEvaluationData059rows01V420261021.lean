-- Prove2me | Definitions.Def_HardyCapsetEvaluationData059rows01V420261021
-- name    : HardyCapsetEvaluationData059rows01V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:35:27.826956+00:00
-- url     : https://prove2.me/theorems/08b7d256-7312-441e-bcde-18db9c141f88
-- title:
--   HardyCapsetEvaluationData059rows01V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er059_064 : Row := { vars := #[99, 107, 115], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 212⟩, ⟨0, 2, 200⟩, ⟨1, 2, 192⟩], triples := #[] }
def er059_065 : Row := { vars := #[100, 108, 116], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 213⟩, ⟨0, 2, 201⟩, ⟨1, 2, 193⟩], triples := #[] }
def er059_066 : Row := { vars := #[102, 125, 130], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 237⟩, ⟨0, 2, 233⟩, ⟨1, 2, 219⟩], triples := #[] }
def er059_067 : Row := { vars := #[109, 117, 295], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 198⟩, ⟨0, 2, 116⟩, ⟨1, 2, 112⟩], triples := #[] }
def er059_068 : Row := { vars := #[126, 290, 284], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 89⟩, ⟨0, 2, 99⟩, ⟨1, 2, 471⟩], triples := #[] }
def er059_069 : Row := { vars := #[135, 263, 300], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 111⟩, ⟨0, 2, 1⟩, ⟨1, 2, 397⟩], triples := #[] }
def er059_070 : Row := { vars := #[144, 150, 274], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 257⟩, ⟨0, 2, 63⟩, ⟨1, 2, 53⟩], triples := #[] }
def er059_071 : Row := { vars := #[155, 215, 223], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 176⟩, ⟨0, 2, 172⟩, ⟨1, 2, 359⟩], triples := #[] }
def er059_072 : Row := { vars := #[156, 161, 166], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 289⟩, ⟨0, 2, 280⟩, ⟨1, 2, 278⟩], triples := #[] }
def er059_073 : Row := { vars := #[160, 193, 240], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 237⟩, ⟨0, 2, 109⟩, ⟨1, 2, 9⟩], triples := #[] }
def er059_074 : Row := { vars := #[169, 249, 255], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 63⟩, ⟨0, 2, 53⟩, ⟨1, 2, 417⟩], triples := #[] }
def er059_075 : Row := { vars := #[170, 229, 209], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 122⟩, ⟨0, 2, 72⟩, ⟨1, 2, 397⟩], triples := #[] }
def er059_076 : Row := { vars := #[179, 185, 231], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 311⟩, ⟨0, 2, 99⟩, ⟨1, 2, 89⟩], triples := #[] }
def er059_077 : Row := { vars := #[266, 271, 261], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 438⟩, ⟨0, 2, 449⟩, ⟨1, 2, 440⟩], triples := #[] }
def er059_078 : Row := { vars := #[301, 306, 296], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 492⟩, ⟨0, 2, 503⟩, ⟨1, 2, 494⟩], triples := #[] }
def er059_079 : Row := { vars := #[3], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_080 : Row := { vars := #[4], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_081 : Row := { vars := #[10], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_082 : Row := { vars := #[13], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_083 : Row := { vars := #[14], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_084 : Row := { vars := #[15], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_085 : Row := { vars := #[16], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_086 : Row := { vars := #[19], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_087 : Row := { vars := #[20], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_088 : Row := { vars := #[23], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_089 : Row := { vars := #[25], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_090 : Row := { vars := #[30], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_091 : Row := { vars := #[34], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_092 : Row := { vars := #[40], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_093 : Row := { vars := #[44], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_094 : Row := { vars := #[47], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_095 : Row := { vars := #[49], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_096 : Row := { vars := #[50], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_097 : Row := { vars := #[53], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_098 : Row := { vars := #[65], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_099 : Row := { vars := #[66], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_100 : Row := { vars := #[69], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_101 : Row := { vars := #[70], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_102 : Row := { vars := #[75], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_103 : Row := { vars := #[77], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_104 : Row := { vars := #[78], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_105 : Row := { vars := #[81], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_106 : Row := { vars := #[84], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_107 : Row := { vars := #[85], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_108 : Row := { vars := #[88], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_109 : Row := { vars := #[93], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_110 : Row := { vars := #[94], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_111 : Row := { vars := #[98], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_112 : Row := { vars := #[105], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_113 : Row := { vars := #[112], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_114 : Row := { vars := #[113], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_115 : Row := { vars := #[114], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_116 : Row := { vars := #[119], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_117 : Row := { vars := #[120], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_118 : Row := { vars := #[122], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_119 : Row := { vars := #[131], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_120 : Row := { vars := #[132], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_121 : Row := { vars := #[133], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_122 : Row := { vars := #[136], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_123 : Row := { vars := #[143], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_124 : Row := { vars := #[146], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_125 : Row := { vars := #[148], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_126 : Row := { vars := #[149], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er059_127 : Row := { vars := #[151], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
end HardyCapset20261020.Cert


