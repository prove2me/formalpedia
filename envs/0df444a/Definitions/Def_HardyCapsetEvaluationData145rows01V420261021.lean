-- Prove2me | Definitions.Def_HardyCapsetEvaluationData145rows01V420261021
-- name    : HardyCapsetEvaluationData145rows01V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:53:57.50646+00:00
-- url     : https://prove2.me/theorems/b5553081-0061-4c07-afd3-5bbf0f8d1515
-- title:
--   HardyCapsetEvaluationData145rows01V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er145_064 : Row := { vars := #[47, 86, 171], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 138⟩, ⟨0, 2, 458⟩, ⟨1, 2, 433⟩], triples := #[] }
def er145_065 : Row := { vars := #[49, 71, 70], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 177⟩, ⟨0, 2, 168⟩, ⟨1, 2, 72⟩], triples := #[] }
def er145_066 : Row := { vars := #[50, 106, 95], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 110⟩, ⟨0, 2, 189⟩, ⟨1, 2, 8⟩], triples := #[] }
def er145_067 : Row := { vars := #[53, 104, 85], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 110⟩, ⟨0, 2, 140⟩, ⟨1, 2, 54⟩], triples := #[] }
def er145_068 : Row := { vars := #[65, 134, 282], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 464⟩, ⟨0, 2, 254⟩, ⟨1, 2, 170⟩], triples := #[] }
def er145_069 : Row := { vars := #[80, 210, 293, 214], coeff := #[1, 1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 359⟩, ⟨0, 2, 224⟩, ⟨0, 3, 375⟩, ⟨1, 2, 147⟩, ⟨1, 3, 350⟩, ⟨2, 3, 167⟩], triples := #[] }
def er145_070 : Row := { vars := #[81, 100, 167], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 42⟩, ⟨0, 2, 416⟩, ⟨1, 2, 394⟩], triples := #[] }
def er145_071 : Row := { vars := #[83, 208, 247], coeff := #[1, 1, 1], bound := 1, weight := 2, edges := #[⟨0, 1, 358⟩, ⟨0, 2, 320⟩, ⟨1, 2, 88⟩], triples := #[] }
def er145_072 : Row := { vars := #[83, 211, 245], coeff := #[1, 1, 1], bound := 1, weight := 2, edges := #[⟨0, 1, 374⟩, ⟨0, 2, 326⟩, ⟨1, 2, 88⟩], triples := #[] }
def er145_073 : Row := { vars := #[93, 122, 139], coeff := #[1, 1, 1], bound := 1, weight := 3, edges := #[⟨0, 1, 54⟩, ⟨0, 2, 469⟩, ⟨1, 2, 414⟩], triples := #[] }
def er145_074 : Row := { vars := #[93, 122, 235], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 54⟩, ⟨0, 2, 309⟩, ⟨1, 2, 254⟩], triples := #[] }
def er145_075 : Row := { vars := #[126, 177, 305], coeff := #[1, 1, 1], bound := 1, weight := 3, edges := #[⟨0, 1, 308⟩, ⟨0, 2, 108⟩, ⟨1, 2, 36⟩], triples := #[] }
def er145_076 : Row := { vars := #[127, 194, 263], coeff := #[1, 1, 1], bound := 1, weight := 2, edges := #[⟨0, 1, 279⟩, ⟨0, 2, 181⟩, ⟨1, 2, 3⟩], triples := #[] }
def er145_077 : Row := { vars := #[145, 260, 175], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 171⟩, ⟨0, 2, 298⟩, ⟨1, 2, 80⟩], triples := #[] }
def er145_078 : Row := { vars := #[157, 193, 305], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 243⟩, ⟨0, 2, 26⟩, ⟨1, 2, 133⟩], triples := #[] }
def er145_079 : Row := { vars := #[161, 193, 303], coeff := #[1, 1, 1], bound := 1, weight := 3, edges := #[⟨0, 1, 239⟩, ⟨0, 2, 18⟩, ⟨1, 2, 141⟩], triples := #[] }
def er145_080 : Row := { vars := #[164, 271, 241], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 80⟩, ⟨0, 2, 171⟩, ⟨1, 2, 458⟩], triples := #[] }
def er145_081 : Row := { vars := #[165, 291, 274], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 8⟩, ⟨0, 2, 83⟩, ⟨1, 2, 359⟩], triples := #[] }
def er145_082 : Row := { vars := #[166, 230, 221], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 189⟩, ⟨0, 2, 180⟩, ⟨1, 2, 383⟩], triples := #[] }
def er145_083 : Row := { vars := #[173, 226, 290], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 181⟩, ⟨0, 2, 21⟩, ⟨1, 2, 449⟩], triples := #[] }
def er145_084 : Row := { vars := #[177, 303, 306, 310], coeff := #[1, 1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 44⟩, ⟨0, 2, 42⟩, ⟨0, 3, 67⟩, ⟨1, 2, 493⟩, ⟨1, 3, 503⟩, ⟨2, 3, 510⟩], triples := #[] }
def er145_085 : Row := { vars := #[178, 261, 195], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 83⟩, ⟨0, 2, 199⟩, ⟨1, 2, 8⟩], triples := #[] }
def er145_086 : Row := { vars := #[196, 304, 204, 307], coeff := #[1, 1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 139⟩, ⟨0, 2, 315⟩, ⟨0, 3, 164⟩, ⟨1, 2, 154⟩, ⟨1, 3, 506⟩, ⟨2, 3, 136⟩], triples := #[] }
def er145_087 : Row := { vars := #[208, 211, 209, 220], coeff := #[1, 1, 1, 1], bound := 1, weight := 2, edges := #[⟨0, 1, 346⟩, ⟨0, 2, 333⟩, ⟨0, 3, 334⟩, ⟨1, 2, 343⟩, ⟨1, 3, 332⟩, ⟨2, 3, 339⟩], triples := #[] }
def er145_088 : Row := { vars := #[210, 214, 290, 302], coeff := #[1, 1, 1, 1], bound := 1, weight := 3, edges := #[⟨0, 1, 350⟩, ⟨0, 2, 139⟩, ⟨0, 3, 157⟩, ⟨1, 2, 164⟩, ⟨1, 3, 144⟩, ⟨2, 3, 475⟩], triples := #[] }
def er145_089 : Row := { vars := #[222, 273, 207], coeff := #[1, 1, 1], bound := 1, weight := 4, edges := #[⟨0, 1, 468⟩, ⟨0, 2, 110⟩, ⟨1, 2, 44⟩], triples := #[] }
def er145_090 : Row := { vars := #[253, 289, 209], coeff := #[1, 1, 1], bound := 1, weight := 2, edges := #[⟨0, 1, 403⟩, ⟨0, 2, 26⟩, ⟨1, 2, 133⟩], triples := #[] }
def er145_091 : Row := { vars := #[260, 268, 306, 310], coeff := #[1, 1, 1, 1], bound := 1, weight := 3, edges := #[⟨0, 1, 421⟩, ⟨0, 2, 358⟩, ⟨0, 3, 374⟩, ⟨1, 2, 362⟩, ⟨1, 3, 354⟩, ⟨2, 3, 510⟩], triples := #[] }
def er145_092 : Row := { vars := #[1, 129, 228, 223], coeff := #[1, 1, 1, 1], bound := 2, weight := 4, edges := #[⟨0, 3, 201⟩, ⟨2, 3, 372⟩], triples := #[⟨0, 1, 2⟩] }
def er145_093 : Row := { vars := #[1, 138, 235, 226], coeff := #[1, 1, 1, 1], bound := 2, weight := 3, edges := #[⟨0, 3, 193⟩, ⟨2, 3, 356⟩], triples := #[⟨0, 1, 2⟩] }
def er145_094 : Row := { vars := #[5, 98, 107, 112], coeff := #[1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨1, 3, 30⟩, ⟨2, 3, 146⟩], triples := #[⟨0, 1, 2⟩] }
def er145_095 : Row := { vars := #[7, 23, 26, 10], coeff := #[1, 1, 1, 1], bound := 2, weight := 4, edges := #[⟨1, 3, 33⟩, ⟨2, 3, 21⟩], triples := #[⟨0, 1, 2⟩] }
def er145_096 : Row := { vars := #[12, 75, 121, 0], coeff := #[1, 1, 1, 1], bound := 2, weight := 4, edges := #[⟨1, 3, 146⟩, ⟨2, 3, 112⟩], triples := #[⟨0, 1, 2⟩] }
def er145_097 : Row := { vars := #[30, 59, 121, 13], coeff := #[1, 1, 1, 1], bound := 2, weight := 4, edges := #[⟨0, 3, 5⟩, ⟨2, 3, 88⟩], triples := #[⟨0, 1, 2⟩] }
def er145_098 : Row := { vars := #[34, 69, 117, 2, 79], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 4, edges := #[⟨3, 4, 164⟩, ⟨1, 3, 136⟩, ⟨2, 3, 130⟩, ⟨1, 4, 87⟩, ⟨2, 4, 67⟩], triples := #[⟨0, 1, 2⟩] }
def er145_099 : Row := { vars := #[98, 127, 294, 26], coeff := #[1, 1, 1, 1], bound := 2, weight := 2, edges := #[⟨0, 3, 160⟩, ⟨2, 3, 256⟩], triples := #[⟨0, 1, 2⟩] }
def er145_100 : Row := { vars := #[110, 117, 124, 263, 269], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 2, edges := #[⟨3, 4, 424⟩, ⟨0, 3, 239⟩, ⟨2, 3, 207⟩, ⟨0, 4, 242⟩, ⟨2, 4, 219⟩], triples := #[⟨0, 1, 2⟩] }
def er145_101 : Row := { vars := #[117, 128, 278, 2, 133], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 4, edges := #[⟨3, 4, 358⟩, ⟨0, 3, 130⟩, ⟨1, 3, 362⟩, ⟨0, 4, 439⟩, ⟨1, 4, 215⟩], triples := #[⟨0, 1, 2⟩] }
def er145_102 : Row := { vars := #[117, 131, 275, 2, 140], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 4, edges := #[⟨3, 4, 374⟩, ⟨0, 3, 130⟩, ⟨1, 3, 354⟩, ⟨0, 4, 449⟩, ⟨1, 4, 199⟩], triples := #[⟨0, 1, 2⟩] }
def er145_103 : Row := { vars := #[117, 179, 227, 51, 183], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 4, edges := #[⟨3, 4, 493⟩, ⟨0, 3, 101⟩, ⟨1, 3, 494⟩, ⟨0, 4, 359⟩, ⟨1, 4, 289⟩], triples := #[⟨0, 1, 2⟩] }
def er145_104 : Row := { vars := #[9], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_105 : Row := { vars := #[11], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_106 : Row := { vars := #[15], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_107 : Row := { vars := #[19], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_108 : Row := { vars := #[22], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_109 : Row := { vars := #[28], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_110 : Row := { vars := #[33], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_111 : Row := { vars := #[35], coeff := #[1], bound := 1, weight := 2, edges := #[], triples := #[] }
def er145_112 : Row := { vars := #[40], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_113 : Row := { vars := #[43], coeff := #[1], bound := 1, weight := 3, edges := #[], triples := #[] }
def er145_114 : Row := { vars := #[44], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_115 : Row := { vars := #[58], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_116 : Row := { vars := #[61], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_117 : Row := { vars := #[62], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_118 : Row := { vars := #[63], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_119 : Row := { vars := #[64], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_120 : Row := { vars := #[74], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_121 : Row := { vars := #[77], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_122 : Row := { vars := #[78], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_123 : Row := { vars := #[87], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_124 : Row := { vars := #[90], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_125 : Row := { vars := #[92], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
def er145_126 : Row := { vars := #[94], coeff := #[1], bound := 1, weight := 3, edges := #[], triples := #[] }
def er145_127 : Row := { vars := #[96], coeff := #[1], bound := 1, weight := 4, edges := #[], triples := #[] }
end HardyCapset20261020.Cert


