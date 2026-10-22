-- Prove2me | Definitions.Def_HardyCapsetEvaluationData184rows01V420261021
-- name    : HardyCapsetEvaluationData184rows01V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T03:34:14.533886+00:00
-- url     : https://prove2.me/theorems/74f5d808-a72a-4494-b855-9dfda9157848
-- title:
--   HardyCapsetEvaluationData184rows01V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er184_064 : Row := { vars := #[241, 274], coeff := #[1, 1], bound := 1, weight := 57654, edges := #[⟨0, 1, 91⟩], triples := #[] }
def er184_065 : Row := { vars := #[247, 377], coeff := #[1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 428⟩], triples := #[] }
def er184_066 : Row := { vars := #[252, 320], coeff := #[1, 1], bound := 1, weight := 763266, edges := #[⟨0, 1, 498⟩], triples := #[] }
def er184_067 : Row := { vars := #[261, 269], coeff := #[1, 1], bound := 1, weight := 473470, edges := #[⟨0, 1, 353⟩], triples := #[] }
def er184_068 : Row := { vars := #[261, 309], coeff := #[1, 1], bound := 1, weight := 58674, edges := #[⟨0, 1, 511⟩], triples := #[] }
def er184_069 : Row := { vars := #[265, 320], coeff := #[1, 1], bound := 1, weight := 236735, edges := #[⟨0, 1, 504⟩], triples := #[] }
def er184_070 : Row := { vars := #[321, 378], coeff := #[1, 1], bound := 1, weight := 204082, edges := #[⟨0, 1, 353⟩], triples := #[] }
def er184_071 : Row := { vars := #[349, 362], coeff := #[1, 1], bound := 1, weight := 78062, edges := #[⟨0, 1, 500⟩], triples := #[] }
def er184_072 : Row := { vars := #[0, 131, 99], coeff := #[1, 1, 1], bound := 1, weight := 65307, edges := #[⟨0, 1, 401⟩, ⟨0, 2, 111⟩, ⟨1, 2, 409⟩], triples := #[] }
def er184_073 : Row := { vars := #[0, 5, 98], coeff := #[1, 1, 1], bound := 1, weight := 472449, edges := #[⟨0, 1, 71⟩, ⟨0, 2, 110⟩, ⟨1, 2, 90⟩], triples := #[] }
def er184_074 : Row := { vars := #[0, 213, 20], coeff := #[1, 1, 1], bound := 1, weight := 129082, edges := #[⟨0, 1, 449⟩, ⟨0, 2, 44⟩, ⟨1, 2, 422⟩], triples := #[] }
def er184_075 : Row := { vars := #[1, 58, 19], coeff := #[1, 1, 1], bound := 1, weight := 558674, edges := #[⟨0, 1, 137⟩, ⟨0, 2, 37⟩, ⟨1, 2, 189⟩], triples := #[] }
def er184_076 : Row := { vars := #[2, 33, 52], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 9⟩, ⟨0, 2, 142⟩, ⟨1, 2, 175⟩], triples := #[] }
def er184_077 : Row := { vars := #[2, 54, 202], coeff := #[1, 1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 140⟩, ⟨0, 2, 406⟩, ⟨1, 2, 366⟩], triples := #[] }
def er184_078 : Row := { vars := #[2, 185, 93], coeff := #[1, 1, 1], bound := 1, weight := 306123, edges := #[⟨0, 1, 470⟩, ⟨0, 2, 123⟩, ⟨1, 2, 366⟩], triples := #[] }
def er184_079 : Row := { vars := #[2, 82, 113], coeff := #[1, 1, 1], bound := 1, weight := 29082, edges := #[⟨0, 1, 80⟩, ⟨0, 2, 354⟩, ⟨1, 2, 409⟩], triples := #[] }
def er184_080 : Row := { vars := #[5, 110, 87], coeff := #[1, 1, 1], bound := 1, weight := 527552, edges := #[⟨0, 1, 401⟩, ⟨0, 2, 126⟩, ⟨1, 2, 405⟩], triples := #[] }
def er184_081 : Row := { vars := #[6, 325, 152], coeff := #[1, 1, 1], bound := 1, weight := 730613, edges := #[⟨0, 1, 299⟩, ⟨0, 2, 492⟩, ⟨1, 2, 111⟩], triples := #[] }
def er184_082 : Row := { vars := #[7, 198, 371], coeff := #[1, 1, 1], bound := 1, weight := 710205, edges := #[⟨0, 1, 438⟩, ⟨0, 2, 245⟩, ⟨1, 2, 171⟩], triples := #[] }
def er184_083 : Row := { vars := #[8, 199, 309], coeff := #[1, 1, 1], bound := 1, weight := 941327, edges := #[⟨0, 1, 438⟩, ⟨0, 2, 308⟩, ⟨1, 2, 44⟩], triples := #[] }
def er184_084 : Row := { vars := #[11, 297, 210], coeff := #[1, 1, 1], bound := 1, weight := 409694, edges := #[⟨0, 1, 333⟩, ⟨0, 2, 414⟩, ⟨1, 2, 37⟩], triples := #[] }
def er184_085 : Row := { vars := #[13, 264, 44], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 235⟩, ⟨0, 2, 189⟩, ⟨1, 2, 302⟩], triples := #[] }
def er184_086 : Row := { vars := #[16, 290, 219], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 202⟩, ⟨0, 2, 415⟩, ⟨1, 2, 72⟩], triples := #[] }
def er184_087 : Row := { vars := #[17, 288, 192], coeff := #[1, 1, 1], bound := 1, weight := 58674, edges := #[⟨0, 1, 201⟩, ⟨0, 2, 459⟩, ⟨1, 2, 181⟩], triples := #[] }
def er184_088 : Row := { vars := #[17, 289, 237], coeff := #[1, 1, 1], bound := 1, weight := 526531, edges := #[⟨0, 1, 200⟩, ⟨0, 2, 405⟩, ⟨1, 2, 121⟩], triples := #[] }
def er184_089 : Row := { vars := #[23, 138, 361], coeff := #[1, 1, 1], bound := 1, weight := 705613, edges := #[⟨0, 1, 391⟩, ⟨0, 2, 254⟩, ⟨1, 2, 110⟩], triples := #[] }
def er184_090 : Row := { vars := #[27, 130, 372], coeff := #[1, 1, 1], bound := 1, weight := 306123, edges := #[⟨0, 1, 352⟩, ⟨0, 2, 277⟩, ⟨1, 2, 81⟩], triples := #[] }
def er184_091 : Row := { vars := #[28, 129, 354], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 354⟩, ⟨0, 2, 244⟩, ⟨1, 2, 111⟩], triples := #[] }
def er184_092 : Row := { vars := #[29, 166, 296], coeff := #[1, 1, 1], bound := 1, weight := 506123, edges := #[⟨0, 1, 458⟩, ⟨0, 2, 311⟩, ⟨1, 2, 121⟩], triples := #[] }
def er184_093 : Row := { vars := #[29, 274, 183], coeff := #[1, 1, 1], bound := 1, weight := 204082, edges := #[⟨0, 1, 197⟩, ⟨0, 2, 491⟩, ⟨1, 2, 133⟩], triples := #[] }
def er184_094 : Row := { vars := #[34, 128, 264], coeff := #[1, 1, 1], bound := 1, weight := 440817, edges := #[⟨0, 1, 379⟩, ⟨0, 2, 224⟩, ⟨1, 2, 57⟩], triples := #[] }
def er184_095 : Row := { vars := #[40, 110, 272], coeff := #[1, 1, 1], bound := 1, weight := 240307, edges := #[⟨0, 1, 384⟩, ⟨0, 2, 211⟩, ⟨1, 2, 70⟩], triples := #[] }
def er184_096 : Row := { vars := #[42, 138, 379], coeff := #[1, 1, 1], bound := 1, weight := 294388, edges := #[⟨0, 1, 372⟩, ⟨0, 2, 277⟩, ⟨1, 2, 81⟩], triples := #[] }
def er184_097 : Row := { vars := #[43, 208, 334], coeff := #[1, 1, 1], bound := 1, weight := 167347, edges := #[⟨0, 1, 427⟩, ⟨0, 2, 330⟩, ⟨1, 2, 8⟩], triples := #[] }
def er184_098 : Row := { vars := #[46, 128, 325], coeff := #[1, 1, 1], bound := 1, weight := 269388, edges := #[⟨0, 1, 492⟩, ⟨0, 2, 255⟩, ⟨1, 2, 141⟩], triples := #[] }
def er184_099 : Row := { vars := #[46, 140, 310], coeff := #[1, 1, 1], bound := 1, weight := 710205, edges := #[⟨0, 1, 470⟩, ⟨0, 2, 277⟩, ⟨1, 2, 140⟩], triples := #[] }
def er184_100 : Row := { vars := #[49, 272, 181], coeff := #[1, 1, 1], bound := 1, weight := 759694, edges := #[⟨0, 1, 333⟩, ⟨0, 2, 415⟩, ⟨1, 2, 133⟩], triples := #[] }
def er184_101 : Row := { vars := #[53, 264, 200], coeff := #[1, 1, 1], bound := 1, weight := 710205, edges := #[⟨0, 1, 299⟩, ⟨0, 2, 376⟩, ⟨1, 2, 93⟩], triples := #[] }
def er184_102 : Row := { vars := #[61, 160, 363], coeff := #[1, 1, 1], bound := 1, weight := 271429, edges := #[⟨0, 1, 411⟩, ⟨0, 2, 235⟩, ⟨1, 2, 45⟩], triples := #[] }
def er184_103 : Row := { vars := #[64, 301, 120], coeff := #[1, 1, 1], bound := 1, weight := 612245, edges := #[⟨0, 1, 288⟩, ⟨0, 2, 490⟩, ⟨1, 2, 144⟩], triples := #[] }
def er184_104 : Row := { vars := #[68, 198, 264], coeff := #[1, 1, 1], bound := 1, weight := 289796, edges := #[⟨0, 1, 392⟩, ⟨0, 2, 308⟩, ⟨1, 2, 92⟩], triples := #[] }
def er184_105 : Row := { vars := #[77, 273, 227], coeff := #[1, 1, 1], bound := 1, weight := 267347, edges := #[⟨0, 1, 279⟩, ⟨0, 2, 469⟩, ⟨1, 2, 73⟩], triples := #[] }
def er184_106 : Row := { vars := #[77, 285, 212], coeff := #[1, 1, 1], bound := 1, weight := 529592, edges := #[⟨0, 1, 257⟩, ⟨0, 2, 491⟩, ⟨1, 2, 72⟩], triples := #[] }
def er184_107 : Row := { vars := #[83, 277, 236], coeff := #[1, 1, 1], bound := 1, weight := 138776, edges := #[⟨0, 1, 280⟩, ⟨0, 2, 469⟩, ⟨1, 2, 73⟩], triples := #[] }
def er184_108 : Row := { vars := #[85, 236, 300], coeff := #[1, 1, 1], bound := 1, weight := 861225, edges := #[⟨0, 1, 468⟩, ⟨0, 2, 200⟩, ⟨1, 2, 1⟩], triples := #[] }
def er184_109 : Row := { vars := #[89, 149, 363], coeff := #[1, 1, 1], bound := 1, weight := 183674, edges := #[⟨0, 1, 427⟩, ⟨0, 2, 331⟩, ⟨1, 2, 80⟩], triples := #[] }
def er184_110 : Row := { vars := #[97, 278, 120], coeff := #[1, 1, 1], bound := 1, weight := 364796, edges := #[⟨0, 1, 250⟩, ⟨0, 2, 415⟩, ⟨1, 2, 48⟩], triples := #[] }
def er184_111 : Row := { vars := #[100, 295, 310], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 144⟩, ⟨0, 2, 180⟩, ⟨1, 2, 437⟩], triples := #[] }
def er184_112 : Row := { vars := #[101, 356, 341], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 120⟩, ⟨0, 2, 84⟩, ⟨1, 2, 491⟩], triples := #[] }
def er184_113 : Row := { vars := #[116, 305, 317], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 167⟩, ⟨0, 2, 180⟩, ⟨1, 2, 437⟩], triples := #[] }
def er184_114 : Row := { vars := #[117, 361, 281], coeff := #[1, 1, 1], bound := 1, weight := 258164, edges := #[⟨0, 1, 121⟩, ⟨0, 2, 69⟩, ⟨1, 2, 414⟩], triples := #[] }
def er184_115 : Row := { vars := #[118, 293, 334], coeff := #[1, 1, 1], bound := 1, weight := 409694, edges := #[⟨0, 1, 34⟩, ⟨0, 2, 169⟩, ⟨1, 2, 490⟩], triples := #[] }
def er184_116 : Row := { vars := #[122, 276, 191], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 41⟩, ⟨0, 2, 323⟩, ⟨1, 2, 132⟩], triples := #[] }
def er184_117 : Row := { vars := #[123, 109, 113], coeff := #[1, 1, 1], bound := 1, weight := 970919, edges := #[⟨0, 1, 201⟩, ⟨0, 2, 199⟩, ⟨1, 2, 221⟩], triples := #[] }
def er184_118 : Row := { vars := #[123, 277, 285], coeff := #[1, 1, 1], bound := 1, weight := 29082, edges := #[⟨0, 1, 42⟩, ⟨0, 2, 21⟩, ⟨1, 2, 377⟩], triples := #[] }
def er184_119 : Row := { vars := #[124, 164, 173], coeff := #[1, 1, 1], bound := 1, weight := 543878, edges := #[⟨0, 1, 335⟩, ⟨0, 2, 345⟩, ⟨1, 2, 262⟩], triples := #[] }
def er184_120 : Row := { vars := #[124, 301, 343], coeff := #[1, 1, 1], bound := 1, weight := 118368, edges := #[⟨0, 1, 138⟩, ⟨0, 2, 93⟩, ⟨1, 2, 378⟩], triples := #[] }
def er184_121 : Row := { vars := #[124, 211, 220], coeff := #[1, 1, 1], bound := 1, weight := 298980, edges := #[⟨0, 1, 281⟩, ⟨0, 2, 291⟩, ⟨1, 2, 316⟩], triples := #[] }
def er184_122 : Row := { vars := #[125, 229, 238], coeff := #[1, 1, 1], bound := 1, weight := 932143, edges := #[⟨0, 1, 261⟩, ⟨0, 2, 271⟩, ⟨1, 2, 338⟩], triples := #[] }
def er184_123 : Row := { vars := #[127, 324, 372], coeff := #[1, 1, 1], bound := 1, weight := 612245, edges := #[⟨0, 1, 143⟩, ⟨0, 2, 73⟩, ⟨1, 2, 395⟩], triples := #[] }
def er184_124 : Row := { vars := #[128, 279, 137], coeff := #[1, 1, 1], bound := 1, weight := 289796, edges := #[⟨0, 1, 34⟩, ⟨0, 2, 230⟩, ⟨1, 2, 10⟩], triples := #[] }
def er184_125 : Row := { vars := #[133, 266, 316], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 70⟩, ⟨0, 2, 168⟩, ⟨1, 2, 491⟩], triples := #[] }
def er184_126 : Row := { vars := #[134, 164, 213], coeff := #[1, 1, 1], bound := 1, weight := 456123, edges := #[⟨0, 1, 315⟩, ⟨0, 2, 258⟩, ⟨1, 2, 225⟩], triples := #[] }
def er184_127 : Row := { vars := #[134, 167, 277], coeff := #[1, 1, 1], bound := 1, weight := 237756, edges := #[⟨0, 1, 312⟩, ⟨0, 2, 5⟩, ⟨1, 2, 176⟩], triples := #[] }
end HardyCapset20261020.Cert


