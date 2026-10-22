-- Prove2me | Definitions.Def_HardyCapsetEvaluationData017rows02V420261021
-- name    : HardyCapsetEvaluationData017rows02V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T01:53:23.113696+00:00
-- url     : https://prove2.me/theorems/fb6520c2-f506-4e45-aa25-4b3ed95fb077
-- title:
--   HardyCapsetEvaluationData017rows02V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er017_128 : Row := { vars := #[86, 132, 158, 236, 11], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 337⟩, ⟨0, 3, 134⟩, ⟨1, 3, 84⟩, ⟨1, 4, 497⟩, ⟨2, 4, 445⟩], triples := #[⟨0, 1, 2⟩] }
def er017_129 : Row := { vars := #[87, 111, 116, 220, 76], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 192308, edges := #[⟨3, 4, 253⟩, ⟨0, 3, 11⟩, ⟨2, 3, 40⟩, ⟨1, 4, 428⟩, ⟨2, 4, 413⟩], triples := #[⟨0, 1, 2⟩] }
def er017_130 : Row := { vars := #[95, 130, 166, 27], coeff := #[1, 1, 1, 1], bound := 2, weight := 500000, edges := #[⟨1, 3, 475⟩, ⟨2, 3, 431⟩], triples := #[⟨0, 1, 2⟩] }
def er017_131 : Row := { vars := #[98, 114, 122, 41], coeff := #[1, 1, 1, 1], bound := 2, weight := 151924, edges := #[⟨1, 3, 506⟩, ⟨2, 3, 473⟩], triples := #[⟨0, 1, 2⟩] }
def er017_132 : Row := { vars := #[102, 110, 123, 217], coeff := #[1, 1, 1, 1], bound := 2, weight := 205770, edges := #[⟨0, 3, 46⟩, ⟨1, 3, 34⟩], triples := #[⟨0, 1, 2⟩] }
def er017_133 : Row := { vars := #[105, 106, 112, 193, 77], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 348077, edges := #[⟨3, 4, 286⟩, ⟨0, 3, 47⟩, ⟨1, 3, 39⟩, ⟨1, 4, 424⟩, ⟨2, 4, 420⟩], triples := #[⟨0, 1, 2⟩] }
def er017_134 : Row := { vars := #[106, 131, 178, 235, 50], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 205770, edges := #[⟨3, 4, 282⟩, ⟨1, 3, 83⟩, ⟨2, 3, 4⟩, ⟨0, 4, 477⟩, ⟨1, 4, 442⟩], triples := #[⟨0, 1, 2⟩] }
def er017_135 : Row := { vars := #[110, 126, 178, 51, 214], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 794231, edges := #[⟨3, 4, 314⟩, ⟨0, 3, 474⟩, ⟨1, 3, 445⟩, ⟨0, 4, 10⟩, ⟨2, 4, 74⟩], triples := #[⟨0, 1, 2⟩] }
def er017_136 : Row := { vars := #[115, 116, 122, 195, 49], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 40385, edges := #[⟨3, 4, 348⟩, ⟨0, 3, 11⟩, ⟨1, 3, 3⟩, ⟨1, 4, 467⟩, ⟨2, 4, 466⟩], triples := #[⟨0, 1, 2⟩] }
def er017_137 : Row := { vars := #[115, 132, 168, 12], coeff := #[1, 1, 1, 1], bound := 2, weight := 500000, edges := #[⟨1, 3, 496⟩, ⟨2, 3, 423⟩], triples := #[⟨0, 1, 2⟩] }
def er017_138 : Row := { vars := #[116, 135, 164, 83, 268], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 473077, edges := #[⟨3, 4, 314⟩, ⟨0, 3, 447⟩, ⟨2, 3, 474⟩, ⟨1, 4, 40⟩, ⟨2, 4, 144⟩], triples := #[⟨0, 1, 2⟩] }
def er017_139 : Row := { vars := #[125, 126, 130, 193, 57], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 318⟩, ⟨0, 3, 144⟩, ⟨1, 3, 136⟩, ⟨1, 4, 425⟩, ⟨2, 4, 421⟩], triples := #[⟨0, 1, 2⟩] }
def er017_140 : Row := { vars := #[131, 139, 154, 64], coeff := #[1, 1, 1, 1], bound := 2, weight := 750001, edges := #[⟨0, 3, 377⟩, ⟨1, 3, 399⟩], triples := #[⟨0, 1, 2⟩] }
def er017_141 : Row := { vars := #[131, 139, 154, 281], coeff := #[1, 1, 1, 1], bound := 2, weight := 44231, edges := #[⟨0, 3, 59⟩, ⟨1, 3, 11⟩], triples := #[⟨0, 1, 2⟩] }
def er017_142 : Row := { vars := #[157, 158, 162, 266, 36], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 219⟩, ⟨0, 3, 134⟩, ⟨2, 3, 142⟩, ⟨1, 4, 383⟩, ⟨2, 4, 379⟩], triples := #[⟨0, 1, 2⟩] }
def er017_143 : Row := { vars := #[189, 210, 225, 42, 121], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 44231, edges := #[⟨3, 4, 474⟩, ⟨1, 3, 340⟩, ⟨2, 3, 314⟩, ⟨0, 4, 4⟩, ⟨2, 4, 47⟩], triples := #[⟨0, 1, 2⟩] }
def er017_144 : Row := { vars := #[190, 210, 224, 55, 120], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 607693, edges := #[⟨3, 4, 504⟩, ⟨1, 3, 307⟩, ⟨2, 3, 344⟩, ⟨0, 4, 4⟩, ⟨2, 4, 46⟩], triples := #[⟨0, 1, 2⟩] }
def er017_145 : Row := { vars := #[190, 236, 262, 132, 54], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 44231, edges := #[⟨3, 4, 428⟩, ⟨0, 3, 134⟩, ⟨1, 3, 84⟩, ⟨1, 4, 268⟩, ⟨2, 4, 233⟩], triples := #[⟨0, 1, 2⟩] }
def er017_146 : Row := { vars := #[195, 229, 267, 22], coeff := #[1, 1, 1, 1], bound := 2, weight := 205770, edges := #[⟨0, 3, 233⟩, ⟨2, 3, 268⟩], triples := #[⟨0, 1, 2⟩] }
def er017_147 : Row := { vars := #[199, 215, 228, 96], coeff := #[1, 1, 1, 1], bound := 2, weight := 250000, edges := #[⟨1, 3, 70⟩, ⟨2, 3, 10⟩], triples := #[⟨0, 1, 2⟩] }
def er017_148 : Row := { vars := #[210, 250, 267, 163, 22], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 544231, edges := #[⟨3, 4, 428⟩, ⟨1, 3, 4⟩, ⟨2, 3, 143⟩, ⟨0, 4, 220⟩, ⟨2, 4, 268⟩], triples := #[⟨0, 1, 2⟩] }
def er017_149 : Row := { vars := #[214, 244, 279, 156], coeff := #[1, 1, 1, 1], bound := 2, weight := 205770, edges := #[⟨0, 3, 156⟩, ⟨1, 3, 84⟩], triples := #[⟨0, 1, 2⟩] }
def er017_150 : Row := { vars := #[219, 220, 226, 122, 68], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 44231, edges := #[⟨3, 4, 420⟩, ⟨0, 3, 40⟩, ⟨2, 3, 48⟩, ⟨1, 4, 264⟩, ⟨2, 4, 260⟩], triples := #[⟨0, 1, 2⟩] }
def er017_151 : Row := { vars := #[219, 220, 226, 122, 49], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 763462, edges := #[⟨3, 4, 466⟩, ⟨0, 3, 40⟩, ⟨2, 3, 48⟩, ⟨1, 4, 307⟩, ⟨2, 4, 306⟩], triples := #[⟨0, 1, 2⟩] }
def er017_152 : Row := { vars := #[224, 253, 291, 1], coeff := #[1, 1, 1, 1], bound := 2, weight := 392308, edges := #[⟨0, 3, 196⟩, ⟨1, 3, 305⟩], triples := #[⟨0, 1, 2⟩] }
def er017_153 : Row := { vars := #[225, 239, 262, 84, 121], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 794231, edges := #[⟨3, 4, 442⟩, ⟨0, 3, 282⟩, ⟨2, 3, 319⟩, ⟨0, 4, 47⟩, ⟨1, 4, 134⟩], triples := #[⟨0, 1, 2⟩] }
def er017_154 : Row := { vars := #[225, 239, 262, 135], coeff := #[1, 1, 1, 1], bound := 2, weight := 161539, edges := #[⟨0, 3, 134⟩, ⟨2, 3, 47⟩], triples := #[⟨0, 1, 2⟩] }
def er017_155 : Row := { vars := #[229, 230, 234, 126, 81], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 750001, edges := #[⟨3, 4, 393⟩, ⟨0, 3, 82⟩, ⟨1, 3, 74⟩, ⟨1, 4, 233⟩, ⟨2, 4, 232⟩], triples := #[⟨0, 1, 2⟩] }
def er017_156 : Row := { vars := #[266, 279, 286, 48], coeff := #[1, 1, 1, 1], bound := 2, weight := 446154, edges := #[⟨0, 3, 242⟩, ⟨2, 3, 206⟩], triples := #[⟨0, 1, 2⟩] }
def er017_157 : Row := { vars := #[6], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er017_158 : Row := { vars := #[7], coeff := #[1], bound := 1, weight := 151924, edges := #[], triples := #[] }
def er017_159 : Row := { vars := #[9], coeff := #[1], bound := 1, weight := 19231, edges := #[], triples := #[] }
def er017_160 : Row := { vars := #[12], coeff := #[1], bound := 1, weight := 313462, edges := #[], triples := #[] }
def er017_161 : Row := { vars := #[13], coeff := #[1], bound := 1, weight := 205770, edges := #[], triples := #[] }
def er017_162 : Row := { vars := #[18], coeff := #[1], bound := 1, weight := 250000, edges := #[], triples := #[] }
def er017_163 : Row := { vars := #[19], coeff := #[1], bound := 1, weight := 571154, edges := #[], triples := #[] }
def er017_164 : Row := { vars := #[20], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er017_165 : Row := { vars := #[23], coeff := #[1], bound := 1, weight := 44231, edges := #[], triples := #[] }
def er017_166 : Row := { vars := #[25], coeff := #[1], bound := 1, weight := 400001, edges := #[], triples := #[] }
def er017_167 : Row := { vars := #[27], coeff := #[1], bound := 1, weight := 500000, edges := #[], triples := #[] }
def er017_168 : Row := { vars := #[29], coeff := #[1], bound := 1, weight := 473077, edges := #[], triples := #[] }
def er017_169 : Row := { vars := #[33], coeff := #[1], bound := 1, weight := 750001, edges := #[], triples := #[] }
def er017_170 : Row := { vars := #[34], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er017_171 : Row := { vars := #[35], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er017_172 : Row := { vars := #[38], coeff := #[1], bound := 1, weight := 401924, edges := #[], triples := #[] }
def er017_173 : Row := { vars := #[41], coeff := #[1], bound := 1, weight := 848077, edges := #[], triples := #[] }
def er017_174 : Row := { vars := #[43], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er017_175 : Row := { vars := #[44], coeff := #[1], bound := 1, weight := 250000, edges := #[], triples := #[] }
def er017_176 : Row := { vars := #[50], coeff := #[1], bound := 1, weight := 544231, edges := #[], triples := #[] }
def er017_177 : Row := { vars := #[51], coeff := #[1], bound := 1, weight := 205770, edges := #[], triples := #[] }
def er017_178 : Row := { vars := #[56], coeff := #[1], bound := 1, weight := 221154, edges := #[], triples := #[] }
def er017_179 : Row := { vars := #[60], coeff := #[1], bound := 1, weight := 750001, edges := #[], triples := #[] }
def er017_180 : Row := { vars := #[61], coeff := #[1], bound := 1, weight := 250000, edges := #[], triples := #[] }
def er017_181 : Row := { vars := #[62], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er017_182 : Row := { vars := #[63], coeff := #[1], bound := 1, weight := 294231, edges := #[], triples := #[] }
def er017_183 : Row := { vars := #[65], coeff := #[1], bound := 1, weight := 750001, edges := #[], triples := #[] }
def er017_184 : Row := { vars := #[68], coeff := #[1], bound := 1, weight := 955770, edges := #[], triples := #[] }
def er017_185 : Row := { vars := #[70], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er017_186 : Row := { vars := #[71], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er017_187 : Row := { vars := #[75], coeff := #[1], bound := 1, weight := 588462, edges := #[], triples := #[] }
def er017_188 : Row := { vars := #[76], coeff := #[1], bound := 1, weight := 655770, edges := #[], triples := #[] }
def er017_189 : Row := { vars := #[77], coeff := #[1], bound := 1, weight := 215385, edges := #[], triples := #[] }
def er017_190 : Row := { vars := #[78], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er017_191 : Row := { vars := #[82], coeff := #[1], bound := 1, weight := 759616, edges := #[], triples := #[] }
end HardyCapset20261020.Cert


