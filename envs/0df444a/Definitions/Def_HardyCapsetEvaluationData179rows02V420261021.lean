-- Prove2me | Definitions.Def_HardyCapsetEvaluationData179rows02V420261021
-- name    : HardyCapsetEvaluationData179rows02V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T03:21:46.144404+00:00
-- url     : https://prove2.me/theorems/131993cb-7c03-467f-b970-ff61859233db
-- title:
--   HardyCapsetEvaluationData179rows02V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er179_128 : Row := { vars := #[178, 232, 278, 222, 108], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 74⟩, ⟨0, 3, 511⟩, ⟨1, 3, 425⟩, ⟨1, 4, 92⟩, ⟨2, 4, 41⟩], triples := #[⟨0, 1, 2⟩] }
def er179_129 : Row := { vars := #[183, 228, 290, 73, 276], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 866667, edges := #[⟨3, 4, 78⟩, ⟨0, 3, 58⟩, ⟨1, 3, 174⟩, ⟨0, 4, 418⟩, ⟨2, 4, 495⟩], triples := #[⟨0, 1, 2⟩] }
def er179_130 : Row := { vars := #[183, 228, 290, 81, 159], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 66667, edges := #[⟨3, 4, 6⟩, ⟨0, 3, 22⟩, ⟨1, 3, 150⟩, ⟨0, 4, 361⟩, ⟨2, 4, 421⟩], triples := #[⟨0, 1, 2⟩] }
def er179_131 : Row := { vars := #[183, 247, 271, 234, 123], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 88889, edges := #[⟨3, 4, 6⟩, ⟨0, 3, 472⟩, ⟨1, 3, 443⟩, ⟨0, 4, 92⟩, ⟨2, 4, 187⟩], triples := #[⟨0, 1, 2⟩] }
def er179_132 : Row := { vars := #[186, 248, 267, 121], coeff := #[1, 1, 1, 1], bound := 2, weight := 66667, edges := #[⟨0, 3, 96⟩, ⟨1, 3, 20⟩], triples := #[⟨0, 1, 2⟩] }
def er179_133 : Row := { vars := #[191, 237, 265, 3, 261], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 444445, edges := #[⟨3, 4, 257⟩, ⟨1, 3, 300⟩, ⟨2, 3, 267⟩, ⟨0, 4, 445⟩, ⟨2, 4, 488⟩], triples := #[⟨0, 1, 2⟩] }
def er179_134 : Row := { vars := #[191, 237, 265, 94, 247], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 200001, edges := #[⟨3, 4, 92⟩, ⟨1, 3, 74⟩, ⟨2, 3, 30⟩, ⟨0, 4, 488⟩, ⟨1, 4, 445⟩], triples := #[⟨0, 1, 2⟩] }
def er179_135 : Row := { vars := #[192, 240, 264, 16, 274], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 248⟩, ⟨1, 3, 343⟩, ⟨2, 3, 246⟩, ⟨0, 4, 456⟩, ⟨2, 4, 479⟩], triples := #[⟨0, 1, 2⟩] }
def er179_136 : Row := { vars := #[196, 233, 264, 144], coeff := #[1, 1, 1, 1], bound := 2, weight := 133334, edges := #[⟨0, 3, 104⟩, ⟨2, 3, 134⟩], triples := #[⟨0, 1, 2⟩] }
def er179_137 : Row := { vars := #[205, 247, 278, 69, 237], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 355556, edges := #[⟨3, 4, 134⟩, ⟨1, 3, 152⟩, ⟨2, 3, 79⟩, ⟨0, 4, 511⟩, ⟨1, 4, 445⟩], triples := #[⟨0, 1, 2⟩] }
def er179_138 : Row := { vars := #[216, 223, 239, 249, 122], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 22⟩, ⟨0, 3, 433⟩, ⟨2, 3, 447⟩, ⟨1, 4, 66⟩, ⟨2, 4, 4⟩], triples := #[⟨0, 1, 2⟩] }
def er179_139 : Row := { vars := #[219, 224, 230, 196, 107], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 800000, edges := #[⟨3, 4, 162⟩, ⟨0, 3, 489⟩, ⟨1, 3, 479⟩, ⟨0, 4, 79⟩, ⟨2, 4, 94⟩], triples := #[⟨0, 1, 2⟩] }
def er179_140 : Row := { vars := #[219, 224, 230, 171, 4], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 133334, edges := #[⟨3, 4, 241⟩, ⟨0, 3, 510⟩, ⟨1, 3, 500⟩, ⟨0, 4, 311⟩, ⟨2, 4, 312⟩], triples := #[⟨0, 1, 2⟩] }
def er179_141 : Row := { vars := #[220, 223, 233, 168, 28], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 133334, edges := #[⟨3, 4, 301⟩, ⟨1, 3, 509⟩, ⟨2, 3, 499⟩, ⟨0, 4, 278⟩, ⟨1, 4, 289⟩], triples := #[⟨0, 1, 2⟩] }
def er179_142 : Row := { vars := #[253, 272, 283, 93], coeff := #[1, 1, 1, 1], bound := 2, weight := 177778, edges := #[⟨0, 3, 41⟩, ⟨1, 3, 22⟩], triples := #[⟨0, 1, 2⟩] }
def er179_143 : Row := { vars := #[255, 261, 290, 42, 265], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 66667, edges := #[⟨3, 4, 215⟩, ⟨1, 3, 199⟩, ⟨2, 3, 238⟩, ⟨0, 4, 500⟩, ⟨1, 4, 488⟩], triples := #[⟨0, 1, 2⟩] }
def er179_144 : Row := { vars := #[263, 265, 275, 273, 143], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 154⟩, ⟨0, 3, 478⟩, ⟨2, 3, 488⟩, ⟨0, 4, 136⟩, ⟨1, 4, 164⟩], triples := #[⟨0, 1, 2⟩] }
def er179_145 : Row := { vars := #[281, 282, 292, 291, 15], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 866667, edges := #[⟨3, 4, 280⟩, ⟨0, 3, 501⟩, ⟨2, 3, 511⟩, ⟨0, 4, 278⟩, ⟨1, 4, 289⟩], triples := #[⟨0, 1, 2⟩] }
def er179_146 : Row := { vars := #[3], coeff := #[1], bound := 1, weight := 555556, edges := #[], triples := #[] }
def er179_147 : Row := { vars := #[4], coeff := #[1], bound := 1, weight := 44445, edges := #[], triples := #[] }
def er179_148 : Row := { vars := #[13], coeff := #[1], bound := 1, weight := 800000, edges := #[], triples := #[] }
def er179_149 : Row := { vars := #[15], coeff := #[1], bound := 1, weight := 133334, edges := #[], triples := #[] }
def er179_150 : Row := { vars := #[18], coeff := #[1], bound := 1, weight := 400001, edges := #[], triples := #[] }
def er179_151 : Row := { vars := #[19], coeff := #[1], bound := 1, weight := 866667, edges := #[], triples := #[] }
def er179_152 : Row := { vars := #[25], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er179_153 : Row := { vars := #[27], coeff := #[1], bound := 1, weight := 400001, edges := #[], triples := #[] }
def er179_154 : Row := { vars := #[29], coeff := #[1], bound := 1, weight := 200001, edges := #[], triples := #[] }
def er179_155 : Row := { vars := #[30], coeff := #[1], bound := 1, weight := 133334, edges := #[], triples := #[] }
def er179_156 : Row := { vars := #[39], coeff := #[1], bound := 1, weight := 933334, edges := #[], triples := #[] }
def er179_157 : Row := { vars := #[43], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er179_158 : Row := { vars := #[47], coeff := #[1], bound := 1, weight := 200001, edges := #[], triples := #[] }
def er179_159 : Row := { vars := #[48], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er179_160 : Row := { vars := #[50], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er179_161 : Row := { vars := #[53], coeff := #[1], bound := 1, weight := 400000, edges := #[], triples := #[] }
def er179_162 : Row := { vars := #[55], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er179_163 : Row := { vars := #[58], coeff := #[1], bound := 1, weight := 866667, edges := #[], triples := #[] }
def er179_164 : Row := { vars := #[60], coeff := #[1], bound := 1, weight := 200001, edges := #[], triples := #[] }
def er179_165 : Row := { vars := #[69], coeff := #[1], bound := 1, weight := 644445, edges := #[], triples := #[] }
def er179_166 : Row := { vars := #[77], coeff := #[1], bound := 1, weight := 200001, edges := #[], triples := #[] }
def er179_167 : Row := { vars := #[78], coeff := #[1], bound := 1, weight := 866667, edges := #[], triples := #[] }
def er179_168 : Row := { vars := #[93], coeff := #[1], bound := 1, weight := 822223, edges := #[], triples := #[] }
def er179_169 : Row := { vars := #[106], coeff := #[1], bound := 1, weight := 933334, edges := #[], triples := #[] }
def er179_170 : Row := { vars := #[116], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er179_171 : Row := { vars := #[137], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er179_172 : Row := { vars := #[138], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er179_173 : Row := { vars := #[140], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er179_174 : Row := { vars := #[142], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er179_175 : Row := { vars := #[144], coeff := #[1], bound := 1, weight := 800000, edges := #[], triples := #[] }
def er179_176 : Row := { vars := #[154], coeff := #[1], bound := 1, weight := 333334, edges := #[], triples := #[] }
def er179_177 : Row := { vars := #[156], coeff := #[1], bound := 1, weight := 66667, edges := #[], triples := #[] }
def er179_178 : Row := { vars := #[157], coeff := #[1], bound := 1, weight := 933334, edges := #[], triples := #[] }
def er179_179 : Row := { vars := #[158], coeff := #[1], bound := 1, weight := 88889, edges := #[], triples := #[] }
def er179_180 : Row := { vars := #[159], coeff := #[1], bound := 1, weight := 933334, edges := #[], triples := #[] }
def er179_181 : Row := { vars := #[160], coeff := #[1], bound := 1, weight := 866667, edges := #[], triples := #[] }
def er179_182 : Row := { vars := #[175], coeff := #[1], bound := 1, weight := 133334, edges := #[], triples := #[] }
def er179_183 : Row := { vars := #[190], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er179_184 : Row := { vars := #[193], coeff := #[1], bound := 1, weight := 866667, edges := #[], triples := #[] }
def er179_185 : Row := { vars := #[197], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er179_186 : Row := { vars := #[205], coeff := #[1], bound := 1, weight := 333334, edges := #[], triples := #[] }
def er179_187 : Row := { vars := #[208], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er179_188 : Row := { vars := #[213], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er179_189 : Row := { vars := #[225], coeff := #[1], bound := 1, weight := 733334, edges := #[], triples := #[] }
def er179_190 : Row := { vars := #[229], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er179_191 : Row := { vars := #[233], coeff := #[1], bound := 1, weight := 733334, edges := #[], triples := #[] }
end HardyCapset20261020.Cert


