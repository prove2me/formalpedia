-- Prove2me | Definitions.Def_HardyCapsetEvaluationData178rows03V420261021
-- name    : HardyCapsetEvaluationData178rows03V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T03:16:37.479874+00:00
-- url     : https://prove2.me/theorems/29b813bf-7801-4268-9c2f-30fa6319c6b9
-- title:
--   HardyCapsetEvaluationData178rows03V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er178_192 : Row := { vars := #[8, 162, 271, 360, 276], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 2539, edges := #[⟨3, 4, 404⟩, ⟨1, 3, 109⟩, ⟨2, 3, 410⟩, ⟨1, 4, 34⟩, ⟨2, 4, 357⟩], triples := #[⟨0, 1, 2⟩] }
def er178_193 : Row := { vars := #[11, 133, 303, 129, 224], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 89986, edges := #[⟨3, 4, 276⟩, ⟨1, 3, 217⟩, ⟨2, 3, 9⟩, ⟨1, 4, 278⟩, ⟨2, 4, 94⟩], triples := #[⟨0, 1, 2⟩] }
def er178_194 : Row := { vars := #[15, 216, 338, 276], coeff := #[1, 1, 1, 1], bound := 2, weight := 275036, edges := #[⟨0, 3, 234⟩, ⟨2, 3, 480⟩], triples := #[⟨0, 1, 2⟩] }
def er178_195 : Row := { vars := #[21, 101, 309, 224], coeff := #[1, 1, 1, 1], bound := 2, weight := 224824, edges := #[⟨0, 3, 414⟩, ⟨1, 3, 290⟩], triples := #[⟨0, 1, 2⟩] }
def er178_196 : Row := { vars := #[23, 156, 261, 18, 59], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 362483, edges := #[⟨3, 4, 190⟩, ⟨0, 3, 35⟩, ⟨2, 3, 236⟩, ⟨1, 4, 473⟩, ⟨2, 4, 299⟩], triples := #[⟨0, 1, 2⟩] }
def er178_197 : Row := { vars := #[23, 156, 261, 218, 98], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 542455, edges := #[⟨3, 4, 485⟩, ⟨0, 3, 449⟩, ⟨2, 3, 76⟩, ⟨1, 4, 443⟩, ⟨2, 4, 254⟩], triples := #[⟨0, 1, 2⟩] }
def er178_198 : Row := { vars := #[27, 126, 294, 366], coeff := #[1, 1, 1, 1], bound := 2, weight := 324401, edges := #[⟨0, 3, 245⟩, ⟨2, 3, 432⟩], triples := #[⟨0, 1, 2⟩] }
def er178_199 : Row := { vars := #[27, 226, 324, 332], coeff := #[1, 1, 1, 1], bound := 2, weight := 2539, edges := #[⟨1, 3, 1⟩, ⟨2, 3, 448⟩], triples := #[⟨0, 1, 2⟩] }
def er178_200 : Row := { vars := #[28, 145, 272, 142, 82], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 539916, edges := #[⟨3, 4, 451⟩, ⟨0, 3, 359⟩, ⟨2, 3, 57⟩, ⟨1, 4, 443⟩, ⟨2, 4, 244⟩], triples := #[⟨0, 1, 2⟩] }
def er178_201 : Row := { vars := #[31, 114, 295, 24, 60], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 814951, edges := #[⟨3, 4, 172⟩, ⟨0, 3, 40⟩, ⟨1, 3, 391⟩, ⟨1, 4, 458⟩, ⟨2, 4, 350⟩], triples := #[⟨0, 1, 2⟩] }
def er178_202 : Row := { vars := #[35, 149, 246, 174], coeff := #[1, 1, 1, 1], bound := 2, weight := 642596, edges := #[⟨0, 3, 486⟩, ⟨2, 3, 133⟩], triples := #[⟨0, 1, 2⟩] }
def er178_203 : Row := { vars := #[43, 141, 261, 38, 88], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 994923, edges := #[⟨3, 4, 118⟩, ⟨0, 3, 71⟩, ⟨2, 3, 226⟩, ⟨1, 4, 443⟩, ⟨2, 4, 244⟩], triples := #[⟨0, 1, 2⟩] }
def er178_204 : Row := { vars := #[46, 212, 272, 142, 93], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 185050, edges := #[⟨3, 4, 430⟩, ⟨0, 3, 493⟩, ⟨2, 3, 57⟩, ⟨1, 4, 495⟩, ⟨2, 4, 277⟩], triples := #[⟨0, 1, 2⟩] }
def er178_205 : Row := { vars := #[48, 237, 294, 369], coeff := #[1, 1, 1, 1], bound := 2, weight := 324401, edges := #[⟨1, 3, 133⟩, ⟨2, 3, 426⟩], triples := #[⟨0, 1, 2⟩] }
def er178_206 : Row := { vars := #[50, 164, 367, 238], coeff := #[1, 1, 1, 1], bound := 2, weight := 820029, edges := #[⟨1, 3, 290⟩, ⟨2, 3, 140⟩], triples := #[⟨0, 1, 2⟩] }
def er178_207 : Row := { vars := #[51, 149, 378, 252], coeff := #[1, 1, 1, 1], bound := 2, weight := 992384, edges := #[⟨0, 3, 299⟩, ⟨2, 3, 432⟩], triples := #[⟨0, 1, 2⟩] }
def er178_208 : Row := { vars := #[55, 133, 349, 132, 319], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 185050, edges := #[⟨3, 4, 132⟩, ⟨0, 3, 458⟩, ⟨1, 3, 218⟩, ⟨0, 4, 248⟩, ⟨1, 4, 134⟩], triples := #[⟨0, 1, 2⟩] }
def er178_209 : Row := { vars := #[61, 206, 271, 353, 287], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 89986, edges := #[⟨3, 4, 436⟩, ⟨1, 3, 145⟩, ⟨2, 3, 411⟩, ⟨1, 4, 120⟩, ⟨2, 4, 403⟩], triples := #[⟨0, 1, 2⟩] }
def er178_210 : Row := { vars := #[61, 216, 279, 58], coeff := #[1, 1, 1, 1], bound := 2, weight := 82370, edges := #[⟨0, 3, 105⟩, ⟨1, 3, 381⟩], triples := #[⟨0, 1, 2⟩] }
def er178_211 : Row := { vars := #[62, 221, 309, 117], coeff := #[1, 1, 1, 1], bound := 2, weight := 516785, edges := #[⟨0, 3, 458⟩, ⟨1, 3, 290⟩], triples := #[⟨0, 1, 2⟩] }
def er178_212 : Row := { vars := #[63, 232, 294, 298], coeff := #[1, 1, 1, 1], bound := 2, weight := 351199, edges := #[⟨0, 3, 316⟩, ⟨1, 3, 122⟩], triples := #[⟨0, 1, 2⟩] }
def er178_213 : Row := { vars := #[74, 177, 271, 287, 174], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 357405, edges := #[⟨3, 4, 183⟩, ⟨0, 3, 276⟩, ⟨2, 3, 403⟩, ⟨0, 4, 357⟩, ⟨2, 4, 166⟩], triples := #[⟨0, 1, 2⟩] }
def er178_214 : Row := { vars := #[83, 128, 316, 320, 34], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 724965, edges := #[⟨3, 4, 317⟩, ⟨0, 3, 203⟩, ⟨1, 3, 147⟩, ⟨1, 4, 384⟩, ⟨2, 4, 329⟩], triples := #[⟨0, 1, 2⟩] }
def er178_215 : Row := { vars := #[83, 128, 316, 305, 69], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 185050, edges := #[⟨3, 4, 340⟩, ⟨0, 3, 258⟩, ⟨1, 3, 13⟩, ⟨1, 4, 469⟩, ⟨2, 4, 275⟩], triples := #[⟨0, 1, 2⟩] }
def er178_216 : Row := { vars := #[84, 179, 246, 196], coeff := #[1, 1, 1, 1], bound := 2, weight := 185050, edges := #[⟨1, 3, 262⟩, ⟨2, 3, 171⟩], triples := #[⟨0, 1, 2⟩] }
def er178_217 : Row := { vars := #[85, 149, 338, 276], coeff := #[1, 1, 1, 1], bound := 2, weight := 722426, edges := #[⟨0, 3, 245⟩, ⟨2, 3, 480⟩], triples := #[⟨0, 1, 2⟩] }
def er178_218 : Row := { vars := #[89, 171, 261, 86, 40], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 179972, edges := #[⟨3, 4, 119⟩, ⟨0, 3, 165⟩, ⟨2, 3, 246⟩, ⟨1, 4, 475⟩, ⟨2, 4, 224⟩], triples := #[⟨0, 1, 2⟩] }
def er178_219 : Row := { vars := #[133, 193, 239, 299, 222], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 89986, edges := #[⟨3, 4, 73⟩, ⟨0, 3, 20⟩, ⟨1, 3, 153⟩, ⟨0, 4, 284⟩, ⟨1, 4, 229⟩], triples := #[⟨0, 1, 2⟩] }
def er178_220 : Row := { vars := #[133, 193, 239, 185, 351], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 28491, edges := #[⟨3, 4, 37⟩, ⟨0, 3, 338⟩, ⟨2, 3, 206⟩, ⟨0, 4, 94⟩, ⟨1, 4, 57⟩], triples := #[⟨0, 1, 2⟩] }
def er178_221 : Row := { vars := #[133, 193, 239, 238, 117], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 66573, edges := #[⟨3, 4, 254⟩, ⟨0, 3, 268⟩, ⟨1, 3, 219⟩, ⟨0, 4, 194⟩, ⟨1, 4, 332⟩], triples := #[⟨0, 1, 2⟩] }
def er178_222 : Row := { vars := #[133, 203, 229, 321, 298], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 409874, edges := #[⟨3, 4, 484⟩, ⟨0, 3, 135⟩, ⟨2, 3, 38⟩, ⟨0, 4, 21⟩, ⟨2, 4, 94⟩], triples := #[⟨0, 1, 2⟩] }
def er178_223 : Row := { vars := #[133, 204, 228, 198, 109], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 179972, edges := #[⟨3, 4, 329⟩, ⟨0, 3, 310⟩, ⟨2, 3, 195⟩, ⟨0, 4, 203⟩, ⟨1, 4, 312⟩], triples := #[⟨0, 1, 2⟩] }
def er178_224 : Row := { vars := #[133, 204, 228, 119, 197], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 211002, edges := #[⟨3, 4, 327⟩, ⟨0, 3, 192⟩, ⟨2, 3, 278⟩, ⟨0, 4, 312⟩, ⟨2, 4, 203⟩], triples := #[⟨0, 1, 2⟩] }
def er178_225 : Row := { vars := #[136, 177, 216, 58], coeff := #[1, 1, 1, 1], bound := 2, weight := 642596, edges := #[⟨1, 3, 411⟩, ⟨2, 3, 381⟩], triples := #[⟨0, 1, 2⟩] }
def er178_226 : Row := { vars := #[164, 203, 241, 201, 196], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 179972, edges := #[⟨3, 4, 282⟩, ⟨0, 3, 344⟩, ⟨1, 3, 290⟩, ⟨0, 4, 338⟩, ⟨1, 4, 284⟩], triples := #[⟨0, 1, 2⟩] }
def er178_227 : Row := { vars := #[179, 193, 202, 227, 222], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 814951, edges := #[⟨3, 4, 314⟩, ⟨1, 3, 232⟩, ⟨2, 3, 218⟩, ⟨1, 4, 229⟩, ⟨2, 4, 206⟩], triples := #[⟨0, 1, 2⟩] }
def er178_228 : Row := { vars := #[264, 318, 361, 317], coeff := #[1, 1, 1, 1], bound := 2, weight := 539916, edges := #[⟨0, 3, 465⟩, ⟨2, 3, 380⟩], triples := #[⟨0, 1, 2⟩] }
def er178_229 : Row := { vars := #[266, 288, 309, 12], coeff := #[1, 1, 1, 1], bound := 2, weight := 258393, edges := #[⟨1, 3, 228⟩, ⟨2, 3, 207⟩], triples := #[⟨0, 1, 2⟩] }
def er178_230 : Row := { vars := #[271, 334, 382, 340, 323], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 2539, edges := #[⟨3, 4, 434⟩, ⟨0, 3, 486⟩, ⟨1, 3, 413⟩, ⟨0, 4, 464⟩, ⟨1, 4, 448⟩], triples := #[⟨0, 1, 2⟩] }
def er178_231 : Row := { vars := #[271, 334, 382, 360, 377], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 2539, edges := #[⟨3, 4, 487⟩, ⟨0, 3, 410⟩, ⟨2, 3, 480⟩, ⟨0, 4, 432⟩, ⟨1, 4, 381⟩], triples := #[⟨0, 1, 2⟩] }
def er178_232 : Row := { vars := #[271, 344, 372, 277, 343], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 2539, edges := #[⟨3, 4, 469⟩, ⟨0, 3, 356⟩, ⟨1, 3, 471⟩, ⟨0, 4, 480⟩, ⟨2, 4, 371⟩], triples := #[⟨0, 1, 2⟩] }
def er178_233 : Row := { vars := #[271, 346, 370, 158, 340], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 542455, edges := #[⟨3, 4, 183⟩, ⟨0, 3, 33⟩, ⟨2, 3, 107⟩, ⟨0, 4, 486⟩, ⟨2, 4, 380⟩], triples := #[⟨0, 1, 2⟩] }
def er178_234 : Row := { vars := #[324, 335, 344, 380, 377], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 997462, edges := #[⟨3, 4, 511⟩, ⟨1, 3, 371⟩, ⟨2, 3, 400⟩, ⟨1, 4, 383⟩, ⟨2, 4, 403⟩], triples := #[⟨0, 1, 2⟩] }
def er178_235 : Row := { vars := #[361, 372, 381, 329, 332], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 460085, edges := #[⟨3, 4, 433⟩, ⟨1, 3, 393⟩, ⟨2, 3, 382⟩, ⟨1, 4, 390⟩, ⟨2, 4, 370⟩], triples := #[⟨0, 1, 2⟩] }
def er178_236 : Row := { vars := #[10], coeff := #[1], bound := 1, weight := 539916, edges := #[], triples := #[] }
def er178_237 : Row := { vars := #[35], coeff := #[1], bound := 1, weight := 357405, edges := #[], triples := #[] }
def er178_238 : Row := { vars := #[42], coeff := #[1], bound := 1, weight := 814951, edges := #[], triples := #[] }
def er178_239 : Row := { vars := #[48], coeff := #[1], bound := 1, weight := 675600, edges := #[], triples := #[] }
def er178_240 : Row := { vars := #[56], coeff := #[1], bound := 1, weight := 786742, edges := #[], triples := #[] }
def er178_241 : Row := { vars := #[57], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_242 : Row := { vars := #[62], coeff := #[1], bound := 1, weight := 483216, edges := #[], triples := #[] }
def er178_243 : Row := { vars := #[63], coeff := #[1], bound := 1, weight := 648802, edges := #[], triples := #[] }
def er178_244 : Row := { vars := #[66], coeff := #[1], bound := 1, weight := 814951, edges := #[], triples := #[] }
def er178_245 : Row := { vars := #[74], coeff := #[1], bound := 1, weight := 489140, edges := #[], triples := #[] }
def er178_246 : Row := { vars := #[75], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_247 : Row := { vars := #[76], coeff := #[1], bound := 1, weight := 447391, edges := #[], triples := #[] }
def er178_248 : Row := { vars := #[78], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_249 : Row := { vars := #[82], coeff := #[1], bound := 1, weight := 460085, edges := #[], triples := #[] }
def er178_250 : Row := { vars := #[85], coeff := #[1], bound := 1, weight := 277575, edges := #[], triples := #[] }
def er178_251 : Row := { vars := #[91], coeff := #[1], bound := 1, weight := 629902, edges := #[], triples := #[] }
def er178_252 : Row := { vars := #[92], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_253 : Row := { vars := #[94], coeff := #[1], bound := 1, weight := 195205, edges := #[], triples := #[] }
def er178_254 : Row := { vars := #[95], coeff := #[1], bound := 1, weight := 737659, edges := #[], triples := #[] }
def er178_255 : Row := { vars := #[96], coeff := #[1], bound := 1, weight := 54161, edges := #[], triples := #[] }
end HardyCapset20261020.Cert


