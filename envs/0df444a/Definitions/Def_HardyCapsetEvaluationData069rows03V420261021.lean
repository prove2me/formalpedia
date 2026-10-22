-- Prove2me | Definitions.Def_HardyCapsetEvaluationData069rows03V420261021
-- name    : HardyCapsetEvaluationData069rows03V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:43:34.513727+00:00
-- url     : https://prove2.me/theorems/6c2b151a-ef6a-4fe3-aac3-02f0ad866d64
-- title:
--   HardyCapsetEvaluationData069rows03V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er069_192 : Row := { vars := #[71, 266, 315], coeff := #[1, 1, 1], bound := 1, weight := 60976, edges := #[⟨0, 1, 384⟩, ⟨0, 2, 315⟩, ⟨1, 2, 119⟩], triples := #[] }
def er069_193 : Row := { vars := #[73, 103, 263], coeff := #[1, 1, 1], bound := 1, weight := 725610, edges := #[⟨0, 1, 45⟩, ⟨0, 2, 386⟩, ⟨1, 2, 494⟩], triples := #[] }
def er069_194 : Row := { vars := #[77, 197, 245], coeff := #[1, 1, 1], bound := 1, weight := 725610, edges := #[⟨0, 1, 415⟩, ⟨0, 2, 392⟩, ⟨1, 2, 206⟩], triples := #[] }
def er069_195 : Row := { vars := #[78, 99, 377, 411], coeff := #[1, 1, 1, 1], bound := 1, weight := 713415, edges := #[⟨0, 1, 22⟩, ⟨0, 2, 295⟩, ⟨0, 3, 209⟩, ⟨1, 2, 233⟩, ⟨1, 3, 340⟩, ⟨2, 3, 373⟩], triples := #[] }
def er069_196 : Row := { vars := #[79, 199, 254], coeff := #[1, 1, 1], bound := 1, weight := 109757, edges := #[⟨0, 1, 413⟩, ⟨0, 2, 383⟩, ⟨1, 2, 225⟩], triples := #[] }
def er069_197 : Row := { vars := #[80, 188, 431], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 490⟩, ⟨0, 2, 242⟩, ⟨1, 2, 126⟩], triples := #[] }
def er069_198 : Row := { vars := #[81, 87, 179, 323, 293], coeff := #[1, 1, 1, 1, 1], bound := 1, weight := 786586, edges := #[⟨0, 1, 123⟩, ⟨0, 2, 509⟩, ⟨0, 3, 345⟩, ⟨0, 4, 325⟩, ⟨1, 2, 499⟩, ⟨1, 3, 335⟩, ⟨1, 4, 315⟩, ⟨2, 3, 36⟩, ⟨2, 4, 0⟩, ⟨3, 4, 384⟩], triples := #[] }
def er069_199 : Row := { vars := #[82, 192, 344], coeff := #[1, 1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 426⟩, ⟨0, 2, 266⟩, ⟨1, 2, 72⟩], triples := #[] }
def er069_200 : Row := { vars := #[84, 268, 403], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 383⟩, ⟨0, 2, 208⟩, ⟨1, 2, 175⟩], triples := #[] }
def er069_201 : Row := { vars := #[84, 268, 271], coeff := #[1, 1, 1], bound := 1, weight := 390244, edges := #[⟨0, 1, 383⟩, ⟨0, 2, 379⟩, ⟨1, 2, 326⟩], triples := #[] }
def er069_202 : Row := { vars := #[85, 338, 139], coeff := #[1, 1, 1], bound := 1, weight := 725610, edges := #[⟨0, 1, 350⟩, ⟨0, 2, 67⟩, ⟨1, 2, 294⟩], triples := #[] }
def er069_203 : Row := { vars := #[86, 388, 391], coeff := #[1, 1, 1], bound := 1, weight := 323171, edges := #[⟨0, 1, 295⟩, ⟨0, 2, 291⟩, ⟨1, 2, 456⟩], triples := #[] }
def er069_204 : Row := { vars := #[86, 99, 408, 377], coeff := #[1, 1, 1, 1], bound := 1, weight := 286586, edges := #[⟨0, 1, 7⟩, ⟨0, 2, 209⟩, ⟨0, 3, 285⟩, ⟨1, 2, 350⟩, ⟨1, 3, 233⟩, ⟨2, 3, 353⟩], triples := #[] }
def er069_205 : Row := { vars := #[86, 171, 225], coeff := #[1, 1, 1], bound := 1, weight := 390244, edges := #[⟨0, 1, 500⟩, ⟨0, 2, 445⟩, ⟨1, 2, 330⟩], triples := #[] }
def er069_206 : Row := { vars := #[87, 419, 112], coeff := #[1, 1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 219⟩, ⟨0, 2, 34⟩, ⟨1, 2, 345⟩], triples := #[] }
def er069_207 : Row := { vars := #[90, 330, 244], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 255⟩, ⟨0, 2, 458⟩, ⟨1, 2, 109⟩], triples := #[] }
def er069_208 : Row := { vars := #[91, 165, 317], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 438⟩, ⟨0, 2, 278⟩, ⟨1, 2, 4⟩], triples := #[] }
def er069_209 : Row := { vars := #[92, 166, 318], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 439⟩, ⟨0, 2, 279⟩, ⟨1, 2, 7⟩], triples := #[] }
def er069_210 : Row := { vars := #[97, 261, 264], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 499⟩, ⟨0, 2, 495⟩, ⟨1, 2, 318⟩], triples := #[] }
def er069_211 : Row := { vars := #[102, 290, 202, 346], coeff := #[1, 1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 469⟩, ⟨0, 2, 402⟩, ⟨0, 3, 223⟩, ⟨1, 2, 209⟩, ⟨1, 3, 19⟩, ⟨2, 3, 120⟩], triples := #[] }
def er069_212 : Row := { vars := #[103, 391, 125], coeff := #[1, 1, 1], bound := 1, weight := 274391, edges := #[⟨0, 1, 227⟩, ⟨0, 2, 183⟩, ⟨1, 2, 212⟩], triples := #[] }
def er069_213 : Row := { vars := #[104, 339, 198], coeff := #[1, 1, 1], bound := 1, weight := 725610, edges := #[⟨0, 1, 271⟩, ⟨0, 2, 380⟩, ⟨1, 2, 179⟩], triples := #[] }
def er069_214 : Row := { vars := #[105, 257, 409], coeff := #[1, 1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 502⟩, ⟨0, 2, 342⟩, ⟨1, 2, 169⟩], triples := #[] }
def er069_215 : Row := { vars := #[109, 387, 390], coeff := #[1, 1, 1], bound := 1, weight := 560976, edges := #[⟨0, 1, 233⟩, ⟨0, 2, 232⟩, ⟨1, 2, 454⟩], triples := #[] }
def er069_216 : Row := { vars := #[110, 324, 270], coeff := #[1, 1, 1], bound := 1, weight := 396342, edges := #[⟨0, 1, 264⟩, ⟨0, 2, 509⟩, ⟨1, 2, 88⟩], triples := #[] }
def er069_217 : Row := { vars := #[110, 427, 270], coeff := #[1, 1, 1], bound := 1, weight := 603659, edges := #[⟨0, 1, 317⟩, ⟨0, 2, 509⟩, ⟨1, 2, 148⟩], triples := #[] }
def er069_218 : Row := { vars := #[113, 368, 117], coeff := #[1, 1, 1], bound := 1, weight := 890244, edges := #[⟨0, 1, 242⟩, ⟨0, 2, 181⟩, ⟨1, 2, 224⟩], triples := #[] }
def er069_219 : Row := { vars := #[118, 222, 316], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 385⟩, ⟨0, 2, 271⟩, ⟨1, 2, 173⟩], triples := #[] }
def er069_220 : Row := { vars := #[120, 271, 226, 358], coeff := #[1, 1, 1, 1], bound := 1, weight := 603659, edges := #[⟨0, 1, 469⟩, ⟨0, 2, 378⟩, ⟨0, 3, 233⟩, ⟨1, 2, 209⟩, ⟨1, 3, 19⟩, ⟨2, 3, 72⟩], triples := #[] }
def er069_221 : Row := { vars := #[123, 397, 433], coeff := #[1, 1, 1], bound := 1, weight := 390244, edges := #[⟨0, 1, 335⟩, ⟨0, 2, 298⟩, ⟨1, 2, 485⟩], triples := #[] }
def er069_222 : Row := { vars := #[125, 265, 226, 358], coeff := #[1, 1, 1, 1], bound := 1, weight := 6098, edges := #[⟨0, 1, 469⟩, ⟨0, 2, 366⟩, ⟨0, 3, 230⟩, ⟨1, 2, 221⟩, ⟨1, 3, 27⟩, ⟨2, 3, 72⟩], triples := #[] }
def er069_223 : Row := { vars := #[127, 365, 134], coeff := #[1, 1, 1], bound := 1, weight := 786586, edges := #[⟨0, 1, 227⟩, ⟨0, 2, 141⟩, ⟨1, 2, 201⟩], triples := #[] }
def er069_224 : Row := { vars := #[130, 193, 249], coeff := #[1, 1, 1], bound := 1, weight := 396342, edges := #[⟨0, 1, 392⟩, ⟨0, 2, 469⟩, ⟨1, 2, 206⟩], triples := #[] }
def er069_225 : Row := { vars := #[131, 172, 434], coeff := #[1, 1, 1], bound := 1, weight := 548781, edges := #[⟨0, 1, 457⟩, ⟨0, 2, 339⟩, ⟨1, 2, 130⟩], triples := #[] }
def er069_226 : Row := { vars := #[133, 210, 351], coeff := #[1, 1, 1], bound := 1, weight := 500001, edges := #[⟨0, 1, 371⟩, ⟨0, 2, 221⟩, ⟨1, 2, 117⟩], triples := #[] }
def er069_227 : Row := { vars := #[135, 399, 345], coeff := #[1, 1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 309⟩, ⟨0, 2, 229⟩, ⟨1, 2, 378⟩], triples := #[] }
def er069_228 : Row := { vars := #[137, 306, 354], coeff := #[1, 1, 1], bound := 1, weight := 286586, edges := #[⟨0, 1, 273⟩, ⟨0, 2, 211⟩, ⟨1, 2, 494⟩], triples := #[] }
def er069_229 : Row := { vars := #[141, 331, 143], coeff := #[1, 1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 0⟩, ⟨0, 2, 196⟩, ⟨1, 2, 5⟩], triples := #[] }
def er069_230 : Row := { vars := #[149, 178, 151], coeff := #[1, 1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 233⟩, ⟨0, 2, 208⟩, ⟨1, 2, 232⟩], triples := #[] }
def er069_231 : Row := { vars := #[152, 252, 336], coeff := #[1, 1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 294⟩, ⟨0, 2, 16⟩, ⟨1, 2, 103⟩], triples := #[] }
def er069_232 : Row := { vars := #[155, 173, 339], coeff := #[1, 1, 1], bound := 1, weight := 274391, edges := #[⟨0, 1, 228⟩, ⟨0, 2, 30⟩, ⟨1, 2, 57⟩], triples := #[] }
def er069_233 : Row := { vars := #[156, 178, 158], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 230⟩, ⟨0, 2, 220⟩, ⟨1, 2, 229⟩], triples := #[] }
def er069_234 : Row := { vars := #[161, 432, 275], coeff := #[1, 1, 1], bound := 1, weight := 609757, edges := #[⟨0, 1, 72⟩, ⟨0, 2, 244⟩, ⟨1, 2, 181⟩], triples := #[] }
def er069_235 : Row := { vars := #[161, 199, 358], coeff := #[1, 1, 1], bound := 1, weight := 390244, edges := #[⟨0, 1, 309⟩, ⟨0, 2, 169⟩, ⟨1, 2, 108⟩], triples := #[] }
def er069_236 : Row := { vars := #[167, 269, 93], coeff := #[1, 1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 261⟩, ⟨0, 2, 451⟩, ⟨1, 2, 490⟩], triples := #[] }
def er069_237 : Row := { vars := #[168, 430, 444], coeff := #[1, 1, 1], bound := 1, weight := 170732, edges := #[⟨0, 1, 72⟩, ⟨0, 2, 88⟩, ⟨1, 2, 501⟩], triples := #[] }
def er069_238 : Row := { vars := #[168, 314, 375], coeff := #[1, 1, 1], bound := 1, weight := 554879, edges := #[⟨0, 1, 1⟩, ⟨0, 2, 133⟩, ⟨1, 2, 458⟩], triples := #[] }
def er069_239 : Row := { vars := #[168, 341, 363], coeff := #[1, 1, 1], bound := 1, weight := 274391, edges := #[⟨0, 1, 180⟩, ⟨0, 2, 179⟩, ⟨1, 2, 457⟩], triples := #[] }
def er069_240 : Row := { vars := #[171, 397, 225], coeff := #[1, 1, 1], bound := 1, weight := 109757, edges := #[⟨0, 1, 108⟩, ⟨0, 2, 330⟩, ⟨1, 2, 1⟩], triples := #[] }
def er069_241 : Row := { vars := #[172, 332, 200], coeff := #[1, 1, 1], bound := 1, weight := 6098, edges := #[⟨0, 1, 37⟩, ⟨0, 2, 298⟩, ⟨1, 2, 132⟩], triples := #[] }
def er069_242 : Row := { vars := #[173, 333, 284], coeff := #[1, 1, 1], bound := 1, weight := 725610, edges := #[⟨0, 1, 42⟩, ⟨0, 2, 296⟩, ⟨1, 2, 128⟩], triples := #[] }
def er069_243 : Row := { vars := #[179, 428, 365], coeff := #[1, 1, 1], bound := 1, weight := 213415, edges := #[⟨0, 1, 120⟩, ⟨0, 2, 158⟩, ⟨1, 2, 381⟩], triples := #[] }
def er069_244 : Row := { vars := #[180, 352, 442], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 132⟩, ⟨0, 2, 126⟩, ⟨1, 2, 368⟩], triples := #[] }
def er069_245 : Row := { vars := #[181, 355, 404], coeff := #[1, 1, 1], bound := 1, weight := 664635, edges := #[⟨0, 1, 136⟩, ⟨0, 2, 78⟩, ⟨1, 2, 387⟩], triples := #[] }
def er069_246 : Row := { vars := #[182, 356, 404], coeff := #[1, 1, 1], bound := 1, weight := 170732, edges := #[⟨0, 1, 139⟩, ⟨0, 2, 75⟩, ⟨1, 2, 386⟩], triples := #[] }
def er069_247 : Row := { vars := #[182, 404, 424], coeff := #[1, 1, 1], bound := 1, weight := 54879, edges := #[⟨0, 1, 75⟩, ⟨0, 2, 90⟩, ⟨1, 2, 478⟩], triples := #[] }
def er069_248 : Row := { vars := #[184, 385, 326], coeff := #[1, 1, 1], bound := 1, weight := 164635, edges := #[⟨0, 1, 186⟩, ⟨0, 2, 66⟩, ⟨1, 2, 511⟩], triples := #[] }
def er069_249 : Row := { vars := #[184, 404, 415], coeff := #[1, 1, 1], bound := 1, weight := 109757, edges := #[⟨0, 1, 103⟩, ⟨0, 2, 90⟩, ⟨1, 2, 488⟩], triples := #[] }
def er069_250 : Row := { vars := #[191, 218, 221], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 285⟩, ⟨0, 2, 281⟩, ⟨1, 2, 274⟩], triples := #[] }
def er069_251 : Row := { vars := #[192, 21, 344], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 486⟩, ⟨0, 2, 72⟩, ⟨1, 2, 326⟩], triples := #[] }
def er069_252 : Row := { vars := #[193, 376, 324], coeff := #[1, 1, 1], bound := 1, weight := 603659, edges := #[⟨0, 1, 109⟩, ⟨0, 2, 168⟩, ⟨1, 2, 490⟩], triples := #[] }
def er069_253 : Row := { vars := #[194, 354, 364], coeff := #[1, 1, 1], bound := 1, weight := 487805, edges := #[⟨0, 1, 120⟩, ⟨0, 2, 130⟩, ⟨1, 2, 434⟩], triples := #[] }
def er069_254 : Row := { vars := #[194, 325, 391], coeff := #[1, 1, 1], bound := 1, weight := 176830, edges := #[⟨0, 1, 169⟩, ⟨0, 2, 113⟩, ⟨1, 2, 500⟩], triples := #[] }
def er069_255 : Row := { vars := #[194, 430, 437], coeff := #[1, 1, 1], bound := 1, weight := 225610, edges := #[⟨0, 1, 1⟩, ⟨0, 2, 29⟩, ⟨1, 2, 511⟩], triples := #[] }
end HardyCapset20261020.Cert


