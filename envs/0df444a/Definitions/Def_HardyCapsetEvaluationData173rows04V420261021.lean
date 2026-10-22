-- Prove2me | Definitions.Def_HardyCapsetEvaluationData173rows04V420261021
-- name    : HardyCapsetEvaluationData173rows04V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T03:08:16.759337+00:00
-- url     : https://prove2.me/theorems/7787e865-9f50-480a-8f22-30e39c61d472
-- title:
--   HardyCapsetEvaluationData173rows04V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er173_256 : Row := { vars := #[120, 125, 278], coeff := #[1, 1, 1], bound := 1, weight := 509779, edges := #[⟨0, 1, 96⟩, ⟨0, 2, 10⟩, ⟨1, 2, 2⟩], triples := #[] }
def er173_257 : Row := { vars := #[121, 648, 437], coeff := #[1, 1, 1], bound := 1, weight := 274570, edges := #[⟨0, 1, 197⟩, ⟨0, 2, 375⟩, ⟨1, 2, 150⟩], triples := #[] }
def er173_258 : Row := { vars := #[121, 126, 254], coeff := #[1, 1, 1], bound := 1, weight := 438707, edges := #[⟨0, 1, 97⟩, ⟨0, 2, 47⟩, ⟨1, 2, 39⟩], triples := #[] }
def er173_259 : Row := { vars := #[121, 126, 255], coeff := #[1, 1, 1], bound := 1, weight := 286725, edges := #[⟨0, 1, 97⟩, ⟨0, 2, 46⟩, ⟨1, 2, 38⟩], triples := #[] }
def er173_260 : Row := { vars := #[123, 426, 244], coeff := #[1, 1, 1], bound := 1, weight := 351956, edges := #[⟨0, 1, 415⟩, ⟨0, 2, 54⟩, ⟨1, 2, 353⟩], triples := #[] }
def er173_261 : Row := { vars := #[124, 142, 367, 488, 457, 438], coeff := #[1, 1, 1, 1, 1, 1], bound := 1, weight := 274975, edges := #[⟨0, 1, 74⟩, ⟨0, 2, 408⟩, ⟨0, 3, 393⟩, ⟨0, 4, 403⟩, ⟨0, 5, 381⟩, ⟨1, 2, 406⟩, ⟨1, 3, 390⟩, ⟨1, 4, 400⟩, ⟨1, 5, 369⟩, ⟨2, 3, 232⟩, ⟨2, 4, 242⟩, ⟨2, 5, 217⟩, ⟨3, 4, 301⟩, ⟨3, 5, 311⟩, ⟨4, 5, 333⟩], triples := #[] }
def er173_262 : Row := { vars := #[124, 142, 367, 357, 440, 439], coeff := #[1, 1, 1, 1, 1, 1], bound := 1, weight := 29436, edges := #[⟨0, 1, 74⟩, ⟨0, 2, 408⟩, ⟨0, 3, 413⟩, ⟨0, 4, 382⟩, ⟨0, 5, 383⟩, ⟨1, 2, 406⟩, ⟨1, 3, 410⟩, ⟨1, 4, 370⟩, ⟨1, 5, 371⟩, ⟨2, 3, 252⟩, ⟨2, 4, 218⟩, ⟨2, 5, 219⟩, ⟨3, 4, 196⟩, ⟨3, 5, 198⟩, ⟨4, 5, 301⟩], triples := #[] }
def er173_263 : Row := { vars := #[124, 547, 562, 615], coeff := #[1, 1, 1, 1], bound := 1, weight := 559019, edges := #[⟨0, 1, 349⟩, ⟨0, 2, 327⟩, ⟨0, 3, 275⟩, ⟨1, 2, 354⟩, ⟨1, 3, 460⟩, ⟨2, 3, 492⟩], triples := #[] }
def er173_264 : Row := { vars := #[125, 448, 376, 143], coeff := #[1, 1, 1, 1], bound := 1, weight := 490222, edges := #[⟨0, 1, 363⟩, ⟨0, 2, 454⟩, ⟨0, 3, 75⟩, ⟨1, 2, 242⟩, ⟨1, 3, 355⟩, ⟨2, 3, 448⟩], triples := #[] }
def er173_265 : Row := { vars := #[127, 267, 143], coeff := #[1, 1, 1], bound := 1, weight := 208128, edges := #[⟨0, 1, 24⟩, ⟨0, 2, 79⟩, ⟨1, 2, 9⟩], triples := #[] }
def er173_266 : Row := { vars := #[127, 144, 245], coeff := #[1, 1, 1], bound := 1, weight := 19358, edges := #[⟨0, 1, 78⟩, ⟨0, 2, 60⟩, ⟨1, 2, 45⟩], triples := #[] }
def er173_267 : Row := { vars := #[127, 463, 366], coeff := #[1, 1, 1], bound := 1, weight := 84110, edges := #[⟨0, 1, 400⟩, ⟨0, 2, 409⟩, ⟨1, 2, 240⟩], triples := #[] }
def er173_268 : Row := { vars := #[127, 362, 246], coeff := #[1, 1, 1], bound := 1, weight := 688406, edges := #[⟨0, 1, 410⟩, ⟨0, 2, 61⟩, ⟨1, 2, 398⟩], triples := #[] }
def er173_269 : Row := { vars := #[128, 139, 273], coeff := #[1, 1, 1], bound := 1, weight := 307179, edges := #[⟨0, 1, 74⟩, ⟨0, 2, 10⟩, ⟨1, 2, 33⟩], triples := #[] }
def er173_270 : Row := { vars := #[128, 139, 312], coeff := #[1, 1, 1], bound := 1, weight := 474900, edges := #[⟨0, 1, 74⟩, ⟨0, 2, 460⟩, ⟨1, 2, 465⟩], triples := #[] }
def er173_271 : Row := { vars := #[128, 275, 443], coeff := #[1, 1, 1], bound := 1, weight := 217923, edges := #[⟨0, 1, 8⟩, ⟨0, 2, 368⟩, ⟨1, 2, 469⟩], triples := #[] }
def er173_272 : Row := { vars := #[129, 140, 338, 453], coeff := #[1, 1, 1, 1], bound := 1, weight := 690719, edges := #[⟨0, 1, 75⟩, ⟨0, 2, 488⟩, ⟨0, 3, 355⟩, ⟨1, 2, 478⟩, ⟨1, 3, 375⟩, ⟨2, 3, 261⟩], triples := #[] }
def er173_273 : Row := { vars := #[129, 295, 301], coeff := #[1, 1, 1], bound := 1, weight := 37807, edges := #[⟨0, 1, 464⟩, ⟨0, 2, 463⟩, ⟨1, 2, 211⟩], triples := #[] }
def er173_274 : Row := { vars := #[130, 144, 317], coeff := #[1, 1, 1], bound := 1, weight := 262906, edges := #[⟨0, 1, 79⟩, ⟨0, 2, 508⟩, ⟨1, 2, 501⟩], triples := #[] }
def er173_275 : Row := { vars := #[130, 276, 252], coeff := #[1, 1, 1], bound := 1, weight := 75856, edges := #[⟨0, 1, 5⟩, ⟨0, 2, 45⟩, ⟨1, 2, 167⟩], triples := #[] }
def er173_276 : Row := { vars := #[130, 95, 136], coeff := #[1, 1, 1], bound := 1, weight := 661240, edges := #[⟨0, 1, 170⟩, ⟨0, 2, 84⟩, ⟨1, 2, 178⟩], triples := #[] }
def er173_277 : Row := { vars := #[131, 173, 379], coeff := #[1, 1, 1], bound := 1, weight := 237060, edges := #[⟨0, 1, 118⟩, ⟨0, 2, 457⟩, ⟨1, 2, 405⟩], triples := #[] }
def er173_278 : Row := { vars := #[132, 432, 590], coeff := #[1, 1, 1], bound := 1, weight := 751831, edges := #[⟨0, 1, 414⟩, ⟨0, 2, 290⟩, ⟨1, 2, 96⟩], triples := #[] }
def er173_279 : Row := { vars := #[133, 400, 614], coeff := #[1, 1, 1], bound := 1, weight := 536638, edges := #[⟨0, 1, 436⟩, ⟨0, 2, 268⟩, ⟨1, 2, 97⟩], triples := #[] }
def er173_280 : Row := { vars := #[133, 318, 599], coeff := #[1, 1, 1], bound := 1, weight := 225676, edges := #[⟨0, 1, 506⟩, ⟨0, 2, 283⟩, ⟨1, 2, 179⟩], triples := #[] }
def er173_281 : Row := { vars := #[133, 238, 148], coeff := #[1, 1, 1], bound := 1, weight := 21058, edges := #[⟨0, 1, 65⟩, ⟨0, 2, 84⟩, ⟨1, 2, 55⟩], triples := #[] }
def er173_282 : Row := { vars := #[145, 584, 268], coeff := #[1, 1, 1], bound := 1, weight := 127614, edges := #[⟨0, 1, 252⟩, ⟨0, 2, 4⟩, ⟨1, 2, 226⟩], triples := #[] }
def er173_283 : Row := { vars := #[145, 560, 55], coeff := #[1, 1, 1], bound := 1, weight := 475378, edges := #[⟨0, 1, 315⟩, ⟨0, 2, 191⟩, ⟨1, 2, 209⟩], triples := #[] }
def er173_284 : Row := { vars := #[145, 152, 694], coeff := #[1, 1, 1], bound := 1, weight := 124312, edges := #[⟨0, 1, 127⟩, ⟨0, 2, 232⟩, ⟨1, 2, 210⟩], triples := #[] }
def er173_285 : Row := { vars := #[145, 373, 411], coeff := #[1, 1, 1], bound := 1, weight := 24528, edges := #[⟨0, 1, 413⟩, ⟨0, 2, 426⟩, ⟨1, 2, 266⟩], triples := #[] }
def er173_286 : Row := { vars := #[146, 261, 244], coeff := #[1, 1, 1], bound := 1, weight := 320106, edges := #[⟨0, 1, 18⟩, ⟨0, 2, 41⟩, ⟨1, 2, 167⟩], triples := #[] }
def er173_287 : Row := { vars := #[146, 441, 454], coeff := #[1, 1, 1], bound := 1, weight := 488559, edges := #[⟨0, 1, 368⟩, ⟨0, 2, 380⟩, ⟨1, 2, 304⟩], triples := #[] }
def er173_288 : Row := { vars := #[147, 560, 299], coeff := #[1, 1, 1], bound := 1, weight := 77293, edges := #[⟨0, 1, 314⟩, ⟨0, 2, 459⟩, ⟨1, 2, 35⟩], triples := #[] }
def er173_289 : Row := { vars := #[148, 546, 499], coeff := #[1, 1, 1], bound := 1, weight := 281462, edges := #[⟨0, 1, 337⟩, ⟨0, 2, 384⟩, ⟨1, 2, 107⟩], triples := #[] }
def er173_290 : Row := { vars := #[149, 151, 478], coeff := #[1, 1, 1], bound := 1, weight := 117742, edges := #[⟨0, 1, 110⟩, ⟨0, 2, 390⟩, ⟨1, 2, 389⟩], triples := #[] }
def er173_291 : Row := { vars := #[149, 158, 364], coeff := #[1, 1, 1], bound := 1, weight := 589251, edges := #[⟨0, 1, 118⟩, ⟨0, 2, 457⟩, ⟨1, 2, 447⟩], triples := #[] }
def er173_292 : Row := { vars := #[149, 165, 197, 199], coeff := #[1, 1, 1, 1], bound := 1, weight := 192115, edges := #[⟨0, 1, 114⟩, ⟨0, 2, 47⟩, ⟨0, 3, 48⟩, ⟨1, 2, 60⟩, ⟨1, 3, 61⟩, ⟨2, 3, 138⟩], triples := #[] }
def er173_293 : Row := { vars := #[149, 165, 398, 511], coeff := #[1, 1, 1, 1], bound := 1, weight := 100894, edges := #[⟨0, 1, 114⟩, ⟨0, 2, 426⟩, ⟨0, 3, 371⟩, ⟨1, 2, 432⟩, ⟨1, 3, 383⟩, ⟨2, 3, 217⟩], triples := #[] }
def er173_294 : Row := { vars := #[150, 166, 488], coeff := #[1, 1, 1], bound := 1, weight := 509779, edges := #[⟨0, 1, 115⟩, ⟨0, 2, 353⟩, ⟨1, 2, 361⟩], triples := #[] }
def er173_295 : Row := { vars := #[150, 375, 429], coeff := #[1, 1, 1], bound := 1, weight := 241173, edges := #[⟨0, 1, 415⟩, ⟨0, 2, 410⟩, ⟨1, 2, 250⟩], triples := #[] }
def er173_296 : Row := { vars := #[151, 257, 460], coeff := #[1, 1, 1], bound := 1, weight := 349735, edges := #[⟨0, 1, 19⟩, ⟨0, 2, 385⟩, ⟨1, 2, 480⟩], triples := #[] }
def er173_297 : Row := { vars := #[152, 161, 378], coeff := #[1, 1, 1], bound := 1, weight := 276905, edges := #[⟨0, 1, 118⟩, ⟨0, 2, 414⟩, ⟨1, 2, 433⟩], triples := #[] }
def er173_298 : Row := { vars := #[153, 286, 309, 644], coeff := #[1, 1, 1, 1], bound := 1, weight := 788164, edges := #[⟨0, 1, 508⟩, ⟨0, 2, 502⟩, ⟨0, 3, 242⟩, ⟨1, 2, 193⟩, ⟨1, 3, 97⟩, ⟨2, 3, 84⟩], triples := #[] }
def er173_299 : Row := { vars := #[154, 287, 566, 310], coeff := #[1, 1, 1, 1], bound := 1, weight := 410750, edges := #[⟨0, 1, 508⟩, ⟨0, 2, 306⟩, ⟨0, 3, 502⟩, ⟨1, 2, 24⟩, ⟨1, 3, 194⟩, ⟨2, 3, 11⟩], triples := #[] }
def er173_300 : Row := { vars := #[154, 296, 305, 586], coeff := #[1, 1, 1, 1], bound := 1, weight := 178927, edges := #[⟨0, 1, 511⟩, ⟨0, 2, 501⟩, ⟨0, 3, 281⟩, ⟨1, 2, 194⟩, ⟨1, 3, 143⟩, ⟨2, 3, 166⟩], triples := #[] }
def er173_301 : Row := { vars := #[155, 512, 643], coeff := #[1, 1, 1], bound := 1, weight := 492918, edges := #[⟨0, 1, 363⟩, ⟨0, 2, 242⟩, ⟨1, 2, 171⟩], triples := #[] }
def er173_302 : Row := { vars := #[155, 286, 177], coeff := #[1, 1, 1], bound := 1, weight := 112424, edges := #[⟨0, 1, 507⟩, ⟨0, 2, 82⟩, ⟨1, 2, 485⟩], triples := #[] }
def er173_303 : Row := { vars := #[156, 538, 447], coeff := #[1, 1, 1], bound := 1, weight := 112275, edges := #[⟨0, 1, 337⟩, ⟨0, 2, 401⟩, ⟨1, 2, 80⟩], triples := #[] }
def er173_304 : Row := { vars := #[156, 201, 203], coeff := #[1, 1, 1], bound := 1, weight := 395500, edges := #[⟨0, 1, 47⟩, ⟨0, 2, 45⟩, ⟨1, 2, 141⟩], triples := #[] }
def er173_305 : Row := { vars := #[157, 213, 231], coeff := #[1, 1, 1], bound := 1, weight := 627662, edges := #[⟨0, 1, 61⟩, ⟨0, 2, 48⟩, ⟨1, 2, 136⟩], triples := #[] }
def er173_306 : Row := { vars := #[159, 256, 477], coeff := #[1, 1, 1], bound := 1, weight := 193620, edges := #[⟨0, 1, 8⟩, ⟨0, 2, 384⟩, ⟨1, 2, 489⟩], triples := #[] }
def er173_307 : Row := { vars := #[160, 92, 224], coeff := #[1, 1, 1], bound := 1, weight := 49379, edges := #[⟨0, 1, 144⟩, ⟨0, 2, 44⟩, ⟨1, 2, 119⟩], triples := #[] }
def er173_308 : Row := { vars := #[160, 223, 94], coeff := #[1, 1, 1], bound := 1, weight := 240054, edges := #[⟨0, 1, 47⟩, ⟨0, 2, 140⟩, ⟨1, 2, 118⟩], triples := #[] }
def er173_309 : Row := { vars := #[160, 383, 387], coeff := #[1, 1, 1], bound := 1, weight := 710569, edges := #[⟨0, 1, 426⟩, ⟨0, 2, 422⟩, ⟨1, 2, 266⟩], triples := #[] }
def er173_310 : Row := { vars := #[161, 174, 378], coeff := #[1, 1, 1], bound := 1, weight := 377415, edges := #[⟨0, 1, 100⟩, ⟨0, 2, 433⟩, ⟨1, 2, 404⟩], triples := #[] }
def er173_311 : Row := { vars := #[162, 390, 379], coeff := #[1, 1, 1], bound := 1, weight := 762941, edges := #[⟨0, 1, 424⟩, ⟨0, 2, 434⟩, ⟨1, 2, 274⟩], triples := #[] }
def er173_312 : Row := { vars := #[162, 235, 205], coeff := #[1, 1, 1], bound := 1, weight := 237060, edges := #[⟨0, 1, 46⟩, ⟨0, 2, 69⟩, ⟨1, 2, 157⟩], triples := #[] }
def er173_313 : Row := { vars := #[163, 391, 500, 351], coeff := #[1, 1, 1, 1], bound := 1, weight := 618319, edges := #[⟨0, 1, 425⟩, ⟨0, 2, 371⟩, ⟨0, 3, 460⟩, ⟨1, 2, 211⟩, ⟨1, 3, 300⟩, ⟨2, 3, 279⟩], triples := #[] }
def er173_314 : Row := { vars := #[163, 391, 284], coeff := #[1, 1, 1], bound := 1, weight := 262315, edges := #[⟨0, 1, 425⟩, ⟨0, 2, 511⟩, ⟨1, 2, 351⟩], triples := #[] }
def er173_315 : Row := { vars := #[164, 392, 362], coeff := #[1, 1, 1], bound := 1, weight := 94521, edges := #[⟨0, 1, 427⟩, ⟨0, 2, 438⟩, ⟨1, 2, 278⟩], triples := #[] }
def er173_316 : Row := { vars := #[164, 392, 382], coeff := #[1, 1, 1], bound := 1, weight := 704617, edges := #[⟨0, 1, 427⟩, ⟨0, 2, 416⟩, ⟨1, 2, 256⟩], triples := #[] }
def er173_317 : Row := { vars := #[164, 684, 371, 225], coeff := #[1, 1, 1, 1], bound := 1, weight := 156589, edges := #[⟨0, 1, 198⟩, ⟨0, 2, 455⟩, ⟨0, 3, 65⟩, ⟨1, 2, 11⟩, ⟨1, 3, 310⟩, ⟨2, 3, 383⟩], triples := #[] }
def er173_318 : Row := { vars := #[164, 685, 333, 95], coeff := #[1, 1, 1, 1], bound := 1, weight := 44276, edges := #[⟨0, 1, 197⟩, ⟨0, 2, 487⟩, ⟨0, 3, 161⟩, ⟨1, 2, 84⟩, ⟨1, 3, 278⟩, ⟨2, 3, 381⟩], triples := #[] }
def er173_319 : Row := { vars := #[168, 401, 309], coeff := #[1, 1, 1], bound := 1, weight := 211837, edges := #[⟨0, 1, 430⟩, ⟨0, 2, 509⟩, ⟨1, 2, 349⟩], triples := #[] }
end HardyCapset20261020.Cert


