-- Prove2me | Definitions.Def_HardyCapsetEvaluationData028rows04V420261021
-- name    : HardyCapsetEvaluationData028rows04V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:22:56.923617+00:00
-- url     : https://prove2.me/theorems/632b774c-171e-407d-bda5-99c519a017e1
-- title:
--   HardyCapsetEvaluationData028rows04V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er028_256 : Row := { vars := #[174, 471, 499, 248], coeff := #[1, 1, 1, 1], bound := 1, weight := 58131, edges := #[⟨0, 1, 196⟩, ⟨0, 2, 200⟩, ⟨0, 3, 392⟩, ⟨1, 2, 444⟩, ⟨1, 3, 106⟩, ⟨2, 3, 83⟩], triples := #[] }
def er028_257 : Row := { vars := #[175, 396, 500], coeff := #[1, 1, 1], bound := 1, weight := 42958, edges := #[⟨0, 1, 462⟩, ⟨0, 2, 202⟩, ⟨1, 2, 67⟩], triples := #[] }
def er028_258 : Row := { vars := #[175, 472, 368], coeff := #[1, 1, 1], bound := 1, weight := 522851, edges := #[⟨0, 1, 198⟩, ⟨0, 2, 461⟩, ⟨1, 2, 39⟩], triples := #[] }
def er028_259 : Row := { vars := #[176, 297, 214], coeff := #[1, 1, 1], bound := 1, weight := 143795, edges := #[⟨0, 1, 370⟩, ⟨0, 2, 137⟩, ⟨1, 2, 396⟩], triples := #[] }
def er028_260 : Row := { vars := #[178, 294, 214], coeff := #[1, 1, 1], bound := 1, weight := 427413, edges := #[⟨0, 1, 370⟩, ⟨0, 2, 134⟩, ⟨1, 2, 397⟩], triples := #[] }
def er028_261 : Row := { vars := #[178, 280, 206], coeff := #[1, 1, 1], bound := 1, weight := 22960, edges := #[⟨0, 1, 382⟩, ⟨0, 2, 152⟩, ⟨1, 2, 401⟩], triples := #[] }
def er028_262 : Row := { vars := #[180, 274, 476], coeff := #[1, 1, 1], bound := 1, weight := 305467, edges := #[⟨0, 1, 387⟩, ⟨0, 2, 214⟩, ⟨1, 2, 96⟩], triples := #[] }
def er028_263 : Row := { vars := #[180, 301, 463], coeff := #[1, 1, 1], bound := 1, weight := 110985, edges := #[⟨0, 1, 362⟩, ⟨0, 2, 226⟩, ⟨1, 2, 86⟩], triples := #[] }
def er028_264 : Row := { vars := #[180, 435, 315], coeff := #[1, 1, 1], bound := 1, weight := 583549, edges := #[⟨0, 1, 231⟩, ⟨0, 2, 358⟩, ⟨1, 2, 96⟩], triples := #[] }
def er028_265 : Row := { vars := #[181, 391, 285], coeff := #[1, 1, 1], bound := 1, weight := 413776, edges := #[⟨0, 1, 462⟩, ⟨0, 2, 375⟩, ⟨1, 2, 243⟩], triples := #[] }
def er028_266 : Row := { vars := #[182, 279, 307, 426], coeff := #[1, 1, 1, 1], bound := 1, weight := 359929, edges := #[⟨0, 1, 372⟩, ⟨0, 2, 352⟩, ⟨0, 3, 232⟩, ⟨1, 2, 284⟩, ⟨1, 3, 86⟩, ⟨2, 3, 96⟩], triples := #[] }
def er028_267 : Row := { vars := #[182, 429, 309], coeff := #[1, 1, 1], bound := 1, weight := 149494, edges := #[⟨0, 1, 231⟩, ⟨0, 2, 358⟩, ⟨1, 2, 93⟩], triples := #[] }
def er028_268 : Row := { vars := #[182, 446, 471], coeff := #[1, 1, 1], bound := 1, weight := 201584, edges := #[⟨0, 1, 228⟩, ⟨0, 2, 212⟩, ⟨1, 2, 412⟩], triples := #[] }
def er028_269 : Row := { vars := #[183, 560, 311], coeff := #[1, 1, 1], bound := 1, weight := 149546, edges := #[⟨0, 1, 305⟩, ⟨0, 2, 358⟩, ⟨1, 2, 57⟩], triples := #[] }
def er028_270 : Row := { vars := #[183, 471, 499, 367], coeff := #[1, 1, 1, 1], bound := 1, weight := 369620, edges := #[⟨0, 1, 215⟩, ⟨0, 2, 195⟩, ⟨0, 3, 466⟩, ⟨1, 2, 444⟩, ⟨1, 3, 50⟩, ⟨2, 3, 60⟩], triples := #[] }
def er028_271 : Row := { vars := #[185, 470, 235], coeff := #[1, 1, 1], bound := 1, weight := 90881, edges := #[⟨0, 1, 209⟩, ⟨0, 2, 388⟩, ⟨1, 2, 85⟩], triples := #[] }
def er028_272 : Row := { vars := #[187, 249, 504], coeff := #[1, 1, 1], bound := 1, weight := 311487, edges := #[⟨0, 1, 387⟩, ⟨0, 2, 217⟩, ⟨1, 2, 74⟩], triples := #[] }
def er028_273 : Row := { vars := #[188, 301, 438], coeff := #[1, 1, 1], bound := 1, weight := 300724, edges := #[⟨0, 1, 354⟩, ⟨0, 2, 228⟩, ⟨1, 2, 106⟩], triples := #[] }
def er028_274 : Row := { vars := #[188, 190, 200, 202], coeff := #[1, 1, 1, 1], bound := 1, weight := 81603, edges := #[⟨0, 1, 176⟩, ⟨0, 2, 145⟩, ⟨0, 3, 142⟩, ⟨1, 2, 137⟩, ⟨1, 3, 134⟩, ⟨2, 3, 186⟩], triples := #[] }
def er028_275 : Row := { vars := #[189, 405, 492], coeff := #[1, 1, 1], bound := 1, weight := 465572, edges := #[⟨0, 1, 465⟩, ⟨0, 2, 198⟩, ⟨1, 2, 47⟩], triples := #[] }
def er028_276 : Row := { vars := #[190, 268, 484], coeff := #[1, 1, 1], bound := 1, weight := 457163, edges := #[⟨0, 1, 391⟩, ⟨0, 2, 198⟩, ⟨1, 2, 75⟩], triples := #[] }
def er028_277 : Row := { vars := #[191, 293, 296, 587], coeff := #[1, 1, 1, 1], bound := 1, weight := 96882, edges := #[⟨0, 1, 359⟩, ⟨0, 2, 355⟩, ⟨0, 3, 306⟩, ⟨1, 2, 284⟩, ⟨1, 3, 50⟩, ⟨2, 3, 47⟩], triples := #[] }
def er028_278 : Row := { vars := #[192, 202, 530, 338], coeff := #[1, 1, 1, 1], bound := 1, weight := 18315, edges := #[⟨0, 1, 188⟩, ⟨0, 2, 305⟩, ⟨0, 3, 465⟩, ⟨1, 2, 302⟩, ⟨1, 3, 462⟩, ⟨2, 3, 174⟩], triples := #[] }
def er028_279 : Row := { vars := #[192, 208, 516, 338], coeff := #[1, 1, 1, 1], bound := 1, weight := 151983, edges := #[⟨0, 1, 186⟩, ⟨0, 2, 301⟩, ⟨0, 3, 465⟩, ⟨1, 2, 302⟩, ⟨1, 3, 460⟩, ⟨2, 3, 176⟩], triples := #[] }
def er028_280 : Row := { vars := #[192, 208, 7, 19], coeff := #[1, 1, 1, 1], bound := 1, weight := 47349, edges := #[⟨0, 1, 186⟩, ⟨0, 2, 86⟩, ⟨0, 3, 103⟩, ⟨1, 2, 96⟩, ⟨1, 3, 75⟩, ⟨2, 3, 27⟩], triples := #[] }
def er028_281 : Row := { vars := #[193, 203, 16, 18], coeff := #[1, 1, 1, 1], bound := 1, weight := 467950, edges := #[⟨0, 1, 189⟩, ⟨0, 2, 105⟩, ⟨0, 3, 102⟩, ⟨1, 2, 95⟩, ⟨1, 3, 92⟩, ⟨2, 3, 18⟩], triples := #[] }
def er028_282 : Row := { vars := #[193, 464, 119], coeff := #[1, 1, 1], bound := 1, weight := 52794, edges := #[⟨0, 1, 205⟩, ⟨0, 2, 51⟩, ⟨1, 2, 248⟩], triples := #[] }
def er028_283 : Row := { vars := #[194, 210, 232, 424], coeff := #[1, 1, 1, 1], bound := 1, weight := 339063, edges := #[⟨0, 1, 186⟩, ⟨0, 2, 388⟩, ⟨0, 3, 228⟩, ⟨1, 2, 391⟩, ⟨1, 3, 231⟩, ⟨2, 3, 98⟩], triples := #[] }
def er028_284 : Row := { vars := #[196, 270, 482, 242], coeff := #[1, 1, 1, 1], bound := 1, weight := 424564, edges := #[⟨0, 1, 362⟩, ⟨0, 2, 243⟩, ⟨0, 3, 358⟩, ⟨1, 2, 76⟩, ⟨1, 3, 266⟩, ⟨2, 3, 104⟩], triples := #[] }
def er028_285 : Row := { vars := #[196, 272, 506], coeff := #[1, 1, 1], bound := 1, weight := 474545, edges := #[⟨0, 1, 360⟩, ⟨0, 2, 238⟩, ⟨1, 2, 107⟩], triples := #[] }
def er028_286 : Row := { vars := #[198, 283, 433], coeff := #[1, 1, 1], bound := 1, weight := 805422, edges := #[⟨0, 1, 396⟩, ⟨0, 2, 192⟩, ⟨1, 2, 79⟩], triples := #[] }
def er028_287 : Row := { vars := #[198, 472, 456], coeff := #[1, 1, 1], bound := 1, weight := 102371, edges := #[⟨0, 1, 237⟩, ⟨0, 2, 202⟩, ⟨1, 2, 409⟩], triples := #[] }
def er028_288 : Row := { vars := #[200, 446, 352], coeff := #[1, 1, 1], bound := 1, weight := 345087, edges := #[⟨0, 1, 211⟩, ⟨0, 2, 461⟩, ⟨1, 2, 12⟩], triples := #[] }
def er028_289 : Row := { vars := #[203, 430, 291], coeff := #[1, 1, 1], bound := 1, weight := 494755, edges := #[⟨0, 1, 221⟩, ⟨0, 2, 398⟩, ⟨1, 2, 105⟩], triples := #[] }
def er028_290 : Row := { vars := #[204, 434, 276, 462], coeff := #[1, 1, 1, 1], bound := 1, weight := 452097, edges := #[⟨0, 1, 214⟩, ⟨0, 2, 403⟩, ⟨0, 3, 194⟩, ⟨1, 2, 79⟩, ⟨1, 3, 426⟩, ⟨2, 3, 94⟩], triples := #[] }
def er028_291 : Row := { vars := #[204, 462, 465, 290], coeff := #[1, 1, 1, 1], bound := 1, weight := 361625, edges := #[⟨0, 1, 194⟩, ⟨0, 2, 198⟩, ⟨0, 3, 400⟩, ⟨1, 2, 432⟩, ⟨1, 3, 76⟩, ⟨2, 3, 79⟩], triples := #[] }
def er028_292 : Row := { vars := #[206, 267, 308], coeff := #[1, 1, 1], bound := 1, weight := 142031, edges := #[⟨0, 1, 358⟩, ⟨0, 2, 396⟩, ⟨1, 2, 252⟩], triples := #[] }
def er028_293 : Row := { vars := #[206, 280, 461], coeff := #[1, 1, 1], bound := 1, weight := 356022, edges := #[⟨0, 1, 401⟩, ⟨0, 2, 196⟩, ⟨1, 2, 94⟩], triples := #[] }
def er028_294 : Row := { vars := #[209, 211, 248, 440], coeff := #[1, 1, 1, 1], bound := 1, weight := 432258, edges := #[⟨0, 1, 189⟩, ⟨0, 2, 354⟩, ⟨0, 3, 194⟩, ⟨1, 2, 358⟩, ⟨1, 3, 198⟩, ⟨2, 3, 114⟩], triples := #[] }
def er028_295 : Row := { vars := #[211, 305, 439], coeff := #[1, 1, 1], bound := 1, weight := 36834, edges := #[⟨0, 1, 401⟩, ⟨0, 2, 205⟩, ⟨1, 2, 92⟩], triples := #[] }
def er028_296 : Row := { vars := #[211, 241, 497], coeff := #[1, 1, 1], bound := 1, weight := 362678, edges := #[⟨0, 1, 369⟩, ⟨0, 2, 241⟩, ⟨1, 2, 95⟩], triples := #[] }
def er028_297 : Row := { vars := #[212, 289, 453], coeff := #[1, 1, 1], bound := 1, weight := 870496, edges := #[⟨0, 1, 398⟩, ⟨0, 2, 192⟩, ⟨1, 2, 107⟩], triples := #[] }
def er028_298 : Row := { vars := #[213, 256, 351], coeff := #[1, 1, 1], bound := 1, weight := 261177, edges := #[⟨0, 1, 357⟩, ⟨0, 2, 460⟩, ⟨1, 2, 230⟩], triples := #[] }
def er028_299 : Row := { vars := #[215, 345, 250], coeff := #[1, 1, 1], bound := 1, weight := 356794, edges := #[⟨0, 1, 460⟩, ⟨0, 2, 357⟩, ⟨1, 2, 229⟩], triples := #[] }
def er028_300 : Row := { vars := #[216, 565, 484], coeff := #[1, 1, 1], bound := 1, weight := 54710, edges := #[⟨0, 1, 84⟩, ⟨0, 2, 165⟩, ⟨1, 2, 402⟩], triples := #[] }
def er028_301 : Row := { vars := #[218, 501, 478], coeff := #[1, 1, 1], bound := 1, weight := 378373, edges := #[⟨0, 1, 145⟩, ⟨0, 2, 164⟩, ⟨1, 2, 440⟩], triples := #[] }
def er028_302 : Row := { vars := #[220, 479, 599], coeff := #[1, 1, 1], bound := 1, weight := 195395, edges := #[⟨0, 1, 152⟩, ⟨0, 2, 104⟩, ⟨1, 2, 400⟩], triples := #[] }
def er028_303 : Row := { vars := #[226, 467, 443], coeff := #[1, 1, 1], bound := 1, weight := 109226, edges := #[⟨0, 1, 162⟩, ⟨0, 2, 146⟩, ⟨1, 2, 416⟩], triples := #[] }
def er028_304 : Row := { vars := #[227, 7, 437, 448], coeff := #[1, 1, 1, 1], bound := 1, weight := 169532, edges := #[⟨0, 1, 369⟩, ⟨0, 2, 153⟩, ⟨0, 3, 138⟩, ⟨1, 2, 310⟩, ⟨1, 3, 321⟩, ⟨2, 3, 432⟩], triples := #[] }
def er028_305 : Row := { vars := #[227, 551, 431], coeff := #[1, 1, 1], bound := 1, weight := 830469, edges := #[⟨0, 1, 105⟩, ⟨0, 2, 156⟩, ⟨1, 2, 389⟩], triples := #[] }
def er028_306 : Row := { vars := #[228, 518, 590], coeff := #[1, 1, 1], bound := 1, weight := 115832, edges := #[⟨0, 1, 51⟩, ⟨0, 2, 24⟩, ⟨1, 2, 463⟩], triples := #[] }
def er028_307 : Row := { vars := #[228, 552, 568], coeff := #[1, 1, 1], bound := 1, weight := 242619, edges := #[⟨0, 1, 58⟩, ⟨0, 2, 6⟩, ⟨1, 2, 464⟩], triples := #[] }
def er028_308 : Row := { vars := #[230, 541, 548], coeff := #[1, 1, 1], bound := 1, weight := 606591, edges := #[⟨0, 1, 58⟩, ⟨0, 2, 47⟩, ⟨1, 2, 471⟩], triples := #[] }
def er028_309 : Row := { vars := #[234, 552, 498], coeff := #[1, 1, 1], bound := 1, weight := 201907, edges := #[⟨0, 1, 22⟩, ⟨0, 2, 97⟩, ⟨1, 2, 372⟩], triples := #[] }
def er028_310 : Row := { vars := #[236, 264, 199, 531], coeff := #[1, 1, 1, 1], bound := 1, weight := 769649, edges := #[⟨0, 1, 262⟩, ⟨0, 2, 357⟩, ⟨0, 3, 34⟩, ⟨1, 2, 361⟩, ⟨1, 3, 11⟩, ⟨2, 3, 306⟩], triples := #[] }
def er028_311 : Row := { vars := #[236, 396, 9], coeff := #[1, 1, 1], bound := 1, weight := 230352, edges := #[⟨0, 1, 206⟩, ⟨0, 2, 471⟩, ⟨1, 2, 408⟩], triples := #[] }
def er028_312 : Row := { vars := #[237, 531, 405], coeff := #[1, 1, 1], bound := 1, weight := 8135, edges := #[⟨0, 1, 33⟩, ⟨0, 2, 201⟩, ⟨1, 2, 137⟩], triples := #[] }
def er028_313 : Row := { vars := #[237, 510, 160], coeff := #[1, 1, 1], bound := 1, weight := 551789, edges := #[⟨0, 1, 51⟩, ⟨0, 2, 400⟩, ⟨1, 2, 302⟩], triples := #[] }
def er028_314 : Row := { vars := #[238, 406, 483], coeff := #[1, 1, 1], bound := 1, weight := 112792, edges := #[⟨0, 1, 202⟩, ⟨0, 2, 105⟩, ⟨1, 2, 42⟩], triples := #[] }
def er028_315 : Row := { vars := #[239, 311, 515], coeff := #[1, 1, 1], bound := 1, weight := 59698, edges := #[⟨0, 1, 249⟩, ⟨0, 2, 59⟩, ⟨1, 2, 35⟩], triples := #[] }
def er028_316 : Row := { vars := #[240, 517, 377], coeff := #[1, 1, 1], bound := 1, weight := 124629, edges := #[⟨0, 1, 10⟩, ⟨0, 2, 197⟩, ⟨1, 2, 134⟩], triples := #[] }
def er028_317 : Row := { vars := #[240, 391, 545], coeff := #[1, 1, 1], bound := 1, weight := 323504, edges := #[⟨0, 1, 213⟩, ⟨0, 2, 23⟩, ⟨1, 2, 134⟩], triples := #[] }
def er028_318 : Row := { vars := #[240, 523, 199], coeff := #[1, 1, 1], bound := 1, weight := 160955, edges := #[⟨0, 1, 6⟩, ⟨0, 2, 352⟩, ⟨1, 2, 300⟩], triples := #[] }
def er028_319 : Row := { vars := #[240, 247, 510], coeff := #[1, 1, 1], bound := 1, weight := 225160, edges := #[⟨0, 1, 257⟩, ⟨0, 2, 48⟩, ⟨1, 2, 38⟩], triples := #[] }
end HardyCapset20261020.Cert


