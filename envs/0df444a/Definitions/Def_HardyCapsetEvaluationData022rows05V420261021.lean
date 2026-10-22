-- Prove2me | Definitions.Def_HardyCapsetEvaluationData022rows05V420261021
-- name    : HardyCapsetEvaluationData022rows05V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T01:57:48.200416+00:00
-- url     : https://prove2.me/theorems/4dee03a6-7930-42d1-aa70-904188436256
-- title:
--   HardyCapsetEvaluationData022rows05V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er022_320 : Row := { vars := #[214, 272, 445], coeff := #[1, 1, 1], bound := 1, weight := 38390, edges := #[⟨0, 1, 406⟩, ⟨0, 2, 267⟩, ⟨1, 2, 41⟩], triples := #[] }
def er022_321 : Row := { vars := #[216, 227, 492], coeff := #[1, 1, 1], bound := 1, weight := 549467, edges := #[⟨0, 1, 193⟩, ⟨0, 2, 147⟩, ⟨1, 2, 137⟩], triples := #[] }
def er022_322 : Row := { vars := #[217, 28, 387], coeff := #[1, 1, 1], bound := 1, weight := 87022, edges := #[⟨0, 1, 398⟩, ⟨0, 2, 283⟩, ⟨1, 2, 427⟩], triples := #[] }
def er022_323 : Row := { vars := #[217, 486, 247], coeff := #[1, 1, 1], bound := 1, weight := 715887, edges := #[⟨0, 1, 25⟩, ⟨0, 2, 212⟩, ⟨1, 2, 6⟩], triples := #[] }
def er022_324 : Row := { vars := #[218, 224, 457], coeff := #[1, 1, 1], bound := 1, weight := 23802, edges := #[⟨0, 1, 195⟩, ⟨0, 2, 49⟩, ⟨1, 2, 43⟩], triples := #[] }
def er022_325 : Row := { vars := #[218, 225, 456], coeff := #[1, 1, 1], bound := 1, weight := 450534, edges := #[⟨0, 1, 194⟩, ⟨0, 2, 50⟩, ⟨1, 2, 43⟩], triples := #[] }
def er022_326 : Row := { vars := #[218, 559, 245], coeff := #[1, 1, 1], bound := 1, weight := 95012, edges := #[⟨0, 1, 95⟩, ⟨0, 2, 214⟩, ⟨1, 2, 78⟩], triples := #[] }
def er022_327 : Row := { vars := #[218, 245, 468], coeff := #[1, 1, 1], bound := 1, weight := 59895, edges := #[⟨0, 1, 214⟩, ⟨0, 2, 60⟩, ⟨1, 2, 43⟩], triples := #[] }
def er022_328 : Row := { vars := #[221, 263, 552], coeff := #[1, 1, 1], bound := 1, weight := 143954, edges := #[⟨0, 1, 200⟩, ⟨0, 2, 107⟩, ⟨1, 2, 74⟩], triples := #[] }
def er022_329 : Row := { vars := #[221, 263, 480], coeff := #[1, 1, 1], bound := 1, weight := 294696, edges := #[⟨0, 1, 200⟩, ⟨0, 2, 35⟩, ⟨1, 2, 3⟩], triples := #[] }
def er022_330 : Row := { vars := #[224, 353, 469], coeff := #[1, 1, 1], bound := 1, weight := 158493, edges := #[⟨0, 1, 317⟩, ⟨0, 2, 58⟩, ⟨1, 2, 164⟩], triples := #[] }
def er022_331 : Row := { vars := #[224, 239, 504], coeff := #[1, 1, 1], bound := 1, weight := 639171, edges := #[⟨0, 1, 213⟩, ⟨0, 2, 154⟩, ⟨1, 2, 145⟩], triples := #[] }
def er022_332 : Row := { vars := #[225, 26, 485], coeff := #[1, 1, 1], bound := 1, weight := 197974, edges := #[⟨0, 1, 398⟩, ⟨0, 2, 33⟩, ⟨1, 2, 197⟩], triples := #[] }
def er022_333 : Row := { vars := #[227, 546, 122], coeff := #[1, 1, 1], bound := 1, weight := 157900, edges := #[⟨0, 1, 77⟩, ⟨0, 2, 483⟩, ⟨1, 2, 231⟩], triples := #[] }
def er022_334 : Row := { vars := #[229, 552, 255], coeff := #[1, 1, 1], bound := 1, weight := 447563, edges := #[⟨0, 1, 104⟩, ⟨0, 2, 200⟩, ⟨1, 2, 82⟩], triples := #[] }
def er022_335 : Row := { vars := #[231, 498, 401], coeff := #[1, 1, 1], bound := 1, weight := 116032, edges := #[⟨0, 1, 162⟩, ⟨0, 2, 275⟩, ⟨1, 2, 21⟩], triples := #[] }
def er022_336 : Row := { vars := #[235, 475, 240], coeff := #[1, 1, 1], bound := 1, weight := 563739, edges := #[⟨0, 1, 33⟩, ⟨0, 2, 201⟩, ⟨1, 2, 32⟩], triples := #[] }
def er022_337 : Row := { vars := #[236, 321, 481], coeff := #[1, 1, 1], bound := 1, weight := 175164, edges := #[⟨0, 1, 346⟩, ⟨0, 2, 25⟩, ⟨1, 2, 166⟩], triples := #[] }
def er022_338 : Row := { vars := #[238, 257, 553], coeff := #[1, 1, 1], bound := 1, weight := 794720, edges := #[⟨0, 1, 194⟩, ⟨0, 2, 95⟩, ⟨1, 2, 78⟩], triples := #[] }
def er022_339 : Row := { vars := #[240, 469, 254], coeff := #[1, 1, 1], bound := 1, weight := 436262, edges := #[⟨0, 1, 40⟩, ⟨0, 2, 199⟩, ⟨1, 2, 69⟩], triples := #[] }
def er022_340 : Row := { vars := #[241, 558, 255], coeff := #[1, 1, 1], bound := 1, weight := 191798, edges := #[⟨0, 1, 76⟩, ⟨0, 2, 196⟩, ⟨1, 2, 105⟩], triples := #[] }
def er022_341 : Row := { vars := #[241, 254, 559], coeff := #[1, 1, 1], bound := 1, weight := 202909, edges := #[⟨0, 1, 198⟩, ⟨0, 2, 75⟩, ⟨1, 2, 105⟩], triples := #[] }
def er022_342 : Row := { vars := #[242, 505, 252], coeff := #[1, 1, 1], bound := 1, weight := 563368, edges := #[⟨0, 1, 134⟩, ⟨0, 2, 199⟩, ⟨1, 2, 166⟩], triples := #[] }
def er022_343 : Row := { vars := #[243, 119, 556], coeff := #[1, 1, 1], bound := 1, weight := 365645, edges := #[⟨0, 1, 481⟩, ⟨0, 2, 96⟩, ⟨1, 2, 231⟩], triples := #[] }
def er022_344 : Row := { vars := #[244, 463, 250], coeff := #[1, 1, 1], bound := 1, weight := 343598, edges := #[⟨0, 1, 58⟩, ⟨0, 2, 195⟩, ⟨1, 2, 49⟩], triples := #[] }
def er022_345 : Row := { vars := #[245, 26, 478], coeff := #[1, 1, 1], bound := 1, weight := 295627, edges := #[⟨0, 1, 397⟩, ⟨0, 2, 33⟩, ⟨1, 2, 201⟩], triples := #[] }
def er022_346 : Row := { vars := #[245, 480, 251], coeff := #[1, 1, 1], bound := 1, weight := 549467, edges := #[⟨0, 1, 22⟩, ⟨0, 2, 192⟩, ⟨1, 2, 14⟩], triples := #[] }
def er022_347 : Row := { vars := #[246, 505, 382], coeff := #[1, 1, 1], bound := 1, weight := 188175, edges := #[⟨0, 1, 137⟩, ⟨0, 2, 285⟩, ⟨1, 2, 39⟩], triples := #[] }
def er022_348 : Row := { vars := #[247, 498, 248], coeff := #[1, 1, 1], bound := 1, weight := 284114, edges := #[⟨0, 1, 152⟩, ⟨0, 2, 193⟩, ⟨1, 2, 147⟩], triples := #[] }
def er022_349 : Row := { vars := #[248, 321, 475], coeff := #[1, 1, 1], bound := 1, weight := 15527, edges := #[⟨0, 1, 336⟩, ⟨0, 2, 25⟩, ⟨1, 2, 143⟩], triples := #[] }
def er022_350 : Row := { vars := #[248, 258, 493], coeff := #[1, 1, 1], bound := 1, weight := 444324, edges := #[⟨0, 1, 215⟩, ⟨0, 2, 156⟩, ⟨1, 2, 152⟩], triples := #[] }
def er022_351 : Row := { vars := #[249, 8, 488], coeff := #[1, 1, 1], bound := 1, weight := 344770, edges := #[⟨0, 1, 398⟩, ⟨0, 2, 30⟩, ⟨1, 2, 201⟩], triples := #[] }
def er022_352 : Row := { vars := #[251, 492, 393], coeff := #[1, 1, 1], bound := 1, weight := 450534, edges := #[⟨0, 1, 155⟩, ⟨0, 2, 261⟩, ⟨1, 2, 11⟩], triples := #[] }
def er022_353 : Row := { vars := #[263, 135, 556], coeff := #[1, 1, 1], bound := 1, weight := 115089, edges := #[⟨0, 1, 481⟩, ⟨0, 2, 86⟩, ⟨1, 2, 226⟩], triples := #[] }
def er022_354 : Row := { vars := #[264, 442, 449], coeff := #[1, 1, 1], bound := 1, weight := 467890, edges := #[⟨0, 1, 60⟩, ⟨0, 2, 58⟩, ⟨1, 2, 374⟩], triples := #[] }
def er022_355 : Row := { vars := #[265, 426, 432], coeff := #[1, 1, 1], bound := 1, weight := 360830, edges := #[⟨0, 1, 69⟩, ⟨0, 2, 68⟩, ⟨1, 2, 363⟩], triples := #[] }
def er022_356 : Row := { vars := #[265, 442, 448], coeff := #[1, 1, 1], bound := 1, weight := 62545, edges := #[⟨0, 1, 59⟩, ⟨0, 2, 58⟩, ⟨1, 2, 375⟩], triples := #[] }
def er022_357 : Row := { vars := #[266, 326, 528], coeff := #[1, 1, 1], bound := 1, weight := 365445, edges := #[⟨0, 1, 325⟩, ⟨0, 2, 145⟩, ⟨1, 2, 107⟩], triples := #[] }
def er022_358 : Row := { vars := #[267, 583, 305], coeff := #[1, 1, 1], bound := 1, weight := 284458, edges := #[⟨0, 1, 84⟩, ⟨0, 2, 333⟩, ⟨1, 2, 4⟩], triples := #[] }
def er022_359 : Row := { vars := #[269, 329, 534], coeff := #[1, 1, 1], bound := 1, weight := 435535, edges := #[⟨0, 1, 329⟩, ⟨0, 2, 162⟩, ⟨1, 2, 94⟩], triples := #[] }
def er022_360 : Row := { vars := #[269, 303, 582], coeff := #[1, 1, 1], bound := 1, weight := 73713, edges := #[⟨0, 1, 333⟩, ⟨0, 2, 74⟩, ⟨1, 2, 11⟩], triples := #[] }
def er022_361 : Row := { vars := #[270, 449, 430], coeff := #[1, 1, 1], bound := 1, weight := 252881, edges := #[⟨0, 1, 43⟩, ⟨0, 2, 60⟩, ⟨1, 2, 354⟩], triples := #[] }
def er022_362 : Row := { vars := #[270, 597, 441], coeff := #[1, 1, 1], bound := 1, weight := 228045, edges := #[⟨0, 1, 84⟩, ⟨0, 2, 51⟩, ⟨1, 2, 430⟩], triples := #[] }
def er022_363 : Row := { vars := #[271, 428, 531], coeff := #[1, 1, 1], bound := 1, weight := 399168, edges := #[⟨0, 1, 61⟩, ⟨0, 2, 167⟩, ⟨1, 2, 483⟩], triples := #[] }
def er022_364 : Row := { vars := #[273, 370, 535], coeff := #[1, 1, 1], bound := 1, weight := 406796, edges := #[⟨0, 1, 278⟩, ⟨0, 2, 157⟩, ⟨1, 2, 7⟩], triples := #[] }
def er022_365 : Row := { vars := #[276, 417, 430], coeff := #[1, 1, 1], bound := 1, weight := 144269, edges := #[⟨0, 1, 58⟩, ⟨0, 2, 50⟩, ⟨1, 2, 374⟩], triples := #[] }
def er022_366 : Row := { vars := #[276, 417, 599], coeff := #[1, 1, 1], bound := 1, weight := 235047, edges := #[⟨0, 1, 58⟩, ⟨0, 2, 104⟩, ⟨1, 2, 424⟩], triples := #[] }
def er022_367 : Row := { vars := #[277, 436, 410], coeff := #[1, 1, 1], bound := 1, weight := 531106, edges := #[⟨0, 1, 43⟩, ⟨0, 2, 59⟩, ⟨1, 2, 375⟩], triples := #[] }
def er022_368 : Row := { vars := #[278, 321, 528], coeff := #[1, 1, 1], bound := 1, weight := 482556, edges := #[⟨0, 1, 315⟩, ⟨0, 2, 155⟩, ⟨1, 2, 84⟩], triples := #[] }
def er022_369 : Row := { vars := #[280, 368, 529], coeff := #[1, 1, 1], bound := 1, weight := 175627, edges := #[⟨0, 1, 289⟩, ⟨0, 2, 154⟩, ⟨1, 2, 25⟩], triples := #[] }
def er022_370 : Row := { vars := #[286, 302, 564], coeff := #[1, 1, 1], bound := 1, weight := 284458, edges := #[⟨0, 1, 310⟩, ⟨0, 2, 77⟩, ⟨1, 2, 50⟩], triples := #[] }
def er022_371 : Row := { vars := #[287, 6, 421], coeff := #[1, 1, 1], bound := 1, weight := 512977, edges := #[⟨0, 1, 353⟩, ⟨0, 2, 13⟩, ⟨1, 2, 236⟩], triples := #[] }
def er022_372 : Row := { vars := #[287, 401, 570], coeff := #[1, 1, 1], bound := 1, weight := 178552, edges := #[⟨0, 1, 295⟩, ⟨0, 2, 102⟩, ⟨1, 2, 153⟩], triples := #[] }
def er022_373 : Row := { vars := #[288, 453, 415], coeff := #[1, 1, 1], bound := 1, weight := 698627, edges := #[⟨0, 1, 4⟩, ⟨0, 2, 34⟩, ⟨1, 2, 360⟩], triples := #[] }
def er022_374 : Row := { vars := #[288, 455, 413], coeff := #[1, 1, 1], bound := 1, weight := 301374, edges := #[⟨0, 1, 3⟩, ⟨0, 2, 35⟩, ⟨1, 2, 360⟩], triples := #[] }
def er022_375 : Row := { vars := #[289, 436, 443], coeff := #[1, 1, 1], bound := 1, weight := 468895, edges := #[⟨0, 1, 22⟩, ⟨0, 2, 13⟩, ⟨1, 2, 353⟩], triples := #[] }
def er022_376 : Row := { vars := #[290, 510, 364], coeff := #[1, 1, 1], bound := 1, weight := 56105, edges := #[⟨0, 1, 165⟩, ⟨0, 2, 258⟩, ⟨1, 2, 66⟩], triples := #[] }
def er022_377 : Row := { vars := #[291, 304, 576], coeff := #[1, 1, 1], bound := 1, weight := 304004, edges := #[⟨0, 1, 321⟩, ⟨0, 2, 85⟩, ⟨1, 2, 57⟩], triples := #[] }
def er022_378 : Row := { vars := #[291, 570, 316], coeff := #[1, 1, 1], bound := 1, weight := 621068, edges := #[⟨0, 1, 95⟩, ⟨0, 2, 310⟩, ⟨1, 2, 42⟩], triples := #[] }
def er022_379 : Row := { vars := #[292, 315, 577], coeff := #[1, 1, 1], bound := 1, weight := 590306, edges := #[⟨0, 1, 311⟩, ⟨0, 2, 75⟩, ⟨1, 2, 71⟩], triples := #[] }
def er022_380 : Row := { vars := #[292, 452, 27], coeff := #[1, 1, 1], bound := 1, weight := 125238, edges := #[⟨0, 1, 14⟩, ⟨0, 2, 352⟩, ⟨1, 2, 241⟩], triples := #[] }
def er022_381 : Row := { vars := #[293, 516, 368], coeff := #[1, 1, 1], bound := 1, weight := 532016, edges := #[⟨0, 1, 152⟩, ⟨0, 2, 256⟩, ⟨1, 2, 49⟩], triples := #[] }
def er022_382 : Row := { vars := #[297, 424, 29], coeff := #[1, 1, 1], bound := 1, weight := 284458, edges := #[⟨0, 1, 6⟩, ⟨0, 2, 372⟩, ⟨1, 2, 236⟩], triples := #[] }
def er022_383 : Row := { vars := #[300, 408, 419], coeff := #[1, 1, 1], bound := 1, weight := 421255, edges := #[⟨0, 1, 147⟩, ⟨0, 2, 137⟩, ⟨1, 2, 353⟩], triples := #[] }
end HardyCapset20261020.Cert


