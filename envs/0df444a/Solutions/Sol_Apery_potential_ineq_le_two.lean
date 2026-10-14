-- Prove2me | solution 1 for Apery.potential_ineq_le_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T00:35:27.246956+00:00
-- url     : https://prove2.me/submissions/da2a396d-c96f-421d-98bb-afdba6bf89a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
# The potential inequality for `t ≤ 2`: assembly of the 107 Table-2 blocks

Case split over the grid of the Table-2 certificate, using the platform block
theorems `Apery.table2_block_i_j` (each porting the point bounds `U_pt_k`/`V_pt_k`
and interval lemmas `I_k` of `Apery/Table2`). Faithful to the case chain
`J_0_684` of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
`Apery/Table2/All.lean`.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceMeasure
import Definitions.Def_Zeta5_SourceAnalytic
import Definitions.Def_Zeta5_SourceEnergy
import Theorems.Thm_Apery_table2_block_0_7
import Theorems.Thm_Apery_table2_block_8_15
import Theorems.Thm_Apery_table2_block_16_23
import Theorems.Thm_Apery_table2_block_24_31
import Theorems.Thm_Apery_table2_block_32_38
import Theorems.Thm_Apery_table2_block_39_45
import Theorems.Thm_Apery_table2_block_46_52
import Theorems.Thm_Apery_table2_block_53_59
import Theorems.Thm_Apery_table2_block_60_66
import Theorems.Thm_Apery_table2_block_67_73
import Theorems.Thm_Apery_table2_block_74_80
import Theorems.Thm_Apery_table2_block_81_87
import Theorems.Thm_Apery_table2_block_88_94
import Theorems.Thm_Apery_table2_block_95_101
import Theorems.Thm_Apery_table2_block_102_108
import Theorems.Thm_Apery_table2_block_109_115
import Theorems.Thm_Apery_table2_block_116_122
import Theorems.Thm_Apery_table2_block_123_129
import Theorems.Thm_Apery_table2_block_130_136
import Theorems.Thm_Apery_table2_block_137_143
import Theorems.Thm_Apery_table2_block_144_150
import Theorems.Thm_Apery_table2_block_151_157
import Theorems.Thm_Apery_table2_block_158_164
import Theorems.Thm_Apery_table2_block_165_171
import Theorems.Thm_Apery_table2_block_172_178
import Theorems.Thm_Apery_table2_block_179_185
import Theorems.Thm_Apery_table2_block_186_192
import Theorems.Thm_Apery_table2_block_193_199
import Theorems.Thm_Apery_table2_block_200_206
import Theorems.Thm_Apery_table2_block_207_213
import Theorems.Thm_Apery_table2_block_214_220
import Theorems.Thm_Apery_table2_block_221_227
import Theorems.Thm_Apery_table2_block_228_234
import Theorems.Thm_Apery_table2_block_235_241
import Theorems.Thm_Apery_table2_block_242_248
import Theorems.Thm_Apery_table2_block_249_255
import Theorems.Thm_Apery_table2_block_256_262
import Theorems.Thm_Apery_table2_block_263_269
import Theorems.Thm_Apery_table2_block_270_276
import Theorems.Thm_Apery_table2_block_277_283
import Theorems.Thm_Apery_table2_block_284_290
import Theorems.Thm_Apery_table2_block_291_296
import Theorems.Thm_Apery_table2_block_297_302
import Theorems.Thm_Apery_table2_block_303_308
import Theorems.Thm_Apery_table2_block_309_314
import Theorems.Thm_Apery_table2_block_315_320
import Theorems.Thm_Apery_table2_block_321_326
import Theorems.Thm_Apery_table2_block_327_332
import Theorems.Thm_Apery_table2_block_333_338
import Theorems.Thm_Apery_table2_block_339_344
import Theorems.Thm_Apery_table2_block_345_350
import Theorems.Thm_Apery_table2_block_351_356
import Theorems.Thm_Apery_table2_block_357_362
import Theorems.Thm_Apery_table2_block_363_368
import Theorems.Thm_Apery_table2_block_369_374
import Theorems.Thm_Apery_table2_block_375_380
import Theorems.Thm_Apery_table2_block_381_386
import Theorems.Thm_Apery_table2_block_387_392
import Theorems.Thm_Apery_table2_block_393_398
import Theorems.Thm_Apery_table2_block_399_404
import Theorems.Thm_Apery_table2_block_405_410
import Theorems.Thm_Apery_table2_block_411_416
import Theorems.Thm_Apery_table2_block_417_422
import Theorems.Thm_Apery_table2_block_423_428
import Theorems.Thm_Apery_table2_block_429_434
import Theorems.Thm_Apery_table2_block_435_440
import Theorems.Thm_Apery_table2_block_441_446
import Theorems.Thm_Apery_table2_block_447_452
import Theorems.Thm_Apery_table2_block_453_458
import Theorems.Thm_Apery_table2_block_459_464
import Theorems.Thm_Apery_table2_block_465_470
import Theorems.Thm_Apery_table2_block_471_476
import Theorems.Thm_Apery_table2_block_477_482
import Theorems.Thm_Apery_table2_block_483_488
import Theorems.Thm_Apery_table2_block_489_494
import Theorems.Thm_Apery_table2_block_495_500
import Theorems.Thm_Apery_table2_block_501_506
import Theorems.Thm_Apery_table2_block_507_512
import Theorems.Thm_Apery_table2_block_513_518
import Theorems.Thm_Apery_table2_block_519_524
import Theorems.Thm_Apery_table2_block_525_530
import Theorems.Thm_Apery_table2_block_531_536
import Theorems.Thm_Apery_table2_block_537_542
import Theorems.Thm_Apery_table2_block_543_548
import Theorems.Thm_Apery_table2_block_549_554
import Theorems.Thm_Apery_table2_block_555_560
import Theorems.Thm_Apery_table2_block_561_566
import Theorems.Thm_Apery_table2_block_567_572
import Theorems.Thm_Apery_table2_block_573_578
import Theorems.Thm_Apery_table2_block_579_584
import Theorems.Thm_Apery_table2_block_585_590
import Theorems.Thm_Apery_table2_block_591_596
import Theorems.Thm_Apery_table2_block_597_602
import Theorems.Thm_Apery_table2_block_603_608
import Theorems.Thm_Apery_table2_block_609_614
import Theorems.Thm_Apery_table2_block_615_620
import Theorems.Thm_Apery_table2_block_621_626
import Theorems.Thm_Apery_table2_block_627_632
import Theorems.Thm_Apery_table2_block_633_638
import Theorems.Thm_Apery_table2_block_639_644
import Theorems.Thm_Apery_table2_block_645_649
import Theorems.Thm_Apery_table2_block_650_654
import Theorems.Thm_Apery_table2_block_655_659
import Theorems.Thm_Apery_table2_block_660_665
import Theorems.Thm_Apery_table2_block_666_671
import Theorems.Thm_Apery_table2_block_672_677
import Theorems.Thm_Apery_table2_block_678_683

open Finset Filter Topology Set MeasureTheory

theorem solution (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 2) :
    2 * Apery.Uρ t - Apery.Vfield t ≤ Apery.M0 := by
  rcases le_or_gt t (55761057 / 500000000000 : ℝ) with h0 | h0
  · exact Apery.table2_block_0_7 t ht h0
  · rcases le_or_gt t (974522519 / 2000000000000 : ℝ) with h1 | h1
    · exact Apery.table2_block_8_15 t h0 h1
    · rcases le_or_gt t (280457333 / 200000000000 : ℝ) with h2 | h2
      · exact Apery.table2_block_16_23 t h1 h2
      · rcases le_or_gt t (59205077 / 10000000000 : ℝ) with h3 | h3
        · exact Apery.table2_block_24_31 t h2 h3
        · rcases le_or_gt t (12166846693 / 1000000000000 : ℝ) with h4 | h4
          · exact Apery.table2_block_32_38 t h3 h4
          · rcases le_or_gt t (71753174289 / 4000000000000 : ℝ) with h5 | h5
            · exact Apery.table2_block_39_45 t h4 h5
            · rcases le_or_gt t (34934779437 / 1600000000000 : ℝ) with h6 | h6
              · exact Apery.table2_block_46_52 t h5 h6
              · rcases le_or_gt t (912352469539 / 32000000000000 : ℝ) with h7 | h7
                · exact Apery.table2_block_53_59 t h6 h7
                · rcases le_or_gt t (484490180433 / 16000000000000 : ℝ) with h8 | h8
                  · exact Apery.table2_block_60_66 t h7 h8
                  · rcases le_or_gt t (6763975897 / 200000000000 : ℝ) with h9 | h9
                    · exact Apery.table2_block_67_73 t h8 h9
                    · rcases le_or_gt t (71843627457 / 1600000000000 : ℝ) with h10 | h10
                      · exact Apery.table2_block_74_80 t h9 h10
                      · rcases le_or_gt t (3041335677499 / 64000000000000 : ℝ) with h11 | h11
                        · exact Apery.table2_block_81_87 t h10 h11
                        · rcases le_or_gt t (1604463128359 / 32000000000000 : ℝ) with h12 | h12
                          · exact Apery.table2_block_88_94 t h11 h12
                          · rcases le_or_gt t (886026853789 / 16000000000000 : ℝ) with h13 | h13
                            · exact Apery.table2_block_95_101 t h12 h13
                            · rcases le_or_gt t (2208124710979 / 32000000000000 : ℝ) with h14 | h14
                              · exact Apery.table2_block_102_108 t h13 h14
                              · rcases le_or_gt t (930331812041 / 12800000000000 : ℝ) with h15 | h15
                                · exact Apery.table2_block_109_115 t h14 h15
                                · rcases le_or_gt t (4786178853489 / 64000000000000 : ℝ) with h16 | h16
                                  · exact Apery.table2_block_116_122 t h15 h16
                                  · rcases le_or_gt t (2477164297547 / 32000000000000 : ℝ) with h17 | h17
                                    · exact Apery.table2_block_123_129 t h16 h17
                                    · rcases le_or_gt t (2611684090831 / 32000000000000 : ℝ) with h18 | h18
                                      · exact Apery.table2_block_130_136 t h17 h18
                                      · rcases le_or_gt t (762218354751 / 8000000000000 : ℝ) with h19 | h19
                                        · exact Apery.table2_block_137_143 t h18 h19
                                        · rcases le_or_gt t (3385194315371 / 32000000000000 : ℝ) with h20 | h20
                                          · exact Apery.table2_block_144_150 t h19 h20
                                          · rcases le_or_gt t (1748653019653 / 16000000000000 : ℝ) with h21 | h21
                                            · exact Apery.table2_block_151_157 t h20 h21
                                            · rcases le_or_gt t (7151568492121 / 64000000000000 : ℝ) with h22 | h22
                                              · exact Apery.table2_block_158_164 t h21 h22
                                              · rcases le_or_gt t (730852490563 / 6400000000000 : ℝ) with h23 | h23
                                                · exact Apery.table2_block_165_171 t h22 h23
                                                · rcases le_or_gt t (3788796521537 / 32000000000000 : ℝ) with h24 | h24
                                                  · exact Apery.table2_block_172_178 t h23 h24
                                                  · rcases le_or_gt t (2017721157097 / 16000000000000 : ℝ) with h25 | h25
                                                    · exact Apery.table2_block_179_185 t h24 h25
                                                    · rcases le_or_gt t (2365991674599 / 16000000000000 : ℝ) with h26 | h26
                                                      · exact Apery.table2_block_186_192 t h25 h26
                                                      · rcases le_or_gt t (2479551745141 / 16000000000000 : ℝ) with h27 | h27
                                                        · exact Apery.table2_block_193_199 t h26 h27
                                                        · rcases le_or_gt t (809354968321 / 5120000000000 : ℝ) with h28 | h28
                                                          · exact Apery.table2_block_200_206 t h27 h28
                                                          · rcases le_or_gt t (10315667227461 / 64000000000000 : ℝ) with h29 | h29
                                                            · exact Apery.table2_block_207_213 t h28 h29
                                                            · rcases le_or_gt t (21028794701819 / 128000000000000 : ℝ) with h30 | h30
                                                              · exact Apery.table2_block_214_220 t h29 h30
                                                              · rcases le_or_gt t (108266875449 / 640000000000 : ℝ) with h31 | h31
                                                                · exact Apery.table2_block_221_227 t h30 h31
                                                                · rcases le_or_gt t (1139448789761 / 6400000000000 : ℝ) with h32 | h32
                                                                  · exact Apery.table2_block_228_234 t h31 h32
                                                                  · rcases le_or_gt t (3251812320751 / 16000000000000 : ℝ) with h33 | h33
                                                                    · exact Apery.table2_block_235_241 t h32 h33
                                                                    · rcases le_or_gt t (1362141139057 / 6400000000000 : ℝ) with h34 | h34
                                                                      · exact Apery.table2_block_242_248 t h33 h34
                                                                      · rcases le_or_gt t (6947186163633 / 32000000000000 : ℝ) with h35 | h35
                                                                        · exact Apery.table2_block_249_255 t h34 h35
                                                                        · rcases le_or_gt t (4522628207 / 20480000000 : ℝ) with h36 | h36
                                                                          · exact Apery.table2_block_256_262 t h35 h36
                                                                          · rcases le_or_gt t (3593013491621 / 16000000000000 : ℝ) with h37 | h37
                                                                            · exact Apery.table2_block_263_269 t h36 h37
                                                                            · rcases le_or_gt t (732250745159 / 3200000000000 : ℝ) with h38 | h38
                                                                              · exact Apery.table2_block_270_276 t h37 h38
                                                                              · rcases le_or_gt t (7561348271199 / 32000000000000 : ℝ) with h39 | h39
                                                                                · exact Apery.table2_block_277_283 t h38 h39
                                                                                · rcases le_or_gt t (504571876719 / 2000000000000 : ℝ) with h40 | h40
                                                                                  · exact Apery.table2_block_284_290 t h39 h40
                                                                                  · rcases le_or_gt t (1770460514531 / 6400000000000 : ℝ) with h41 | h41
                                                                                    · exact Apery.table2_block_291_296 t h40 h41
                                                                                    · rcases le_or_gt t (4542766622207 / 16000000000000 : ℝ) with h42 | h42
                                                                                      · exact Apery.table2_block_297_302 t h41 h42
                                                                                      · rcases le_or_gt t (18404297160587 / 64000000000000 : ℝ) with h43 | h43
                                                                                        · exact Apery.table2_block_303_308 t h42 h43
                                                                                        · rcases le_or_gt t (9318763916173 / 32000000000000 : ℝ) with h44 | h44
                                                                                          · exact Apery.table2_block_309_314 t h43 h44
                                                                                          · rcases le_or_gt t (3774151700821 / 12800000000000 : ℝ) with h45 | h45
                                                                                            · exact Apery.table2_block_315_320 t h44 h45
                                                                                            · rcases le_or_gt t (2387998646983 / 8000000000000 : ℝ) with h46 | h46
                                                                                              · exact Apery.table2_block_321_326 t h45 h46
                                                                                              · rcases le_or_gt t (4853740851219 / 16000000000000 : ℝ) with h47 | h47
                                                                                                · exact Apery.table2_block_327_332 t h46 h47
                                                                                                · rcases le_or_gt t (9940712374197 / 32000000000000 : ℝ) with h48 | h48
                                                                                                  · exact Apery.table2_block_333_338 t h47 h48
                                                                                                  · rcases le_or_gt t (1310614659371 / 4000000000000 : ℝ) with h49 | h49
                                                                                                    · exact Apery.table2_block_339_344 t h48 h49
                                                                                                    · rcases le_or_gt t (1127430003351 / 3200000000000 : ℝ) with h50 | h50
                                                                                                      · exact Apery.table2_block_345_350 t h49 h50
                                                                                                      · rcases le_or_gt t (23134620118833 / 64000000000000 : ℝ) with h51 | h51
                                                                                                        · exact Apery.table2_block_351_356 t h50 h51
                                                                                                        · rcases le_or_gt t (46855260289479 / 128000000000000 : ℝ) with h52 | h52
                                                                                                          · exact Apery.table2_block_357_362 t h51 h52
                                                                                                          · rcases le_or_gt t (47357563191033 / 128000000000000 : ℝ) with h53 | h53
                                                                                                            · exact Apery.table2_block_363_368 t h52 h53
                                                                                                            · rcases le_or_gt t (47859866092587 / 128000000000000 : ℝ) with h54 | h54
                                                                                                              · exact Apery.table2_block_369_374 t h53 h54
                                                                                                              · rcases le_or_gt t (48362168994141 / 128000000000000 : ℝ) with h55 | h55
                                                                                                                · exact Apery.table2_block_375_380 t h54 h55
                                                                                                                · rcases le_or_gt t (9772894379139 / 25600000000000 : ℝ) with h56 | h56
                                                                                                                  · exact Apery.table2_block_381_386 t h55 h56
                                                                                                                  · rcases le_or_gt t (777896258571 / 2000000000000 : ℝ) with h57 | h57
                                                                                                                    · exact Apery.table2_block_387_392 t h56 h57
                                                                                                                    · rcases le_or_gt t (3195302184543 / 8000000000000 : ℝ) with h58 | h58
                                                                                                                      · exact Apery.table2_block_393_398 t h57 h58
                                                                                                                      · rcases le_or_gt t (3362736485061 / 8000000000000 : ℝ) with h59 | h59
                                                                                                                        · exact Apery.table2_block_399_404 t h58 h59
                                                                                                                        · rcases le_or_gt t (880153607101 / 2000000000000 : ℝ) with h60 | h60
                                                                                                                          · exact Apery.table2_block_405_410 t h59 h60
                                                                                                                          · rcases le_or_gt t (896045205619 / 2000000000000 : ℝ) with h61 | h61
                                                                                                                            · exact Apery.table2_block_411_416 t h60 h61
                                                                                                                            · rcases le_or_gt t (451995502439 / 1000000000000 : ℝ) with h62 | h62
                                                                                                                              · exact Apery.table2_block_417_422 t h61 h62
                                                                                                                              · rcases le_or_gt t (911936804137 / 2000000000000 : ℝ) with h63 | h63
                                                                                                                                · exact Apery.table2_block_423_428 t h62 h63
                                                                                                                                · rcases le_or_gt t (229970650849 / 500000000000 : ℝ) with h64 | h64
                                                                                                                                  · exact Apery.table2_block_429_434 t h63 h64
                                                                                                                                  · rcases le_or_gt t (185565680531 / 400000000000 : ℝ) with h65 | h65
                                                                                                                                    · exact Apery.table2_block_435_440 t h64 h65
                                                                                                                                    · rcases le_or_gt t (938422801667 / 2000000000000 : ℝ) with h66 | h66
                                                                                                                                      · exact Apery.table2_block_441_446 t h65 h66
                                                                                                                                      · rcases le_or_gt t (190862880037 / 400000000000 : ℝ) with h67 | h67
                                                                                                                                        · exact Apery.table2_block_447_452 t h66 h67
                                                                                                                                        · rcases le_or_gt t (489075898981 / 1000000000000 : ℝ) with h68 | h68
                                                                                                                                          · exact Apery.table2_block_453_458 t h67 h68
                                                                                                                                          · rcases le_or_gt t (102052939401 / 200000000000 : ℝ) with h69 | h69
                                                                                                                                            · exact Apery.table2_block_459_464 t h68 h69
                                                                                                                                            · rcases le_or_gt t (4204382054123 / 8000000000000 : ℝ) with h70 | h70
                                                                                                                                              · exact Apery.table2_block_465_470 t h69 h70
                                                                                                                                              · rcases le_or_gt t (17057188862597 / 32000000000000 : ℝ) with h71 | h71
                                                                                                                                                · exact Apery.table2_block_471_476 t h70 h71
                                                                                                                                                · rcases le_or_gt t (68787963624633 / 128000000000000 : ℝ) with h72 | h72
                                                                                                                                                  · exact Apery.table2_block_477_482 t h71 h72
                                                                                                                                                  · rcases le_or_gt t (69267284916843 / 128000000000000 : ℝ) with h73 | h73
                                                                                                                                                    · exact Apery.table2_block_483_488 t h72 h73
                                                                                                                                                    · rcases le_or_gt t (69746606209053 / 128000000000000 : ℝ) with h74 | h74
                                                                                                                                                      · exact Apery.table2_block_489_494 t h73 h74
                                                                                                                                                      · rcases le_or_gt t (35152907191649 / 64000000000000 : ℝ) with h75 | h75
                                                                                                                                                        · exact Apery.table2_block_495_500 t h74 h75
                                                                                                                                                        · rcases le_or_gt t (35632228483859 / 64000000000000 : ℝ) with h76 | h76
                                                                                                                                                          · exact Apery.table2_block_501_506 t h75 h76
                                                                                                                                                          · rcases le_or_gt t (36111549776069 / 64000000000000 : ℝ) with h77 | h77
                                                                                                                                                            · exact Apery.table2_block_507_512 t h76 h77
                                                                                                                                                            · rcases le_or_gt t (18495152739227 / 32000000000000 : ℝ) with h78 | h78
                                                                                                                                                              · exact Apery.table2_block_513_518 t h77 h78
                                                                                                                                                              · rcases le_or_gt t (9595973061673 / 16000000000000 : ℝ) with h79 | h79
                                                                                                                                                                · exact Apery.table2_block_519_524 t h78 h79
                                                                                                                                                                · rcases le_or_gt t (38865440481251 / 64000000000000 : ℝ) with h80 | h80
                                                                                                                                                                  · exact Apery.table2_block_525_530 t h79 h80
                                                                                                                                                                  · rcases le_or_gt t (39278196110873 / 64000000000000 : ℝ) with h81 | h81
                                                                                                                                                                    · exact Apery.table2_block_531_536 t h80 h81
                                                                                                                                                                    · rcases le_or_gt t (7938190348099 / 12800000000000 : ℝ) with h82 | h82
                                                                                                                                                                      · exact Apery.table2_block_537_542 t h81 h82
                                                                                                                                                                      · rcases le_or_gt t (40103707370117 / 64000000000000 : ℝ) with h83 | h83
                                                                                                                                                                        · exact Apery.table2_block_543_548 t h82 h83
                                                                                                                                                                        · rcases le_or_gt t (40516462999739 / 64000000000000 : ℝ) with h84 | h84
                                                                                                                                                                          · exact Apery.table2_block_549_554 t h83 h84
                                                                                                                                                                          · rcases le_or_gt t (20499005617149 / 32000000000000 : ℝ) with h85 | h85
                                                                                                                                                                            · exact Apery.table2_block_555_560 t h84 h85
                                                                                                                                                                            · rcases le_or_gt t (20911761246771 / 32000000000000 : ℝ) with h86 | h86
                                                                                                                                                                              · exact Apery.table2_block_561_566 t h85 h86
                                                                                                                                                                              · rcases le_or_gt t (21411481852343 / 32000000000000 : ℝ) with h87 | h87
                                                                                                                                                                                · exact Apery.table2_block_567_572 t h86 h87
                                                                                                                                                                                · rcases le_or_gt t (21619158626859 / 32000000000000 : ℝ) with h88 | h88
                                                                                                                                                                                  · exact Apery.table2_block_573_578 t h87 h88
                                                                                                                                                                                  · rcases le_or_gt t (10887458103873 / 16000000000000 : ℝ) with h89 | h89
                                                                                                                                                                                    · exact Apery.table2_block_579_584 t h88 h89
                                                                                                                                                                                    · rcases le_or_gt t (21930673788633 / 32000000000000 : ℝ) with h90 | h90
                                                                                                                                                                                      · exact Apery.table2_block_585_590 t h89 h90
                                                                                                                                                                                      · rcases le_or_gt t (276080392119 / 400000000000 : ℝ) with h91 | h91
                                                                                                                                                                                        · exact Apery.table2_block_591_596 t h90 h91
                                                                                                                                                                                        · rcases le_or_gt t (22242188950407 / 32000000000000 : ℝ) with h92 | h92
                                                                                                                                                                                          · exact Apery.table2_block_597_602 t h91 h92
                                                                                                                                                                                          · rcases le_or_gt t (22553704112181 / 32000000000000 : ℝ) with h93 | h93
                                                                                                                                                                                            · exact Apery.table2_block_603_608 t h92 h93
                                                                                                                                                                                            · rcases le_or_gt t (89520072139 / 125000000000 : ℝ) with h94 | h94
                                                                                                                                                                                              · exact Apery.table2_block_609_614 t h93 h94
                                                                                                                                                                                              · rcases le_or_gt t (23130475497483 / 32000000000000 : ℝ) with h95 | h95
                                                                                                                                                                                                · exact Apery.table2_block_615_620 t h94 h95
                                                                                                                                                                                                · rcases le_or_gt t (932533432353 / 1280000000000 : ℝ) with h96 | h96
                                                                                                                                                                                                  · exact Apery.table2_block_621_626 t h95 h96
                                                                                                                                                                                                  · rcases le_or_gt t (23496196120167 / 32000000000000 : ℝ) with h97 | h97
                                                                                                                                                                                                    · exact Apery.table2_block_627_632 t h96 h97
                                                                                                                                                                                                    · rcases le_or_gt t (23679056431509 / 32000000000000 : ℝ) with h98 | h98
                                                                                                                                                                                                      · exact Apery.table2_block_633_638 t h97 h98
                                                                                                                                                                                                      · rcases le_or_gt t (746637295669 / 1000000000000 : ℝ) with h99 | h99
                                                                                                                                                                                                        · exact Apery.table2_block_639_644 t h98 h99
                                                                                                                                                                                                        · rcases le_or_gt t (770823404286711 / 1024000000000000 : ℝ) with h100 | h100
                                                                                                                                                                                                          · exact Apery.table2_block_645_649 t h99 h100
                                                                                                                                                                                                          · rcases le_or_gt t (388545108904183 / 512000000000000 : ℝ) with h101 | h101
                                                                                                                                                                                                            · exact Apery.table2_block_650_654 t h100 h101
                                                                                                                                                                                                            · rcases le_or_gt t (197405961212919 / 256000000000000 : ℝ) with h102 | h102
                                                                                                                                                                                                              · exact Apery.table2_block_655_659 t h101 h102
                                                                                                                                                                                                              · rcases le_or_gt t (202419412030243 / 256000000000000 : ℝ) with h103 | h103
                                                                                                                                                                                                                · exact Apery.table2_block_660_665 t h102 h103
                                                                                                                                                                                                                · rcases le_or_gt t (106849838184611 / 128000000000000 : ℝ) with h104 | h104
                                                                                                                                                                                                                  · exact Apery.table2_block_666_671 t h103 h104
                                                                                                                                                                                                                  · rcases le_or_gt t (15706284843697 / 16000000000000 : ℝ) with h105 | h105
                                                                                                                                                                                                                    · exact Apery.table2_block_672_677 t h104 h105
                                                                                                                                                                                                                    · exact Apery.table2_block_678_683 t h105 ht2

