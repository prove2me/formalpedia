-- Prove2me | Definitions.Def_dusart_mesh_upper_chunk3
-- name    : dusart_mesh_upper_chunk3
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T18:11:23.851234+00:00
-- url     : https://prove2.me/theorems/d22703a8-ceaa-4301-b533-c9122c46b202
-- title:
--   Dusart finite mesh: UpperChunk3
-- statement:
--   The UpperChunk3 component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_eval3
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
namespace DusartFiniteMesh.UpperScan

lemma chunk3 (hstart : primorial 52993 ≤ 35933873761357470190686731039059820*2^75922) :
    primorial 70112 ≤ 39094912334171351242361442093496208658*2^100385 ∧
      ∀ k : ℕ, 52993 < k → k ≤ 70112 → 255 ≤ k → Chebyshev.theta (k : ℝ) ≤ k := by
  have h207 := checked_block 256 52993 35933873761357470190686731039059820 75922 96582089188845584395105357413345962 76313 hstart Data.chk207
  have h208 := checked_block 256 53249 96582089188845584395105357413345962 76313 10604302420240366814435842207708564400 76636 h207.1 Data.chk208
  have h209 := checked_block 256 53505 10604302420240366814435842207708564400 76636 88372769230399860442173127009997280203 77010 h208.1 Data.chk209
  have h210 := checked_block 256 53761 88372769230399860442173127009997280203 77010 139961207071161946188762171392570907513 77418 h209.1 Data.chk210
  have h211 := checked_block 256 54017 139961207071161946188762171392570907513 77418 5443198972882919592139446013280129382 77690 h210.1 Data.chk211
  have h212 := checked_block 256 54273 5443198972882919592139446013280129382 77690 1895908528178198128914815396144556305 78132 h211.1 Data.chk212
  have h213 := checked_block 256 54529 1895908528178198128914815396144556305 78132 10337402728109361068023924158557736009 78523 h212.1 Data.chk213
  have h214 := checked_block 256 54785 10337402728109361068023924158557736009 78523 37619163355586305811966586871987921 78846 h213.1 Data.chk214
  have h215 := checked_block 256 55041 37619163355586305811966586871987921 78846 1461151274167434607625310099910715482 79203 h214.1 Data.chk215
  have h216 := checked_block 256 55297 1461151274167434607625310099910715482 79203 2701387362252301847277061249124500 79543 h215.1 Data.chk216
  have h217 := checked_block 256 55553 2701387362252301847277061249124500 79543 23551031705537377045249624500928126 79934 h216.1 Data.chk217
  have h218 := checked_block 256 55809 23551031705537377045249624500928126 79934 97263192706280495007626098243113524 80342 h217.1 Data.chk218
  have h219 := checked_block 256 56065 97263192706280495007626098243113524 80342 5772881991659290725617911359487489659 80699 h218.1 Data.chk219
  have h220 := checked_block 256 56321 5772881991659290725617911359487489659 80699 30624686434124667815389899072547504472 81107 h219.1 Data.chk220
  have h221 := checked_block 256 56577 30624686434124667815389899072547504472 81107 182636304712280208105527598380408260901 81515 h220.1 Data.chk221
  have h222 := checked_block 256 56833 182636304712280208105527598380408260901 81515 9317628146224255150633285194858079 81940 h221.1 Data.chk222
  have h223 := checked_block 256 57089 9317628146224255150633285194858079 81940 159731569221948291697643161559560582 82331 h222.1 Data.chk223
  have h224 := checked_block 256 57345 159731569221948291697643161559560582 82331 36404949987265189377629466917364585699 82671 h223.1 Data.chk224
  have h225 := checked_block 256 57601 36404949987265189377629466917364585699 82671 2644128445941219826845026577368462 83096 h224.1 Data.chk225
  have h226 := checked_block 256 57857 2644128445941219826845026577368462 83096 325868645792594377448671780413450430 83453 h225.1 Data.chk226
  have h227 := checked_block 256 58113 325868645792594377448671780413450430 83453 19627957507936047151742374660921112093 83827 h226.1 Data.chk227
  have h228 := checked_block 256 58369 19627957507936047151742374660921112093 83827 22402445183256019754217431196784440 84201 h227.1 Data.chk228
  have h229 := checked_block 256 58625 22402445183256019754217431196784440 84201 3467894739592899834030481892329177 84473 h228.1 Data.chk229
  have h230 := checked_block 256 58881 3467894739592899834030481892329177 84473 311896853297615976985387767257036160657 84932 h229.1 Data.chk230
  have h231 := checked_block 256 59137 311896853297615976985387767257036160657 84932 98607598842486282552476994007205315 85340 h230.1 Data.chk231
  have h232 := checked_block 256 59393 98607598842486282552476994007205315 85340 9977739389516890597089878961360352344 85714 h231.1 Data.chk232
  have h233 := checked_block 256 59649 9977739389516890597089878961360352344 85714 40819460117297010882255929586990282 86071 h232.1 Data.chk233
  have h234 := checked_block 256 59905 40819460117297010882255929586990282 86071 5128580106564619879068482234540420992 86445 h233.1 Data.chk234
  have h235 := checked_block 256 60161 5128580106564619879068482234540420992 86445 120943521597982100801950302163681217 86768 h234.1 Data.chk235
  have h236 := checked_block 256 60417 120943521597982100801950302163681217 86768 87296364816266629979177320590509589873 87108 h235.1 Data.chk236
  have h237 := checked_block 256 60673 87296364816266629979177320590509589873 87108 52470651663634575145765296785280271 87516 h236.1 Data.chk237
  have h238 := checked_block 256 60929 52470651663634575145765296785280271 87516 3416468518518796233122650822380142 87822 h237.1 Data.chk238
  have h239 := checked_block 256 61185 3416468518518796233122650822380142 87822 14841250293195367545638763538158883385 88128 h238.1 Data.chk239
  have h240 := checked_block 256 61441 14841250293195367545638763538158883385 88128 165853792305795982231593488938141821772 88570 h239.1 Data.chk240
  have h241 := checked_block 256 61697 165853792305795982231593488938141821772 88570 29018001505276209417359107797908396653 88859 h240.1 Data.chk241
  have h242 := checked_block 256 61953 29018001505276209417359107797908396653 88859 6556885177855915286848911788506209 89301 h241.1 Data.chk242
  have h243 := checked_block 256 62209 6556885177855915286848911788506209 89301 2793632415128608755565825253437397 89573 h242.1 Data.chk243
  have h244 := checked_block 256 62465 2793632415128608755565825253437397 89573 944019286661724506824268938911884904 89947 h243.1 Data.chk244
  have h245 := checked_block 256 62721 944019286661724506824268938911884904 89947 11735766577876821861984782650204380 90304 h244.1 Data.chk245
  have h246 := checked_block 256 62977 11735766577876821861984782650204380 90304 89831239671144580736664298864391267573 90610 h245.1 Data.chk246
  have h247 := checked_block 256 63233 89831239671144580736664298864391267573 90610 35383140363154683350270201198716164 91052 h246.1 Data.chk247
  have h248 := checked_block 256 63489 35383140363154683350270201198716164 91052 233169320306296297420207690401598241 91528 h247.1 Data.chk248
  have h249 := checked_block 256 63745 233169320306296297420207690401598241 91528 17351562308176409932966087624620605 91851 h248.1 Data.chk249
  have h250 := checked_block 256 64001 17351562308176409932966087624620605 91851 89902476362978231406580336493415953289 92174 h249.1 Data.chk250
  have h251 := checked_block 256 64257 89902476362978231406580336493415953289 92174 7888354778139523077784387364809318324 92497 h250.1 Data.chk251
  have h252 := checked_block 256 64513 7888354778139523077784387364809318324 92497 749534204781986843940886533837433797 92820 h251.1 Data.chk252
  have h253 := checked_block 256 64769 749534204781986843940886533837433797 92820 38076957832996826226595239129218622 93160 h252.1 Data.chk253
  have h254 := checked_block 256 65025 38076957832996826226595239129218622 93160 8328474042894232965458381006111958306 93568 h253.1 Data.chk254
  have h255 := checked_block 256 65281 8328474042894232965458381006111958306 93568 249174934254088757830861067225184942 93925 h254.1 Data.chk255
  have h256 := checked_block 256 65537 249174934254088757830861067225184942 93925 8398286552644556946094768961629673312 94384 h255.1 Data.chk256
  have h257 := checked_block 256 65793 8398286552644556946094768961629673312 94384 150282403774960912168804174169469520 94758 h256.1 Data.chk257
  have h258 := checked_block 256 66049 150282403774960912168804174169469520 94758 89228760165113013146251266255359614 95047 h257.1 Data.chk258
  have h259 := checked_block 256 66305 89228760165113013146251266255359614 95047 250500964706514480066065836475387662168 95404 h258.1 Data.chk259
  have h260 := checked_block 256 66561 250500964706514480066065836475387662168 95404 11480871212017525799197427972800888208 95761 h259.1 Data.chk260
  have h261 := checked_block 256 66817 11480871212017525799197427972800888208 95761 76457976227027727063598023320740777 96169 h260.1 Data.chk261
  have h262 := checked_block 256 67073 76457976227027727063598023320740777 96169 278274374166653592384768568596209928637 96526 h261.1 Data.chk262
  have h263 := checked_block 256 67329 278274374166653592384768568596209928637 96526 305987624379102129984823473254796703 96985 h262.1 Data.chk263
  have h264 := checked_block 256 67585 305987624379102129984823473254796703 96985 10170329553086325566436210080086853 97359 h263.1 Data.chk264
  have h265 := checked_block 256 67841 10170329553086325566436210080086853 97359 48029313961763151576822090009605231651 97716 h264.1 Data.chk265
  have h266 := checked_block 256 68097 48029313961763151576822090009605231651 97716 25700340876611845740144246970578690308 98022 h265.1 Data.chk266
  have h267 := checked_block 256 68353 25700340876611845740144246970578690308 98022 4050965949210237086531434480941656472 98362 h266.1 Data.chk267
  have h268 := checked_block 256 68609 4050965949210237086531434480941656472 98362 360758786783766540364389018165399787 98719 h267.1 Data.chk268
  have h269 := checked_block 256 68865 360758786783766540364389018165399787 98719 34769526314113490072283602223831754 99076 h268.1 Data.chk269
  have h270 := checked_block 256 69121 34769526314113490072283602223831754 99076 6881923526709051781873934359614073 99416 h269.1 Data.chk270
  have h271 := checked_block 256 69377 6881923526709051781873934359614073 99416 191802496383698907935282536346765919159 99739 h270.1 Data.chk271
  have h272 := checked_block 256 69633 191802496383698907935282536346765919159 99739 44651663354177001459200157721604984205 100079 h271.1 Data.chk272
  have h273 := checked_block 223 69889 44651663354177001459200157721604984205 100079 39094912334171351242361442093496208658 100385 h272.1 Data.chk273
  refine ⟨h273.1, ?_⟩
  intro k hklo hkhi hk255
  by_cases hsplit240 : k ≤ 61441
  · by_cases hsplit223 : k ≤ 57089
    · by_cases hsplit215 : k ≤ 55041
      · by_cases hsplit211 : k ≤ 54017
        · by_cases hsplit209 : k ≤ 53505
          · by_cases hsplit208 : k ≤ 53249
            · exact h207.2 k (by omega) (by omega) hk255
            · exact h208.2 k (by omega) (by omega) hk255
          · by_cases hsplit210 : k ≤ 53761
            · exact h209.2 k (by omega) (by omega) hk255
            · exact h210.2 k (by omega) (by omega) hk255
        · by_cases hsplit213 : k ≤ 54529
          · by_cases hsplit212 : k ≤ 54273
            · exact h211.2 k (by omega) (by omega) hk255
            · exact h212.2 k (by omega) (by omega) hk255
          · by_cases hsplit214 : k ≤ 54785
            · exact h213.2 k (by omega) (by omega) hk255
            · exact h214.2 k (by omega) (by omega) hk255
      · by_cases hsplit219 : k ≤ 56065
        · by_cases hsplit217 : k ≤ 55553
          · by_cases hsplit216 : k ≤ 55297
            · exact h215.2 k (by omega) (by omega) hk255
            · exact h216.2 k (by omega) (by omega) hk255
          · by_cases hsplit218 : k ≤ 55809
            · exact h217.2 k (by omega) (by omega) hk255
            · exact h218.2 k (by omega) (by omega) hk255
        · by_cases hsplit221 : k ≤ 56577
          · by_cases hsplit220 : k ≤ 56321
            · exact h219.2 k (by omega) (by omega) hk255
            · exact h220.2 k (by omega) (by omega) hk255
          · by_cases hsplit222 : k ≤ 56833
            · exact h221.2 k (by omega) (by omega) hk255
            · exact h222.2 k (by omega) (by omega) hk255
    · by_cases hsplit231 : k ≤ 59137
      · by_cases hsplit227 : k ≤ 58113
        · by_cases hsplit225 : k ≤ 57601
          · by_cases hsplit224 : k ≤ 57345
            · exact h223.2 k (by omega) (by omega) hk255
            · exact h224.2 k (by omega) (by omega) hk255
          · by_cases hsplit226 : k ≤ 57857
            · exact h225.2 k (by omega) (by omega) hk255
            · exact h226.2 k (by omega) (by omega) hk255
        · by_cases hsplit229 : k ≤ 58625
          · by_cases hsplit228 : k ≤ 58369
            · exact h227.2 k (by omega) (by omega) hk255
            · exact h228.2 k (by omega) (by omega) hk255
          · by_cases hsplit230 : k ≤ 58881
            · exact h229.2 k (by omega) (by omega) hk255
            · exact h230.2 k (by omega) (by omega) hk255
      · by_cases hsplit235 : k ≤ 60161
        · by_cases hsplit233 : k ≤ 59649
          · by_cases hsplit232 : k ≤ 59393
            · exact h231.2 k (by omega) (by omega) hk255
            · exact h232.2 k (by omega) (by omega) hk255
          · by_cases hsplit234 : k ≤ 59905
            · exact h233.2 k (by omega) (by omega) hk255
            · exact h234.2 k (by omega) (by omega) hk255
        · by_cases hsplit237 : k ≤ 60673
          · by_cases hsplit236 : k ≤ 60417
            · exact h235.2 k (by omega) (by omega) hk255
            · exact h236.2 k (by omega) (by omega) hk255
          · by_cases hsplit238 : k ≤ 60929
            · exact h237.2 k (by omega) (by omega) hk255
            · by_cases hsplit239 : k ≤ 61185
              · exact h238.2 k (by omega) (by omega) hk255
              · exact h239.2 k (by omega) (by omega) hk255
  · by_cases hsplit257 : k ≤ 65793
    · by_cases hsplit248 : k ≤ 63489
      · by_cases hsplit244 : k ≤ 62465
        · by_cases hsplit242 : k ≤ 61953
          · by_cases hsplit241 : k ≤ 61697
            · exact h240.2 k (by omega) (by omega) hk255
            · exact h241.2 k (by omega) (by omega) hk255
          · by_cases hsplit243 : k ≤ 62209
            · exact h242.2 k (by omega) (by omega) hk255
            · exact h243.2 k (by omega) (by omega) hk255
        · by_cases hsplit246 : k ≤ 62977
          · by_cases hsplit245 : k ≤ 62721
            · exact h244.2 k (by omega) (by omega) hk255
            · exact h245.2 k (by omega) (by omega) hk255
          · by_cases hsplit247 : k ≤ 63233
            · exact h246.2 k (by omega) (by omega) hk255
            · exact h247.2 k (by omega) (by omega) hk255
      · by_cases hsplit252 : k ≤ 64513
        · by_cases hsplit250 : k ≤ 64001
          · by_cases hsplit249 : k ≤ 63745
            · exact h248.2 k (by omega) (by omega) hk255
            · exact h249.2 k (by omega) (by omega) hk255
          · by_cases hsplit251 : k ≤ 64257
            · exact h250.2 k (by omega) (by omega) hk255
            · exact h251.2 k (by omega) (by omega) hk255
        · by_cases hsplit254 : k ≤ 65025
          · by_cases hsplit253 : k ≤ 64769
            · exact h252.2 k (by omega) (by omega) hk255
            · exact h253.2 k (by omega) (by omega) hk255
          · by_cases hsplit255 : k ≤ 65281
            · exact h254.2 k (by omega) (by omega) hk255
            · by_cases hsplit256 : k ≤ 65537
              · exact h255.2 k (by omega) (by omega) hk255
              · exact h256.2 k (by omega) (by omega) hk255
    · by_cases hsplit265 : k ≤ 67841
      · by_cases hsplit261 : k ≤ 66817
        · by_cases hsplit259 : k ≤ 66305
          · by_cases hsplit258 : k ≤ 66049
            · exact h257.2 k (by omega) (by omega) hk255
            · exact h258.2 k (by omega) (by omega) hk255
          · by_cases hsplit260 : k ≤ 66561
            · exact h259.2 k (by omega) (by omega) hk255
            · exact h260.2 k (by omega) (by omega) hk255
        · by_cases hsplit263 : k ≤ 67329
          · by_cases hsplit262 : k ≤ 67073
            · exact h261.2 k (by omega) (by omega) hk255
            · exact h262.2 k (by omega) (by omega) hk255
          · by_cases hsplit264 : k ≤ 67585
            · exact h263.2 k (by omega) (by omega) hk255
            · exact h264.2 k (by omega) (by omega) hk255
      · by_cases hsplit269 : k ≤ 68865
        · by_cases hsplit267 : k ≤ 68353
          · by_cases hsplit266 : k ≤ 68097
            · exact h265.2 k (by omega) (by omega) hk255
            · exact h266.2 k (by omega) (by omega) hk255
          · by_cases hsplit268 : k ≤ 68609
            · exact h267.2 k (by omega) (by omega) hk255
            · exact h268.2 k (by omega) (by omega) hk255
        · by_cases hsplit271 : k ≤ 69377
          · by_cases hsplit270 : k ≤ 69121
            · exact h269.2 k (by omega) (by omega) hk255
            · exact h270.2 k (by omega) (by omega) hk255
          · by_cases hsplit272 : k ≤ 69633
            · exact h271.2 k (by omega) (by omega) hk255
            · by_cases hsplit273 : k ≤ 69889
              · exact h272.2 k (by omega) (by omega) hk255
              · exact h273.2 k (by omega) (by omega) hk255

end DusartFiniteMesh.UpperScan


