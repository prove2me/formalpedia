-- Prove2me | Definitions.Def_dusart_mesh_upper_chunk0
-- name    : dusart_mesh_upper_chunk0
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T18:00:21.213989+00:00
-- url     : https://prove2.me/theorems/39e2f295-05e2-4b6e-8bf1-c508620d6af5
-- title:
--   Dusart finite mesh: UpperChunk0
-- statement:
--   The UpperChunk0 component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_eval0
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
namespace DusartFiniteMesh.UpperScan

lemma chunk0 (hstart : primorial 1 ≤ 1*2^0) :
    primorial 17665 ≤ 3491261729215954653573072618368350052*2^25143 ∧
      ∀ k : ℕ, 1 < k → k ≤ 17665 → 255 ≤ k → Chebyshev.theta (k : ℝ) ≤ k := by
  have h0 := checked_block 256 1 1 0 4901032557613177986016250345410456213 221 hstart Data.chk0
  have h1 := checked_block 256 257 4901032557613177986016250345410456213 221 32309090488692673639778817867962141081 578 h0.1 Data.chk1
  have h2 := checked_block 256 513 32309090488692673639778817867962141081 578 25377800521428871134023002861319235 952 h1.1 Data.chk2
  have h3 := checked_block 256 769 25377800521428871134023002861319235 952 244336375691992013306199842204349370213 1292 h2.1 Data.chk3
  have h4 := checked_block 256 1025 244336375691992013306199842204349370213 1292 94996186625023525266703357008366312179 1649 h3.1 Data.chk4
  have h5 := checked_block 256 1281 94996186625023525266703357008366312179 1649 365855399014840851988102976524377246 2023 h4.1 Data.chk5
  have h6 := checked_block 256 1537 365855399014840851988102976524377246 2023 6011068534052663247538269627538023 2414 h5.1 Data.chk6
  have h7 := checked_block 256 1793 6011068534052663247538269627538023 2414 237527708122809930740518549691847573889 2737 h6.1 Data.chk7
  have h8 := checked_block 256 2049 237527708122809930740518549691847573889 2737 837990461640363586003654286053547189 3111 h7.1 Data.chk8
  have h9 := checked_block 256 2305 837990461640363586003654286053547189 3111 110881169615222765500531613124565386 3485 h8.1 Data.chk9
  have h10 := checked_block 256 2561 110881169615222765500531613124565386 3485 9900021672594410795445892123196697 3876 h9.1 Data.chk10
  have h11 := checked_block 256 2817 9900021672594410795445892123196697 3876 505169022033751132712809352739866461 4216 h10.1 Data.chk11
  have h12 := checked_block 256 3073 505169022033751132712809352739866461 4216 2721265013812837414746267153728371 4573 h11.1 Data.chk12
  have h13 := checked_block 256 3329 2721265013812837414746267153728371 4573 45622327376551161839950703503905607833 4947 h12.1 Data.chk13
  have h14 := checked_block 256 3585 45622327376551161839950703503905607833 4947 18663262541475453526281614940808309869 5304 h13.1 Data.chk14
  have h15 := checked_block 256 3841 18663262541475453526281614940808309869 5304 51852580307713247345346993413233551 5695 h14.1 Data.chk15
  have h16 := checked_block 256 4097 51852580307713247345346993413233551 5695 1038240068047149219338822027543873242 6052 h15.1 Data.chk16
  have h17 := checked_block 256 4353 1038240068047149219338822027543873242 6052 27820867847532939054943433345019231 6409 h16.1 Data.chk17
  have h18 := checked_block 256 4609 27820867847532939054943433345019231 6409 96593352977948017345538963467780335 6749 h17.1 Data.chk18
  have h19 := checked_block 256 4865 96593352977948017345538963467780335 6749 83203198875209655117589981956224497441 7157 h18.1 Data.chk19
  have h20 := checked_block 256 5121 83203198875209655117589981956224497441 7157 3027172605305656151982000381686001138 7446 h19.1 Data.chk20
  have h21 := checked_block 256 5377 3027172605305656151982000381686001138 7446 48803368510702139076196305060987954 7837 h20.1 Data.chk21
  have h22 := checked_block 256 5633 48803368510702139076196305060987954 7837 10226310050773441709153638449855610233 8279 h21.1 Data.chk22
  have h23 := checked_block 256 5889 10226310050773441709153638449855610233 8279 117891865935863103450137890794059111777 8602 h22.1 Data.chk23
  have h24 := checked_block 256 6145 117891865935863103450137890794059111777 8602 298336889296641494514278622165630672 9027 h23.1 Data.chk24
  have h25 := checked_block 256 6401 298336889296641494514278622165630672 9027 1696027883795929217605328033861331251 9316 h24.1 Data.chk25
  have h26 := checked_block 256 6657 1696027883795929217605328033861331251 9316 1029506811516665231945364056575959742 9724 h25.1 Data.chk26
  have h27 := checked_block 256 6913 1029506811516665231945364056575959742 9724 34124240618094944701453187953502714759 10064 h26.1 Data.chk27
  have h28 := checked_block 256 7169 34124240618094944701453187953502714759 10064 7216478505965366389481678273826418767 10387 h27.1 Data.chk28
  have h29 := checked_block 256 7425 7216478505965366389481678273826418767 10387 7960195767070364172119029646965668124 10812 h28.1 Data.chk29
  have h30 := checked_block 256 7681 7960195767070364172119029646965668124 10812 16154889782184696159672283346682518602 11186 h29.1 Data.chk30
  have h31 := checked_block 256 7937 16154889782184696159672283346682518602 11186 45370298842301617149852801770428236432 11509 h30.1 Data.chk31
  have h32 := checked_block 256 8193 45370298842301617149852801770428236432 11509 4374326166363665924194128799207201 11900 h31.1 Data.chk32
  have h33 := checked_block 256 8449 4374326166363665924194128799207201 11900 32746426958941103410866625027492573079 12240 h32.1 Data.chk33
  have h34 := checked_block 256 8705 32746426958941103410866625027492573079 12240 17092436030985943844799088662015127 12631 h33.1 Data.chk34
  have h35 := checked_block 256 8961 17092436030985943844799088662015127 12631 2768718580399612371641403684537687745 13005 h34.1 Data.chk35
  have h36 := checked_block 256 9217 2768718580399612371641403684537687745 13005 381139636034616138208367961492141140 13430 h35.1 Data.chk36
  have h37 := checked_block 256 9473 381139636034616138208367961492141140 13430 81227145007598331075038006659843365136 13753 h36.1 Data.chk37
  have h38 := checked_block 256 9729 81227145007598331075038006659843365136 13753 77389195575057126310091328936995389 14161 h37.1 Data.chk38
  have h39 := checked_block 256 9985 77389195575057126310091328936995389 14161 60427663430636379463666966157504290741 14484 h38.1 Data.chk39
  have h40 := checked_block 256 10241 60427663430636379463666966157504290741 14484 3289179199555868766642440352503827791 14875 h39.1 Data.chk40
  have h41 := checked_block 256 10497 3289179199555868766642440352503827791 14875 4759891019973858384500097147275612740 15249 h40.1 Data.chk41
  have h42 := checked_block 256 10753 4759891019973858384500097147275612740 15249 179620787704652768109496272434637591 15589 h41.1 Data.chk42
  have h43 := checked_block 256 11009 179620787704652768109496272434637591 15589 133728189909962916613805628604634026643 15929 h42.1 Data.chk43
  have h44 := checked_block 256 11265 133728189909962916613805628604634026643 15929 118870762973359472052220203994733525 16303 h43.1 Data.chk44
  have h45 := checked_block 256 11521 118870762973359472052220203994733525 16303 2950545177352582005465115221589863 16592 h44.1 Data.chk45
  have h46 := checked_block 256 11777 2950545177352582005465115221589863 16592 105736097386751134376149655407015666155 16983 h45.1 Data.chk46
  have h47 := checked_block 256 12033 105736097386751134376149655407015666155 16983 57080953613084861379146287752105699008 17391 h46.1 Data.chk47
  have h48 := checked_block 256 12289 57080953613084861379146287752105699008 17391 50420675845848392305903031279287542 17782 h47.1 Data.chk48
  have h49 := checked_block 256 12545 50420675845848392305903031279287542 17782 9810776204490165302491558734998738108 18156 h48.1 Data.chk49
  have h50 := checked_block 256 12801 9810776204490165302491558734998738108 18156 2596453082376535309612363873674022 18564 h49.1 Data.chk50
  have h51 := checked_block 256 13057 2596453082376535309612363873674022 18564 155064454907340153164521711172655563297 18904 h50.1 Data.chk51
  have h52 := checked_block 256 13313 155064454907340153164521711172655563297 18904 83537698865331517953384227259065903 19244 h51.1 Data.chk52
  have h53 := checked_block 256 13569 83537698865331517953384227259065903 19244 145076666402482558307459921602346487996 19618 h52.1 Data.chk53
  have h54 := checked_block 256 13825 145076666402482558307459921602346487996 19618 29961410140398202712666710058175771864 19992 h53.1 Data.chk54
  have h55 := checked_block 256 14081 29961410140398202712666710058175771864 19992 48346875800715834128533257495858973132 20281 h54.1 Data.chk55
  have h56 := checked_block 256 14337 48346875800715834128533257495858973132 20281 330568541142942882372737046161493235 20689 h55.1 Data.chk56
  have h57 := checked_block 256 14593 330568541142942882372737046161493235 20689 3771944129123210691493984507488286 21097 h56.1 Data.chk57
  have h58 := checked_block 256 14849 3771944129123210691493984507488286 21097 406762927081882287793832236206759498 21437 h57.1 Data.chk58
  have h59 := checked_block 256 15105 406762927081882287793832236206759498 21437 22160870418991103098055877992846293408 21862 h58.1 Data.chk59
  have h60 := checked_block 256 15361 22160870418991103098055877992846293408 21862 42205411087134082167169121013252033 22219 h59.1 Data.chk60
  have h61 := checked_block 256 15617 42205411087134082167169121013252033 22219 26890912063234670918964868154967731 22610 h60.1 Data.chk61
  have h62 := checked_block 256 15873 26890912063234670918964868154967731 22610 3372919699747896006012278013808614 23018 h61.1 Data.chk62
  have h63 := checked_block 256 16129 3372919699747896006012278013808614 23018 186812902556672481103877091933152603987 23324 h62.1 Data.chk63
  have h64 := checked_block 256 16385 186812902556672481103877091933152603987 23324 14114596170554738781985182043681144824 23664 h63.1 Data.chk64
  have h65 := checked_block 256 16641 14114596170554738781985182043681144824 23664 1522294938443717222468200748518070401 24004 h64.1 Data.chk65
  have h66 := checked_block 256 16897 1522294938443717222468200748518070401 24004 67457577239594892847764655407043386158 24378 h65.1 Data.chk66
  have h67 := checked_block 256 17153 67457577239594892847764655407043386158 24378 35141267505656986348738897576765875 24769 h66.1 Data.chk67
  have h68 := checked_block 256 17409 35141267505656986348738897576765875 24769 3491261729215954653573072618368350052 25143 h67.1 Data.chk68
  refine ⟨h68.1, ?_⟩
  intro k hklo hkhi hk255
  by_cases hsplit34 : k ≤ 8705
  · by_cases hsplit17 : k ≤ 4353
    · by_cases hsplit8 : k ≤ 2049
      · by_cases hsplit4 : k ≤ 1025
        · by_cases hsplit2 : k ≤ 513
          · by_cases hsplit1 : k ≤ 257
            · exact h0.2 k (by omega) (by omega) hk255
            · exact h1.2 k (by omega) (by omega) hk255
          · by_cases hsplit3 : k ≤ 769
            · exact h2.2 k (by omega) (by omega) hk255
            · exact h3.2 k (by omega) (by omega) hk255
        · by_cases hsplit6 : k ≤ 1537
          · by_cases hsplit5 : k ≤ 1281
            · exact h4.2 k (by omega) (by omega) hk255
            · exact h5.2 k (by omega) (by omega) hk255
          · by_cases hsplit7 : k ≤ 1793
            · exact h6.2 k (by omega) (by omega) hk255
            · exact h7.2 k (by omega) (by omega) hk255
      · by_cases hsplit12 : k ≤ 3073
        · by_cases hsplit10 : k ≤ 2561
          · by_cases hsplit9 : k ≤ 2305
            · exact h8.2 k (by omega) (by omega) hk255
            · exact h9.2 k (by omega) (by omega) hk255
          · by_cases hsplit11 : k ≤ 2817
            · exact h10.2 k (by omega) (by omega) hk255
            · exact h11.2 k (by omega) (by omega) hk255
        · by_cases hsplit14 : k ≤ 3585
          · by_cases hsplit13 : k ≤ 3329
            · exact h12.2 k (by omega) (by omega) hk255
            · exact h13.2 k (by omega) (by omega) hk255
          · by_cases hsplit15 : k ≤ 3841
            · exact h14.2 k (by omega) (by omega) hk255
            · by_cases hsplit16 : k ≤ 4097
              · exact h15.2 k (by omega) (by omega) hk255
              · exact h16.2 k (by omega) (by omega) hk255
    · by_cases hsplit25 : k ≤ 6401
      · by_cases hsplit21 : k ≤ 5377
        · by_cases hsplit19 : k ≤ 4865
          · by_cases hsplit18 : k ≤ 4609
            · exact h17.2 k (by omega) (by omega) hk255
            · exact h18.2 k (by omega) (by omega) hk255
          · by_cases hsplit20 : k ≤ 5121
            · exact h19.2 k (by omega) (by omega) hk255
            · exact h20.2 k (by omega) (by omega) hk255
        · by_cases hsplit23 : k ≤ 5889
          · by_cases hsplit22 : k ≤ 5633
            · exact h21.2 k (by omega) (by omega) hk255
            · exact h22.2 k (by omega) (by omega) hk255
          · by_cases hsplit24 : k ≤ 6145
            · exact h23.2 k (by omega) (by omega) hk255
            · exact h24.2 k (by omega) (by omega) hk255
      · by_cases hsplit29 : k ≤ 7425
        · by_cases hsplit27 : k ≤ 6913
          · by_cases hsplit26 : k ≤ 6657
            · exact h25.2 k (by omega) (by omega) hk255
            · exact h26.2 k (by omega) (by omega) hk255
          · by_cases hsplit28 : k ≤ 7169
            · exact h27.2 k (by omega) (by omega) hk255
            · exact h28.2 k (by omega) (by omega) hk255
        · by_cases hsplit31 : k ≤ 7937
          · by_cases hsplit30 : k ≤ 7681
            · exact h29.2 k (by omega) (by omega) hk255
            · exact h30.2 k (by omega) (by omega) hk255
          · by_cases hsplit32 : k ≤ 8193
            · exact h31.2 k (by omega) (by omega) hk255
            · by_cases hsplit33 : k ≤ 8449
              · exact h32.2 k (by omega) (by omega) hk255
              · exact h33.2 k (by omega) (by omega) hk255
  · by_cases hsplit51 : k ≤ 13057
    · by_cases hsplit42 : k ≤ 10753
      · by_cases hsplit38 : k ≤ 9729
        · by_cases hsplit36 : k ≤ 9217
          · by_cases hsplit35 : k ≤ 8961
            · exact h34.2 k (by omega) (by omega) hk255
            · exact h35.2 k (by omega) (by omega) hk255
          · by_cases hsplit37 : k ≤ 9473
            · exact h36.2 k (by omega) (by omega) hk255
            · exact h37.2 k (by omega) (by omega) hk255
        · by_cases hsplit40 : k ≤ 10241
          · by_cases hsplit39 : k ≤ 9985
            · exact h38.2 k (by omega) (by omega) hk255
            · exact h39.2 k (by omega) (by omega) hk255
          · by_cases hsplit41 : k ≤ 10497
            · exact h40.2 k (by omega) (by omega) hk255
            · exact h41.2 k (by omega) (by omega) hk255
      · by_cases hsplit46 : k ≤ 11777
        · by_cases hsplit44 : k ≤ 11265
          · by_cases hsplit43 : k ≤ 11009
            · exact h42.2 k (by omega) (by omega) hk255
            · exact h43.2 k (by omega) (by omega) hk255
          · by_cases hsplit45 : k ≤ 11521
            · exact h44.2 k (by omega) (by omega) hk255
            · exact h45.2 k (by omega) (by omega) hk255
        · by_cases hsplit48 : k ≤ 12289
          · by_cases hsplit47 : k ≤ 12033
            · exact h46.2 k (by omega) (by omega) hk255
            · exact h47.2 k (by omega) (by omega) hk255
          · by_cases hsplit49 : k ≤ 12545
            · exact h48.2 k (by omega) (by omega) hk255
            · by_cases hsplit50 : k ≤ 12801
              · exact h49.2 k (by omega) (by omega) hk255
              · exact h50.2 k (by omega) (by omega) hk255
    · by_cases hsplit60 : k ≤ 15361
      · by_cases hsplit55 : k ≤ 14081
        · by_cases hsplit53 : k ≤ 13569
          · by_cases hsplit52 : k ≤ 13313
            · exact h51.2 k (by omega) (by omega) hk255
            · exact h52.2 k (by omega) (by omega) hk255
          · by_cases hsplit54 : k ≤ 13825
            · exact h53.2 k (by omega) (by omega) hk255
            · exact h54.2 k (by omega) (by omega) hk255
        · by_cases hsplit57 : k ≤ 14593
          · by_cases hsplit56 : k ≤ 14337
            · exact h55.2 k (by omega) (by omega) hk255
            · exact h56.2 k (by omega) (by omega) hk255
          · by_cases hsplit58 : k ≤ 14849
            · exact h57.2 k (by omega) (by omega) hk255
            · by_cases hsplit59 : k ≤ 15105
              · exact h58.2 k (by omega) (by omega) hk255
              · exact h59.2 k (by omega) (by omega) hk255
      · by_cases hsplit64 : k ≤ 16385
        · by_cases hsplit62 : k ≤ 15873
          · by_cases hsplit61 : k ≤ 15617
            · exact h60.2 k (by omega) (by omega) hk255
            · exact h61.2 k (by omega) (by omega) hk255
          · by_cases hsplit63 : k ≤ 16129
            · exact h62.2 k (by omega) (by omega) hk255
            · exact h63.2 k (by omega) (by omega) hk255
        · by_cases hsplit66 : k ≤ 16897
          · by_cases hsplit65 : k ≤ 16641
            · exact h64.2 k (by omega) (by omega) hk255
            · exact h65.2 k (by omega) (by omega) hk255
          · by_cases hsplit67 : k ≤ 17153
            · exact h66.2 k (by omega) (by omega) hk255
            · by_cases hsplit68 : k ≤ 17409
              · exact h67.2 k (by omega) (by omega) hk255
              · exact h68.2 k (by omega) (by omega) hk255

end DusartFiniteMesh.UpperScan


