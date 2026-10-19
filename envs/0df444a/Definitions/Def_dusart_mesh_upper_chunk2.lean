-- Prove2me | Definitions.Def_dusart_mesh_upper_chunk2
-- name    : dusart_mesh_upper_chunk2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T18:07:31.48573+00:00
-- url     : https://prove2.me/theorems/49939e20-2518-48d6-8c24-eeeac7d90fdc
-- title:
--   Dusart finite mesh: UpperChunk2
-- statement:
--   The UpperChunk2 component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_eval2
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
namespace DusartFiniteMesh.UpperScan

lemma chunk2 (hstart : primorial 35329 ≤ 251061393072232692188673451629438816136*2^50575) :
    primorial 52993 ≤ 35933873761357470190686731039059820*2^75922 ∧
      ∀ k : ℕ, 35329 < k → k ≤ 52993 → 255 ≤ k → Chebyshev.theta (k : ℝ) ≤ k := by
  have h138 := checked_block 256 35329 251061393072232692188673451629438816136 50575 102135575044352544001359081642268978 50949 hstart Data.chk138
  have h139 := checked_block 256 35585 102135575044352544001359081642268978 50949 8997016564382152857354230441291495 51255 h138.1 Data.chk139
  have h140 := checked_block 256 35841 8997016564382152857354230441291495 51255 50942378469256115054985890470755693 51646 h139.1 Data.chk140
  have h141 := checked_block 256 36097 50942378469256115054985890470755693 51646 4561646463720119922270288006364163018 52003 h140.1 Data.chk141
  have h142 := checked_block 256 36353 4561646463720119922270288006364163018 52003 3716650362103625280608305286681787 52377 h141.1 Data.chk142
  have h143 := checked_block 256 36609 3716650362103625280608305286681787 52377 36391432625631247099516523778071404 52768 h142.1 Data.chk143
  have h144 := checked_block 256 36865 36391432625631247099516523778071404 52768 421755284723984684575195205184944540 53159 h143.1 Data.chk144
  have h145 := checked_block 256 37121 421755284723984684575195205184944540 53159 73615995166606625036130727538725401612 53516 h144.1 Data.chk145
  have h146 := checked_block 256 37377 73615995166606625036130727538725401612 53516 101860924619957023989826004628193219466 53941 h145.1 Data.chk146
  have h147 := checked_block 256 37633 101860924619957023989826004628193219466 53941 7860762550469751476031184677652455997 54264 h146.1 Data.chk147
  have h148 := checked_block 256 37889 7860762550469751476031184677652455997 54264 28382169884328182978875337392318391868 54536 h147.1 Data.chk148
  have h149 := checked_block 256 38145 28382169884328182978875337392318391868 54536 233639716764299129615613952446183255146 54944 h148.1 Data.chk149
  have h150 := checked_block 256 38401 233639716764299129615613952446183255146 54944 94119962691101380589302517648446301057 55250 h149.1 Data.chk150
  have h151 := checked_block 256 38657 94119962691101380589302517648446301057 55250 28529909334811046380459180841826105 55658 h150.1 Data.chk151
  have h152 := checked_block 256 38913 28529909334811046380459180841826105 55658 1359441101520510517266076886945050339 56049 h151.1 Data.chk152
  have h153 := checked_block 256 39169 1359441101520510517266076886945050339 56049 76559802135077299692895061427268244499 56440 h152.1 Data.chk153
  have h154 := checked_block 256 39425 76559802135077299692895061427268244499 56440 4711740598447181415328793896589190856 56780 h153.1 Data.chk154
  have h155 := checked_block 256 39681 4711740598447181415328793896589190856 56780 2849394615625381091709640027476248 57188 h154.1 Data.chk155
  have h156 := checked_block 256 39937 2849394615625381091709640027476248 57188 877090025712096560683830299655295829 57562 h155.1 Data.chk156
  have h157 := checked_block 256 40193 877090025712096560683830299655295829 57562 29871325923787566204935810528837303188 57817 h156.1 Data.chk157
  have h158 := checked_block 256 40449 29871325923787566204935810528837303188 57817 989414140530315863095752327897054344 58174 h157.1 Data.chk158
  have h159 := checked_block 256 40705 989414140530315863095752327897054344 58174 151850381353458377679367792234787120795 58565 h158.1 Data.chk159
  have h160 := checked_block 256 40961 151850381353458377679367792234787120795 58565 670659369740670555218284449975124638 58956 h159.1 Data.chk160
  have h161 := checked_block 256 41217 670659369740670555218284449975124638 58956 34158581649848023945372198338667210 59313 h160.1 Data.chk161
  have h162 := checked_block 256 41473 34158581649848023945372198338667210 59313 2683959978694599692836029350434866331 59721 h161.1 Data.chk162
  have h163 := checked_block 256 41729 2683959978694599692836029350434866331 59721 251917313170051223521467472252804422835 60129 h162.1 Data.chk163
  have h164 := checked_block 256 41985 251917313170051223521467472252804422835 60129 659138747720153486184398292281278803 60537 h163.1 Data.chk164
  have h165 := checked_block 256 42241 659138747720153486184398292281278803 60537 8987403003069351463437914955794384728 60979 h164.1 Data.chk165
  have h166 := checked_block 256 42497 8987403003069351463437914955794384728 60979 99507757452450624289614842268837474 61370 h165.1 Data.chk166
  have h167 := checked_block 256 42753 99507757452450624289614842268837474 61370 3869093906514500512941997418112681 61744 h166.1 Data.chk167
  have h168 := checked_block 256 43009 3869093906514500512941997418112681 61744 14706287493219458629552315868206335 62050 h167.1 Data.chk168
  have h169 := checked_block 256 43265 14706287493219458629552315868206335 62050 63241933449427401865875436964638056 62356 h168.1 Data.chk169
  have h170 := checked_block 256 43521 63241933449427401865875436964638056 62356 11269832302725224031331748185189571 62713 h169.1 Data.chk170
  have h171 := checked_block 256 43777 11269832302725224031331748185189571 62713 34067253026889702400224750832420065689 63087 h170.1 Data.chk171
  have h172 := checked_block 256 44033 34067253026889702400224750832420065689 63087 34741145475212074766168895792957334 63529 h171.1 Data.chk172
  have h173 := checked_block 256 44289 34741145475212074766168895792957334 63529 241519406117679807231730757351078076 63835 h172.1 Data.chk173
  have h174 := checked_block 256 44545 241519406117679807231730757351078076 63835 8567110774341394774923417247036511 64226 h173.1 Data.chk174
  have h175 := checked_block 256 44801 8567110774341394774923417247036511 64226 8641132761451511768387923438115686 64566 h174.1 Data.chk175
  have h176 := checked_block 256 45057 8641132761451511768387923438115686 64566 9914964989073830592072581045783248 64906 h175.1 Data.chk176
  have h177 := checked_block 256 45313 9914964989073830592072581045783248 64906 202433340253514628759779697837568947057 65263 h176.1 Data.chk177
  have h178 := checked_block 256 45569 202433340253514628759779697837568947057 65263 298307739200585337739234549446570125166 65603 h177.1 Data.chk178
  have h179 := checked_block 256 45825 298307739200585337739234549446570125166 65603 10761939031886309254297955118762514 65943 h178.1 Data.chk179
  have h180 := checked_block 256 46081 10761939031886309254297955118762514 65943 116112203364742598310837164746616462559 66317 h179.1 Data.chk180
  have h181 := checked_block 256 46337 116112203364742598310837164746616462559 66317 87941607025937114891551414719240013428 66674 h180.1 Data.chk181
  have h182 := checked_block 256 46593 87941607025937114891551414719240013428 66674 9538088727501035211099058345606554058 67065 h181.1 Data.chk182
  have h183 := checked_block 256 46849 9538088727501035211099058345606554058 67065 11870716864553758210662182453119877 67354 h182.1 Data.chk183
  have h184 := checked_block 256 47105 11870716864553758210662182453119877 67354 221016550058209140131239185838948926948 67728 h183.1 Data.chk184
  have h185 := checked_block 256 47361 221016550058209140131239185838948926948 67728 36027733711832638103318315152097595751 68119 h184.1 Data.chk185
  have h186 := checked_block 256 47617 36027733711832638103318315152097595751 68119 2442107396266545702424936995334465681 68527 h185.1 Data.chk186
  have h187 := checked_block 256 47873 2442107396266545702424936995334465681 68527 10585206235440169701519055575164259124 68867 h186.1 Data.chk187
  have h188 := checked_block 256 48129 10585206235440169701519055575164259124 68867 140310662717469709531830042980342075315 69190 h187.1 Data.chk188
  have h189 := checked_block 256 48385 140310662717469709531830042980342075315 69190 38888412033938126538268117702860439530 69581 h188.1 Data.chk189
  have h190 := checked_block 256 48641 38888412033938126538268117702860439530 69581 1713357363273526766623614160824217989 70006 h189.1 Data.chk190
  have h191 := checked_block 256 48897 1713357363273526766623614160824217989 70006 11899301491222378698108729929123445858 70346 h190.1 Data.chk191
  have h192 := checked_block 256 49153 11899301491222378698108729929123445858 70346 4880479259962738730886356908182332262 70737 h191.1 Data.chk192
  have h193 := checked_block 256 49409 4880479259962738730886356908182332262 70737 6020512730476004023608062340325680390 71111 h192.1 Data.chk193
  have h194 := checked_block 256 49665 6020512730476004023608062340325680390 71111 3201734163781751367507767032291854523 71502 h193.1 Data.chk194
  have h195 := checked_block 256 49921 3201734163781751367507767032291854523 71502 108411880755026342810148089965591856 71944 h194.1 Data.chk195
  have h196 := checked_block 256 50177 108411880755026342810148089965591856 71944 1327263206016511096582140582854632474 72284 h195.1 Data.chk196
  have h197 := checked_block 256 50433 1327263206016511096582140582854632474 72284 46845054015701164363109368933761100034 72607 h196.1 Data.chk197
  have h198 := checked_block 256 50689 46845054015701164363109368933761100034 72607 36277309291277014445141933898645987 72930 h197.1 Data.chk198
  have h199 := checked_block 256 50945 36277309291277014445141933898645987 72930 240245666020585093243025859232886012 73287 h198.1 Data.chk199
  have h200 := checked_block 256 51201 240245666020585093243025859232886012 73287 107672424939509840607860931211398373 73695 h199.1 Data.chk200
  have h201 := checked_block 256 51457 107672424939509840607860931211398373 73695 21449428786680467353859786420303276 74120 h200.1 Data.chk201
  have h202 := checked_block 256 51713 21449428786680467353859786420303276 74120 199933193577634145267715463047160168 74477 h201.1 Data.chk202
  have h203 := checked_block 256 51969 199933193577634145267715463047160168 74477 829105154283277237189319363856145328 74851 h202.1 Data.chk203
  have h204 := checked_block 256 52225 829105154283277237189319363856145328 74851 2887637217466552688879115895025352 75157 h203.1 Data.chk204
  have h205 := checked_block 256 52481 2887637217466552688879115895025352 75157 320437304905366075373867168193275496466 75548 h204.1 Data.chk205
  have h206 := checked_block 256 52737 320437304905366075373867168193275496466 75548 35933873761357470190686731039059820 75922 h205.1 Data.chk206
  refine ⟨h206.1, ?_⟩
  intro k hklo hkhi hk255
  by_cases hsplit172 : k ≤ 44033
  · by_cases hsplit155 : k ≤ 39681
    · by_cases hsplit146 : k ≤ 37377
      · by_cases hsplit142 : k ≤ 36353
        · by_cases hsplit140 : k ≤ 35841
          · by_cases hsplit139 : k ≤ 35585
            · exact h138.2 k (by omega) (by omega) hk255
            · exact h139.2 k (by omega) (by omega) hk255
          · by_cases hsplit141 : k ≤ 36097
            · exact h140.2 k (by omega) (by omega) hk255
            · exact h141.2 k (by omega) (by omega) hk255
        · by_cases hsplit144 : k ≤ 36865
          · by_cases hsplit143 : k ≤ 36609
            · exact h142.2 k (by omega) (by omega) hk255
            · exact h143.2 k (by omega) (by omega) hk255
          · by_cases hsplit145 : k ≤ 37121
            · exact h144.2 k (by omega) (by omega) hk255
            · exact h145.2 k (by omega) (by omega) hk255
      · by_cases hsplit150 : k ≤ 38401
        · by_cases hsplit148 : k ≤ 37889
          · by_cases hsplit147 : k ≤ 37633
            · exact h146.2 k (by omega) (by omega) hk255
            · exact h147.2 k (by omega) (by omega) hk255
          · by_cases hsplit149 : k ≤ 38145
            · exact h148.2 k (by omega) (by omega) hk255
            · exact h149.2 k (by omega) (by omega) hk255
        · by_cases hsplit152 : k ≤ 38913
          · by_cases hsplit151 : k ≤ 38657
            · exact h150.2 k (by omega) (by omega) hk255
            · exact h151.2 k (by omega) (by omega) hk255
          · by_cases hsplit153 : k ≤ 39169
            · exact h152.2 k (by omega) (by omega) hk255
            · by_cases hsplit154 : k ≤ 39425
              · exact h153.2 k (by omega) (by omega) hk255
              · exact h154.2 k (by omega) (by omega) hk255
    · by_cases hsplit163 : k ≤ 41729
      · by_cases hsplit159 : k ≤ 40705
        · by_cases hsplit157 : k ≤ 40193
          · by_cases hsplit156 : k ≤ 39937
            · exact h155.2 k (by omega) (by omega) hk255
            · exact h156.2 k (by omega) (by omega) hk255
          · by_cases hsplit158 : k ≤ 40449
            · exact h157.2 k (by omega) (by omega) hk255
            · exact h158.2 k (by omega) (by omega) hk255
        · by_cases hsplit161 : k ≤ 41217
          · by_cases hsplit160 : k ≤ 40961
            · exact h159.2 k (by omega) (by omega) hk255
            · exact h160.2 k (by omega) (by omega) hk255
          · by_cases hsplit162 : k ≤ 41473
            · exact h161.2 k (by omega) (by omega) hk255
            · exact h162.2 k (by omega) (by omega) hk255
      · by_cases hsplit167 : k ≤ 42753
        · by_cases hsplit165 : k ≤ 42241
          · by_cases hsplit164 : k ≤ 41985
            · exact h163.2 k (by omega) (by omega) hk255
            · exact h164.2 k (by omega) (by omega) hk255
          · by_cases hsplit166 : k ≤ 42497
            · exact h165.2 k (by omega) (by omega) hk255
            · exact h166.2 k (by omega) (by omega) hk255
        · by_cases hsplit169 : k ≤ 43265
          · by_cases hsplit168 : k ≤ 43009
            · exact h167.2 k (by omega) (by omega) hk255
            · exact h168.2 k (by omega) (by omega) hk255
          · by_cases hsplit170 : k ≤ 43521
            · exact h169.2 k (by omega) (by omega) hk255
            · by_cases hsplit171 : k ≤ 43777
              · exact h170.2 k (by omega) (by omega) hk255
              · exact h171.2 k (by omega) (by omega) hk255
  · by_cases hsplit189 : k ≤ 48385
    · by_cases hsplit180 : k ≤ 46081
      · by_cases hsplit176 : k ≤ 45057
        · by_cases hsplit174 : k ≤ 44545
          · by_cases hsplit173 : k ≤ 44289
            · exact h172.2 k (by omega) (by omega) hk255
            · exact h173.2 k (by omega) (by omega) hk255
          · by_cases hsplit175 : k ≤ 44801
            · exact h174.2 k (by omega) (by omega) hk255
            · exact h175.2 k (by omega) (by omega) hk255
        · by_cases hsplit178 : k ≤ 45569
          · by_cases hsplit177 : k ≤ 45313
            · exact h176.2 k (by omega) (by omega) hk255
            · exact h177.2 k (by omega) (by omega) hk255
          · by_cases hsplit179 : k ≤ 45825
            · exact h178.2 k (by omega) (by omega) hk255
            · exact h179.2 k (by omega) (by omega) hk255
      · by_cases hsplit184 : k ≤ 47105
        · by_cases hsplit182 : k ≤ 46593
          · by_cases hsplit181 : k ≤ 46337
            · exact h180.2 k (by omega) (by omega) hk255
            · exact h181.2 k (by omega) (by omega) hk255
          · by_cases hsplit183 : k ≤ 46849
            · exact h182.2 k (by omega) (by omega) hk255
            · exact h183.2 k (by omega) (by omega) hk255
        · by_cases hsplit186 : k ≤ 47617
          · by_cases hsplit185 : k ≤ 47361
            · exact h184.2 k (by omega) (by omega) hk255
            · exact h185.2 k (by omega) (by omega) hk255
          · by_cases hsplit187 : k ≤ 47873
            · exact h186.2 k (by omega) (by omega) hk255
            · by_cases hsplit188 : k ≤ 48129
              · exact h187.2 k (by omega) (by omega) hk255
              · exact h188.2 k (by omega) (by omega) hk255
    · by_cases hsplit198 : k ≤ 50689
      · by_cases hsplit193 : k ≤ 49409
        · by_cases hsplit191 : k ≤ 48897
          · by_cases hsplit190 : k ≤ 48641
            · exact h189.2 k (by omega) (by omega) hk255
            · exact h190.2 k (by omega) (by omega) hk255
          · by_cases hsplit192 : k ≤ 49153
            · exact h191.2 k (by omega) (by omega) hk255
            · exact h192.2 k (by omega) (by omega) hk255
        · by_cases hsplit195 : k ≤ 49921
          · by_cases hsplit194 : k ≤ 49665
            · exact h193.2 k (by omega) (by omega) hk255
            · exact h194.2 k (by omega) (by omega) hk255
          · by_cases hsplit196 : k ≤ 50177
            · exact h195.2 k (by omega) (by omega) hk255
            · by_cases hsplit197 : k ≤ 50433
              · exact h196.2 k (by omega) (by omega) hk255
              · exact h197.2 k (by omega) (by omega) hk255
      · by_cases hsplit202 : k ≤ 51713
        · by_cases hsplit200 : k ≤ 51201
          · by_cases hsplit199 : k ≤ 50945
            · exact h198.2 k (by omega) (by omega) hk255
            · exact h199.2 k (by omega) (by omega) hk255
          · by_cases hsplit201 : k ≤ 51457
            · exact h200.2 k (by omega) (by omega) hk255
            · exact h201.2 k (by omega) (by omega) hk255
        · by_cases hsplit204 : k ≤ 52225
          · by_cases hsplit203 : k ≤ 51969
            · exact h202.2 k (by omega) (by omega) hk255
            · exact h203.2 k (by omega) (by omega) hk255
          · by_cases hsplit205 : k ≤ 52481
            · exact h204.2 k (by omega) (by omega) hk255
            · by_cases hsplit206 : k ≤ 52737
              · exact h205.2 k (by omega) (by omega) hk255
              · exact h206.2 k (by omega) (by omega) hk255

end DusartFiniteMesh.UpperScan


