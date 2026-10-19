-- Prove2me | Definitions.Def_dusart_mesh_upper_chunk1
-- name    : dusart_mesh_upper_chunk1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T18:04:47.66899+00:00
-- url     : https://prove2.me/theorems/450113a8-53b3-4d0f-9e70-a5f63633f2ed
-- title:
--   Dusart finite mesh: UpperChunk1
-- statement:
--   The UpperChunk1 component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_eval1
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
namespace DusartFiniteMesh.UpperScan

lemma chunk1 (hstart : primorial 17665 ≤ 3491261729215954653573072618368350052*2^25143) :
    primorial 35329 ≤ 251061393072232692188673451629438816136*2^50575 ∧
      ∀ k : ℕ, 17665 < k → k ≤ 35329 → 255 ≤ k → Chebyshev.theta (k : ℝ) ≤ k := by
  have h69 := checked_block 256 17665 3491261729215954653573072618368350052 25143 216350209319429725485265983026372798 25500 hstart Data.chk69
  have h70 := checked_block 256 17921 216350209319429725485265983026372798 25500 6468478479387927107806794803391815345 25891 h69.1 Data.chk70
  have h71 := checked_block 256 18177 6468478479387927107806794803391815345 25891 40024301940702029764408672835936122465 26299 h70.1 Data.chk71
  have h72 := checked_block 256 18433 40024301940702029764408672835936122465 26299 18604231165066482425873588546576313 26622 h71.1 Data.chk72
  have h73 := checked_block 256 18689 18604231165066482425873588546576313 26622 10742378676709291450946861391442164296 26911 h72.1 Data.chk73
  have h74 := checked_block 256 18945 10742378676709291450946861391442164296 26911 9216285589851003960548563440808557 27234 h73.1 Data.chk74
  have h75 := checked_block 256 19201 9216285589851003960548563440808557 27234 41564089031847909497734398112665121 27659 h74.1 Data.chk75
  have h76 := checked_block 256 19457 41564089031847909497734398112665121 27659 27601709485119196355580316418769057 28016 h75.1 Data.chk76
  have h77 := checked_block 256 19713 27601709485119196355580316418769057 28016 3903111349652076330179656626716372 28390 h76.1 Data.chk77
  have h78 := checked_block 256 19969 3903111349652076330179656626716372 28390 360482411808879200423182653491353688 28798 h77.1 Data.chk78
  have h79 := checked_block 256 20225 360482411808879200423182653491353688 28798 99205155165146755181033034101750070 29172 h78.1 Data.chk79
  have h80 := checked_block 256 20481 99205155165146755181033034101750070 29172 61682561887623146145215345169248041929 29478 h79.1 Data.chk80
  have h81 := checked_block 256 20737 61682561887623146145215345169248041929 29478 32148336505632962818888835429046640793 29852 h80.1 Data.chk81
  have h82 := checked_block 256 20993 32148336505632962818888835429046640793 29852 598351577451728148169051855573335849 30260 h81.1 Data.chk82
  have h83 := checked_block 256 21249 598351577451728148169051855573335849 30260 3676267620559875269882425809184091078 30617 h82.1 Data.chk83
  have h84 := checked_block 256 21505 3676267620559875269882425809184091078 30617 133436234906342821707717506087925703 31025 h83.1 Data.chk84
  have h85 := checked_block 256 21761 133436234906342821707717506087925703 31025 1449453145083722330260005052656421237 31382 h84.1 Data.chk85
  have h86 := checked_block 256 22017 1449453145083722330260005052656421237 31382 100376831881879991547287292438672447 31790 h85.1 Data.chk86
  have h87 := checked_block 256 22273 100376831881879991547287292438672447 31790 66074916352091094067356264122712033524 32113 h86.1 Data.chk87
  have h88 := checked_block 256 22529 66074916352091094067356264122712033524 32113 1532047686804330119497059106230720182 32538 h87.1 Data.chk88
  have h89 := checked_block 256 22785 1532047686804330119497059106230720182 32538 9363496823333026924255326044959056648 32912 h88.1 Data.chk89
  have h90 := checked_block 256 23041 9363496823333026924255326044959056648 32912 74682148371365975725007728668841678675 33286 h89.1 Data.chk90
  have h91 := checked_block 256 23297 74682148371365975725007728668841678675 33286 185945479958586480630840240757927300097 33575 h90.1 Data.chk91
  have h92 := checked_block 256 23553 185945479958586480630840240757927300097 33575 15229305801215228855986586178118650895 34000 h91.1 Data.chk92
  have h93 := checked_block 256 23809 15229305801215228855986586178118650895 34000 1721017393209859517531105819469550395 34425 h92.1 Data.chk93
  have h94 := checked_block 256 24065 1721017393209859517531105819469550395 34425 222543949193010091914673335848268493870 34782 h93.1 Data.chk94
  have h95 := checked_block 256 24321 222543949193010091914673335848268493870 34782 1576195664265910688648288696075274667 35139 h94.1 Data.chk95
  have h96 := checked_block 256 24577 1576195664265910688648288696075274667 35139 11439774277036728822261172278722015884 35428 h95.1 Data.chk96
  have h97 := checked_block 256 24833 11439774277036728822261172278722015884 35428 132676601870537542638537491872291652 35785 h96.1 Data.chk97
  have h98 := checked_block 256 25089 132676601870537542638537491872291652 35785 9591000507019966048716768934116771934 36159 h97.1 Data.chk98
  have h99 := checked_block 256 25345 9591000507019966048716768934116771934 36159 182109886493542057168376958017145309 36516 h98.1 Data.chk99
  have h100 := checked_block 256 25601 182109886493542057168376958017145309 36516 22052699763926603043333605870986002894 36890 h99.1 Data.chk100
  have h101 := checked_block 256 25857 22052699763926603043333605870986002894 36890 26589752338966245069648132192027864 37281 h100.1 Data.chk101
  have h102 := checked_block 256 26113 26589752338966245069648132192027864 37281 27023635559458456582307500981860237147 37638 h101.1 Data.chk102
  have h103 := checked_block 256 26369 27023635559458456582307500981860237147 37638 31749876756654121926108515231304608675 37961 h102.1 Data.chk103
  have h104 := checked_block 256 26625 31749876756654121926108515231304608675 37961 3756954648796781399665464718753596755 38420 h103.1 Data.chk104
  have h105 := checked_block 256 26881 3756954648796781399665464718753596755 38420 12361189043502785433725859740257826 38811 h104.1 Data.chk105
  have h106 := checked_block 256 27137 12361189043502785433725859740257826 38811 14772784597709512105986964564997089706 39066 h105.1 Data.chk106
  have h107 := checked_block 256 27393 14772784597709512105986964564997089706 39066 8461797705595843847450909987566552997 39406 h106.1 Data.chk107
  have h108 := checked_block 256 27649 8461797705595843847450909987566552997 39406 71721357590447200513209297619510480513 39831 h107.1 Data.chk108
  have h109 := checked_block 256 27905 71721357590447200513209297619510480513 39831 2879290459336051358825968665068331709 40205 h108.1 Data.chk109
  have h110 := checked_block 256 28161 2879290459336051358825968665068331709 40205 14573378167165791066996349548639273140 40528 h109.1 Data.chk110
  have h111 := checked_block 256 28417 14573378167165791066996349548639273140 40528 2875918402578226887602249279141730421 41004 h110.1 Data.chk111
  have h112 := checked_block 256 28673 2875918402578226887602249279141730421 41004 229139213394257342883499411800259142 41378 h111.1 Data.chk112
  have h113 := checked_block 256 28929 229139213394257342883499411800259142 41378 466465774435693912620963682272179134 41718 h112.1 Data.chk113
  have h114 := checked_block 256 29185 466465774435693912620963682272179134 41718 2892092248165291490660697460684160 42126 h113.1 Data.chk114
  have h115 := checked_block 256 29441 2892092248165291490660697460684160 42126 38766657154068109736125263177194272 42449 h114.1 Data.chk115
  have h116 := checked_block 256 29697 38766657154068109736125263177194272 42449 2763281505482175682307239066802132424 42755 h115.1 Data.chk116
  have h117 := checked_block 256 29953 2763281505482175682307239066802132424 42755 658777871612079667509355888380421939 43129 h116.1 Data.chk117
  have h118 := checked_block 256 30209 658777871612079667509355888380421939 43129 66279920491644611631382258656677397800 43435 h117.1 Data.chk118
  have h119 := checked_block 256 30465 66279920491644611631382258656677397800 43435 5558141713164881776198058667199237941 43826 h118.1 Data.chk119
  have h120 := checked_block 256 30721 5558141713164881776198058667199237941 43826 2475367734870960976910034207759693722 44200 h119.1 Data.chk120
  have h121 := checked_block 256 30977 2475367734870960976910034207759693722 44200 323424217076388598162392849425781809 44591 h120.1 Data.chk121
  have h122 := checked_block 256 31233 323424217076388598162392849425781809 44591 889803444208233124441434794126704304 44948 h121.1 Data.chk122
  have h123 := checked_block 256 31489 889803444208233124441434794126704304 44948 731158620593352414872101015064822810 45322 h122.1 Data.chk123
  have h124 := checked_block 256 31745 731158620593352414872101015064822810 45322 110891511437610134026346238182949343 45594 h123.1 Data.chk124
  have h125 := checked_block 256 32001 110891511437610134026346238182949343 45594 260950588597023955038915930563177810027 46002 h124.1 Data.chk125
  have h126 := checked_block 256 32257 260950588597023955038915930563177810027 46002 1453801803052984632944096910083161451 46444 h125.1 Data.chk126
  have h127 := checked_block 256 32513 1453801803052984632944096910083161451 46444 42093441046192226963634123697440419236 46784 h126.1 Data.chk127
  have h128 := checked_block 256 32769 42093441046192226963634123697440419236 46784 1466218215749758646806646668964350671 47209 h127.1 Data.chk128
  have h129 := checked_block 256 33025 1466218215749758646806646668964350671 47209 239414190424350723511600980165517963864 47532 h128.1 Data.chk129
  have h130 := checked_block 256 33281 239414190424350723511600980165517963864 47532 12798362865200929153929585173245351116 47957 h129.1 Data.chk130
  have h131 := checked_block 256 33537 12798362865200929153929585173245351116 47957 217929516458344864635561389323692416 48399 h130.1 Data.chk131
  have h132 := checked_block 256 33793 217929516458344864635561389323692416 48399 15358966203153330936238832809190940869 48739 h131.1 Data.chk132
  have h133 := checked_block 256 34049 15358966203153330936238832809190940869 48739 2618494175523092672768592994919183 49113 h132.1 Data.chk133
  have h134 := checked_block 256 34305 2618494175523092672768592994919183 49113 4762983173832626037221111146491702 49504 h133.1 Data.chk134
  have h135 := checked_block 256 34561 4762983173832626037221111146491702 49504 149048392824467044794474443660050159 49861 h134.1 Data.chk135
  have h136 := checked_block 256 34817 149048392824467044794474443660050159 49861 78189070719139074251447423682292418846 50184 h135.1 Data.chk136
  have h137 := checked_block 256 35073 78189070719139074251447423682292418846 50184 251061393072232692188673451629438816136 50575 h136.1 Data.chk137
  refine ⟨h137.1, ?_⟩
  intro k hklo hkhi hk255
  by_cases hsplit103 : k ≤ 26369
  · by_cases hsplit86 : k ≤ 22017
    · by_cases hsplit77 : k ≤ 19713
      · by_cases hsplit73 : k ≤ 18689
        · by_cases hsplit71 : k ≤ 18177
          · by_cases hsplit70 : k ≤ 17921
            · exact h69.2 k (by omega) (by omega) hk255
            · exact h70.2 k (by omega) (by omega) hk255
          · by_cases hsplit72 : k ≤ 18433
            · exact h71.2 k (by omega) (by omega) hk255
            · exact h72.2 k (by omega) (by omega) hk255
        · by_cases hsplit75 : k ≤ 19201
          · by_cases hsplit74 : k ≤ 18945
            · exact h73.2 k (by omega) (by omega) hk255
            · exact h74.2 k (by omega) (by omega) hk255
          · by_cases hsplit76 : k ≤ 19457
            · exact h75.2 k (by omega) (by omega) hk255
            · exact h76.2 k (by omega) (by omega) hk255
      · by_cases hsplit81 : k ≤ 20737
        · by_cases hsplit79 : k ≤ 20225
          · by_cases hsplit78 : k ≤ 19969
            · exact h77.2 k (by omega) (by omega) hk255
            · exact h78.2 k (by omega) (by omega) hk255
          · by_cases hsplit80 : k ≤ 20481
            · exact h79.2 k (by omega) (by omega) hk255
            · exact h80.2 k (by omega) (by omega) hk255
        · by_cases hsplit83 : k ≤ 21249
          · by_cases hsplit82 : k ≤ 20993
            · exact h81.2 k (by omega) (by omega) hk255
            · exact h82.2 k (by omega) (by omega) hk255
          · by_cases hsplit84 : k ≤ 21505
            · exact h83.2 k (by omega) (by omega) hk255
            · by_cases hsplit85 : k ≤ 21761
              · exact h84.2 k (by omega) (by omega) hk255
              · exact h85.2 k (by omega) (by omega) hk255
    · by_cases hsplit94 : k ≤ 24065
      · by_cases hsplit90 : k ≤ 23041
        · by_cases hsplit88 : k ≤ 22529
          · by_cases hsplit87 : k ≤ 22273
            · exact h86.2 k (by omega) (by omega) hk255
            · exact h87.2 k (by omega) (by omega) hk255
          · by_cases hsplit89 : k ≤ 22785
            · exact h88.2 k (by omega) (by omega) hk255
            · exact h89.2 k (by omega) (by omega) hk255
        · by_cases hsplit92 : k ≤ 23553
          · by_cases hsplit91 : k ≤ 23297
            · exact h90.2 k (by omega) (by omega) hk255
            · exact h91.2 k (by omega) (by omega) hk255
          · by_cases hsplit93 : k ≤ 23809
            · exact h92.2 k (by omega) (by omega) hk255
            · exact h93.2 k (by omega) (by omega) hk255
      · by_cases hsplit98 : k ≤ 25089
        · by_cases hsplit96 : k ≤ 24577
          · by_cases hsplit95 : k ≤ 24321
            · exact h94.2 k (by omega) (by omega) hk255
            · exact h95.2 k (by omega) (by omega) hk255
          · by_cases hsplit97 : k ≤ 24833
            · exact h96.2 k (by omega) (by omega) hk255
            · exact h97.2 k (by omega) (by omega) hk255
        · by_cases hsplit100 : k ≤ 25601
          · by_cases hsplit99 : k ≤ 25345
            · exact h98.2 k (by omega) (by omega) hk255
            · exact h99.2 k (by omega) (by omega) hk255
          · by_cases hsplit101 : k ≤ 25857
            · exact h100.2 k (by omega) (by omega) hk255
            · by_cases hsplit102 : k ≤ 26113
              · exact h101.2 k (by omega) (by omega) hk255
              · exact h102.2 k (by omega) (by omega) hk255
  · by_cases hsplit120 : k ≤ 30721
    · by_cases hsplit111 : k ≤ 28417
      · by_cases hsplit107 : k ≤ 27393
        · by_cases hsplit105 : k ≤ 26881
          · by_cases hsplit104 : k ≤ 26625
            · exact h103.2 k (by omega) (by omega) hk255
            · exact h104.2 k (by omega) (by omega) hk255
          · by_cases hsplit106 : k ≤ 27137
            · exact h105.2 k (by omega) (by omega) hk255
            · exact h106.2 k (by omega) (by omega) hk255
        · by_cases hsplit109 : k ≤ 27905
          · by_cases hsplit108 : k ≤ 27649
            · exact h107.2 k (by omega) (by omega) hk255
            · exact h108.2 k (by omega) (by omega) hk255
          · by_cases hsplit110 : k ≤ 28161
            · exact h109.2 k (by omega) (by omega) hk255
            · exact h110.2 k (by omega) (by omega) hk255
      · by_cases hsplit115 : k ≤ 29441
        · by_cases hsplit113 : k ≤ 28929
          · by_cases hsplit112 : k ≤ 28673
            · exact h111.2 k (by omega) (by omega) hk255
            · exact h112.2 k (by omega) (by omega) hk255
          · by_cases hsplit114 : k ≤ 29185
            · exact h113.2 k (by omega) (by omega) hk255
            · exact h114.2 k (by omega) (by omega) hk255
        · by_cases hsplit117 : k ≤ 29953
          · by_cases hsplit116 : k ≤ 29697
            · exact h115.2 k (by omega) (by omega) hk255
            · exact h116.2 k (by omega) (by omega) hk255
          · by_cases hsplit118 : k ≤ 30209
            · exact h117.2 k (by omega) (by omega) hk255
            · by_cases hsplit119 : k ≤ 30465
              · exact h118.2 k (by omega) (by omega) hk255
              · exact h119.2 k (by omega) (by omega) hk255
    · by_cases hsplit129 : k ≤ 33025
      · by_cases hsplit124 : k ≤ 31745
        · by_cases hsplit122 : k ≤ 31233
          · by_cases hsplit121 : k ≤ 30977
            · exact h120.2 k (by omega) (by omega) hk255
            · exact h121.2 k (by omega) (by omega) hk255
          · by_cases hsplit123 : k ≤ 31489
            · exact h122.2 k (by omega) (by omega) hk255
            · exact h123.2 k (by omega) (by omega) hk255
        · by_cases hsplit126 : k ≤ 32257
          · by_cases hsplit125 : k ≤ 32001
            · exact h124.2 k (by omega) (by omega) hk255
            · exact h125.2 k (by omega) (by omega) hk255
          · by_cases hsplit127 : k ≤ 32513
            · exact h126.2 k (by omega) (by omega) hk255
            · by_cases hsplit128 : k ≤ 32769
              · exact h127.2 k (by omega) (by omega) hk255
              · exact h128.2 k (by omega) (by omega) hk255
      · by_cases hsplit133 : k ≤ 34049
        · by_cases hsplit131 : k ≤ 33537
          · by_cases hsplit130 : k ≤ 33281
            · exact h129.2 k (by omega) (by omega) hk255
            · exact h130.2 k (by omega) (by omega) hk255
          · by_cases hsplit132 : k ≤ 33793
            · exact h131.2 k (by omega) (by omega) hk255
            · exact h132.2 k (by omega) (by omega) hk255
        · by_cases hsplit135 : k ≤ 34561
          · by_cases hsplit134 : k ≤ 34305
            · exact h133.2 k (by omega) (by omega) hk255
            · exact h134.2 k (by omega) (by omega) hk255
          · by_cases hsplit136 : k ≤ 34817
            · exact h135.2 k (by omega) (by omega) hk255
            · by_cases hsplit137 : k ≤ 35073
              · exact h136.2 k (by omega) (by omega) hk255
              · exact h137.2 k (by omega) (by omega) hk255

end DusartFiniteMesh.UpperScan


