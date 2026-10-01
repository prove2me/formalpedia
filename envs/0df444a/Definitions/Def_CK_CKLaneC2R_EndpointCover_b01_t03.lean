-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b01_t03
-- name    : CK_CKLaneC2R_EndpointCover_b01_t03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:54:51.038405+00:00
-- url     : https://prove2.me/theorems/41012dd6-de58-4eb4-8e86-9ed61f9bc143
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 4 of 5 of 1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 4 of 5 of 1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 4 of 5 of 1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 4 of 5 of 1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 4 of 5 of 1).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B042
import Definitions.Def_CK_CKLaneC2R_EpCells_B043
import Definitions.Def_CK_CKLaneC2R_EpCells_B044
namespace CKLaneC2R.EndpointCover

theorem cover_sub_008 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : ¬ (a ≤ ((10449/64000 : ℚ) : ℝ))) (h1029 : a ≤ ((21747/128000 : ℚ) : ℝ)) (h1030 : a ≤ ((8529/51200 : ℚ) : ℝ)) (h1031 : a ≤ ((84441/512000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1032 : a ≤ ((168033/1024000 : ℚ) : ℝ)
  · -- left
    by_cases h1033 : a ≤ ((335217/2048000 : ℚ) : ℝ)
    · -- left
      by_cases h1034 : a ≤ ((133917/819200 : ℚ) : ℝ)
      · -- left
        by_cases h1035 : a ≤ ((1338321/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h1036 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1037 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1038 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2552_pos (not_le.mp h5).le h1035 hz1 h1038 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2554_pos (not_le.mp h5).le h1035 (not_le.mp h1038).le h1037 hz
            · -- right
              by_cases h1039 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2560_pos (not_le.mp h5).le h1035 (not_le.mp h1037).le h1039 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2562_pos (not_le.mp h5).le h1035 (not_le.mp h1039).le h1036 hz
          · -- right
            by_cases h1040 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1041 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2584_pos (not_le.mp h5).le h1035 (not_le.mp h1036).le h1041 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2586_pos (not_le.mp h5).le h1035 (not_le.mp h1041).le h1040 hz
            · -- right
              by_cases h1042 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2592_pos (not_le.mp h5).le h1035 (not_le.mp h1040).le h1042 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2594_pos (not_le.mp h5).le h1035 (not_le.mp h1042).le hz2 hz
        · -- right
          by_cases h1043 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1044 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1045 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2553_pos (not_le.mp h1035).le h1034 hz1 h1045 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2555_pos (not_le.mp h1035).le h1034 (not_le.mp h1045).le h1044 hz
            · -- right
              by_cases h1046 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2561_pos (not_le.mp h1035).le h1034 (not_le.mp h1044).le h1046 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2563_pos (not_le.mp h1035).le h1034 (not_le.mp h1046).le h1043 hz
          · -- right
            by_cases h1047 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1048 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2585_pos (not_le.mp h1035).le h1034 (not_le.mp h1043).le h1048 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2587_pos (not_le.mp h1035).le h1034 (not_le.mp h1048).le h1047 hz
            · -- right
              by_cases h1049 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2593_pos (not_le.mp h1035).le h1034 (not_le.mp h1047).le h1049 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2595_pos (not_le.mp h1035).le h1034 (not_le.mp h1049).le hz2 hz
      · -- right
        by_cases h1050 : a ≤ ((1340019/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h1051 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1052 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1053 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2556_pos (not_le.mp h1034).le h1050 hz1 h1053 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2558_pos (not_le.mp h1034).le h1050 (not_le.mp h1053).le h1052 hz
            · -- right
              by_cases h1054 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2564_pos (not_le.mp h1034).le h1050 (not_le.mp h1052).le h1054 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2566_pos (not_le.mp h1034).le h1050 (not_le.mp h1054).le h1051 hz
          · -- right
            by_cases h1055 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1056 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2588_pos (not_le.mp h1034).le h1050 (not_le.mp h1051).le h1056 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2590_pos (not_le.mp h1034).le h1050 (not_le.mp h1056).le h1055 hz
            · -- right
              by_cases h1057 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2596_pos (not_le.mp h1034).le h1050 (not_le.mp h1055).le h1057 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2598_pos (not_le.mp h1034).le h1050 (not_le.mp h1057).le hz2 hz
        · -- right
          by_cases h1058 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1059 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1060 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2557_pos (not_le.mp h1050).le h1033 hz1 h1060 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2559_pos (not_le.mp h1050).le h1033 (not_le.mp h1060).le h1059 hz
            · -- right
              by_cases h1061 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2565_pos (not_le.mp h1050).le h1033 (not_le.mp h1059).le h1061 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2567_pos (not_le.mp h1050).le h1033 (not_le.mp h1061).le h1058 hz
          · -- right
            by_cases h1062 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1063 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2589_pos (not_le.mp h1050).le h1033 (not_le.mp h1058).le h1063 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2591_pos (not_le.mp h1050).le h1033 (not_le.mp h1063).le h1062 hz
            · -- right
              by_cases h1064 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2597_pos (not_le.mp h1050).le h1033 (not_le.mp h1062).le h1064 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2599_pos (not_le.mp h1050).le h1033 (not_le.mp h1064).le hz2 hz
    · -- right
      by_cases h1065 : a ≤ ((671283/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h1066 : a ≤ ((1341717/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h1067 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1068 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1069 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2568_pos (not_le.mp h1033).le h1066 hz1 h1069 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2570_pos (not_le.mp h1033).le h1066 (not_le.mp h1069).le h1068 hz
            · -- right
              by_cases h1070 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2576_pos (not_le.mp h1033).le h1066 (not_le.mp h1068).le h1070 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2578_pos (not_le.mp h1033).le h1066 (not_le.mp h1070).le h1067 hz
          · -- right
            by_cases h1071 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1072 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2600_pos (not_le.mp h1033).le h1066 (not_le.mp h1067).le h1072 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2602_pos (not_le.mp h1033).le h1066 (not_le.mp h1072).le h1071 hz
            · -- right
              by_cases h1073 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2608_pos (not_le.mp h1033).le h1066 (not_le.mp h1071).le h1073 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2610_pos (not_le.mp h1033).le h1066 (not_le.mp h1073).le hz2 hz
        · -- right
          by_cases h1074 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1075 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1076 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2569_pos (not_le.mp h1066).le h1065 hz1 h1076 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2571_pos (not_le.mp h1066).le h1065 (not_le.mp h1076).le h1075 hz
            · -- right
              by_cases h1077 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2577_pos (not_le.mp h1066).le h1065 (not_le.mp h1075).le h1077 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2579_pos (not_le.mp h1066).le h1065 (not_le.mp h1077).le h1074 hz
          · -- right
            by_cases h1078 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1079 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2601_pos (not_le.mp h1066).le h1065 (not_le.mp h1074).le h1079 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2603_pos (not_le.mp h1066).le h1065 (not_le.mp h1079).le h1078 hz
            · -- right
              by_cases h1080 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2609_pos (not_le.mp h1066).le h1065 (not_le.mp h1078).le h1080 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2611_pos (not_le.mp h1066).le h1065 (not_le.mp h1080).le hz2 hz
      · -- right
        by_cases h1081 : a ≤ ((268683/1638400 : ℚ) : ℝ)
        · -- left
          by_cases h1082 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1083 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1084 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2572_pos (not_le.mp h1065).le h1081 hz1 h1084 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2574_pos (not_le.mp h1065).le h1081 (not_le.mp h1084).le h1083 hz
            · -- right
              by_cases h1085 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2580_pos (not_le.mp h1065).le h1081 (not_le.mp h1083).le h1085 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2582_pos (not_le.mp h1065).le h1081 (not_le.mp h1085).le h1082 hz
          · -- right
            by_cases h1086 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1087 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2604_pos (not_le.mp h1065).le h1081 (not_le.mp h1082).le h1087 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2606_pos (not_le.mp h1065).le h1081 (not_le.mp h1087).le h1086 hz
            · -- right
              by_cases h1088 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2612_pos (not_le.mp h1065).le h1081 (not_le.mp h1086).le h1088 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2614_pos (not_le.mp h1065).le h1081 (not_le.mp h1088).le hz2 hz
        · -- right
          by_cases h1089 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1090 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1091 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2573_pos (not_le.mp h1081).le h1032 hz1 h1091 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2575_pos (not_le.mp h1081).le h1032 (not_le.mp h1091).le h1090 hz
            · -- right
              by_cases h1092 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2581_pos (not_le.mp h1081).le h1032 (not_le.mp h1090).le h1092 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2583_pos (not_le.mp h1081).le h1032 (not_le.mp h1092).le h1089 hz
          · -- right
            by_cases h1093 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1094 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2605_pos (not_le.mp h1081).le h1032 (not_le.mp h1089).le h1094 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2607_pos (not_le.mp h1081).le h1032 (not_le.mp h1094).le h1093 hz
            · -- right
              by_cases h1095 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2613_pos (not_le.mp h1081).le h1032 (not_le.mp h1093).le h1095 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2615_pos (not_le.mp h1081).le h1032 (not_le.mp h1095).le hz2 hz
  · -- right
    by_cases h1096 : a ≤ ((67383/409600 : ℚ) : ℝ)
    · -- left
      by_cases h1097 : a ≤ ((672981/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h1098 : a ≤ ((1345113/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h1099 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1100 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1101 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2616_pos (not_le.mp h1032).le h1098 hz1 h1101 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2618_pos (not_le.mp h1032).le h1098 (not_le.mp h1101).le h1100 hz
            · -- right
              by_cases h1102 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2624_pos (not_le.mp h1032).le h1098 (not_le.mp h1100).le h1102 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2626_pos (not_le.mp h1032).le h1098 (not_le.mp h1102).le h1099 hz
          · -- right
            by_cases h1103 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1104 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2648_pos (not_le.mp h1032).le h1098 (not_le.mp h1099).le h1104 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2650_pos (not_le.mp h1032).le h1098 (not_le.mp h1104).le h1103 hz
            · -- right
              by_cases h1105 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2656_pos (not_le.mp h1032).le h1098 (not_le.mp h1103).le h1105 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2658_pos (not_le.mp h1032).le h1098 (not_le.mp h1105).le hz2 hz
        · -- right
          by_cases h1106 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1107 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1108 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2617_pos (not_le.mp h1098).le h1097 hz1 h1108 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2619_pos (not_le.mp h1098).le h1097 (not_le.mp h1108).le h1107 hz
            · -- right
              by_cases h1109 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2625_pos (not_le.mp h1098).le h1097 (not_le.mp h1107).le h1109 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2627_pos (not_le.mp h1098).le h1097 (not_le.mp h1109).le h1106 hz
          · -- right
            by_cases h1110 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1111 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2649_pos (not_le.mp h1098).le h1097 (not_le.mp h1106).le h1111 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2651_pos (not_le.mp h1098).le h1097 (not_le.mp h1111).le h1110 hz
            · -- right
              by_cases h1112 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2657_pos (not_le.mp h1098).le h1097 (not_le.mp h1110).le h1112 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2659_pos (not_le.mp h1098).le h1097 (not_le.mp h1112).le hz2 hz
      · -- right
        by_cases h1113 : a ≤ ((1346811/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h1114 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1115 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1116 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2620_pos (not_le.mp h1097).le h1113 hz1 h1116 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2622_pos (not_le.mp h1097).le h1113 (not_le.mp h1116).le h1115 hz
            · -- right
              by_cases h1117 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2628_pos (not_le.mp h1097).le h1113 (not_le.mp h1115).le h1117 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2630_pos (not_le.mp h1097).le h1113 (not_le.mp h1117).le h1114 hz
          · -- right
            by_cases h1118 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1119 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2652_pos (not_le.mp h1097).le h1113 (not_le.mp h1114).le h1119 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2654_pos (not_le.mp h1097).le h1113 (not_le.mp h1119).le h1118 hz
            · -- right
              by_cases h1120 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2660_pos (not_le.mp h1097).le h1113 (not_le.mp h1118).le h1120 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2662_pos (not_le.mp h1097).le h1113 (not_le.mp h1120).le hz2 hz
        · -- right
          by_cases h1121 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1122 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1123 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2621_pos (not_le.mp h1113).le h1096 hz1 h1123 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2623_pos (not_le.mp h1113).le h1096 (not_le.mp h1123).le h1122 hz
            · -- right
              by_cases h1124 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2629_pos (not_le.mp h1113).le h1096 (not_le.mp h1122).le h1124 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2631_pos (not_le.mp h1113).le h1096 (not_le.mp h1124).le h1121 hz
          · -- right
            by_cases h1125 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1126 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2653_pos (not_le.mp h1113).le h1096 (not_le.mp h1121).le h1126 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2655_pos (not_le.mp h1113).le h1096 (not_le.mp h1126).le h1125 hz
            · -- right
              by_cases h1127 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2661_pos (not_le.mp h1113).le h1096 (not_le.mp h1125).le h1127 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2663_pos (not_le.mp h1113).le h1096 (not_le.mp h1127).le hz2 hz
    · -- right
      by_cases h1128 : a ≤ ((674679/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h1129 : a ≤ ((1348509/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h1130 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1131 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1132 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2632_pos (not_le.mp h1096).le h1129 hz1 h1132 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2634_pos (not_le.mp h1096).le h1129 (not_le.mp h1132).le h1131 hz
            · -- right
              by_cases h1133 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2640_pos (not_le.mp h1096).le h1129 (not_le.mp h1131).le h1133 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2642_pos (not_le.mp h1096).le h1129 (not_le.mp h1133).le h1130 hz
          · -- right
            by_cases h1134 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1135 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2664_pos (not_le.mp h1096).le h1129 (not_le.mp h1130).le h1135 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2666_pos (not_le.mp h1096).le h1129 (not_le.mp h1135).le h1134 hz
            · -- right
              by_cases h1136 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2672_pos (not_le.mp h1096).le h1129 (not_le.mp h1134).le h1136 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2674_pos (not_le.mp h1096).le h1129 (not_le.mp h1136).le hz2 hz
        · -- right
          by_cases h1137 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1138 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1139 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2633_pos (not_le.mp h1129).le h1128 hz1 h1139 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2635_pos (not_le.mp h1129).le h1128 (not_le.mp h1139).le h1138 hz
            · -- right
              by_cases h1140 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2641_pos (not_le.mp h1129).le h1128 (not_le.mp h1138).le h1140 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2643_pos (not_le.mp h1129).le h1128 (not_le.mp h1140).le h1137 hz
          · -- right
            by_cases h1141 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1142 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2665_pos (not_le.mp h1129).le h1128 (not_le.mp h1137).le h1142 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2667_pos (not_le.mp h1129).le h1128 (not_le.mp h1142).le h1141 hz
            · -- right
              by_cases h1143 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2673_pos (not_le.mp h1129).le h1128 (not_le.mp h1141).le h1143 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2675_pos (not_le.mp h1129).le h1128 (not_le.mp h1143).le hz2 hz
      · -- right
        by_cases h1144 : a ≤ ((1350207/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h1145 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1146 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1147 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2636_pos (not_le.mp h1128).le h1144 hz1 h1147 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2638_pos (not_le.mp h1128).le h1144 (not_le.mp h1147).le h1146 hz
            · -- right
              by_cases h1148 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2644_pos (not_le.mp h1128).le h1144 (not_le.mp h1146).le h1148 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2646_pos (not_le.mp h1128).le h1144 (not_le.mp h1148).le h1145 hz
          · -- right
            by_cases h1149 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1150 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2668_pos (not_le.mp h1128).le h1144 (not_le.mp h1145).le h1150 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2670_pos (not_le.mp h1128).le h1144 (not_le.mp h1150).le h1149 hz
            · -- right
              by_cases h1151 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2676_pos (not_le.mp h1128).le h1144 (not_le.mp h1149).le h1151 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2678_pos (not_le.mp h1128).le h1144 (not_le.mp h1151).le hz2 hz
        · -- right
          by_cases h1152 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1153 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1154 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B043.e2637_pos (not_le.mp h1144).le h1031 hz1 h1154 hz
              · -- right
                exact CKLaneC2R.EpCells.B043.e2639_pos (not_le.mp h1144).le h1031 (not_le.mp h1154).le h1153 hz
            · -- right
              by_cases h1155 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2645_pos (not_le.mp h1144).le h1031 (not_le.mp h1153).le h1155 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2647_pos (not_le.mp h1144).le h1031 (not_le.mp h1155).le h1152 hz
          · -- right
            by_cases h1156 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1157 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2669_pos (not_le.mp h1144).le h1031 (not_le.mp h1152).le h1157 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2671_pos (not_le.mp h1144).le h1031 (not_le.mp h1157).le h1156 hz
            · -- right
              by_cases h1158 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2677_pos (not_le.mp h1144).le h1031 (not_le.mp h1156).le h1158 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2679_pos (not_le.mp h1144).le h1031 (not_le.mp h1158).le hz2 hz

end CKLaneC2R.EndpointCover


