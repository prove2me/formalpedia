-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b01_t04
-- name    : CK_CKLaneC2R_EndpointCover_b01_t04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:49:33.059452+00:00
-- url     : https://prove2.me/theorems/7c2a7bb4-3a89-4a34-ae92-acc6b22ec938
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 5 of 5 of 1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 5 of 5 of 1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 5 of 5 of 1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 5 of 5 of 1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 5 of 5 of 1).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B044
import Definitions.Def_CK_CKLaneC2R_EpCells_B045
import Definitions.Def_CK_CKLaneC2R_EpCells_B046
namespace CKLaneC2R.EndpointCover

theorem cover_sub_009 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : ¬ (a ≤ ((10449/64000 : ℚ) : ℝ))) (h1029 : a ≤ ((21747/128000 : ℚ) : ℝ)) (h1030 : a ≤ ((8529/51200 : ℚ) : ℝ)) (h1031 : ¬ (a ≤ ((84441/512000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1159 : a ≤ ((169731/1024000 : ℚ) : ℝ)
  · -- left
    by_cases h1160 : a ≤ ((338613/2048000 : ℚ) : ℝ)
    · -- left
      by_cases h1161 : a ≤ ((676377/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h1162 : a ≤ ((270381/1638400 : ℚ) : ℝ)
        · -- left
          by_cases h1163 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1164 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1165 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2680_pos (not_le.mp h1031).le h1162 hz1 h1165 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2682_pos (not_le.mp h1031).le h1162 (not_le.mp h1165).le h1164 hz
            · -- right
              by_cases h1166 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2688_pos (not_le.mp h1031).le h1162 (not_le.mp h1164).le h1166 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2690_pos (not_le.mp h1031).le h1162 (not_le.mp h1166).le h1163 hz
          · -- right
            by_cases h1167 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1168 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2712_pos (not_le.mp h1031).le h1162 (not_le.mp h1163).le h1168 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2714_pos (not_le.mp h1031).le h1162 (not_le.mp h1168).le h1167 hz
            · -- right
              by_cases h1169 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2720_pos (not_le.mp h1031).le h1162 (not_le.mp h1167).le h1169 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2722_pos (not_le.mp h1031).le h1162 (not_le.mp h1169).le hz2 hz
        · -- right
          by_cases h1170 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1171 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1172 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2681_pos (not_le.mp h1162).le h1161 hz1 h1172 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2683_pos (not_le.mp h1162).le h1161 (not_le.mp h1172).le h1171 hz
            · -- right
              by_cases h1173 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2689_pos (not_le.mp h1162).le h1161 (not_le.mp h1171).le h1173 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2691_pos (not_le.mp h1162).le h1161 (not_le.mp h1173).le h1170 hz
          · -- right
            by_cases h1174 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1175 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2713_pos (not_le.mp h1162).le h1161 (not_le.mp h1170).le h1175 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2715_pos (not_le.mp h1162).le h1161 (not_le.mp h1175).le h1174 hz
            · -- right
              by_cases h1176 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2721_pos (not_le.mp h1162).le h1161 (not_le.mp h1174).le h1176 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2723_pos (not_le.mp h1162).le h1161 (not_le.mp h1176).le hz2 hz
      · -- right
        by_cases h1177 : a ≤ ((1353603/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h1178 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1179 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1180 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2684_pos (not_le.mp h1161).le h1177 hz1 h1180 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2686_pos (not_le.mp h1161).le h1177 (not_le.mp h1180).le h1179 hz
            · -- right
              by_cases h1181 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2692_pos (not_le.mp h1161).le h1177 (not_le.mp h1179).le h1181 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2694_pos (not_le.mp h1161).le h1177 (not_le.mp h1181).le h1178 hz
          · -- right
            by_cases h1182 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1183 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2716_pos (not_le.mp h1161).le h1177 (not_le.mp h1178).le h1183 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2718_pos (not_le.mp h1161).le h1177 (not_le.mp h1183).le h1182 hz
            · -- right
              by_cases h1184 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2724_pos (not_le.mp h1161).le h1177 (not_le.mp h1182).le h1184 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2726_pos (not_le.mp h1161).le h1177 (not_le.mp h1184).le hz2 hz
        · -- right
          by_cases h1185 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1186 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1187 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2685_pos (not_le.mp h1177).le h1160 hz1 h1187 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2687_pos (not_le.mp h1177).le h1160 (not_le.mp h1187).le h1186 hz
            · -- right
              by_cases h1188 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2693_pos (not_le.mp h1177).le h1160 (not_le.mp h1186).le h1188 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2695_pos (not_le.mp h1177).le h1160 (not_le.mp h1188).le h1185 hz
          · -- right
            by_cases h1189 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1190 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2717_pos (not_le.mp h1177).le h1160 (not_le.mp h1185).le h1190 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2719_pos (not_le.mp h1177).le h1160 (not_le.mp h1190).le h1189 hz
            · -- right
              by_cases h1191 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2725_pos (not_le.mp h1177).le h1160 (not_le.mp h1189).le h1191 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2727_pos (not_le.mp h1177).le h1160 (not_le.mp h1191).le hz2 hz
    · -- right
      by_cases h1192 : a ≤ ((27123/163840 : ℚ) : ℝ)
      · -- left
        by_cases h1193 : a ≤ ((1355301/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h1194 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1195 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1196 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2696_pos (not_le.mp h1160).le h1193 hz1 h1196 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2698_pos (not_le.mp h1160).le h1193 (not_le.mp h1196).le h1195 hz
            · -- right
              by_cases h1197 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2704_pos (not_le.mp h1160).le h1193 (not_le.mp h1195).le h1197 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2706_pos (not_le.mp h1160).le h1193 (not_le.mp h1197).le h1194 hz
          · -- right
            by_cases h1198 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1199 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2728_pos (not_le.mp h1160).le h1193 (not_le.mp h1194).le h1199 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2730_pos (not_le.mp h1160).le h1193 (not_le.mp h1199).le h1198 hz
            · -- right
              by_cases h1200 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2736_pos (not_le.mp h1160).le h1193 (not_le.mp h1198).le h1200 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2738_pos (not_le.mp h1160).le h1193 (not_le.mp h1200).le hz2 hz
        · -- right
          by_cases h1201 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1202 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1203 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B044.e2697_pos (not_le.mp h1193).le h1192 hz1 h1203 hz
              · -- right
                exact CKLaneC2R.EpCells.B044.e2699_pos (not_le.mp h1193).le h1192 (not_le.mp h1203).le h1202 hz
            · -- right
              by_cases h1204 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2705_pos (not_le.mp h1193).le h1192 (not_le.mp h1202).le h1204 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2707_pos (not_le.mp h1193).le h1192 (not_le.mp h1204).le h1201 hz
          · -- right
            by_cases h1205 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1206 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2729_pos (not_le.mp h1193).le h1192 (not_le.mp h1201).le h1206 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2731_pos (not_le.mp h1193).le h1192 (not_le.mp h1206).le h1205 hz
            · -- right
              by_cases h1207 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2737_pos (not_le.mp h1193).le h1192 (not_le.mp h1205).le h1207 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2739_pos (not_le.mp h1193).le h1192 (not_le.mp h1207).le hz2 hz
      · -- right
        by_cases h1208 : a ≤ ((1356999/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h1209 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1210 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1211 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2700_pos (not_le.mp h1192).le h1208 hz1 h1211 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2702_pos (not_le.mp h1192).le h1208 (not_le.mp h1211).le h1210 hz
            · -- right
              by_cases h1212 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2708_pos (not_le.mp h1192).le h1208 (not_le.mp h1210).le h1212 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2710_pos (not_le.mp h1192).le h1208 (not_le.mp h1212).le h1209 hz
          · -- right
            by_cases h1213 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1214 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2732_pos (not_le.mp h1192).le h1208 (not_le.mp h1209).le h1214 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2734_pos (not_le.mp h1192).le h1208 (not_le.mp h1214).le h1213 hz
            · -- right
              by_cases h1215 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2740_pos (not_le.mp h1192).le h1208 (not_le.mp h1213).le h1215 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2742_pos (not_le.mp h1192).le h1208 (not_le.mp h1215).le hz2 hz
        · -- right
          by_cases h1216 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1217 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1218 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2701_pos (not_le.mp h1208).le h1159 hz1 h1218 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2703_pos (not_le.mp h1208).le h1159 (not_le.mp h1218).le h1217 hz
            · -- right
              by_cases h1219 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2709_pos (not_le.mp h1208).le h1159 (not_le.mp h1217).le h1219 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2711_pos (not_le.mp h1208).le h1159 (not_le.mp h1219).le h1216 hz
          · -- right
            by_cases h1220 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1221 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2733_pos (not_le.mp h1208).le h1159 (not_le.mp h1216).le h1221 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2735_pos (not_le.mp h1208).le h1159 (not_le.mp h1221).le h1220 hz
            · -- right
              by_cases h1222 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2741_pos (not_le.mp h1208).le h1159 (not_le.mp h1220).le h1222 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2743_pos (not_le.mp h1208).le h1159 (not_le.mp h1222).le hz2 hz
  · -- right
    by_cases h1223 : a ≤ ((340311/2048000 : ℚ) : ℝ)
    · -- left
      by_cases h1224 : a ≤ ((679773/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h1225 : a ≤ ((1358697/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h1226 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1227 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1228 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2744_pos (not_le.mp h1159).le h1225 hz1 h1228 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2746_pos (not_le.mp h1159).le h1225 (not_le.mp h1228).le h1227 hz
            · -- right
              by_cases h1229 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2752_pos (not_le.mp h1159).le h1225 (not_le.mp h1227).le h1229 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2754_pos (not_le.mp h1159).le h1225 (not_le.mp h1229).le h1226 hz
          · -- right
            by_cases h1230 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1231 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2776_pos (not_le.mp h1159).le h1225 (not_le.mp h1226).le h1231 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2778_pos (not_le.mp h1159).le h1225 (not_le.mp h1231).le h1230 hz
            · -- right
              by_cases h1232 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2784_pos (not_le.mp h1159).le h1225 (not_le.mp h1230).le h1232 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2786_pos (not_le.mp h1159).le h1225 (not_le.mp h1232).le hz2 hz
        · -- right
          by_cases h1233 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1234 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1235 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2745_pos (not_le.mp h1225).le h1224 hz1 h1235 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2747_pos (not_le.mp h1225).le h1224 (not_le.mp h1235).le h1234 hz
            · -- right
              by_cases h1236 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2753_pos (not_le.mp h1225).le h1224 (not_le.mp h1234).le h1236 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2755_pos (not_le.mp h1225).le h1224 (not_le.mp h1236).le h1233 hz
          · -- right
            by_cases h1237 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1238 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2777_pos (not_le.mp h1225).le h1224 (not_le.mp h1233).le h1238 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2779_pos (not_le.mp h1225).le h1224 (not_le.mp h1238).le h1237 hz
            · -- right
              by_cases h1239 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2785_pos (not_le.mp h1225).le h1224 (not_le.mp h1237).le h1239 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2787_pos (not_le.mp h1225).le h1224 (not_le.mp h1239).le hz2 hz
      · -- right
        by_cases h1240 : a ≤ ((272079/1638400 : ℚ) : ℝ)
        · -- left
          by_cases h1241 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1242 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1243 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2748_pos (not_le.mp h1224).le h1240 hz1 h1243 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2750_pos (not_le.mp h1224).le h1240 (not_le.mp h1243).le h1242 hz
            · -- right
              by_cases h1244 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2756_pos (not_le.mp h1224).le h1240 (not_le.mp h1242).le h1244 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2758_pos (not_le.mp h1224).le h1240 (not_le.mp h1244).le h1241 hz
          · -- right
            by_cases h1245 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1246 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2780_pos (not_le.mp h1224).le h1240 (not_le.mp h1241).le h1246 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2782_pos (not_le.mp h1224).le h1240 (not_le.mp h1246).le h1245 hz
            · -- right
              by_cases h1247 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2788_pos (not_le.mp h1224).le h1240 (not_le.mp h1245).le h1247 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2790_pos (not_le.mp h1224).le h1240 (not_le.mp h1247).le hz2 hz
        · -- right
          by_cases h1248 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1249 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1250 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2749_pos (not_le.mp h1240).le h1223 hz1 h1250 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2751_pos (not_le.mp h1240).le h1223 (not_le.mp h1250).le h1249 hz
            · -- right
              by_cases h1251 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B045.e2757_pos (not_le.mp h1240).le h1223 (not_le.mp h1249).le h1251 hz
              · -- right
                exact CKLaneC2R.EpCells.B045.e2759_pos (not_le.mp h1240).le h1223 (not_le.mp h1251).le h1248 hz
          · -- right
            by_cases h1252 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1253 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2781_pos (not_le.mp h1240).le h1223 (not_le.mp h1248).le h1253 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2783_pos (not_le.mp h1240).le h1223 (not_le.mp h1253).le h1252 hz
            · -- right
              by_cases h1254 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2789_pos (not_le.mp h1240).le h1223 (not_le.mp h1252).le h1254 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2791_pos (not_le.mp h1240).le h1223 (not_le.mp h1254).le hz2 hz
    · -- right
      by_cases h1255 : a ≤ ((681471/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h1256 : a ≤ ((1362093/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h1257 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1258 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1259 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2760_pos (not_le.mp h1223).le h1256 hz1 h1259 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2762_pos (not_le.mp h1223).le h1256 (not_le.mp h1259).le h1258 hz
            · -- right
              by_cases h1260 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2768_pos (not_le.mp h1223).le h1256 (not_le.mp h1258).le h1260 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2770_pos (not_le.mp h1223).le h1256 (not_le.mp h1260).le h1257 hz
          · -- right
            by_cases h1261 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1262 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2792_pos (not_le.mp h1223).le h1256 (not_le.mp h1257).le h1262 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2794_pos (not_le.mp h1223).le h1256 (not_le.mp h1262).le h1261 hz
            · -- right
              by_cases h1263 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2800_pos (not_le.mp h1223).le h1256 (not_le.mp h1261).le h1263 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2802_pos (not_le.mp h1223).le h1256 (not_le.mp h1263).le hz2 hz
        · -- right
          by_cases h1264 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1265 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1266 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2761_pos (not_le.mp h1256).le h1255 hz1 h1266 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2763_pos (not_le.mp h1256).le h1255 (not_le.mp h1266).le h1265 hz
            · -- right
              by_cases h1267 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2769_pos (not_le.mp h1256).le h1255 (not_le.mp h1265).le h1267 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2771_pos (not_le.mp h1256).le h1255 (not_le.mp h1267).le h1264 hz
          · -- right
            by_cases h1268 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1269 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2793_pos (not_le.mp h1256).le h1255 (not_le.mp h1264).le h1269 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2795_pos (not_le.mp h1256).le h1255 (not_le.mp h1269).le h1268 hz
            · -- right
              by_cases h1270 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2801_pos (not_le.mp h1256).le h1255 (not_le.mp h1268).le h1270 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2803_pos (not_le.mp h1256).le h1255 (not_le.mp h1270).le hz2 hz
      · -- right
        by_cases h1271 : a ≤ ((1363791/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h1272 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1273 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1274 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2764_pos (not_le.mp h1255).le h1271 hz1 h1274 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2766_pos (not_le.mp h1255).le h1271 (not_le.mp h1274).le h1273 hz
            · -- right
              by_cases h1275 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2772_pos (not_le.mp h1255).le h1271 (not_le.mp h1273).le h1275 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2774_pos (not_le.mp h1255).le h1271 (not_le.mp h1275).le h1272 hz
          · -- right
            by_cases h1276 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1277 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2796_pos (not_le.mp h1255).le h1271 (not_le.mp h1272).le h1277 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2798_pos (not_le.mp h1255).le h1271 (not_le.mp h1277).le h1276 hz
            · -- right
              by_cases h1278 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2804_pos (not_le.mp h1255).le h1271 (not_le.mp h1276).le h1278 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2806_pos (not_le.mp h1255).le h1271 (not_le.mp h1278).le hz2 hz
        · -- right
          by_cases h1279 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1280 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1281 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2765_pos (not_le.mp h1271).le h1030 hz1 h1281 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2767_pos (not_le.mp h1271).le h1030 (not_le.mp h1281).le h1280 hz
            · -- right
              by_cases h1282 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2773_pos (not_le.mp h1271).le h1030 (not_le.mp h1280).le h1282 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2775_pos (not_le.mp h1271).le h1030 (not_le.mp h1282).le h1279 hz
          · -- right
            by_cases h1283 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1284 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2797_pos (not_le.mp h1271).le h1030 (not_le.mp h1279).le h1284 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2799_pos (not_le.mp h1271).le h1030 (not_le.mp h1284).le h1283 hz
            · -- right
              by_cases h1285 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B046.e2805_pos (not_le.mp h1271).le h1030 (not_le.mp h1283).le h1285 hz
              · -- right
                exact CKLaneC2R.EpCells.B046.e2807_pos (not_le.mp h1271).le h1030 (not_le.mp h1285).le hz2 hz

end CKLaneC2R.EndpointCover


