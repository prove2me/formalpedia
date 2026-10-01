-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b04_t02
-- name    : CK_CKLaneC2R_EndpointCover_b04_t02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T09:14:16.776408+00:00
-- url     : https://prove2.me/theorems/e1981eaa-ed20-4caa-bcf8-1f20c9e7135c
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 3 of 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 3 of 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 3 of 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 3 of 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 3 of 3 of 4).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B000
import Definitions.Def_CK_CKLaneC2R_EpCells_B001
import Definitions.Def_CK_CKLaneC2R_EpCells_B002
import Definitions.Def_CK_CKLaneC2R_EpCells_B003__2
import Definitions.Def_CK_CKLaneC2R_EpCells_B008
import Definitions.Def_CK_CKLaneC2R_EpCells_B009
import Definitions.Def_CK_CKLaneC2R_EpCells_B023
import Definitions.Def_CK_CKLaneC2R_EpCells_B025
import Definitions.Def_CK_CKLaneC2R_EpCells_B048
namespace CKLaneC2R.EndpointCover

theorem cover_sub_022 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : ¬ (a ≤ ((1149/2000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h2805 : a ≤ ((3147/4000 : ℚ) : ℝ)
  · -- left
    by_cases h2806 : a ≤ ((1089/1600 : ℚ) : ℝ)
    · -- left
      by_cases h2807 : a ≤ ((10041/16000 : ℚ) : ℝ)
      · -- left
        by_cases h2808 : a ≤ ((19233/32000 : ℚ) : ℝ)
        · -- left
          by_cases h2809 : a ≤ ((37617/64000 : ℚ) : ℝ)
          · -- left
            by_cases h2810 : a ≤ ((14877/25600 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e2_pos (not_le.mp h0).le h2810 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e3_pos (not_le.mp h2810).le h2809 hz1 hz2 hz
          · -- right
            by_cases h2811 : a ≤ ((76083/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e4_pos (not_le.mp h2809).le h2811 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e5_pos (not_le.mp h2811).le h2808 hz1 hz2 hz
        · -- right
          by_cases h2812 : a ≤ ((7863/12800 : ℚ) : ℝ)
          · -- left
            by_cases h2813 : a ≤ ((77781/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e6_pos (not_le.mp h2808).le h2813 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e7_pos (not_le.mp h2813).le h2812 hz1 hz2 hz
          · -- right
            by_cases h2814 : a ≤ ((79479/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e8_pos (not_le.mp h2812).le h2814 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e9_pos (not_le.mp h2814).le h2807 hz1 hz2 hz
      · -- right
        by_cases h2815 : a ≤ ((20931/32000 : ℚ) : ℝ)
        · -- left
          by_cases h2816 : a ≤ ((41013/64000 : ℚ) : ℝ)
          · -- left
            by_cases h2817 : a ≤ ((81177/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e10_pos (not_le.mp h2807).le h2817 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e11_pos (not_le.mp h2817).le h2816 hz1 hz2 hz
          · -- right
            by_cases h2818 : a ≤ ((663/1024 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e12_pos (not_le.mp h2816).le h2818 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e13_pos (not_le.mp h2818).le h2815 hz1 hz2 hz
        · -- right
          by_cases h2819 : a ≤ ((42711/64000 : ℚ) : ℝ)
          · -- left
            by_cases h2820 : a ≤ ((84573/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e14_pos (not_le.mp h2815).le h2820 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e15_pos (not_le.mp h2820).le h2819 hz1 hz2 hz
          · -- right
            by_cases h2821 : a ≤ ((86271/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e16_pos (not_le.mp h2819).le h2821 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e17_pos (not_le.mp h2821).le h2806 hz1 hz2 hz
    · -- right
      by_cases h2822 : a ≤ ((11739/16000 : ℚ) : ℝ)
      · -- left
        by_cases h2823 : a ≤ ((22629/32000 : ℚ) : ℝ)
        · -- left
          by_cases h2824 : a ≤ ((44409/64000 : ℚ) : ℝ)
          · -- left
            by_cases h2825 : a ≤ ((87969/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e18_pos (not_le.mp h2806).le h2825 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e19_pos (not_le.mp h2825).le h2824 hz1 hz2 hz
          · -- right
            by_cases h2826 : a ≤ ((89667/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e20_pos (not_le.mp h2824).le h2826 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e21_pos (not_le.mp h2826).le h2823 hz1 hz2 hz
        · -- right
          by_cases h2827 : a ≤ ((46107/64000 : ℚ) : ℝ)
          · -- left
            by_cases h2828 : a ≤ ((18273/25600 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e22_pos (not_le.mp h2823).le h2828 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e23_pos (not_le.mp h2828).le h2827 hz1 hz2 hz
          · -- right
            by_cases h2829 : a ≤ ((93063/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e24_pos (not_le.mp h2827).le h2829 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e25_pos (not_le.mp h2829).le h2822 hz1 hz2 hz
      · -- right
        by_cases h2830 : a ≤ ((24327/32000 : ℚ) : ℝ)
        · -- left
          by_cases h2831 : a ≤ ((9561/12800 : ℚ) : ℝ)
          · -- left
            by_cases h2832 : a ≤ ((94761/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e26_pos (not_le.mp h2822).le h2832 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e27_pos (not_le.mp h2832).le h2831 hz1 hz2 hz
          · -- right
            by_cases h2833 : a ≤ ((96459/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e28_pos (not_le.mp h2831).le h2833 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e29_pos (not_le.mp h2833).le h2830 hz1 hz2 hz
        · -- right
          by_cases h2834 : a ≤ ((49503/64000 : ℚ) : ℝ)
          · -- left
            by_cases h2835 : a ≤ ((98157/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e30_pos (not_le.mp h2830).le h2835 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e31_pos (not_le.mp h2835).le h2834 hz1 hz2 hz
          · -- right
            by_cases h2836 : a ≤ ((19971/25600 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e32_pos (not_le.mp h2834).le h2836 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e33_pos (not_le.mp h2836).le h2805 hz1 hz2 hz
  · -- right
    by_cases h2837 : a ≤ ((7143/8000 : ℚ) : ℝ)
    · -- left
      by_cases h2838 : a ≤ ((13437/16000 : ℚ) : ℝ)
      · -- left
        by_cases h2839 : a ≤ ((1041/1280 : ℚ) : ℝ)
        · -- left
          by_cases h2840 : a ≤ ((51201/64000 : ℚ) : ℝ)
          · -- left
            by_cases h2841 : a ≤ ((101553/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e34_pos (not_le.mp h2805).le h2841 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e35_pos (not_le.mp h2841).le h2840 hz1 hz2 hz
          · -- right
            by_cases h2842 : a ≤ ((103251/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e36_pos (not_le.mp h2840).le h2842 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e37_pos (not_le.mp h2842).le h2839 hz1 hz2 hz
        · -- right
          by_cases h2843 : a ≤ ((52899/64000 : ℚ) : ℝ)
          · -- left
            by_cases h2844 : a ≤ ((104949/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e38_pos (not_le.mp h2839).le h2844 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e39_pos (not_le.mp h2844).le h2843 hz1 hz2 hz
          · -- right
            by_cases h2845 : a ≤ ((106647/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e40_pos (not_le.mp h2843).le h2845 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e41_pos (not_le.mp h2845).le h2838 hz1 hz2 hz
      · -- right
        by_cases h2846 : a ≤ ((27723/32000 : ℚ) : ℝ)
        · -- left
          by_cases h2847 : a ≤ ((54597/64000 : ℚ) : ℝ)
          · -- left
            by_cases h2848 : a ≤ ((21669/25600 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e42_pos (not_le.mp h2838).le h2848 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e43_pos (not_le.mp h2848).le h2847 hz1 hz2 hz
          · -- right
            by_cases h2849 : a ≤ ((110043/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e44_pos (not_le.mp h2847).le h2849 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e45_pos (not_le.mp h2849).le h2846 hz1 hz2 hz
        · -- right
          by_cases h2850 : a ≤ ((11259/12800 : ℚ) : ℝ)
          · -- left
            by_cases h2851 : a ≤ ((111741/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e46_pos (not_le.mp h2846).le h2851 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e47_pos (not_le.mp h2851).le h2850 hz1 hz2 hz
          · -- right
            by_cases h2852 : a ≤ ((113439/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e48_pos (not_le.mp h2850).le h2852 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e49_pos (not_le.mp h2852).le h2837 hz1 hz2 hz
    · -- right
      by_cases h2853 : a ≤ ((3027/3200 : ℚ) : ℝ)
      · -- left
        by_cases h2854 : a ≤ ((29421/32000 : ℚ) : ℝ)
        · -- left
          by_cases h2855 : a ≤ ((57993/64000 : ℚ) : ℝ)
          · -- left
            by_cases h2856 : a ≤ ((115137/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e50_pos (not_le.mp h2837).le h2856 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e51_pos (not_le.mp h2856).le h2855 hz1 hz2 hz
          · -- right
            by_cases h2857 : a ≤ ((23367/25600 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e52_pos (not_le.mp h2855).le h2857 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e53_pos (not_le.mp h2857).le h2854 hz1 hz2 hz
        · -- right
          by_cases h2858 : a ≤ ((59691/64000 : ℚ) : ℝ)
          · -- left
            by_cases h2859 : a ≤ ((118533/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e54_pos (not_le.mp h2854).le h2859 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e55_pos (not_le.mp h2859).le h2858 hz1 hz2 hz
          · -- right
            by_cases h2860 : a ≤ ((120231/128000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e56_pos (not_le.mp h2858).le h2860 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e57_pos (not_le.mp h2860).le h2853 hz1 hz2 hz
      · -- right
        by_cases h2861 : a ≤ ((31119/32000 : ℚ) : ℝ)
        · -- left
          by_cases h2862 : a ≤ ((61389/64000 : ℚ) : ℝ)
          · -- left
            by_cases h2863 : a ≤ ((121929/128000 : ℚ) : ℝ)
            · -- left
              by_cases h2864 : a ≤ ((243009/256000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B001.e96_pos (not_le.mp h2853).le h2864 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B001.e97_pos (not_le.mp h2864).le h2863 hz1 hz2 hz
            · -- right
              by_cases h2865 : a ≤ ((244707/256000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B001.e98_pos (not_le.mp h2863).le h2865 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B001.e99_pos (not_le.mp h2865).le h2862 hz1 hz2 hz
          · -- right
            by_cases h2866 : a ≤ ((123627/128000 : ℚ) : ℝ)
            · -- left
              by_cases h2867 : a ≤ ((49281/51200 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B001.e100_pos (not_le.mp h2862).le h2867 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B001.e101_pos (not_le.mp h2867).le h2866 hz1 hz2 hz
            · -- right
              by_cases h2868 : a ≤ ((248103/256000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B001.e102_pos (not_le.mp h2866).le h2868 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B001.e103_pos (not_le.mp h2868).le h2861 hz1 hz2 hz
        · -- right
          by_cases h2869 : a ≤ ((63087/64000 : ℚ) : ℝ)
          · -- left
            by_cases h2870 : a ≤ ((5013/5120 : ℚ) : ℝ)
            · -- left
              by_cases h2871 : a ≤ ((249801/256000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B001.e104_pos (not_le.mp h2861).le h2871 hz1 hz2 hz
              · -- right
                by_cases h2872 : a ≤ ((500451/512000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B002.e159_pos (not_le.mp h2871).le h2872 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B002.e160_pos (not_le.mp h2872).le h2870 hz1 hz2 hz
            · -- right
              by_cases h2873 : a ≤ ((251499/256000 : ℚ) : ℝ)
              · -- left
                by_cases h2874 : a ≤ ((502149/512000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B002.e161_pos (not_le.mp h2870).le h2874 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B002.e162_pos (not_le.mp h2874).le h2873 hz1 hz2 hz
              · -- right
                by_cases h2875 : a ≤ ((503847/512000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B002.e163_pos (not_le.mp h2873).le h2875 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B002.e164_pos (not_le.mp h2875).le h2869 hz1 hz2 hz
          · -- right
            by_cases h2876 : a ≤ ((127023/128000 : ℚ) : ℝ)
            · -- left
              by_cases h2877 : a ≤ ((253197/256000 : ℚ) : ℝ)
              · -- left
                by_cases h2878 : a ≤ ((101109/102400 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B002.e165_pos (not_le.mp h2869).le h2878 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B002.e166_pos (not_le.mp h2878).le h2877 hz1 hz2 hz
              · -- right
                by_cases h2879 : a ≤ ((507243/512000 : ℚ) : ℝ)
                · -- left
                  by_cases h2880 : a ≤ ((1013637/1024000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B004.e249_pos (not_le.mp h2877).le h2880 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B004.e250_pos (not_le.mp h2880).le h2879 hz1 hz2 hz
                · -- right
                  by_cases h2881 : a ≤ ((203067/204800 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B004.e251_pos (not_le.mp h2879).le h2881 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B004.e252_pos (not_le.mp h2881).le h2876 hz1 hz2 hz
            · -- right
              by_cases h2882 : a ≤ ((50979/51200 : ℚ) : ℝ)
              · -- left
                by_cases h2883 : a ≤ ((508941/512000 : ℚ) : ℝ)
                · -- left
                  by_cases h2884 : a ≤ ((1017033/1024000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B004.e253_pos (not_le.mp h2876).le h2884 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B004.e254_pos (not_le.mp h2884).le h2883 hz1 hz2 hz
                · -- right
                  by_cases h2885 : a ≤ ((1018731/1024000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2886 : z ≤ ((1999/2000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B004.e272_pos (not_le.mp h2883).le h2885 hz1 h2886 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B004.e273_pos (not_le.mp h2883).le h2885 (not_le.mp h2886).le hz2 hz
                  · -- right
                    by_cases h2887 : z ≤ ((1999/2000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B004.e274_pos (not_le.mp h2885).le h2882 hz1 h2887 hz
                    · -- right
                      by_cases h2888 : a ≤ ((2038311/2048000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.EpCells.B008.e532_pos (not_le.mp h2885).le h2888 (not_le.mp h2887).le hz2 hz
                      · -- right
                        exact CKLaneC2R.EpCells.B008.e533_pos (not_le.mp h2888).le h2882 (not_le.mp h2887).le hz2 hz
              · -- right
                by_cases h2889 : a ≤ ((510639/512000 : ℚ) : ℝ)
                · -- left
                  by_cases h2890 : a ≤ ((1020429/1024000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2891 : a ≤ ((2040009/2048000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2892 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.EpCells.B008.e534_pos (not_le.mp h2882).le h2891 hz1 h2892 hz
                      · -- right
                        exact CKLaneC2R.EpCells.B008.e536_pos (not_le.mp h2882).le h2891 (not_le.mp h2892).le hz2 hz
                    · -- right
                      by_cases h2893 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.EpCells.B008.e535_pos (not_le.mp h2891).le h2890 hz1 h2893 hz
                      · -- right
                        exact CKLaneC2R.EpCells.B008.e537_pos (not_le.mp h2891).le h2890 (not_le.mp h2893).le hz2 hz
                  · -- right
                    by_cases h2894 : a ≤ ((2041707/2048000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2895 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.EpCells.B008.e538_pos (not_le.mp h2890).le h2894 hz1 h2895 hz
                      · -- right
                        exact CKLaneC2R.EpCells.B009.e540_pos (not_le.mp h2890).le h2894 (not_le.mp h2895).le hz2 hz
                    · -- right
                      by_cases h2896 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.EpCells.B008.e539_pos (not_le.mp h2894).le h2889 hz1 h2896 hz
                      · -- right
                        exact CKLaneC2R.EpCells.B009.e541_pos (not_le.mp h2894).le h2889 (not_le.mp h2896).le hz2 hz
                · -- right
                  by_cases h2897 : a ≤ ((1022127/1024000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2898 : a ≤ ((408681/409600 : ℚ) : ℝ)
                    · -- left
                      by_cases h2899 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.EpCells.B009.e542_pos (not_le.mp h2889).le h2898 hz1 h2899 hz
                      · -- right
                        by_cases h2900 : z ≤ ((3999/4000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B009.e586_pos (not_le.mp h2889).le h2898 (not_le.mp h2899).le h2900 hz
                        · -- right
                          by_cases h2901 : a ≤ ((4085961/4096000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B023.e1405_pos (not_le.mp h2889).le h2901 (not_le.mp h2900).le hz2 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B023.e1406_pos (not_le.mp h2901).le h2898 (not_le.mp h2900).le hz2 hz
                    · -- right
                      by_cases h2902 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.EpCells.B009.e543_pos (not_le.mp h2898).le h2897 hz1 h2902 hz
                      · -- right
                        by_cases h2903 : a ≤ ((4087659/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2904 : z ≤ ((3999/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B023.e1407_pos (not_le.mp h2898).le h2903 (not_le.mp h2902).le h2904 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B023.e1409_pos (not_le.mp h2898).le h2903 (not_le.mp h2904).le hz2 hz
                        · -- right
                          by_cases h2905 : z ≤ ((3999/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B023.e1408_pos (not_le.mp h2903).le h2897 (not_le.mp h2902).le h2905 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B023.e1410_pos (not_le.mp h2903).le h2897 (not_le.mp h2905).le hz2 hz
                  · -- right
                    by_cases h2906 : a ≤ ((2045103/2048000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2907 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2908 : z ≤ ((3997/4000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B009.e587_pos (not_le.mp h2897).le h2906 hz1 h2908 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B009.e588_pos (not_le.mp h2897).le h2906 (not_le.mp h2908).le h2907 hz
                      · -- right
                        by_cases h2909 : a ≤ ((4089357/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2910 : z ≤ ((3999/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B023.e1413_pos (not_le.mp h2897).le h2909 (not_le.mp h2907).le h2910 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B023.e1415_pos (not_le.mp h2897).le h2909 (not_le.mp h2910).le hz2 hz
                        · -- right
                          by_cases h2911 : z ≤ ((3999/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B023.e1414_pos (not_le.mp h2909).le h2906 (not_le.mp h2907).le h2911 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B023.e1416_pos (not_le.mp h2909).le h2906 (not_le.mp h2911).le hz2 hz
                    · -- right
                      by_cases h2912 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2913 : z ≤ ((3997/4000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B009.e589_pos (not_le.mp h2906).le ha2 hz1 h2913 hz
                        · -- right
                          by_cases h2914 : a ≤ ((818211/819200 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B023.e1411_pos (not_le.mp h2906).le h2914 (not_le.mp h2913).le h2912 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B023.e1412_pos (not_le.mp h2914).le ha2 (not_le.mp h2913).le h2912 hz
                      · -- right
                        by_cases h2915 : a ≤ ((818211/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h2916 : z ≤ ((3999/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B023.e1417_pos (not_le.mp h2906).le h2915 (not_le.mp h2912).le h2916 hz
                          · -- right
                            by_cases h2917 : z ≤ ((7999/8000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B025.e1525_pos (not_le.mp h2906).le h2915 (not_le.mp h2916).le h2917 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B025.e1526_pos (not_le.mp h2906).le h2915 (not_le.mp h2917).le hz2 hz
                        · -- right
                          by_cases h2918 : z ≤ ((3999/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B023.e1418_pos (not_le.mp h2915).le ha2 (not_le.mp h2912).le h2918 hz
                          · -- right
                            by_cases h2919 : z ≤ ((7999/8000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B025.e1527_pos (not_le.mp h2915).le ha2 (not_le.mp h2918).le h2919 hz
                            · -- right
                              by_cases h2920 : a ≤ ((8182959/8192000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B048.e2920_pos (not_le.mp h2915).le h2920 (not_le.mp h2919).le hz2 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B048.e2921_pos (not_le.mp h2920).le ha2 (not_le.mp h2919).le hz2 hz

end CKLaneC2R.EndpointCover


