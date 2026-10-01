-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b04_t01
-- name    : CK_CKLaneC2R_EndpointCover_b04_t01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T09:09:38.806158+00:00
-- url     : https://prove2.me/theorems/990ce47e-d2bb-4568-a2ed-19abc0f1853e
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 2 of 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 2 of 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 2 of 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 2 of 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 2 of 3 of 4).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B000
import Definitions.Def_CK_CKLaneC2R_EpCells_B001
import Definitions.Def_CK_CKLaneC2R_EpCells_B002
namespace CKLaneC2R.EndpointCover

theorem cover_sub_021 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((1449/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h2722 : a ≤ ((3747/8000 : ℚ) : ℝ)
  · -- left
    by_cases h2723 : a ≤ ((1329/3200 : ℚ) : ℝ)
    · -- left
      by_cases h2724 : a ≤ ((12441/32000 : ℚ) : ℝ)
      · -- left
        by_cases h2725 : a ≤ ((24033/64000 : ℚ) : ℝ)
        · -- left
          by_cases h2726 : a ≤ ((47217/128000 : ℚ) : ℝ)
          · -- left
            by_cases h2727 : a ≤ ((18717/51200 : ℚ) : ℝ)
            · -- left
              by_cases h2728 : a ≤ ((186321/512000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B001.e115_pos (not_le.mp h1).le h2728 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B001.e116_pos (not_le.mp h2728).le h2727 hz1 hz2 hz
            · -- right
              by_cases h2729 : a ≤ ((188019/512000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B001.e117_pos (not_le.mp h2727).le h2729 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B001.e118_pos (not_le.mp h2729).le h2726 hz1 hz2 hz
          · -- right
            by_cases h2730 : a ≤ ((95283/256000 : ℚ) : ℝ)
            · -- left
              by_cases h2731 : a ≤ ((189717/512000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B001.e119_pos (not_le.mp h2726).le h2731 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e120_pos (not_le.mp h2731).le h2730 hz1 hz2 hz
            · -- right
              by_cases h2732 : a ≤ ((38283/102400 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e121_pos (not_le.mp h2730).le h2732 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e122_pos (not_le.mp h2732).le h2725 hz1 hz2 hz
        · -- right
          by_cases h2733 : a ≤ ((9783/25600 : ℚ) : ℝ)
          · -- left
            by_cases h2734 : a ≤ ((96981/256000 : ℚ) : ℝ)
            · -- left
              by_cases h2735 : a ≤ ((193113/512000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e123_pos (not_le.mp h2725).le h2735 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e124_pos (not_le.mp h2735).le h2734 hz1 hz2 hz
            · -- right
              by_cases h2736 : a ≤ ((194811/512000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e125_pos (not_le.mp h2734).le h2736 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e126_pos (not_le.mp h2736).le h2733 hz1 hz2 hz
          · -- right
            by_cases h2737 : a ≤ ((98679/256000 : ℚ) : ℝ)
            · -- left
              by_cases h2738 : a ≤ ((196509/512000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e127_pos (not_le.mp h2733).le h2738 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e128_pos (not_le.mp h2738).le h2737 hz1 hz2 hz
            · -- right
              by_cases h2739 : a ≤ ((198207/512000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e129_pos (not_le.mp h2737).le h2739 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e130_pos (not_le.mp h2739).le h2724 hz1 hz2 hz
      · -- right
        by_cases h2740 : a ≤ ((25731/64000 : ℚ) : ℝ)
        · -- left
          by_cases h2741 : a ≤ ((50613/128000 : ℚ) : ℝ)
          · -- left
            by_cases h2742 : a ≤ ((100377/256000 : ℚ) : ℝ)
            · -- left
              by_cases h2743 : a ≤ ((39981/102400 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e131_pos (not_le.mp h2724).le h2743 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e132_pos (not_le.mp h2743).le h2742 hz1 hz2 hz
            · -- right
              by_cases h2744 : a ≤ ((201603/512000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e133_pos (not_le.mp h2742).le h2744 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e134_pos (not_le.mp h2744).le h2741 hz1 hz2 hz
          · -- right
            by_cases h2745 : a ≤ ((4083/10240 : ℚ) : ℝ)
            · -- left
              by_cases h2746 : a ≤ ((203301/512000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e135_pos (not_le.mp h2741).le h2746 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e136_pos (not_le.mp h2746).le h2745 hz1 hz2 hz
            · -- right
              by_cases h2747 : a ≤ ((204999/512000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e137_pos (not_le.mp h2745).le h2747 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e138_pos (not_le.mp h2747).le h2740 hz1 hz2 hz
        · -- right
          by_cases h2748 : a ≤ ((52311/128000 : ℚ) : ℝ)
          · -- left
            by_cases h2749 : a ≤ ((103773/256000 : ℚ) : ℝ)
            · -- left
              by_cases h2750 : a ≤ ((206697/512000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e139_pos (not_le.mp h2740).le h2750 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e140_pos (not_le.mp h2750).le h2749 hz1 hz2 hz
            · -- right
              by_cases h2751 : a ≤ ((41679/102400 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e141_pos (not_le.mp h2749).le h2751 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e142_pos (not_le.mp h2751).le h2748 hz1 hz2 hz
          · -- right
            by_cases h2752 : a ≤ ((105471/256000 : ℚ) : ℝ)
            · -- left
              by_cases h2753 : a ≤ ((210093/512000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e143_pos (not_le.mp h2748).le h2753 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e144_pos (not_le.mp h2753).le h2752 hz1 hz2 hz
            · -- right
              by_cases h2754 : a ≤ ((211791/512000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e145_pos (not_le.mp h2752).le h2754 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e146_pos (not_le.mp h2754).le h2723 hz1 hz2 hz
    · -- right
      by_cases h2755 : a ≤ ((14139/32000 : ℚ) : ℝ)
      · -- left
        by_cases h2756 : a ≤ ((27429/64000 : ℚ) : ℝ)
        · -- left
          by_cases h2757 : a ≤ ((54009/128000 : ℚ) : ℝ)
          · -- left
            by_cases h2758 : a ≤ ((107169/256000 : ℚ) : ℝ)
            · -- left
              by_cases h2759 : a ≤ ((213489/512000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e147_pos (not_le.mp h2723).le h2759 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e148_pos (not_le.mp h2759).le h2758 hz1 hz2 hz
            · -- right
              by_cases h2760 : a ≤ ((215187/512000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e149_pos (not_le.mp h2758).le h2760 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e150_pos (not_le.mp h2760).le h2757 hz1 hz2 hz
          · -- right
            by_cases h2761 : a ≤ ((108867/256000 : ℚ) : ℝ)
            · -- left
              by_cases h2762 : a ≤ ((43377/102400 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e151_pos (not_le.mp h2757).le h2762 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e152_pos (not_le.mp h2762).le h2761 hz1 hz2 hz
            · -- right
              by_cases h2763 : a ≤ ((218583/512000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e153_pos (not_le.mp h2761).le h2763 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e154_pos (not_le.mp h2763).le h2756 hz1 hz2 hz
        · -- right
          by_cases h2764 : a ≤ ((55707/128000 : ℚ) : ℝ)
          · -- left
            by_cases h2765 : a ≤ ((22113/51200 : ℚ) : ℝ)
            · -- left
              by_cases h2766 : a ≤ ((220281/512000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e155_pos (not_le.mp h2756).le h2766 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e156_pos (not_le.mp h2766).le h2765 hz1 hz2 hz
            · -- right
              by_cases h2767 : a ≤ ((221979/512000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B002.e157_pos (not_le.mp h2765).le h2767 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B002.e158_pos (not_le.mp h2767).le h2764 hz1 hz2 hz
          · -- right
            by_cases h2768 : a ≤ ((112263/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B000.e58_pos (not_le.mp h2764).le h2768 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B000.e59_pos (not_le.mp h2768).le h2755 hz1 hz2 hz
      · -- right
        by_cases h2769 : a ≤ ((29127/64000 : ℚ) : ℝ)
        · -- left
          by_cases h2770 : a ≤ ((11481/25600 : ℚ) : ℝ)
          · -- left
            by_cases h2771 : a ≤ ((113961/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e60_pos (not_le.mp h2755).le h2771 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e61_pos (not_le.mp h2771).le h2770 hz1 hz2 hz
          · -- right
            by_cases h2772 : a ≤ ((115659/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e62_pos (not_le.mp h2770).le h2772 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e63_pos (not_le.mp h2772).le h2769 hz1 hz2 hz
        · -- right
          by_cases h2773 : a ≤ ((59103/128000 : ℚ) : ℝ)
          · -- left
            by_cases h2774 : a ≤ ((117357/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e64_pos (not_le.mp h2769).le h2774 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e65_pos (not_le.mp h2774).le h2773 hz1 hz2 hz
          · -- right
            by_cases h2775 : a ≤ ((23811/51200 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e66_pos (not_le.mp h2773).le h2775 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e67_pos (not_le.mp h2775).le h2722 hz1 hz2 hz
  · -- right
    by_cases h2776 : a ≤ ((8343/16000 : ℚ) : ℝ)
    · -- left
      by_cases h2777 : a ≤ ((15837/32000 : ℚ) : ℝ)
      · -- left
        by_cases h2778 : a ≤ ((1233/2560 : ℚ) : ℝ)
        · -- left
          by_cases h2779 : a ≤ ((60801/128000 : ℚ) : ℝ)
          · -- left
            by_cases h2780 : a ≤ ((120753/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e68_pos (not_le.mp h2722).le h2780 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e69_pos (not_le.mp h2780).le h2779 hz1 hz2 hz
          · -- right
            by_cases h2781 : a ≤ ((122451/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e70_pos (not_le.mp h2779).le h2781 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e71_pos (not_le.mp h2781).le h2778 hz1 hz2 hz
        · -- right
          by_cases h2782 : a ≤ ((62499/128000 : ℚ) : ℝ)
          · -- left
            by_cases h2783 : a ≤ ((124149/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e72_pos (not_le.mp h2778).le h2783 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e73_pos (not_le.mp h2783).le h2782 hz1 hz2 hz
          · -- right
            by_cases h2784 : a ≤ ((125847/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e74_pos (not_le.mp h2782).le h2784 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e75_pos (not_le.mp h2784).le h2777 hz1 hz2 hz
      · -- right
        by_cases h2785 : a ≤ ((32523/64000 : ℚ) : ℝ)
        · -- left
          by_cases h2786 : a ≤ ((64197/128000 : ℚ) : ℝ)
          · -- left
            by_cases h2787 : a ≤ ((25509/51200 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e76_pos (not_le.mp h2777).le h2787 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e77_pos (not_le.mp h2787).le h2786 hz1 hz2 hz
          · -- right
            by_cases h2788 : a ≤ ((129243/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e78_pos (not_le.mp h2786).le h2788 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e79_pos (not_le.mp h2788).le h2785 hz1 hz2 hz
        · -- right
          by_cases h2789 : a ≤ ((13179/25600 : ℚ) : ℝ)
          · -- left
            by_cases h2790 : a ≤ ((130941/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e80_pos (not_le.mp h2785).le h2790 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e81_pos (not_le.mp h2790).le h2789 hz1 hz2 hz
          · -- right
            by_cases h2791 : a ≤ ((132639/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e82_pos (not_le.mp h2789).le h2791 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e83_pos (not_le.mp h2791).le h2776 hz1 hz2 hz
    · -- right
      by_cases h2792 : a ≤ ((3507/6400 : ℚ) : ℝ)
      · -- left
        by_cases h2793 : a ≤ ((34221/64000 : ℚ) : ℝ)
        · -- left
          by_cases h2794 : a ≤ ((67593/128000 : ℚ) : ℝ)
          · -- left
            by_cases h2795 : a ≤ ((134337/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e84_pos (not_le.mp h2776).le h2795 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e85_pos (not_le.mp h2795).le h2794 hz1 hz2 hz
          · -- right
            by_cases h2796 : a ≤ ((27207/51200 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e86_pos (not_le.mp h2794).le h2796 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e87_pos (not_le.mp h2796).le h2793 hz1 hz2 hz
        · -- right
          by_cases h2797 : a ≤ ((69291/128000 : ℚ) : ℝ)
          · -- left
            by_cases h2798 : a ≤ ((137733/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e88_pos (not_le.mp h2793).le h2798 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e89_pos (not_le.mp h2798).le h2797 hz1 hz2 hz
          · -- right
            by_cases h2799 : a ≤ ((139431/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e90_pos (not_le.mp h2797).le h2799 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e91_pos (not_le.mp h2799).le h2792 hz1 hz2 hz
      · -- right
        by_cases h2800 : a ≤ ((35919/64000 : ℚ) : ℝ)
        · -- left
          by_cases h2801 : a ≤ ((70989/128000 : ℚ) : ℝ)
          · -- left
            by_cases h2802 : a ≤ ((141129/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e92_pos (not_le.mp h2792).le h2802 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e93_pos (not_le.mp h2802).le h2801 hz1 hz2 hz
          · -- right
            by_cases h2803 : a ≤ ((142827/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.EpCells.B001.e94_pos (not_le.mp h2801).le h2803 hz1 hz2 hz
            · -- right
              exact CKLaneC2R.EpCells.B001.e95_pos (not_le.mp h2803).le h2800 hz1 hz2 hz
        · -- right
          by_cases h2804 : a ≤ ((72687/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.EpCells.B000.e0_pos (not_le.mp h2800).le h2804 hz1 hz2 hz
          · -- right
            exact CKLaneC2R.EpCells.B000.e1_pos (not_le.mp h2804).le h0 hz1 hz2 hz

end CKLaneC2R.EndpointCover


