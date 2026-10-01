-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b01
-- name    : CK_CKLaneC2R_EndpointCover_b01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:59:49.062267+00:00
-- url     : https://prove2.me/theorems/6032eccd-7570-4979-a675-daac5075e104
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 2 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 2 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 2 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 2 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 2 of 5).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B036
import Definitions.Def_CK_CKLaneC2R_EpCells_B037
import Definitions.Def_CK_CKLaneC2R_EpCells_B038
namespace CKLaneC2R.EndpointCover

theorem cover_sub_005 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : a ≤ ((10449/64000 : ℚ) : ℝ)) (h6 : ¬ (a ≤ ((20049/128000 : ℚ) : ℝ))) (h518 : a ≤ ((40947/256000 : ℚ) : ℝ)) (h519 : ¬ (a ≤ ((16209/102400 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h647 : a ≤ ((162939/1024000 : ℚ) : ℝ)
  · -- left
    by_cases h648 : a ≤ ((325029/2048000 : ℚ) : ℝ)
    · -- left
      by_cases h649 : a ≤ ((649209/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h650 : a ≤ ((1297569/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h651 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h652 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h653 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2168_pos (not_le.mp h519).le h650 hz1 h653 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2170_pos (not_le.mp h519).le h650 (not_le.mp h653).le h652 hz
            · -- right
              by_cases h654 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2176_pos (not_le.mp h519).le h650 (not_le.mp h652).le h654 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2178_pos (not_le.mp h519).le h650 (not_le.mp h654).le h651 hz
          · -- right
            by_cases h655 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h656 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2200_pos (not_le.mp h519).le h650 (not_le.mp h651).le h656 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2202_pos (not_le.mp h519).le h650 (not_le.mp h656).le h655 hz
            · -- right
              by_cases h657 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2208_pos (not_le.mp h519).le h650 (not_le.mp h655).le h657 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2210_pos (not_le.mp h519).le h650 (not_le.mp h657).le hz2 hz
        · -- right
          by_cases h658 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h659 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h660 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2169_pos (not_le.mp h650).le h649 hz1 h660 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2171_pos (not_le.mp h650).le h649 (not_le.mp h660).le h659 hz
            · -- right
              by_cases h661 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2177_pos (not_le.mp h650).le h649 (not_le.mp h659).le h661 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2179_pos (not_le.mp h650).le h649 (not_le.mp h661).le h658 hz
          · -- right
            by_cases h662 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h663 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2201_pos (not_le.mp h650).le h649 (not_le.mp h658).le h663 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2203_pos (not_le.mp h650).le h649 (not_le.mp h663).le h662 hz
            · -- right
              by_cases h664 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2209_pos (not_le.mp h650).le h649 (not_le.mp h662).le h664 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2211_pos (not_le.mp h650).le h649 (not_le.mp h664).le hz2 hz
      · -- right
        by_cases h665 : a ≤ ((1299267/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h666 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h667 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h668 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2172_pos (not_le.mp h649).le h665 hz1 h668 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2174_pos (not_le.mp h649).le h665 (not_le.mp h668).le h667 hz
            · -- right
              by_cases h669 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2180_pos (not_le.mp h649).le h665 (not_le.mp h667).le h669 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2182_pos (not_le.mp h649).le h665 (not_le.mp h669).le h666 hz
          · -- right
            by_cases h670 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h671 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2204_pos (not_le.mp h649).le h665 (not_le.mp h666).le h671 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2206_pos (not_le.mp h649).le h665 (not_le.mp h671).le h670 hz
            · -- right
              by_cases h672 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2212_pos (not_le.mp h649).le h665 (not_le.mp h670).le h672 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2214_pos (not_le.mp h649).le h665 (not_le.mp h672).le hz2 hz
        · -- right
          by_cases h673 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h674 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h675 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2173_pos (not_le.mp h665).le h648 hz1 h675 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2175_pos (not_le.mp h665).le h648 (not_le.mp h675).le h674 hz
            · -- right
              by_cases h676 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2181_pos (not_le.mp h665).le h648 (not_le.mp h674).le h676 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2183_pos (not_le.mp h665).le h648 (not_le.mp h676).le h673 hz
          · -- right
            by_cases h677 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h678 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2205_pos (not_le.mp h665).le h648 (not_le.mp h673).le h678 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2207_pos (not_le.mp h665).le h648 (not_le.mp h678).le h677 hz
            · -- right
              by_cases h679 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2213_pos (not_le.mp h665).le h648 (not_le.mp h677).le h679 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2215_pos (not_le.mp h665).le h648 (not_le.mp h679).le hz2 hz
    · -- right
      by_cases h680 : a ≤ ((650907/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h681 : a ≤ ((260193/1638400 : ℚ) : ℝ)
        · -- left
          by_cases h682 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h683 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h684 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2184_pos (not_le.mp h648).le h681 hz1 h684 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2186_pos (not_le.mp h648).le h681 (not_le.mp h684).le h683 hz
            · -- right
              by_cases h685 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2192_pos (not_le.mp h648).le h681 (not_le.mp h683).le h685 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2194_pos (not_le.mp h648).le h681 (not_le.mp h685).le h682 hz
          · -- right
            by_cases h686 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h687 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2216_pos (not_le.mp h648).le h681 (not_le.mp h682).le h687 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2218_pos (not_le.mp h648).le h681 (not_le.mp h687).le h686 hz
            · -- right
              by_cases h688 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2224_pos (not_le.mp h648).le h681 (not_le.mp h686).le h688 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2226_pos (not_le.mp h648).le h681 (not_le.mp h688).le hz2 hz
        · -- right
          by_cases h689 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h690 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h691 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2185_pos (not_le.mp h681).le h680 hz1 h691 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2187_pos (not_le.mp h681).le h680 (not_le.mp h691).le h690 hz
            · -- right
              by_cases h692 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2193_pos (not_le.mp h681).le h680 (not_le.mp h690).le h692 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2195_pos (not_le.mp h681).le h680 (not_le.mp h692).le h689 hz
          · -- right
            by_cases h693 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h694 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2217_pos (not_le.mp h681).le h680 (not_le.mp h689).le h694 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2219_pos (not_le.mp h681).le h680 (not_le.mp h694).le h693 hz
            · -- right
              by_cases h695 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2225_pos (not_le.mp h681).le h680 (not_le.mp h693).le h695 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2227_pos (not_le.mp h681).le h680 (not_le.mp h695).le hz2 hz
      · -- right
        by_cases h696 : a ≤ ((1302663/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h697 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h698 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h699 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2188_pos (not_le.mp h680).le h696 hz1 h699 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2190_pos (not_le.mp h680).le h696 (not_le.mp h699).le h698 hz
            · -- right
              by_cases h700 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2196_pos (not_le.mp h680).le h696 (not_le.mp h698).le h700 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2198_pos (not_le.mp h680).le h696 (not_le.mp h700).le h697 hz
          · -- right
            by_cases h701 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h702 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2220_pos (not_le.mp h680).le h696 (not_le.mp h697).le h702 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2222_pos (not_le.mp h680).le h696 (not_le.mp h702).le h701 hz
            · -- right
              by_cases h703 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2228_pos (not_le.mp h680).le h696 (not_le.mp h701).le h703 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2230_pos (not_le.mp h680).le h696 (not_le.mp h703).le hz2 hz
        · -- right
          by_cases h704 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h705 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h706 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2189_pos (not_le.mp h696).le h647 hz1 h706 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2191_pos (not_le.mp h696).le h647 (not_le.mp h706).le h705 hz
            · -- right
              by_cases h707 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2197_pos (not_le.mp h696).le h647 (not_le.mp h705).le h707 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2199_pos (not_le.mp h696).le h647 (not_le.mp h707).le h704 hz
          · -- right
            by_cases h708 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h709 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2221_pos (not_le.mp h696).le h647 (not_le.mp h704).le h709 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2223_pos (not_le.mp h696).le h647 (not_le.mp h709).le h708 hz
            · -- right
              by_cases h710 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2229_pos (not_le.mp h696).le h647 (not_le.mp h708).le h710 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2231_pos (not_le.mp h696).le h647 (not_le.mp h710).le hz2 hz
  · -- right
    by_cases h711 : a ≤ ((326727/2048000 : ℚ) : ℝ)
    · -- left
      by_cases h712 : a ≤ ((130521/819200 : ℚ) : ℝ)
      · -- left
        by_cases h713 : a ≤ ((1304361/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h714 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h715 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h716 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2232_pos (not_le.mp h647).le h713 hz1 h716 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2234_pos (not_le.mp h647).le h713 (not_le.mp h716).le h715 hz
            · -- right
              by_cases h717 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2240_pos (not_le.mp h647).le h713 (not_le.mp h715).le h717 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2242_pos (not_le.mp h647).le h713 (not_le.mp h717).le h714 hz
          · -- right
            by_cases h718 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h719 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2264_pos (not_le.mp h647).le h713 (not_le.mp h714).le h719 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2266_pos (not_le.mp h647).le h713 (not_le.mp h719).le h718 hz
            · -- right
              by_cases h720 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2272_pos (not_le.mp h647).le h713 (not_le.mp h718).le h720 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2274_pos (not_le.mp h647).le h713 (not_le.mp h720).le hz2 hz
        · -- right
          by_cases h721 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h722 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h723 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2233_pos (not_le.mp h713).le h712 hz1 h723 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2235_pos (not_le.mp h713).le h712 (not_le.mp h723).le h722 hz
            · -- right
              by_cases h724 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2241_pos (not_le.mp h713).le h712 (not_le.mp h722).le h724 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2243_pos (not_le.mp h713).le h712 (not_le.mp h724).le h721 hz
          · -- right
            by_cases h725 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h726 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2265_pos (not_le.mp h713).le h712 (not_le.mp h721).le h726 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2267_pos (not_le.mp h713).le h712 (not_le.mp h726).le h725 hz
            · -- right
              by_cases h727 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2273_pos (not_le.mp h713).le h712 (not_le.mp h725).le h727 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2275_pos (not_le.mp h713).le h712 (not_le.mp h727).le hz2 hz
      · -- right
        by_cases h728 : a ≤ ((1306059/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h729 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h730 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h731 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2236_pos (not_le.mp h712).le h728 hz1 h731 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2238_pos (not_le.mp h712).le h728 (not_le.mp h731).le h730 hz
            · -- right
              by_cases h732 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2244_pos (not_le.mp h712).le h728 (not_le.mp h730).le h732 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2246_pos (not_le.mp h712).le h728 (not_le.mp h732).le h729 hz
          · -- right
            by_cases h733 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h734 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2268_pos (not_le.mp h712).le h728 (not_le.mp h729).le h734 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2270_pos (not_le.mp h712).le h728 (not_le.mp h734).le h733 hz
            · -- right
              by_cases h735 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2276_pos (not_le.mp h712).le h728 (not_le.mp h733).le h735 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2278_pos (not_le.mp h712).le h728 (not_le.mp h735).le hz2 hz
        · -- right
          by_cases h736 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h737 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h738 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2237_pos (not_le.mp h728).le h711 hz1 h738 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2239_pos (not_le.mp h728).le h711 (not_le.mp h738).le h737 hz
            · -- right
              by_cases h739 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2245_pos (not_le.mp h728).le h711 (not_le.mp h737).le h739 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2247_pos (not_le.mp h728).le h711 (not_le.mp h739).le h736 hz
          · -- right
            by_cases h740 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h741 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2269_pos (not_le.mp h728).le h711 (not_le.mp h736).le h741 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2271_pos (not_le.mp h728).le h711 (not_le.mp h741).le h740 hz
            · -- right
              by_cases h742 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2277_pos (not_le.mp h728).le h711 (not_le.mp h740).le h742 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2279_pos (not_le.mp h728).le h711 (not_le.mp h742).le hz2 hz
    · -- right
      by_cases h743 : a ≤ ((654303/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h744 : a ≤ ((1307757/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h745 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h746 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h747 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2248_pos (not_le.mp h711).le h744 hz1 h747 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2250_pos (not_le.mp h711).le h744 (not_le.mp h747).le h746 hz
            · -- right
              by_cases h748 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2256_pos (not_le.mp h711).le h744 (not_le.mp h746).le h748 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2258_pos (not_le.mp h711).le h744 (not_le.mp h748).le h745 hz
          · -- right
            by_cases h749 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h750 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2280_pos (not_le.mp h711).le h744 (not_le.mp h745).le h750 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2282_pos (not_le.mp h711).le h744 (not_le.mp h750).le h749 hz
            · -- right
              by_cases h751 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2288_pos (not_le.mp h711).le h744 (not_le.mp h749).le h751 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2290_pos (not_le.mp h711).le h744 (not_le.mp h751).le hz2 hz
        · -- right
          by_cases h752 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h753 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h754 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2249_pos (not_le.mp h744).le h743 hz1 h754 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2251_pos (not_le.mp h744).le h743 (not_le.mp h754).le h753 hz
            · -- right
              by_cases h755 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2257_pos (not_le.mp h744).le h743 (not_le.mp h753).le h755 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2259_pos (not_le.mp h744).le h743 (not_le.mp h755).le h752 hz
          · -- right
            by_cases h756 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h757 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2281_pos (not_le.mp h744).le h743 (not_le.mp h752).le h757 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2283_pos (not_le.mp h744).le h743 (not_le.mp h757).le h756 hz
            · -- right
              by_cases h758 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2289_pos (not_le.mp h744).le h743 (not_le.mp h756).le h758 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2291_pos (not_le.mp h744).le h743 (not_le.mp h758).le hz2 hz
      · -- right
        by_cases h759 : a ≤ ((261891/1638400 : ℚ) : ℝ)
        · -- left
          by_cases h760 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h761 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h762 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2252_pos (not_le.mp h743).le h759 hz1 h762 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2254_pos (not_le.mp h743).le h759 (not_le.mp h762).le h761 hz
            · -- right
              by_cases h763 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2260_pos (not_le.mp h743).le h759 (not_le.mp h761).le h763 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2262_pos (not_le.mp h743).le h759 (not_le.mp h763).le h760 hz
          · -- right
            by_cases h764 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h765 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2284_pos (not_le.mp h743).le h759 (not_le.mp h760).le h765 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2286_pos (not_le.mp h743).le h759 (not_le.mp h765).le h764 hz
            · -- right
              by_cases h766 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2292_pos (not_le.mp h743).le h759 (not_le.mp h764).le h766 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2294_pos (not_le.mp h743).le h759 (not_le.mp h766).le hz2 hz
        · -- right
          by_cases h767 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h768 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h769 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2253_pos (not_le.mp h759).le h518 hz1 h769 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2255_pos (not_le.mp h759).le h518 (not_le.mp h769).le h768 hz
            · -- right
              by_cases h770 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B037.e2261_pos (not_le.mp h759).le h518 (not_le.mp h768).le h770 hz
              · -- right
                exact CKLaneC2R.EpCells.B037.e2263_pos (not_le.mp h759).le h518 (not_le.mp h770).le h767 hz
          · -- right
            by_cases h771 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h772 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2285_pos (not_le.mp h759).le h518 (not_le.mp h767).le h772 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2287_pos (not_le.mp h759).le h518 (not_le.mp h772).le h771 hz
            · -- right
              by_cases h773 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2293_pos (not_le.mp h759).le h518 (not_le.mp h771).le h773 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2295_pos (not_le.mp h759).le h518 (not_le.mp h773).le hz2 hz

end CKLaneC2R.EndpointCover


