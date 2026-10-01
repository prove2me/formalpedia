-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b01_t01
-- name    : CK_CKLaneC2R_EndpointCover_b01_t01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:52:34.38136+00:00
-- url     : https://prove2.me/theorems/25619628-2421-4502-a510-c79a52ff769f
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 2 of 5 of 1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 2 of 5 of 1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 2 of 5 of 1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 2 of 5 of 1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 2 of 5 of 1).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B038
import Definitions.Def_CK_CKLaneC2R_EpCells_B039
import Definitions.Def_CK_CKLaneC2R_EpCells_B040
namespace CKLaneC2R.EndpointCover

theorem cover_sub_006 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : a ≤ ((10449/64000 : ℚ) : ℝ)) (h6 : ¬ (a ≤ ((20049/128000 : ℚ) : ℝ))) (h518 : ¬ (a ≤ ((40947/256000 : ℚ) : ℝ))) (h774 : a ≤ ((82743/512000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h775 : a ≤ ((164637/1024000 : ℚ) : ℝ)
  · -- left
    by_cases h776 : a ≤ ((13137/81920 : ℚ) : ℝ)
    · -- left
      by_cases h777 : a ≤ ((656001/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h778 : a ≤ ((1311153/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h779 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h780 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h781 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2296_pos (not_le.mp h518).le h778 hz1 h781 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2298_pos (not_le.mp h518).le h778 (not_le.mp h781).le h780 hz
            · -- right
              by_cases h782 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2304_pos (not_le.mp h518).le h778 (not_le.mp h780).le h782 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2306_pos (not_le.mp h518).le h778 (not_le.mp h782).le h779 hz
          · -- right
            by_cases h783 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h784 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2328_pos (not_le.mp h518).le h778 (not_le.mp h779).le h784 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2330_pos (not_le.mp h518).le h778 (not_le.mp h784).le h783 hz
            · -- right
              by_cases h785 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2336_pos (not_le.mp h518).le h778 (not_le.mp h783).le h785 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2338_pos (not_le.mp h518).le h778 (not_le.mp h785).le hz2 hz
        · -- right
          by_cases h786 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h787 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h788 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2297_pos (not_le.mp h778).le h777 hz1 h788 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2299_pos (not_le.mp h778).le h777 (not_le.mp h788).le h787 hz
            · -- right
              by_cases h789 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2305_pos (not_le.mp h778).le h777 (not_le.mp h787).le h789 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2307_pos (not_le.mp h778).le h777 (not_le.mp h789).le h786 hz
          · -- right
            by_cases h790 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h791 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2329_pos (not_le.mp h778).le h777 (not_le.mp h786).le h791 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2331_pos (not_le.mp h778).le h777 (not_le.mp h791).le h790 hz
            · -- right
              by_cases h792 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2337_pos (not_le.mp h778).le h777 (not_le.mp h790).le h792 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2339_pos (not_le.mp h778).le h777 (not_le.mp h792).le hz2 hz
      · -- right
        by_cases h793 : a ≤ ((1312851/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h794 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h795 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h796 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2300_pos (not_le.mp h777).le h793 hz1 h796 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2302_pos (not_le.mp h777).le h793 (not_le.mp h796).le h795 hz
            · -- right
              by_cases h797 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2308_pos (not_le.mp h777).le h793 (not_le.mp h795).le h797 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2310_pos (not_le.mp h777).le h793 (not_le.mp h797).le h794 hz
          · -- right
            by_cases h798 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h799 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2332_pos (not_le.mp h777).le h793 (not_le.mp h794).le h799 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2334_pos (not_le.mp h777).le h793 (not_le.mp h799).le h798 hz
            · -- right
              by_cases h800 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2340_pos (not_le.mp h777).le h793 (not_le.mp h798).le h800 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2342_pos (not_le.mp h777).le h793 (not_le.mp h800).le hz2 hz
        · -- right
          by_cases h801 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h802 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h803 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2301_pos (not_le.mp h793).le h776 hz1 h803 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2303_pos (not_le.mp h793).le h776 (not_le.mp h803).le h802 hz
            · -- right
              by_cases h804 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2309_pos (not_le.mp h793).le h776 (not_le.mp h802).le h804 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2311_pos (not_le.mp h793).le h776 (not_le.mp h804).le h801 hz
          · -- right
            by_cases h805 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h806 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2333_pos (not_le.mp h793).le h776 (not_le.mp h801).le h806 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2335_pos (not_le.mp h793).le h776 (not_le.mp h806).le h805 hz
            · -- right
              by_cases h807 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2341_pos (not_le.mp h793).le h776 (not_le.mp h805).le h807 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2343_pos (not_le.mp h793).le h776 (not_le.mp h807).le hz2 hz
    · -- right
      by_cases h808 : a ≤ ((657699/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h809 : a ≤ ((1314549/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h810 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h811 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h812 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2312_pos (not_le.mp h776).le h809 hz1 h812 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2314_pos (not_le.mp h776).le h809 (not_le.mp h812).le h811 hz
            · -- right
              by_cases h813 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2320_pos (not_le.mp h776).le h809 (not_le.mp h811).le h813 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2322_pos (not_le.mp h776).le h809 (not_le.mp h813).le h810 hz
          · -- right
            by_cases h814 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h815 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2344_pos (not_le.mp h776).le h809 (not_le.mp h810).le h815 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2346_pos (not_le.mp h776).le h809 (not_le.mp h815).le h814 hz
            · -- right
              by_cases h816 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2352_pos (not_le.mp h776).le h809 (not_le.mp h814).le h816 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2354_pos (not_le.mp h776).le h809 (not_le.mp h816).le hz2 hz
        · -- right
          by_cases h817 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h818 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h819 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2313_pos (not_le.mp h809).le h808 hz1 h819 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2315_pos (not_le.mp h809).le h808 (not_le.mp h819).le h818 hz
            · -- right
              by_cases h820 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2321_pos (not_le.mp h809).le h808 (not_le.mp h818).le h820 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2323_pos (not_le.mp h809).le h808 (not_le.mp h820).le h817 hz
          · -- right
            by_cases h821 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h822 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2345_pos (not_le.mp h809).le h808 (not_le.mp h817).le h822 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2347_pos (not_le.mp h809).le h808 (not_le.mp h822).le h821 hz
            · -- right
              by_cases h823 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2353_pos (not_le.mp h809).le h808 (not_le.mp h821).le h823 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2355_pos (not_le.mp h809).le h808 (not_le.mp h823).le hz2 hz
      · -- right
        by_cases h824 : a ≤ ((1316247/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h825 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h826 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h827 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2316_pos (not_le.mp h808).le h824 hz1 h827 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2318_pos (not_le.mp h808).le h824 (not_le.mp h827).le h826 hz
            · -- right
              by_cases h828 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2324_pos (not_le.mp h808).le h824 (not_le.mp h826).le h828 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2326_pos (not_le.mp h808).le h824 (not_le.mp h828).le h825 hz
          · -- right
            by_cases h829 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h830 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2348_pos (not_le.mp h808).le h824 (not_le.mp h825).le h830 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2350_pos (not_le.mp h808).le h824 (not_le.mp h830).le h829 hz
            · -- right
              by_cases h831 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2356_pos (not_le.mp h808).le h824 (not_le.mp h829).le h831 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2358_pos (not_le.mp h808).le h824 (not_le.mp h831).le hz2 hz
        · -- right
          by_cases h832 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h833 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h834 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2317_pos (not_le.mp h824).le h775 hz1 h834 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2319_pos (not_le.mp h824).le h775 (not_le.mp h834).le h833 hz
            · -- right
              by_cases h835 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B038.e2325_pos (not_le.mp h824).le h775 (not_le.mp h833).le h835 hz
              · -- right
                exact CKLaneC2R.EpCells.B038.e2327_pos (not_le.mp h824).le h775 (not_le.mp h835).le h832 hz
          · -- right
            by_cases h836 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h837 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2349_pos (not_le.mp h824).le h775 (not_le.mp h832).le h837 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2351_pos (not_le.mp h824).le h775 (not_le.mp h837).le h836 hz
            · -- right
              by_cases h838 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2357_pos (not_le.mp h824).le h775 (not_le.mp h836).le h838 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2359_pos (not_le.mp h824).le h775 (not_le.mp h838).le hz2 hz
  · -- right
    by_cases h839 : a ≤ ((330123/2048000 : ℚ) : ℝ)
    · -- left
      by_cases h840 : a ≤ ((659397/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h841 : a ≤ ((263589/1638400 : ℚ) : ℝ)
        · -- left
          by_cases h842 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h843 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h844 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2360_pos (not_le.mp h775).le h841 hz1 h844 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2362_pos (not_le.mp h775).le h841 (not_le.mp h844).le h843 hz
            · -- right
              by_cases h845 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2368_pos (not_le.mp h775).le h841 (not_le.mp h843).le h845 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2370_pos (not_le.mp h775).le h841 (not_le.mp h845).le h842 hz
          · -- right
            by_cases h846 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h847 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2392_pos (not_le.mp h775).le h841 (not_le.mp h842).le h847 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2394_pos (not_le.mp h775).le h841 (not_le.mp h847).le h846 hz
            · -- right
              by_cases h848 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2400_pos (not_le.mp h775).le h841 (not_le.mp h846).le h848 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2402_pos (not_le.mp h775).le h841 (not_le.mp h848).le hz2 hz
        · -- right
          by_cases h849 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h850 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h851 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2361_pos (not_le.mp h841).le h840 hz1 h851 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2363_pos (not_le.mp h841).le h840 (not_le.mp h851).le h850 hz
            · -- right
              by_cases h852 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2369_pos (not_le.mp h841).le h840 (not_le.mp h850).le h852 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2371_pos (not_le.mp h841).le h840 (not_le.mp h852).le h849 hz
          · -- right
            by_cases h853 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h854 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2393_pos (not_le.mp h841).le h840 (not_le.mp h849).le h854 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2395_pos (not_le.mp h841).le h840 (not_le.mp h854).le h853 hz
            · -- right
              by_cases h855 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2401_pos (not_le.mp h841).le h840 (not_le.mp h853).le h855 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2403_pos (not_le.mp h841).le h840 (not_le.mp h855).le hz2 hz
      · -- right
        by_cases h856 : a ≤ ((1319643/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h857 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h858 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h859 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2364_pos (not_le.mp h840).le h856 hz1 h859 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2366_pos (not_le.mp h840).le h856 (not_le.mp h859).le h858 hz
            · -- right
              by_cases h860 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2372_pos (not_le.mp h840).le h856 (not_le.mp h858).le h860 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2374_pos (not_le.mp h840).le h856 (not_le.mp h860).le h857 hz
          · -- right
            by_cases h861 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h862 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2396_pos (not_le.mp h840).le h856 (not_le.mp h857).le h862 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2398_pos (not_le.mp h840).le h856 (not_le.mp h862).le h861 hz
            · -- right
              by_cases h863 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2404_pos (not_le.mp h840).le h856 (not_le.mp h861).le h863 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2406_pos (not_le.mp h840).le h856 (not_le.mp h863).le hz2 hz
        · -- right
          by_cases h864 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h865 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h866 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2365_pos (not_le.mp h856).le h839 hz1 h866 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2367_pos (not_le.mp h856).le h839 (not_le.mp h866).le h865 hz
            · -- right
              by_cases h867 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2373_pos (not_le.mp h856).le h839 (not_le.mp h865).le h867 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2375_pos (not_le.mp h856).le h839 (not_le.mp h867).le h864 hz
          · -- right
            by_cases h868 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h869 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2397_pos (not_le.mp h856).le h839 (not_le.mp h864).le h869 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2399_pos (not_le.mp h856).le h839 (not_le.mp h869).le h868 hz
            · -- right
              by_cases h870 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2405_pos (not_le.mp h856).le h839 (not_le.mp h868).le h870 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2407_pos (not_le.mp h856).le h839 (not_le.mp h870).le hz2 hz
    · -- right
      by_cases h871 : a ≤ ((132219/819200 : ℚ) : ℝ)
      · -- left
        by_cases h872 : a ≤ ((1321341/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h873 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h874 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h875 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2376_pos (not_le.mp h839).le h872 hz1 h875 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2378_pos (not_le.mp h839).le h872 (not_le.mp h875).le h874 hz
            · -- right
              by_cases h876 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2384_pos (not_le.mp h839).le h872 (not_le.mp h874).le h876 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2386_pos (not_le.mp h839).le h872 (not_le.mp h876).le h873 hz
          · -- right
            by_cases h877 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h878 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2408_pos (not_le.mp h839).le h872 (not_le.mp h873).le h878 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2410_pos (not_le.mp h839).le h872 (not_le.mp h878).le h877 hz
            · -- right
              by_cases h879 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2416_pos (not_le.mp h839).le h872 (not_le.mp h877).le h879 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2418_pos (not_le.mp h839).le h872 (not_le.mp h879).le hz2 hz
        · -- right
          by_cases h880 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h881 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h882 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2377_pos (not_le.mp h872).le h871 hz1 h882 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2379_pos (not_le.mp h872).le h871 (not_le.mp h882).le h881 hz
            · -- right
              by_cases h883 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2385_pos (not_le.mp h872).le h871 (not_le.mp h881).le h883 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2387_pos (not_le.mp h872).le h871 (not_le.mp h883).le h880 hz
          · -- right
            by_cases h884 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h885 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2409_pos (not_le.mp h872).le h871 (not_le.mp h880).le h885 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2411_pos (not_le.mp h872).le h871 (not_le.mp h885).le h884 hz
            · -- right
              by_cases h886 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2417_pos (not_le.mp h872).le h871 (not_le.mp h884).le h886 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2419_pos (not_le.mp h872).le h871 (not_le.mp h886).le hz2 hz
      · -- right
        by_cases h887 : a ≤ ((1323039/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h888 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h889 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h890 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2380_pos (not_le.mp h871).le h887 hz1 h890 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2382_pos (not_le.mp h871).le h887 (not_le.mp h890).le h889 hz
            · -- right
              by_cases h891 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2388_pos (not_le.mp h871).le h887 (not_le.mp h889).le h891 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2390_pos (not_le.mp h871).le h887 (not_le.mp h891).le h888 hz
          · -- right
            by_cases h892 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h893 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2412_pos (not_le.mp h871).le h887 (not_le.mp h888).le h893 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2414_pos (not_le.mp h871).le h887 (not_le.mp h893).le h892 hz
            · -- right
              by_cases h894 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2420_pos (not_le.mp h871).le h887 (not_le.mp h892).le h894 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2422_pos (not_le.mp h871).le h887 (not_le.mp h894).le hz2 hz
        · -- right
          by_cases h895 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h896 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h897 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2381_pos (not_le.mp h887).le h774 hz1 h897 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2383_pos (not_le.mp h887).le h774 (not_le.mp h897).le h896 hz
            · -- right
              by_cases h898 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B039.e2389_pos (not_le.mp h887).le h774 (not_le.mp h896).le h898 hz
              · -- right
                exact CKLaneC2R.EpCells.B039.e2391_pos (not_le.mp h887).le h774 (not_le.mp h898).le h895 hz
          · -- right
            by_cases h899 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h900 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2413_pos (not_le.mp h887).le h774 (not_le.mp h895).le h900 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2415_pos (not_le.mp h887).le h774 (not_le.mp h900).le h899 hz
            · -- right
              by_cases h901 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2421_pos (not_le.mp h887).le h774 (not_le.mp h899).le h901 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2423_pos (not_le.mp h887).le h774 (not_le.mp h901).le hz2 hz

end CKLaneC2R.EndpointCover


