-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g69_q00
-- name    : CK_CKLaneC2R_CompactCover_S01_g69_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T00:22:04.115261+00:00
-- url     : https://prove2.me/theorems/9f6058fd-51e0-4132-bfd4-9f614f4c9c59
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01 (proof part of strip1) (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01 (proof part of strip1) (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01 (proof part of strip1) (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (proof part of strip1) (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01 (proof part of strip1) (piece 1 of 2).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B000
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B001


namespace CKLaneC2R.CompactCover

theorem strip1_s098 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : ¬ (a ≤ ((21/80 : ℚ) : ℝ))) (h880 : ¬ (a ≤ ((43/160 : ℚ) : ℝ))) (h941 : z ≤ ((217/400 : ℚ) : ℝ)) (h942 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h943 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h957 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h958 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h959 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B017.c358_pos (not_le.mp h880).le h746 (not_le.mp h943).le h959
      · -- right
        exact CKLaneC2R.Cells.S01.B017.c359_pos (not_le.mp h880).le h746 (not_le.mp h959).le h958
    · -- right
      by_cases h960 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B018.c362_pos (not_le.mp h880).le h746 (not_le.mp h958).le h960
      · -- right
        exact CKLaneC2R.Cells.S01.B018.c363_pos (not_le.mp h880).le h746 (not_le.mp h960).le h957
  · -- right
    by_cases h961 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h962 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B018.c374_pos (not_le.mp h880).le h746 (not_le.mp h957).le h962
      · -- right
        exact CKLaneC2R.Cells.S01.B018.c375_pos (not_le.mp h880).le h746 (not_le.mp h962).le h961
    · -- right
      by_cases h963 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B018.c378_pos (not_le.mp h880).le h746 (not_le.mp h961).le h963
      · -- right
        exact CKLaneC2R.Cells.S01.B018.c379_pos (not_le.mp h880).le h746 (not_le.mp h963).le h942

end CKLaneC2R.CompactCover


