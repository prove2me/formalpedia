-- Prove2me | Definitions.Def_CK_CKLaneA1_Bridge
-- name    : CK_CKLaneA1_Bridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T16:01:13.112872+00:00
-- url     : https://prove2.me/theorems/d4100f4e-81e9-4c6a-9da2-02bee933b24f
-- title:
--   Courtade–Kumar proof module `CKLaneA1.Bridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.Bridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.Bridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.Bridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/Bridge.lean)

import Definitions.Def_CK_CKLaneA1_Identities
import Definitions.Def_CK_GeneralCK_CorrectionComplementCharts

/-!
# CKLaneA1.Bridge — from pointwise positivity to `RatioSigns`

`RatioSigns u rho` (the sign strength required by `ChartOwners`) follows from
`0 ≤ actualDetGapCoefficient u w` and `0 < m11 u w` at `w = u + rho (1/2 - u)`, via
`kernel_eq_actual`, `kdet = (w-u)^2 · actualDetGapCoefficient` and
`Mdet_nonneg_iff_Kfactored_nonneg`.
-/

set_option autoImplicit false

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU

theorem ratioSigns_of_pos {u rho : ℝ} (hu : 0 < u) (hu2 : u < 1 / 2) (hr : 0 < rho)
    (hr1 : rho < 1)
    (hcoef : 0 ≤ actualDetGapCoefficient u (u + rho * (1 / 2 - u)))
    (hm : 0 < m11 u (u + rho * (1 / 2 - u))) :
    GeneralCK.Correction.Complement.RatioSigns u rho := by
  have hgap : 0 < rho * (1 / 2 - u) := mul_pos hr (by linarith)
  have huw : u < u + rho * (1 / 2 - u) := by linarith
  have hw : u + rho * (1 / 2 - u) < 1 / 2 := by
    have : rho * (1 / 2 - u) < 1 * (1 / 2 - u) := mul_lt_mul_of_pos_right hr1 (by linarith)
    linarith
  have hk : 0 ≤ kdet u (u + rho * (1 / 2 - u)) := by
    rw [kdet_eq_gap_sq_mul_coefficient hu huw hw]
    exact mul_nonneg (sq_nonneg _) hcoef
  obtain ⟨h1, h2⟩ := kernel_eq_actual hu huw hw
  have hw0 : 0 < H (u + rho * (1 / 2 - u)) := H_pos (hu.trans huw) (by linarith)
  have hw1 : H (u + rho * (1 / 2 - u)) < 1 := by
    have ht := H_strictMonoOn ⟨(hu.trans huw).le, hw.le⟩
      (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc 0 (1 / 2)) hw
    simpa only [H_half] using ht
  unfold GeneralCK.Correction.Complement.RatioSigns
  refine ⟨?_, ?_⟩
  · rw [← h1]; exact hm
  · exact (Mdet_nonneg_iff_Kfactored_nonneg hw0 hw1).2 (by rw [← h2]; exact hk)

#print axioms ratioSigns_of_pos

end CKLaneA1


