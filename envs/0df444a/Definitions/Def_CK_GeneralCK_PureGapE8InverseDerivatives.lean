-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8InverseDerivatives
-- name    : CK_GeneralCK_PureGapE8InverseDerivatives
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:50:35.519245+00:00
-- url     : https://prove2.me/theorems/3c1166b0-5934-4fcc-951d-aa47c92d85c1
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8InverseDerivatives` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8InverseDerivatives` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8InverseDerivatives` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8InverseDerivatives (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8InverseDerivatives.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8Inverse
import Mathlib.Analysis.Calculus.Deriv.Inverse

-- ===== source module GeneralCK.PureGapE8InverseDerivatives =====
section

/-!
# Differentiability of the concrete E8 inverse

The choice-defined `e8Q` is the genuine local inverse of `e8Theta` at every
point of its positive slope range.  This file proves the needed continuity
directly from monotonicity and the intermediate value theorem, then applies
the one-dimensional inverse derivative theorem.
-/

namespace GeneralCK
open Set Filter

theorem e8Q_image_slopeRange : e8Q '' e8SlopeRange = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact e8Q_pos hy
  · intro hx
    refine ⟨e8Theta x, ⟨x, hx, rfl⟩, ?_⟩
    exact e8Q_e8Theta hx

/-- The positive slope range is a neighborhood of each of its points.  This
is the local openness needed for differentiating the choice-defined inverse.
-/
theorem e8SlopeRange_mem_nhds {y : ℝ} (hy : y ∈ e8SlopeRange) :
    e8SlopeRange ∈ nhds y := by
  let x := e8Q y
  have hx : 0 < x := e8Q_pos hy
  let l : ℝ := x / 2
  let u : ℝ := 3 * x / 2
  have hl : 0 < l := by dsimp [l]; positivity
  have hlu : l ≤ u := by dsimp [l, u]; linarith
  have hxu : x < u := by dsimp [u]; linarith
  have hlx : l < x := by dsimp [l]; linarith
  have hθx : e8Theta x = y := e8Theta_e8Q hy
  have hleft : e8Theta l < y := by
    rw [← hθx]
    exact strictMonoOn_e8Theta_pos hl hx hlx
  have hright : y < e8Theta u := by
    rw [← hθx]
    exact strictMonoOn_e8Theta_pos hx (hx.trans hxu) hxu
  have hcont : ContinuousOn e8Theta (Icc l u) :=
    continuousOn_e8Theta_pos.mono (fun _ hz => hl.trans_le hz.1)
  have hiv : Icc (e8Theta l) (e8Theta u) ⊆ e8Theta '' Icc l u :=
    intermediate_value_Icc hlu hcont
  have hsub : Ioo (e8Theta l) (e8Theta u) ⊆ e8SlopeRange := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hiv ⟨hz.1.le, hz.2.le⟩
    exact ⟨w, hl.trans_le hw.1, rfl⟩
  exact mem_of_superset (Ioo_mem_nhds hleft hright) hsub

theorem continuousAt_e8Q {y : ℝ} (hy : y ∈ e8SlopeRange) :
    ContinuousAt e8Q y := by
  apply strictMonoOn_e8Q_range.continuousAt_of_image_mem_nhds
  · exact e8SlopeRange_mem_nhds hy
  · rw [e8Q_image_slopeRange]
    exact Ioi_mem_nhds (e8Q_pos hy)

/-- First inverse-derivative identity for the concrete `e8Q`. -/
theorem hasDerivAt_e8Q {y : ℝ} (hy : y ∈ e8SlopeRange) :
    HasDerivAt e8Q (deriv e8Theta (e8Q y))⁻¹ y := by
  have hq : 0 < e8Q y := e8Q_pos hy
  have hθ := hasDerivAt_e8Theta hq
  have hne : 2 * deriv (deriv (fun r => F r 1)) (2 * e8Q y) ≠ 0 := by
    rw [← hθ.deriv]
    exact ne_of_gt (deriv_e8Theta_pos hq)
  have hinv := hθ.of_local_left_inverse (continuousAt_e8Q hy) hne (by
    filter_upwards [e8SlopeRange_mem_nhds hy] with z hz
    exact e8Theta_e8Q hz)
  rw [hθ.deriv]
  exact hinv

theorem deriv_e8Q {y : ℝ} (hy : y ∈ e8SlopeRange) :
    deriv e8Q y = (deriv e8Theta (e8Q y))⁻¹ :=
  (hasDerivAt_e8Q hy).deriv

theorem deriv_e8Q_pos {y : ℝ} (hy : y ∈ e8SlopeRange) :
    0 < deriv e8Q y := by
  rw [deriv_e8Q hy]
  exact inv_pos.mpr (deriv_e8Theta_pos (e8Q_pos hy))

/-- The already-established radial curvature formula, exposed in the form
needed by interval bounds for the inverse recurrence. -/
theorem deriv_e8Theta {x : ℝ} (hx : 0 < x) :
    deriv e8Theta x =
      2 * deriv (deriv (fun r => F r 1)) (2 * x) :=
  (hasDerivAt_e8Theta hx).deriv

/-- The second inverse-derivative recurrence.  The only input not already
provided by the concrete inverse construction is a derivative enclosure for
`deriv e8Theta` at the corresponding positive contact coordinate. -/
theorem hasDerivAt_deriv_e8Q {y theta2 : ℝ} (hy : y ∈ e8SlopeRange)
    (hθ2 : HasDerivAt (deriv e8Theta) theta2 (e8Q y)) :
    HasDerivAt (deriv e8Q)
      (-theta2 / (deriv e8Theta (e8Q y)) ^ 3) y := by
  have hq := hasDerivAt_e8Q hy
  have hθpos := deriv_e8Theta_pos (e8Q_pos hy)
  have hne : deriv e8Theta (e8Q y) ≠ 0 := ne_of_gt hθpos
  have hcomp := hθ2.comp y hq
  have hinv := hcomp.inv hne
  have heq : deriv e8Q =ᶠ[nhds y]
      fun z => (deriv e8Theta (e8Q z))⁻¹ := by
    filter_upwards [e8SlopeRange_mem_nhds hy] with z hz
    exact deriv_e8Q hz
  have hd := hinv.congr_of_eventuallyEq heq
  simp only [Function.comp_apply] at hd
  convert! hd using 1
  field_simp [hne]

theorem deriv2_e8Q {y theta2 : ℝ} (hy : y ∈ e8SlopeRange)
    (hθ2 : HasDerivAt (deriv e8Theta) theta2 (e8Q y)) :
    deriv (deriv e8Q) y =
      -theta2 / (deriv e8Theta (e8Q y)) ^ 3 :=
  (hasDerivAt_deriv_e8Q hy hθ2).deriv

end GeneralCK

end


