-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_SmoothCutoff_F000
-- name    : LevyStochCalc_Brownian_SmoothCutoff_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:58:20.147069+00:00
-- url     : https://prove2.me/theorems/74de78c2-4820-48da-8bd3-f50df2272b39
-- title:
--   Source declarations: LevyStochCalc.Brownian.SmoothCutoff
-- statement:
--   Source-preserving Lean declaration bundle from LevyStochCalc.Brownian.SmoothCutoff, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A smooth compactly supported cutoff on a finite-dimensional cube

Multiplying a function by a product of one-dimensional smooth transitions leaves it unchanged on a
cube and gives it compact support. The cutoff equals `1` on the cube of radius `3k/2` and vanishes
off the cube of radius `2k`, so on the smaller cube the product agrees with the original function
together with all its derivatives.

## Main statements

* `LevyStochCalc.smoothCut` — the one-dimensional cutoff.
* `LevyStochCalc.boxCut` — its product over the coordinates.
* `LevyStochCalc.boxCut_eventuallyEq_one` — it is identically `1` near a point of the small cube.
* `LevyStochCalc.hasCompactSupport_boxCut` — it has compact support.
* `LevyStochCalc.exists_delta_of_hasCompactSupport` — a continuous function with compact support
  on a proper normed space is uniformly continuous, in `ε`–`δ` form.
-/

namespace LevyStochCalc

open scoped Topology

section OneDim

/-- A smooth one-dimensional cutoff: `1` on `[-3k/2, 3k/2]` and `0` off `(-2k, 2k)`. -/
noncomputable def smoothCut (k t : ℝ) : ℝ :=
  Real.smoothTransition ((4 * k ^ 2 - t ^ 2) * 4 / (7 * k ^ 2))
theorem contDiff_smoothCut (k : ℝ) {N : ℕ∞} : ContDiff ℝ N (smoothCut k) := by
  unfold smoothCut
  exact Real.smoothTransition.contDiff.comp (by fun_prop)
theorem smoothCut_eq_one {k t : ℝ} (hk : 0 < k) (ht : |t| ≤ 3 * k / 2) : smoothCut k t = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 7 * k ^ 2)]
  nlinarith [abs_nonneg t, sq_abs t, ht, hk]
theorem smoothCut_eq_zero {k t : ℝ} (hk : 0 < k) (ht : 2 * k ≤ |t|) : smoothCut k t = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
  nlinarith [abs_nonneg t, sq_abs t, ht, hk]
end OneDim

section Box

variable {n : ℕ}

/-- The product of the one-dimensional cutoffs over the coordinates. -/
noncomputable def boxCut (k : ℝ) (z : Fin n → ℝ) : ℝ := ∏ i, smoothCut k (z i)
theorem contDiff_boxCut (k : ℝ) {N : ℕ∞} : ContDiff ℝ N (boxCut (n := n) k) := by
  unfold boxCut
  exact contDiff_prod fun i _ => (contDiff_smoothCut k).comp (contDiff_apply ℝ ℝ i)
theorem boxCut_eq_one {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ} (hz : ‖z‖ ≤ 3 * k / 2) :
    boxCut k z = 1 := by
  refine Finset.prod_eq_one fun i _ => smoothCut_eq_one hk ?_
  have := (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * k / 2)).mp hz i
  simpa [Real.norm_eq_abs] using this
theorem boxCut_eventuallyEq_one {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ} (hz : ‖z‖ < 3 * k / 2) :
    boxCut (n := n) k =ᶠ[𝓝 z] fun _ => (1 : ℝ) := by
  have hopen : IsOpen {w : Fin n → ℝ | ‖w‖ < 3 * k / 2} :=
    isOpen_lt continuous_norm continuous_const
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact boxCut_eq_one hk (le_of_lt hw)
theorem boxCut_eq_zero {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ} (hz : 2 * k < ‖z‖) :
    boxCut k z = 0 := by
  have hex : ∃ i : Fin n, 2 * k ≤ |z i| := by
    by_contra hcon
    have hcon' : ∀ i : Fin n, |z i| < 2 * k := fun i => not_le.mp fun h => hcon ⟨i, h⟩
    have hle : ‖z‖ ≤ 2 * k := by
      refine (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * k)).mpr fun i => ?_
      simpa [Real.norm_eq_abs] using (hcon' i).le
    linarith
  obtain ⟨i, hi⟩ := hex
  exact Finset.prod_eq_zero (Finset.mem_univ i) (smoothCut_eq_zero hk hi)
theorem hasCompactSupport_boxCut {k : ℝ} (hk : 0 < k) :
    HasCompactSupport (boxCut (n := n) k) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℝ) (2 * k)) fun z hz => ?_
  refine boxCut_eq_zero hk ?_
  simpa [Metric.mem_closedBall, dist_eq_norm] using not_le.mp fun h => hz (by simpa using h)
end Box

section UniformContinuity

/-- **A continuous function with compact support on a proper normed space is uniformly
continuous**, in `ε`–`δ` form. -/
theorem exists_delta_of_hasCompactSupport {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {u : E → F} (hu : Continuous u) (hsupp : HasCompactSupport u)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ∀ z w : E, ‖z - w‖ < δ → ‖u z - u w‖ ≤ ε := by
  have huc : UniformContinuous u :=
    hu.uniformContinuous_of_tendsto_cocompact hsupp.is_zero_at_infty
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  refine ⟨δ, hδ0, fun z w hzw => ?_⟩
  have hd : dist z w < δ := by rwa [dist_eq_norm]
  have := hδ hd
  rw [dist_eq_norm] at this
  exact this.le
end UniformContinuity

end LevyStochCalc


