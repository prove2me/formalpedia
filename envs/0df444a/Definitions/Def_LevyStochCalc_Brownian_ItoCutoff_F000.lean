-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F000
-- name    : LevyStochCalc_Brownian_ItoCutoff_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:45:42.981516+00:00
-- url     : https://prove2.me/theorems/99a78677-8c32-416e-a19d-fb6a8f261fac
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoCutoff
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoCutoff. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F001
import Definitions.Def_LevyStochCalc_Brownian_SmoothCutoff_F000
import Definitions.Def_LevyStochCalc_Brownian_VectorItoFormula_F000
import Definitions.Def_LevyStochCalc_Probability_ExitTime_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a twice continuously differentiable function

Multiplying `f` by a smooth box cutoff leaves it, together with its first two derivatives,
unchanged on a cube and makes them bounded and uniformly continuous. Along a path stopped before
it leaves that cube the two functions therefore give the same integrands, and the local property
of the Itô integral transfers the stochastic terms.

## Main statements

* `LevyStochCalc.cutoffFun` — the cut-off function.
* `LevyStochCalc.fderiv_cutoffFun` — its first two derivatives agree with `f`'s on the cube.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula_of_contDiff` — Itô's formula for a
  twice continuously differentiable function, with no bound on its derivatives.
-/

namespace LevyStochCalc

open scoped Topology

section Cutoff

variable {n : ℕ}

/-- The product of `f` with the smooth box cutoff of radius `k`. -/
noncomputable def cutoffFun (f : (Fin n → ℝ) → ℝ) (k : ℝ) : (Fin n → ℝ) → ℝ :=
  fun z => f z * boxCut k z
theorem contDiff_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    ContDiff ℝ 2 (cutoffFun f k) :=
  hf.mul (contDiff_boxCut (n := n) k)
theorem hasCompactSupport_cutoffFun (f : (Fin n → ℝ) → ℝ) {k : ℝ} (hk : 0 < k) :
    HasCompactSupport (cutoffFun f k) :=
  (hasCompactSupport_boxCut (n := n) hk).mul_left
theorem cutoffFun_eventuallyEq {f : (Fin n → ℝ) → ℝ} {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ}
    (hz : ‖z‖ < 3 * k / 2) : cutoffFun f k =ᶠ[𝓝 z] f := by
  filter_upwards [boxCut_eventuallyEq_one (n := n) hk hz] with w hw
  simp [cutoffFun, hw]
theorem fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ}
    (hz : ‖z‖ < 3 * k / 2) : fderiv ℝ (cutoffFun f k) z = fderiv ℝ f z :=
  (cutoffFun_eventuallyEq hk hz).fderiv_eq
theorem fderiv_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ}
    (hz : ‖z‖ < 3 * k / 2) :
    fderiv ℝ (fderiv ℝ (cutoffFun f k)) z = fderiv ℝ (fderiv ℝ f) z := by
  have hopen : IsOpen {w : Fin n → ℝ | ‖w‖ < 3 * k / 2} :=
    isOpen_lt continuous_norm continuous_const
  have hev : fderiv ℝ (cutoffFun f k) =ᶠ[𝓝 z] fderiv ℝ f := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact fderiv_cutoffFun hk hw
  exact hev.fderiv_eq
theorem continuous_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    Continuous (fderiv ℝ (cutoffFun f k)) :=
  ((contDiff_cutoffFun hf k).fderiv_right (m := 1) (by norm_num)).continuous
theorem continuous_fderiv_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    Continuous (fderiv ℝ (fderiv ℝ (cutoffFun f k))) :=
  (((contDiff_cutoffFun hf k).fderiv_right (m := 1) (by norm_num)).fderiv_right
    (m := 0) (by norm_num)).continuous
theorem differentiable_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    Differentiable ℝ (cutoffFun f k) :=
  (contDiff_cutoffFun hf k).differentiable (by norm_num)
theorem differentiable_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    Differentiable ℝ (fderiv ℝ (cutoffFun f k)) :=
  ((contDiff_cutoffFun hf k).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
theorem cutoffFun_eventuallyEq_zero {f : (Fin n → ℝ) → ℝ} {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ}
    (hz : 2 * k < ‖z‖) : cutoffFun f k =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
  have hopen : IsOpen {w : Fin n → ℝ | 2 * k < ‖w‖} :=
    isOpen_lt continuous_const continuous_norm
  filter_upwards [hopen.mem_nhds hz] with w hw
  simp [cutoffFun, boxCut_eq_zero hk hw]
theorem fderiv_cutoffFun_eq_zero {f : (Fin n → ℝ) → ℝ} {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ}
    (hz : 2 * k < ‖z‖) : fderiv ℝ (cutoffFun f k) z = 0 := by
  rw [(cutoffFun_eventuallyEq_zero (f := f) hk hz).fderiv_eq]
  simp
theorem fderiv_fderiv_cutoffFun_eq_zero {f : (Fin n → ℝ) → ℝ} {k : ℝ} (hk : 0 < k)
    {z : Fin n → ℝ} (hz : 2 * k < ‖z‖) : fderiv ℝ (fderiv ℝ (cutoffFun f k)) z = 0 := by
  have hopen : IsOpen {w : Fin n → ℝ | 2 * k < ‖w‖} :=
    isOpen_lt continuous_const continuous_norm
  have hev : fderiv ℝ (cutoffFun f k) =ᶠ[𝓝 z] fun _ => (0 : (Fin n → ℝ) →L[ℝ] ℝ) := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact fderiv_cutoffFun_eq_zero (f := f) hk hw
  rw [hev.fderiv_eq]
  simp
/-- The coordinates of the first derivative, as a vector. -/
noncomputable def gradVec (g : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) : Fin n → ℝ :=
  fun p => fderiv ℝ g z (Pi.single p 1)
/-- The coordinates of the second derivative, as a vector. -/
noncomputable def hessVec (g : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) : Fin n × Fin n → ℝ :=
  fun pq => fderiv ℝ (fderiv ℝ g) z (Pi.single pq.1 1) (Pi.single pq.2 1)
theorem continuous_gradVec {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    Continuous (gradVec (cutoffFun f k)) :=
  continuous_pi fun _ => (continuous_fderiv_cutoffFun hf k).clm_apply continuous_const
theorem continuous_hessVec {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    Continuous (hessVec (cutoffFun f k)) :=
  continuous_pi fun _ =>
    ((continuous_fderiv_fderiv_cutoffFun hf k).clm_apply continuous_const).clm_apply
      continuous_const
theorem hasCompactSupport_gradVec (f : (Fin n → ℝ) → ℝ) {k : ℝ} (hk : 0 < k) :
    HasCompactSupport (gradVec (cutoffFun f k)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℝ) (2 * k)) fun z hz => ?_
  have hz' : 2 * k < ‖z‖ := by
    by_contra hcon
    exact hz (by simpa [Metric.mem_closedBall, dist_eq_norm] using not_lt.mp hcon)
  funext p
  simp [gradVec, fderiv_cutoffFun_eq_zero (f := f) hk hz']
theorem hasCompactSupport_hessVec (f : (Fin n → ℝ) → ℝ) {k : ℝ} (hk : 0 < k) :
    HasCompactSupport (hessVec (cutoffFun f k)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℝ) (2 * k)) fun z hz => ?_
  have hz' : 2 * k < ‖z‖ := by
    by_contra hcon
    exact hz (by simpa [Metric.mem_closedBall, dist_eq_norm] using not_lt.mp hcon)
  funext pq
  simp [hessVec, fderiv_fderiv_cutoffFun_eq_zero (f := f) hk hz']
end Cutoff

namespace Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim LevyStochCalc.Probability
open scoped NNReal ENNReal

universe u

section Bounded

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Bounded

section Formula

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)

end Formula

end Brownian.Ito

end LevyStochCalc


