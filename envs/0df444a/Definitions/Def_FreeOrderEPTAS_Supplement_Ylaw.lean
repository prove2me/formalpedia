-- Prove2me | Definitions.Def_FreeOrderEPTAS_Supplement_Ylaw
-- name    : FreeOrderEPTAS_Supplement_Ylaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:37:45.744097+00:00
-- url     : https://prove2.me/theorems/59e7bcee-ef25-46e4-b277-330941bf4e5d
-- title:
--   The capped instance $Y_i=\min\{X_i,\kappa_i\}$
-- statement:
--   Given an instance $(X,c)$ of Pandora's Box with Commitment, the Free-Order Prophets instance $Y$ has the independent variables
--   $$Y_i=\min\{X_i,\kappa_i\},\qquad i=1,\dots,n,$$
--   where $\kappa_i$ is Weitzman's index; $Y_i=X_i$ when $c_i=0$.
--
--   **Formalization Note** The law of $Y_i$ is the image of the law of $X_i$ under $x\mapsto\max\{\min\{x,\kappa_i\},0\}$. The clip at $0$ matters only when $\kappa_i<0$, where $Y_i$ would be the negative constant $\kappa_i$; it becomes $0$, which the base instance's non-negativity requires and which changes no stopping value.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, proof of Theorem 6.1, p.31

import Mathlib
import Definitions.Def_FreeOrderEPTAS_Supplement_kappa

open MeasureTheory

namespace FreeOrderEPTAS.Supplement

/-- `x ↦ min{x, κ}` clipped below at `0`, and `x ↦ x` for `κ = ∞`. -/
noncomputable def yMap (k : WithTop ℝ) (x : ℝ) : ℝ :=
  if h : k = ⊤ then x else max (min x (k.untop h)) 0

theorem measurable_yMap (k : WithTop ℝ) : Measurable (yMap k) := by
  unfold yMap
  split_ifs with h
  · exact measurable_id
  · exact ((continuous_id.min continuous_const).max continuous_const).measurable

theorem abs_yMap_le (k : WithTop ℝ) (x : ℝ) : |yMap k x| ≤ |x| := by
  unfold yMap
  split_ifs with h
  · exact le_rfl
  · rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg (le_max_right _ _), abs_of_nonneg hx]
      exact max_le (min_le_left _ _) hx
    · rw [abs_of_nonneg (le_max_right _ _)]
      have : min x (k.untop h) ≤ 0 := (min_le_left _ _).trans hx.le
      rw [max_eq_right this]
      exact abs_nonneg x

/-- The Free-Order Prophets instance `Y_i = min{X_i, κ_i}` of the proof of Theorem 6.1
(arXiv:2007.13121v3, p.31), `κ` being Weitzman's index (`kappa`).

**Formalization Note.** `Y_i` is the push-forward of `μ_i` under `x ↦ max{min{x, κ_i}, 0}`, and
`Y_i = X_i` when `κ_i = ∞` (`c_i = 0`). The clip at `0` matters only when `κ_i < 0`
(`c_i > E[X_i]`), where `min{X_i, κ_i} = κ_i < 0` almost surely and the base instance requires
non-negative values; there `Y_i = 0`. A variable that is a.s. `0` or a.s. negative never raises the
value of a stopping rule, so `V` and `OPT` are the same for both versions. -/
noncomputable def Ylaw {n : ℕ} (P : PandoraInstance n) : Instance n where
  μ i := (P.X.μ i).map (yMap (kappa P i))
  prob i := Measure.isProbabilityMeasure_map (measurable_yMap _).aemeasurable
  nonneg i := by
    rw [Measure.map_apply (measurable_yMap _) measurableSet_Iio]
    by_cases h : kappa P i = ⊤
    · have : yMap (kappa P i) ⁻¹' Set.Iio 0 = Set.Iio 0 := by
        ext x; simp [yMap, h]
      rw [this]; exact P.X.nonneg i
    · have : yMap (kappa P i) ⁻¹' Set.Iio 0 = ∅ := by
        ext x; simp [yMap, h]
      rw [this]; exact measure_empty
  integrable i := by
    rw [integrable_map_measure aestronglyMeasurable_id (measurable_yMap _).aemeasurable]
    refine Integrable.mono' (P.X.integrable i).norm
      ((measurable_yMap _).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
    simpa [Real.norm_eq_abs] using abs_yMap_le (kappa P i) x

end FreeOrderEPTAS.Supplement


