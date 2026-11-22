-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoLevyMixedBounds_F000
-- name    : LevyStochCalc_Ito_ItoLevyMixedBounds_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T10:14:45.379576+00:00
-- url     : https://prove2.me/theorems/b7ef7279-3375-4d01-973b-9f4a253c3354
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoLevyMixedBounds
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoLevyMixedBounds. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_BigJumpPathBridge_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaContinuity_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaMixed_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaTaylorBounds_F000
import Definitions.Def_LevyStochCalc_Ito_LeftLimIntegrandRegularity_F001
import Definitions.Def_LevyStochCalc_Ito_SubsequenceBookkeeping_F000
import Definitions.Def_LevyStochCalc_Ito_TruncatedContinuousPart_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bounds and admissibility of the mixed integrands

Energy bounds on a bounded window for integrands dominated by finitely many square-integrable
ones, the bounds on the four mixed integrands through the bounded derivatives of the state
function, their continuity in the state, and the progressive measurability of a marked integrand
read at a progressively measurable state.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.lintegral_window_sq_le_of_abs_le`,
  `LevyStochCalc.Ito.JumpFormula.lintegral_window_mark_sq_le_of_abs_le` — energy bounds for
  dominated integrands.
* `LevyStochCalc.Ito.JumpFormula.abs_mixedDriftIntegrand_le`,
  `LevyStochCalc.Ito.JumpFormula.abs_mixedJumpIncrement_le` — bounds on the mixed integrands.
* `LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_time_state_jump` — the triple of
  the time, a progressively measurable state and the jump coefficient along a path is marked
  progressively measurable.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Norms

/-- The supremum norm on `Fin n → ℝ` is at most the sum of the absolute coordinates. -/
theorem norm_le_sum_abs {n : ℕ} (v : Fin n → ℝ) : ‖v‖ ≤ ∑ i, |v i| := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)
/-- The square of the sum of `n` absolute values is at most `n` times the sum of the squares. -/
theorem sq_sum_abs_le {n : ℕ} (v : Fin n → ℝ) : (∑ i, |v i|) ^ 2 ≤ (n : ℝ) * ∑ i, v i ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => |v i|)
  simpa [sq_abs] using h
/-- The squared supremum norm is at most `n` times the sum of the squared coordinates. -/
theorem norm_sq_le_card_mul_sum_sq {n : ℕ} (v : Fin n → ℝ) :
    ‖v‖ ^ 2 ≤ (n : ℝ) * ∑ i, v i ^ 2 :=
  (pow_le_pow_left₀ (norm_nonneg v) (norm_le_sum_abs v) 2).trans (sq_sum_abs_le v)
/-- A real dominated by `c` times a sum of `n` absolute values has squared extended norm at most
`c² n` times the sum of the squared extended norms. -/
theorem enorm_sq_le_of_abs_le_mul_sum {n : ℕ} {x c : ℝ} {a : Fin n → ℝ}
    (h : |x| ≤ c * ∑ i, |a i|) :
    (‖x‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (c ^ 2 * n) * ∑ i, (‖a i‖₊ : ℝ≥0∞) ^ 2 := by
  have hreal : x ^ 2 ≤ c ^ 2 * n * ∑ i, a i ^ 2 := by
    calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ (c * ∑ i, |a i|) ^ 2 := pow_le_pow_left₀ (abs_nonneg x) h 2
      _ = c ^ 2 * (∑ i, |a i|) ^ 2 := by ring
      _ ≤ c ^ 2 * ((n : ℝ) * ∑ i, a i ^ 2) :=
          mul_le_mul_of_nonneg_left (sq_sum_abs_le a) (sq_nonneg c)
      _ = c ^ 2 * n * ∑ i, a i ^ 2 := by ring
  have hconv : ∀ y : ℝ, (‖y‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (y ^ 2) := by
    intro y
    rw [show ((‖y‖₊ : ℝ≥0∞)) = ‖y‖ₑ from rfl, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_pow (abs_nonneg y), sq_abs]
  simp_rw [hconv]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg (a i)),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal
end Norms

section Energies

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

omit [IsProbabilityMeasure P] in
/-- The energy of a finite sum of jointly measurable kernels over a window is the sum of the
energies. -/
theorem lintegral_window_sum {ι : Type*} [Fintype ι] {f : ι → Ω → ℝ → ℝ≥0∞}
    (hf : ∀ i, Measurable (Function.uncurry (f i))) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∑ i, f i ω s ∂volume ∂P
      = ∑ i, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, f i ω s ∂volume ∂P := by
  have h1 : ∀ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∑ i, f i ω s ∂volume
      = ∑ i, ∫⁻ s in Set.Icc (0 : ℝ) T, f i ω s ∂volume := fun ω =>
    lintegral_finsetSum _ fun i _ => Measurable.of_uncurry_left (hf i)
  simp_rw [h1]
  exact lintegral_finsetSum _ fun i _ => (hf i).lintegral_prod_right'
omit [IsProbabilityMeasure P] in
/-- The marked energy of a finite sum of jointly measurable kernels over a window is the sum of
the marked energies. -/
theorem lintegral_window_mark_sum {ι : Type*} [Fintype ι] {f : ι → Ω → ℝ → E → ℝ≥0∞}
    (hf : ∀ i, Measurable fun p : Ω × ℝ × E => f i p.1 p.2.1 p.2.2) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, ∑ i, f i ω s e ∂ν ∂volume ∂P
      = ∑ i, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, f i ω s e ∂ν ∂volume ∂P := by
  have h1 : ∀ ω s, ∫⁻ e, ∑ i, f i ω s e ∂ν = ∑ i, ∫⁻ e, f i ω s e ∂ν := fun ω s =>
    lintegral_finsetSum _ fun i _ =>
      (hf i).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have h2 : ∀ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∑ i, ∫⁻ e, f i ω s e ∂ν ∂volume
      = ∑ i, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, f i ω s e ∂ν ∂volume := fun ω =>
    lintegral_finsetSum _ fun i _ =>
      LevyStochCalc.Ito.IntegralLimit.measurable_section_markLIntegral (hf i) ω
  simp_rw [h1, h2]
  exact lintegral_finsetSum _ fun i _ => measurable_markEnergy (hf i) T
omit [IsProbabilityMeasure P] in
/-- A process dominated by `c` times a sum of `n` processes of finite energy on a window has
finite energy on that window. -/
theorem lintegral_window_sq_le_of_abs_le {n : ℕ} {H : Ω → ℝ → ℝ} {a : Fin n → Ω → ℝ → ℝ}
    {c : ℝ} (ha : ∀ i, Measurable (Function.uncurry (a i)))
    (h : ∀ ω s, |H ω s| ≤ c * ∑ i, |a i ω s|) (T : ℝ)
    (hq : ∀ i, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖a i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hpt : ∀ ω s, (‖H ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ ENNReal.ofReal (c ^ 2 * n) * ∑ i, (‖a i ω s‖₊ : ℝ≥0∞) ^ 2 :=
    fun ω s => enorm_sq_le_of_abs_le_mul_sum (h ω s)
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s => hpt ω s) ?_
  have hm : ∀ i, Measurable (Function.uncurry fun ω s => (‖a i ω s‖₊ : ℝ≥0∞) ^ 2) :=
    fun i => ((ha i).nnnorm.coe_nnreal_ennreal).pow_const 2
  have hC : ENNReal.ofReal (c ^ 2 * n) ≠ ⊤ := ENNReal.ofReal_ne_top
  simp_rw [lintegral_const_mul' _ _ hC]
  rw [lintegral_window_sum (f := fun i ω s => (‖a i ω s‖₊ : ℝ≥0∞) ^ 2) hm T]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.mpr fun i _ => hq i)
end Energies

section MixedBounds

variable {n d : ℕ} {E : Type v} {u : ℝ → (Fin n → ℝ) → ℝ}

end MixedBounds

section MixedContinuity

variable {n d : ℕ} {E : Type v} {u : ℝ → (Fin n → ℝ) → ℝ} {z : ℕ → Fin n → ℝ} {w : Fin n → ℝ}

end MixedContinuity

section Progressive

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

end Progressive

end LevyStochCalc.Ito.JumpFormula


