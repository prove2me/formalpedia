-- Prove2me | Definitions.Def_LevyStochCalc_Ito_VectorItoVersionSup_F000
-- name    : LevyStochCalc_Ito_VectorItoVersionSup_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:04:09.181667+00:00
-- url     : https://prove2.me/theorems/db8ab5ed-719a-4b08-9d3f-aa4dd0fd4300
-- title:
--   Source declarations: LevyStochCalc.Ito.VectorItoVersionSup
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.VectorItoVersionSup. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_VectorItoProcessDiff_F000
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F002
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F003
import Definitions.Def_SourceProof_199d6571e2e85cd1e6522226
import Definitions.Def_SourceProof_d76df0724e08b30159a31ac0

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The window supremum of the difference of two vector Itô versions

Two versions driven by different coefficients differ by a drift part, controlled pathwise by
Cauchy–Schwarz, and a martingale part, controlled by Doob's `L²` maximal inequality. Sampling the
paths on the dyadic points of the window turns the supremum into a countable one, which is all the
maximal inequality needs.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_version_sub_le` — the second moment of the
  window supremum of the difference, in terms of the coefficients' energies.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

universe u

section Helpers

variable {Ω : Type u}

/-- The extended norm of a vector is at most the sum of the extended norms of its entries. -/
theorem enorm_pi_le_sum {m : ℕ} (x : Fin m → ℝ) :
    (‖x‖₊ : ℝ≥0∞) ≤ ∑ p, (‖x p‖₊ : ℝ≥0∞) := by
  have hreal : ‖x‖ ≤ ∑ p, ‖x p‖ := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun p _ => norm_nonneg _)).mpr fun p => ?_
    exact Finset.single_le_sum (f := fun q => ‖x q‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ p)
  have hnn : ‖x‖₊ ≤ ∑ p, ‖x p‖₊ := by
    rw [← NNReal.coe_le_coe]
    push_cast
    simpa using hreal
  calc (‖x‖₊ : ℝ≥0∞) ≤ ((∑ p, ‖x p‖₊ : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hnn
    _ = ∑ p, (‖x p‖₊ : ℝ≥0∞) := by rw [ENNReal.ofNNReal_finsetSum]
/-- The extended norm does not see the absolute value. -/
theorem nnnorm_abs_real (x : ℝ) : ‖|x|‖₊ = ‖x‖₊ := by
  rw [← Real.norm_eq_abs, nnnorm_norm]
/-- A squared sum of two terms, up to a constant. -/
theorem add_sq_le_four_mul (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  have h := _root_.Prove2MeSourceProof.h_d76df0724e08b30159a31ac0 (Finset.univ : Finset (Fin 2)) ![a, b]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Finset.card_univ, Fintype.card_fin] at h
  have h4 : ((2 : ℕ) : ℝ≥0∞) ^ 2 = 4 := by norm_num
  rwa [h4] at h
/-- The sampled running maximum only sees the values at the dyadic points. -/
theorem dyadicRunMax_congr {A B : ℝ → Ω → ℝ} {T : ℝ} {ω : Ω}
    (h : ∀ m k : ℕ, A (dyadicTime T m k) ω = B (dyadicTime T m k) ω) (m : ℕ) :
    dyadicRunMax A T m ω = dyadicRunMax B T m ω := by
  simp only [dyadicRunMax]
  refine Finset.sup'_congr _ rfl fun k _ => ?_
  rw [h m k]
/-- The sampled running maximum does not see the absolute value. -/
theorem dyadicRunMax_abs (A : ℝ → Ω → ℝ) (T : ℝ) (m : ℕ) (ω : Ω) :
    dyadicRunMax (fun t ω => |A t ω|) T m ω = dyadicRunMax A T m ω := by
  simp only [dyadicRunMax]
  refine Finset.sup'_congr _ rfl fun k _ => ?_
  simp [Real.norm_eq_abs]
variable [MeasurableSpace Ω] {P : Measure Ω}

/-- A finite sum of martingales is a martingale. -/
theorem martingale_finsetSum {ι : Type*} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (s : Finset ι) (f : ι → ℝ → Ω → ℝ)
    (hf : ∀ i ∈ s, MeasureTheory.Martingale (f i) ℱ P) :
    MeasureTheory.Martingale (fun t ω => ∑ i ∈ s, f i t ω) ℱ P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun (t : ℝ) (ω : Ω) => ∑ i ∈ (∅ : Finset ι), f i t ω) = (0 : ℝ → Ω → ℝ) := by
        funext t ω
        simp
      rw [h0]
      exact MeasureTheory.martingale_zero ℝ ℱ P
  | insert i s hi ih =>
      have hsum : (fun t ω => ∑ j ∈ insert i s, f j t ω)
          = fun t ω => f i t ω + ∑ j ∈ s, f j t ω := by
        funext t ω
        rw [Finset.sum_insert hi]
      rw [hsum]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
end Helpers

section SupBound

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

include hcoord in
/-- The martingale part of a vector Itô process is a martingale. -/
theorem martingale_vectorItoMartingale
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
    (hq : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (p : Fin n) :
    MeasureTheory.Martingale
      (fun t ω => vectorItoMartingale W ℱ hcoord H hm hp hq p t ω) ℱ P := by
  have hrw : (fun (t : ℝ) (ω : Ω) => vectorItoMartingale W ℱ hcoord H hm hp hq p t ω)
      = fun t ω => ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k)
          (hm p k) (hp p k) (hq p k) t ω := rfl
  rw [hrw]
  exact martingale_finsetSum Finset.univ _ fun k _ =>
    _root_.Prove2MeSourceProof.h_199d6571e2e85cd1e6522226 (W.W k) ℱ (hcoord k) (H p k) (hm p k) (hp p k) (hq p k)
end SupBound

end LevyStochCalc.Brownian.Ito


