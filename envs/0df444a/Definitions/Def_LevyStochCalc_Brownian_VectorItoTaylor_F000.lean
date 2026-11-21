-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_VectorItoTaylor_F000
-- name    : LevyStochCalc_Brownian_VectorItoTaylor_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:36:53.295457+00:00
-- url     : https://prove2.me/theorems/26f0d6d4-d991-4a7c-91c1-06c7cb6139fb
-- title:
--   LevyStochCalc source module: LevyStochCalc.Brownian.VectorItoTaylor
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Brownian.VectorItoTaylor in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_TaylorTwoModulus_F000
import Definitions.Def_LevyStochCalc_Brownian_VectorItoThirdMoment_F000
import Definitions.Def_SourceProof_51f76ce41cba72e9e1f79ed9

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Taylor remainder of a vector Itô process along a uniform grid

Expanding a twice-differentiable function of a vector Itô process cell by cell leaves a
second-order Taylor remainder. For a Lipschitz second derivative that remainder is cubic in the
increment, so the third moments of the increments bound it in `L¹`; across a uniform grid of `m`
cells the bound is of order `m^{-1/2}`.

## Main statements

* `LevyStochCalc.Brownian.Ito.measurable_taylorRemainderNormed` — the remainder along a
  measurable sequence is measurable.
* `LevyStochCalc.Brownian.Ito.sum_integral_sq_norm_vectorItoIncrement_le` — the second moments of
  the increments sum to `O(1)`.
* `LevyStochCalc.Brownian.Ito.integral_abs_vectorTaylorRemainder_le_affine` — the `L¹` bound under
  an affine oscillation bound on the second derivative.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section RemainderMeasurable

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The second-order Taylor remainder along a measurable sequence of a function with continuous
first and second derivatives is measurable. -/
theorem measurable_taylorRemainderNormed {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} (hfc : Continuous f) (hf'c : Continuous f')
    (hf''c : Continuous f'') {x : ℕ → Ω → E} (hx : ∀ i, Measurable (x i)) (m : ℕ) :
    Measurable fun ω => taylorRemainderNormed f f' f'' (fun i => x i ω) m := by
  have hfirst : ∀ i : ℕ, Measurable fun ω => f' (x i ω) (x (i + 1) ω - x i ω) := by
    intro i
    have hcont : Continuous fun p : E × E => f' p.1 (p.2 - p.1) :=
      (hf'c.comp continuous_fst).clm_apply (continuous_snd.sub continuous_fst)
    exact hcont.measurable.comp ((hx i).prodMk (hx (i + 1)))
  have hsecond : ∀ i : ℕ,
      Measurable fun ω => f'' (x i ω) (x (i + 1) ω - x i ω) (x (i + 1) ω - x i ω) := by
    intro i
    have hcont : Continuous fun p : E × E => f'' p.1 (p.2 - p.1) (p.2 - p.1) :=
      ((hf''c.comp continuous_fst).clm_apply
        (continuous_snd.sub continuous_fst)).clm_apply (continuous_snd.sub continuous_fst)
    exact hcont.measurable.comp ((hx i).prodMk (hx (i + 1)))
  unfold taylorRemainderNormed
  exact ((hfc.measurable.comp (hx m)).sub (hfc.measurable.comp (hx 0))).sub
    ((Finset.measurable_sum _ fun i _ => hfirst i).add
      (Finset.measurable_sum _ fun i _ => (hsecond i).div_const 2))
end RemainderMeasurable

section VectorTaylor

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

include hC0 hCH in
/-- **The second moments of a vector Itô process's increments along a uniform grid sum to
`O(1)`.** -/
theorem sum_integral_sq_norm_vectorItoIncrement_le (X₀ : Ω → Fin n → ℝ)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∑ i ∈ Finset.range m, ∫ ω,
        ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
          - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 2 ∂P
      ≤ (n : ℝ) * (2 * (B ^ 2 * (T * (T / (m : ℝ)))) + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * T))) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hTm : (m : ℝ) * (T / (m : ℝ)) = T := by field_simp
  have hterm : ∀ i ∈ Finset.range m, ∫ ω,
      ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
        - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 2 ∂P
      ≤ (n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
        + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))) := by
    intro i _
    have hle := (_root_.Prove2MeSourceProof.h_51f76ce41cba72e9e1f79ed9 W ℱ hcoord H hHm hHp hHs
      hC0 hCH X₀ bdrift hbm hB0 hB (unifGrid_nonneg hT.le m i) (unifGrid_lt_succ hT hm0 i)).2
    rwa [unifGrid_succ_sub hm0 i] at hle
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsplit : (m : ℝ) * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
        + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))))
      = (n : ℝ) * (2 * (B ^ 2 * (((m : ℝ) * (T / (m : ℝ))) * (T / (m : ℝ))))
        + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * ((m : ℝ) * (T / (m : ℝ)))))) := by ring
  rw [hsplit, hTm]
end VectorTaylor

end LevyStochCalc.Brownian.Ito


