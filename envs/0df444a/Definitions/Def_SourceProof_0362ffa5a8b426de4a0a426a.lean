-- Prove2me | Definitions.Def_SourceProof_0362ffa5a8b426de4a0a426a
-- name    : SourceProof_0362ffa5a8b426de4a0a426a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:40:31.434172+00:00
-- url     : https://prove2.me/theorems/88fa55c5-687c-449a-ab4d-e1a6301fde40
-- title:
--   LevyStochCalc source module: SourceProof_0362ffa5a8b426de4a0a426a
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_abs_vectorTaylorRemainder_le_affine` comes from the `LevyStochCalc.Brownian.VectorItoTaylor` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoTaylor_F000
import Definitions.Def_SourceProof_634f76b800914bf6a7065ea9
import Definitions.Def_SourceProof_746f2da768f1cbb4ee1d5a85
import Definitions.Def_SourceProof_aea7414832604db6673f52a2

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

theorem _root_.Prove2MeSourceProof.h_0362ffa5a8b426de4a0a426a (X₀ : Ω → Fin n → ℝ)
    (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A)
    (hK0 : 0 ≤ K) (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf''c : Continuous f'') (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => taylorRemainderNormed f f' f''
        (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m) P
      ∧ ∫ ω, |taylorRemainderNormed f f' f''
          (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m| ∂P
        ≤ A * ((n : ℝ) * (2 * (B ^ 2 * (T * (T / (m : ℝ)))) + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * T))))
          + K * ((n : ℝ) ^ 2 * ((n : ℝ) * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
            + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
              * (T * Real.sqrt (T / (m : ℝ))))))))) := by
  have hX : ∀ i : ℕ,
      Measurable (LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i)) :=
    fun i => LevyStochCalc.Brownian.Ito.measurable_vectorItoProcess W ℱ hcoord H hHm hHp hHs hX₀ hbm _
  have hfd : Differentiable ℝ f := fun z => (hf z).differentiableAt
  have hf'd : Differentiable ℝ f' := fun z => (hf' z).differentiableAt
  have hR := LevyStochCalc.Brownian.Ito.measurable_taylorRemainderNormed hfd.continuous hf'd.continuous hf''c hX m
  have hptw : ∀ ω : Ω, |LevyStochCalc.taylorRemainderNormed f f' f''
      (fun i => LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m|
      ≤ A * ∑ i ∈ Finset.range m,
          ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
            - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 2
        + K * ∑ i ∈ Finset.range m,
          ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
            - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 3 :=
    fun ω => _root_.Prove2MeSourceProof.h_634f76b800914bf6a7065ea9 hA0 hK0 hf hf' hf'' _ m
  have hsq : ∀ i ∈ Finset.range m, Integrable (fun ω : Ω =>
      ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 2) P :=
    fun i _ => (_root_.Prove2MeSourceProof.h_51f76ce41cba72e9e1f79ed9 W ℱ hcoord H hHm hHp hHs hC0 hCH
      X₀ bdrift hbm hB0 hB (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i) (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i)).1
  have hcu : ∀ i ∈ Finset.range m, Integrable (fun ω : Ω =>
      ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 3) P :=
    fun i _ => _root_.Prove2MeSourceProof.h_aea7414832604db6673f52a2 W ℱ hcoord H hHm hHp hHs hC0 hCH
      X₀ bdrift hbm hB0 hB (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i) (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i)
  have hsumint : Integrable (fun ω : Ω =>
      A * ∑ i ∈ Finset.range m,
        ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
          - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 2
      + K * ∑ i ∈ Finset.range m,
        ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
          - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 3) P :=
    ((MeasureTheory.integrable_finsetSum _ hsq).const_mul A).add
      ((MeasureTheory.integrable_finsetSum _ hcu).const_mul K)
  have hRint : Integrable (fun ω : Ω => |LevyStochCalc.taylorRemainderNormed f f' f''
      (fun i => LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m|) P := by
    refine hsumint.mono hR.abs.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    exact (hptw ω).trans (le_abs_self _)
  have hRint0 : Integrable (fun ω : Ω => LevyStochCalc.taylorRemainderNormed f f' f''
      (fun i => LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m) P := by
    refine hsumint.mono hR.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hptw ω).trans (le_abs_self _)
  refine ⟨hRint0, ?_⟩
  calc ∫ ω, |LevyStochCalc.taylorRemainderNormed f f' f''
        (fun i => LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m| ∂P
      ≤ ∫ ω, (A * ∑ i ∈ Finset.range m,
            ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 2
          + K * ∑ i ∈ Finset.range m,
            ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 3) ∂P :=
        MeasureTheory.integral_mono hRint hsumint hptw
    _ = A * ∑ i ∈ Finset.range m, ∫ ω,
            ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 2 ∂P
          + K * ∑ i ∈ Finset.range m, ∫ ω,
            ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 3 ∂P := by
        rw [MeasureTheory.integral_add ((MeasureTheory.integrable_finsetSum _ hsq).const_mul A)
          ((MeasureTheory.integrable_finsetSum _ hcu).const_mul K),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_finsetSum _ hsq, MeasureTheory.integral_finsetSum _ hcu]
    _ ≤ A * ((n : ℝ) * (2 * (B ^ 2 * (T * (T / (m : ℝ)))) + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * T))))
          + K * ((n : ℝ) ^ 2 * ((n : ℝ) * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
            + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2
              * (T * Real.sqrt (T / (m : ℝ))))))))) := by
        gcongr
        · exact LevyStochCalc.Brownian.Ito.sum_integral_sq_norm_vectorItoIncrement_le W ℱ hcoord H hHm hHp hHs hC0 hCH
            X₀ bdrift hbm hB0 hB hT hm0
        · exact _root_.Prove2MeSourceProof.h_746f2da768f1cbb4ee1d5a85 W ℱ hcoord H hHm hHp hHs
            hC0 hCH X₀ bdrift hbm hB0 hB hT hm0
end VectorTaylor

end LevyStochCalc.Brownian.Ito


