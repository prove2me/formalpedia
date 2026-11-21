-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand_F001
-- name    : LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:32:42.918109+00:00
-- url     : https://prove2.me/theorems/54caaa52-137c-4bde-8ea4-a985fd313c22
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoAlgebraSimpleIntegrand
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoAlgebraSimpleIntegrand. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionIncrement_F001
import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineAppend_F001
import Definitions.Def_SourceProof_3d4df4df753a663d9a385c25
import Definitions.Def_SourceProof_c5a0aac77ea3887770fece7e

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Simple integrands as integrands of the `L²` Brownian Itô integral

A simple integrand is uniformly bounded in both variables, jointly measurable, square-integrable
on every time window and, when its coefficients are adapted to a filtration, progressively
measurable, so it is an admissible integrand for the `L²` Itô integral in its own right; the two
elementary integrals of adapted simple integrands obey the Itô isometry for their difference at
an intermediate time, and the `L²` Itô integral of a simple integrand agrees almost everywhere
with its elementary integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- A finite sum of step processes `1_{(aᵢ, bᵢ]}(s) · ξᵢ ω`, with `ξᵢ` measurable for
`ℱ (aᵢ)`, is progressively measurable. -/
theorem progressivelyMeasurable_sum_indicator_Ioc
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {n : ℕ} (a b : Fin n → ℝ)
    (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ (a i)) (ξ i)) :
    Probability.ProgressivelyMeasurable ℱ
      (fun ω s => ∑ i : Fin n, (Set.Ioc (a i) (b i)).indicator (fun _ => ξ i ω) s) := by
  classical
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator
        (fun s => ∑ i : Fin n, (Set.Ioc (a i) (b i)).indicator (fun _ => ξ i p.1) s) p.2)
      = fun p : Ω × ℝ => ∑ i : Fin n,
        (Set.univ ×ˢ (Set.Ioc (a i) (b i) ∩ Set.Iic t)).indicator
          (fun q : Ω × ℝ => ξ i q.1) p := by
    funext p
    by_cases hp : p.2 ≤ t
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hp)]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : p.2 ∈ Set.Ioc (a i) (b i)
      · have hmem : p ∈ Set.univ ×ˢ (Set.Ioc (a i) (b i) ∩ Set.Iic t) :=
          ⟨Set.mem_univ _, hi, Set.mem_Iic.mpr hp⟩
        rw [Set.indicator_of_mem hi, Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem]
        rintro ⟨-, hmem, -⟩
        exact hi hmem
    · rw [Set.indicator_of_notMem (by simpa using hp)]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [Set.indicator_of_notMem]
      rintro ⟨-, -, hmem⟩
      exact hp (Set.mem_Iic.mp hmem)
  letI : MeasurableSpace Ω := ℱ t
  rw [key]
  refine Finset.stronglyMeasurable_fun_sum _ fun i _ => ?_
  by_cases hi : a i < t
  · refine MeasureTheory.StronglyMeasurable.indicator ?_
      (MeasurableSet.univ.prod (measurableSet_Ioc.inter measurableSet_Iic))
    exact ((hξ i).mono (ℱ.mono hi.le)).comp_measurable measurable_fst
  · have hempty : Set.Ioc (a i) (b i) ∩ Set.Iic t = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun s hs =>
        absurd (lt_of_lt_of_le hs.1.1 hs.2) (not_lt.mpr (not_lt.mp hi))
    rw [hempty, Set.prod_empty, Set.indicator_empty]
    exact MeasureTheory.stronglyMeasurable_const
/-- A simple integrand with `ℱ`-adapted coefficients is progressively measurable. -/
theorem SimplePredictable.progressivelyMeasurable_eval {T : ℝ} (G : SimplePredictable Ω T)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i)) :
    Probability.ProgressivelyMeasurable ℱ (fun ω s => G.eval s ω) := by
  have hfun : (fun ω s => G.eval s ω)
      = fun ω s => ∑ i : Fin G.N,
        (Set.Ioc (G.partition i.castSucc) (G.partition i.succ)).indicator
          (fun _ => G.ξ i ω) s := by
    funext ω s; exact eval_eq_sum_indicator G s ω
  rw [hfun]
  exact progressivelyMeasurable_sum_indicator_Ioc ℱ _ _ _ h_adapt
/-- Difference isometry at an intermediate time for two adapted simple integrands whose
horizons need not agree. -/
theorem simpleIntegral_diff_isometry_of_adapted
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T₁ T₂ : ℝ} (G₁ : SimplePredictable Ω T₁) (G₂ : SimplePredictable Ω T₂)
    (h₁ : ∀ i : Fin G₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G₁.partition i.castSucc)) (G₁.ξ i))
    (h₂ : ∀ i : Fin G₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G₂.partition i.castSucc)) (G₂.ξ i))
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω,
        (‖simpleIntegral W G₁ t ω - simpleIntegral W G₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖G₁.eval s ω - G₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  set K : ℝ :=
    max (G₁.partition (Fin.last G₁.N)) (G₂.partition (Fin.last G₂.N)) + 1 with hK
  have hK₁ : G₁.partition (Fin.last G₁.N) < K := by
    have := le_max_left (G₁.partition (Fin.last G₁.N)) (G₂.partition (Fin.last G₂.N))
    rw [hK]; linarith
  have hK₂ : G₂.partition (Fin.last G₂.N) < K := by
    have := le_max_right (G₁.partition (Fin.last G₁.N)) (G₂.partition (Fin.last G₂.N))
    rw [hK]; linarith
  have h_eq : (G₁.appendInterval hK₁).partition (Fin.last (G₁.appendInterval hK₁).N)
      = (G₂.appendInterval hK₂).partition (Fin.last (G₂.appendInterval hK₂).N) :=
    (G₁.appendInterval_partition_last hK₁).trans (G₂.appendInterval_partition_last hK₂).symm
  have hiso := simpleIntegral_intermediate_diff_isometry W ℱ hℱ (G₁.appendInterval hK₁)
    (G₂.appendInterval hK₂) h_eq (G₁.appendInterval_adapt ℱ hK₁ h₁)
    (G₂.appendInterval_adapt ℱ hK₂ h₂) ht
  have hL : ∫⁻ ω,
        (‖simpleIntegral W G₁ t ω - simpleIntegral W G₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖simpleIntegral W (G₁.appendInterval hK₁) t ω
          - simpleIntegral W (G₂.appendInterval hK₂) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
    lintegral_congr fun ω => by
      rw [(fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_c5a0aac77ea3887770fece7e p2mMethodArg0 G₁) W hK₁ t ω,
        (fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_c5a0aac77ea3887770fece7e p2mMethodArg0 G₂) W hK₂ t ω]
  have hR : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖G₁.eval s ω - G₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖(G₁.appendInterval hK₁).eval s ω
          - (G₂.appendInterval hK₂).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
    lintegral_congr fun ω => MeasureTheory.setLIntegral_congr_fun measurableSet_Icc fun s _ => by
      rw [(_root_.Prove2MeSourceProof.h_3d4df4df753a663d9a385c25 G₁) hK₁ s ω, (_root_.Prove2MeSourceProof.h_3d4df4df753a663d9a385c25 G₂) hK₂ s ω]
  rw [hL, hR]; exact hiso
/-- A simple integrand is jointly measurable in the form the integral consumes. -/
theorem SimplePredictable.measurable_uncurry_eval {T : ℝ} (G : SimplePredictable Ω T) :
    Measurable (Function.uncurry fun ω s => G.eval s ω) := G.eval_jointly_measurable
/-- A simple integrand times a jointly measurable process is jointly measurable. -/
theorem SimplePredictable.measurable_uncurry_eval_mul {T : ℝ} (G : SimplePredictable Ω T)
    {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry fun ω s => G.eval s ω * H ω s) :=
  G.eval_jointly_measurable.mul hm
/-- A simple integrand with adapted coefficients times a progressively measurable process is
progressively measurable. -/
theorem SimplePredictable.progressivelyMeasurable_eval_mul {T : ℝ} (G : SimplePredictable Ω T)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {H : Ω → ℝ → ℝ} (hp : Probability.ProgressivelyMeasurable ℱ H) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω * H ω s :=
  (G.progressivelyMeasurable_eval ℱ h_adapt).mul hp
section EvalSimple

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (hm : Measurable (Function.uncurry fun ω s => G.eval s ω))
  (hp : Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end EvalSimple

end LevyStochCalc.Brownian.Ito


