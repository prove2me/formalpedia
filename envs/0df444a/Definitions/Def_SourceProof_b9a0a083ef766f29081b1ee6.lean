-- Prove2me | Definitions.Def_SourceProof_b9a0a083ef766f29081b1ee6
-- name    : SourceProof_b9a0a083ef766f29081b1ee6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:53:09.992853+00:00
-- url     : https://prove2.me/theorems/a55a4054-4c56-45bb-ac94-357f58b7ffa7
-- title:
--   LevyStochCalc source module: SourceProof_b9a0a083ef766f29081b1ee6
-- statement:
--   The original source theorem `LevyStochCalc.Driver.pairing_cell_multidim_joint_eq_zero` comes from the `LevyStochCalc.Driver.JointMultidim` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPMultidim_F000
import Definitions.Def_LevyStochCalc_Driver_JointGrid_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The mixed cell lemma for a multidimensional Brownian motion

A character of a vector of Brownian increments across a cell is the character of the increment
of a unit combination, scaled by the length of the weight vector, so the mixed cell lemma for a
single Brownian motion carries over to the multidimensional driver with the Poisson character
riding along unchanged.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Cell

variable (W : MultidimBrownianMotion P d) (N : PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)


theorem _root_.Prove2MeSourceProof.h_b9a0a083ef766f29081b1ee6 (hd : 0 < d)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱN : IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℂ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, ‖V ω‖ ≤ Mv) (hZV : ∫ ω, ((Z ω : ℝ) : ℂ) * V ω ∂P = 0) (lam : Fin d → ℝ) :
    ∫ ω, ((Z ω : ℝ) : ℂ) * V ω
      * (Complex.exp (Complex.I
          * ((∑ i, lam i * ((W.W i).W b ω - (W.W i).W a ω) : ℝ) : ℂ))
        * charAt N w Bfam b ω) ∂P = 0 := by
  classical
  by_cases hzero : ∀ i, lam i = 0
  · set c : Fin d → ℝ := fun i => if i = (⟨0, hd⟩ : Fin d) then 1 else 0 with hcdef
    have hc : ∑ i, c i ^ 2 = 1 := by
      simp [hcdef]
    have hcell := _root_.Prove2MeSourceProof.h_c6ee0296156065258c568141 N hℱN (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.combineBM W hc)
      (hℱB hc) hℱ0 hnull ha hab 0 hT hbT hA hAν w hBm hBsub he₀ hZ2
      (_root_.Prove2MeSourceProof.h_b23612bd7f724e39ce57d7eb W hc ℱ (hℱB hc) hℱi (LevyStochCalc.Brownian.Ito.memLp_ofReal hZ2) hperp)
      hZcomp hVa hMv0 hVb hZV
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)) hcell
    have hs : (∑ i, lam i * ((W.W i).W b ω - (W.W i).W a ω)) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hzero i, zero_mul]
    simp [hs]
  · obtain ⟨j, hj⟩ := not_forall.mp hzero
    have hsum_pos : 0 < ∑ i, lam i ^ 2 := by
      refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ j, ?_⟩
      rcases lt_trichotomy (lam j) 0 with h | h | h
      · nlinarith
      · exact absurd h hj
      · nlinarith
    have hc : ∑ i, (lam i / Real.sqrt (∑ k, lam k ^ 2)) ^ 2 = 1 := by
      simp only [div_pow]
      rw [← Finset.sum_div, Real.sq_sqrt hsum_pos.le]
      exact div_self hsum_pos.ne'
    have hexp : ∀ ω : Ω, (∑ i, lam i * ((W.W i).W b ω - (W.W i).W a ω))
        = Real.sqrt (∑ k, lam k ^ 2)
          * (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.combine W
              (fun i => lam i / Real.sqrt (∑ k, lam k ^ 2)) b ω
            - LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.combine W
              (fun i => lam i / Real.sqrt (∑ k, lam k ^ 2)) a ω) := by
      intro ω
      rw [LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.combine_sub, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    have hcell := _root_.Prove2MeSourceProof.h_c6ee0296156065258c568141 N hℱN (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.combineBM W hc)
      (hℱB hc) hℱ0 hnull ha hab (Real.sqrt (∑ k, lam k ^ 2)) hT hbT hA hAν w hBm hBsub he₀
      hZ2 (_root_.Prove2MeSourceProof.h_b23612bd7f724e39ce57d7eb W hc ℱ (hℱB hc) hℱi (LevyStochCalc.Brownian.Ito.memLp_ofReal hZ2) hperp)
      hZcomp hVa hMv0 hVb hZV
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)) hcell
    simp only [hexp ω]
    rfl
end Cell

section Grid

variable (W : MultidimBrownianMotion P d) (N : PoissonRandomMeasure P ν)

variable (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

end Grid

end LevyStochCalc.Driver


