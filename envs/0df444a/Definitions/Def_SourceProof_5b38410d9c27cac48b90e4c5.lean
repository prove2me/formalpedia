-- Prove2me | Definitions.Def_SourceProof_5b38410d9c27cac48b90e4c5
-- name    : SourceProof_5b38410d9c27cac48b90e4c5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:27:11.86335+00:00
-- url     : https://prove2.me/theorems/b0a3e7d2-81d8-4654-8e55-324b73fe5382
-- title:
--   LevyStochCalc source module: SourceProof_5b38410d9c27cac48b90e4c5
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_mul_cross_increment_eq_zero` comes from the `LevyStochCalc.Brownian.CrossVariation` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossVariation_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionApi_F002
import Definitions.Def_SourceProof_52bc6f9c5c34d4f858067e35

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cross-variation of Itô integrals against distinct coordinates

A coefficient measurable at the left endpoint of a cell, carried on that cell, is a simple
integrand, so multiplying an increment of an Itô integral by such a coefficient is again an Itô
integral. The product of increments against two distinct Brownian coordinates therefore pairs to
zero against every weight known at the left endpoint, which is to say it is conditionally
centred there.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section TwoCell

end TwoCell

section PullOut

variable (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end PullOut

section Cross

open LevyStochCalc.Brownian.Multidim

variable {d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
  (hHp : Probability.ProgressivelyMeasurable ℱ H)
  (hHs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hKm : Measurable (Function.uncurry K))
  (hKp : Probability.ProgressivelyMeasurable ℱ K)
  (hKs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)


theorem _root_.Prove2MeSourceProof.h_5b38410d9c27cac48b90e4c5 {i j : Fin d} (hij : i ≠ j) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) {Z : Ω → ℝ} (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M)
    (hZa : StronglyMeasurable[ℱ a] Z) :
    ∫ ω, Z ω * ((stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
        * (stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs b ω
          - stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a ω)) ∂P = 0 := by
  have ht : (0 : ℝ) ≤ b := le_trans ha hab.le
  have hone : ∀ _ω : Ω, |(1 : ℝ)| ≤ 1 := fun _ => le_of_eq abs_one
  obtain ⟨G, hGm, hGp, hGs, h1⟩ := LevyStochCalc.Brownian.Ito.exists_pullout_mul_sub_stochasticIntegralBrownian
    (W.W i) (hcoord i) H hHm hHp hHs ha hab hZm hZb hZa (le_refl b)
  obtain ⟨G', hGm', hGp', hGs', h2⟩ := LevyStochCalc.Brownian.Ito.exists_pullout_mul_sub_stochasticIntegralBrownian
    (W.W j) (hcoord j) K hKm hKp hKs ha hab (Z := fun _ => (1 : ℝ)) measurable_const hone
    stronglyMeasurable_const (le_refl b)
  have hcross := _root_.Prove2MeSourceProof.h_52bc6f9c5c34d4f858067e35 W hij hcoord
    hGm hGp hGs hGm' hGp' hGs' ht
  simp only [LevyStochCalc.Brownian.Ito.stochasticIntegral] at hcross
  refine Eq.trans ?_ hcross
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with ω e1 e2
  simp only [one_mul] at e2
  rw [← e1, ← e2]
  ring
end Cross

end LevyStochCalc.Brownian.Ito


