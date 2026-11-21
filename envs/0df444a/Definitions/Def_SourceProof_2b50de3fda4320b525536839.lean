-- Prove2me | Definitions.Def_SourceProof_2b50de3fda4320b525536839
-- name    : SourceProof_2b50de3fda4320b525536839
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:29:04.804565+00:00
-- url     : https://prove2.me/theorems/edb01dde-86b9-46db-9ac7-cf6169c876a9
-- title:
--   LevyStochCalc source module: SourceProof_2b50de3fda4320b525536839
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.condExp_mul_cross_increment_eq_zero` comes from the `LevyStochCalc.Brownian.CrossVariation` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F001
import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F002
import Definitions.Def_SourceProof_5b38410d9c27cac48b90e4c5

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


theorem _root_.Prove2MeSourceProof.h_2b50de3fda4320b525536839 {i j : Fin d} (hij : i ≠ j) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) :
    P[fun ω => (stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
        * (stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs b ω
          - stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a ω) | ℱ a]
      =ᵐ[P] 0 := by
  classical
  have hLi : ∀ u : ℝ,
      MemLp (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs u) 2 P :=
    fun u => (MeasureTheory.Lp.memLp _).ae_eq
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq (W.W i) ℱ (hcoord i) H hHm hHp hHs u).symm
  have hLj : ∀ u : ℝ,
      MemLp (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs u) 2 P :=
    fun u => (MeasureTheory.Lp.memLp _).ae_eq
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq (W.W j) ℱ (hcoord j) K hKm hKp hKs u).symm
  have hint : Integrable (fun ω =>
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
        * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a ω)) P :=
    MemLp.integrable_mul ((hLi b).sub (hLi a)) ((hLj b).sub (hLj a))
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le a) hint
    (fun s _ _ => (integrable_zero Ω ℝ P).integrableOn) (fun s hs _ => ?_)
    (aestronglyMeasurable_const (b := (0 : ℝ)))).symm
  simp only [Pi.zero_apply, MeasureTheory.integral_zero]
  have hind : StronglyMeasurable[ℱ a] (s.indicator fun _ : Ω => (1 : ℝ)) :=
    stronglyMeasurable_const.indicator hs
  have hbd : ∀ ω : Ω, |s.indicator (fun _ : Ω => (1 : ℝ)) ω| ≤ 1 := by
    intro ω
    by_cases hω : ω ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
  have hkey := _root_.Prove2MeSourceProof.h_5b38410d9c27cac48b90e4c5 W hcoord hHm hHp hHs hKm hKp hKs hij
    ha hab (Z := s.indicator fun _ => (1 : ℝ))
    ((measurable_const : Measurable fun _ : Ω => (1 : ℝ)).indicator (ℱ.le a s hs)) hbd hind
  refine (Eq.trans ?_ hkey).symm
  rw [← MeasureTheory.integral_indicator (ℱ.le a s hs)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  by_cases hω : ω ∈ s <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
end Cross

end LevyStochCalc.Brownian.Ito


