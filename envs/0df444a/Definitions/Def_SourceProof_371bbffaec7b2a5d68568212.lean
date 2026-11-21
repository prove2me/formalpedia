-- Prove2me | Definitions.Def_SourceProof_371bbffaec7b2a5d68568212
-- name    : SourceProof_371bbffaec7b2a5d68568212
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:51:38.025463+00:00
-- url     : https://prove2.me/theorems/9c3d4243-580f-4d99-b78b-b52267419088
-- title:
--   LevyStochCalc source module: SourceProof_371bbffaec7b2a5d68568212
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indicator_Ioc` comes from the `LevyStochCalc.Brownian.ItoAlgebraAssociativity` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F002
import Definitions.Def_SourceProof_29dfa31cfdf118b2f60dc2a9
import Definitions.Def_SourceProof_f7873a967b51c0099c698616

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Associativity and locality of the `L²` Brownian Itô integral

Summing the increments of the `L²` Itô integral of a process `H` against the coefficients of a
simple integrand `G` gives the `L²` Itô integral of the product `G · H`; specialising to the step
integrands `1_{(a, b]}` identifies the `L²` Itô integral of an integrand restricted to `(a, b]`
with the increment of the integral of the unrestricted integrand across `(a, b]`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section Associativity

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hmm : Measurable (Function.uncurry fun ω s => G.eval s ω * H ω s))
  (hmp : Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω * H ω s)
  (hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end Associativity


theorem _root_.Prove2MeSourceProof.h_371bbffaec7b2a5d68568212
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (him : Measurable (Function.uncurry fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s))
    (hip : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s)
    (hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s) him hip hiq t
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min b t) ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min a t) ω := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hfun : (fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω * H ω s)
        = fun ω s => (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s * H ω s := by
      funext ω s; rw [_root_.Prove2MeSourceProof.h_29dfa31cfdf118b2f60dc2a9]
    have hpt : ∀ (ω : Ω) (s : ℝ), (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω * H ω s
        = (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s * H ω s :=
      fun ω s => congrFun (congrFun hfun ω) s
    have him' : Measurable
        (Function.uncurry fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω * H ω s) := by
      rw [hfun]; exact him
    have hip' : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
        (fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω * H ω s) := by rw [hfun]; exact hip
    have hiq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT; simp_rw [hpt]; exact hiq T hT
    have hkey := _root_.Prove2MeSourceProof.h_f7873a967b51c0099c698616 W ℱ hℱ (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab)
      (LevyStochCalc.Brownian.Ito.stepIoc₀_adapt ℱ hab) H hm hp hq him' hip' hiq' ht
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun him' hip' hiq' him hip hiq t] at hkey
    exact hkey.symm.trans
      (Filter.Eventually.of_forall fun ω => LevyStochCalc.Brownian.Ito.stepIoc₀_integralAgainst hab _ t ω)
  · have hfun : (fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω * H ω s)
        = fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s := by
      funext ω s; rw [LevyStochCalc.Brownian.Ito.stepIoc_eval]
    have hpt : ∀ (ω : Ω) (s : ℝ), (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω * H ω s
        = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s :=
      fun ω s => congrFun (congrFun hfun ω) s
    have him' : Measurable
        (Function.uncurry fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω * H ω s) := by
      rw [hfun]; exact him
    have hip' : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
        (fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω * H ω s) := by rw [hfun]; exact hip
    have hiq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT; simp_rw [hpt]; exact hiq T hT
    have hkey := _root_.Prove2MeSourceProof.h_f7873a967b51c0099c698616 W ℱ hℱ (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab)
      (LevyStochCalc.Brownian.Ito.stepIoc_adapt ℱ ha' hab) H hm hp hq him' hip' hiq' ht
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun him' hip' hiq' him hip hiq t] at hkey
    exact hkey.symm.trans
      (Filter.Eventually.of_forall fun ω => LevyStochCalc.Brownian.Ito.stepIoc_integralAgainst ha' hab _ t ω)
end LevyStochCalc.Brownian.Ito


