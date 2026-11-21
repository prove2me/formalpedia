-- Prove2me | Definitions.Def_SourceProof_52bc6f9c5c34d4f858067e35
-- name    : SourceProof_52bc6f9c5c34d4f858067e35
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:22:38.402907+00:00
-- url     : https://prove2.me/theorems/5f113eba-ffb9-4597-a2b2-6db0658a3a57
-- title:
--   LevyStochCalc source module: SourceProof_52bc6f9c5c34d4f858067e35
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_stochasticIntegral_mul_eq_zero` comes from the `LevyStochCalc.Brownian.CrossOrthogonalityLimit` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionApi_F002
import Definitions.Def_SourceProof_17d129a5f040a8f2ef70238f
import Definitions.Def_SourceProof_2554b195ead815ae5442020c
import Definitions.Def_SourceProof_f13a945dd65a666877de115a

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonality of Itô integrals against distinct Brownian coordinates

Cross terms over intervals in any relative position reduce to the direct cross identity by
splitting at the later left endpoint, so elementary integrals against two distinct coordinates
`Wⁱ` and `Wʲ` of a `d`-dimensional Brownian motion have zero pairing. Continuity of the `L²`
pairing carries that vanishing to the limit along approximating simple integrands, giving the
orthogonality in `L²` of the Itô integrals against `Wⁱ` and against `Wʲ`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

namespace Multidim.MultidimBrownianMotion

section SimpleIntegrands

open LevyStochCalc.Brownian.Ito

variable {W : MultidimBrownianMotion P d}

end SimpleIntegrands

section L2Limit

open LevyStochCalc.Brownian.Ito


theorem _root_.Prove2MeSourceProof.h_52bc6f9c5c34d4f858067e35 (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
    (hHp : Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hKm : Measurable (Function.uncurry K))
    (hKp : Probability.ProgressivelyMeasurable ℱ K)
    (hKs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, stochasticIntegral (W.W i) ℱ (hcoord i) H hHm hHp hHs t ω
      * stochasticIntegral (W.W j) ℱ (hcoord j) K hKm hKp hKs t ω ∂P = 0 := by
  have hui : MemLp (LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W i) ℱ (hcoord i) H hHm hHp hHs t) 2 P :=
    (MeasureTheory.Lp.memLp _).ae_eq (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq (W.W i)
      ℱ (hcoord i) H hHm hHp hHs t).symm
  have huj : MemLp (LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hcoord j) K hKm hKp hKs t) 2 P :=
    (MeasureTheory.Lp.memLp _).ae_eq (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq (W.W j)
      ℱ (hcoord j) K hKm hKp hKs t).symm
  refine _root_.Prove2MeSourceProof.h_17d129a5f040a8f2ef70238f
    (un := fun n ω => LevyStochCalc.Brownian.Ito.simpleIntegral (W.W i) (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hHm hHp hHs n) t ω)
    (vn := fun n ω => LevyStochCalc.Brownian.Ito.simpleIntegral (W.W j) (LevyStochCalc.Brownian.Ito.masterApprox ℱ K hKm hKp hKs n) t ω)
    hui huj (fun n => _root_.Prove2MeSourceProof.h_f13a945dd65a666877de115a _ _ t) (fun n => _root_.Prove2MeSourceProof.h_f13a945dd65a666877de115a _ _ t)
    (fun n => LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_simpleIntegral_mul_eq_zero W hij hcoord _ _
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H hHm hHp hHs n)
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ K hKm hKp hKs n) t t)
    (_root_.Prove2MeSourceProof.h_2554b195ead815ae5442020c (W.W i) ℱ (hcoord i) H hHm hHp hHs ht)
    (_root_.Prove2MeSourceProof.h_2554b195ead815ae5442020c (W.W j) ℱ (hcoord j) K hKm hKp hKs ht)
end L2Limit

end Multidim.MultidimBrownianMotion

end LevyStochCalc.Brownian


