-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F002
-- name    : LevyStochCalc_Brownian_ItoAlgebraProduct_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:43:55.567384+00:00
-- url     : https://prove2.me/theorems/89b88554-146e-4888-870c-ea8950d6a9f3
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoAlgebraProduct
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoAlgebraProduct. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F002
import Definitions.Def_SourceProof_1031d9d29bf1c82a34c725ef
import Definitions.Def_SourceProof_37464a1abdaa096cc46d9376
import Definitions.Def_SourceProof_9ab1096355abba8f677466b8

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Products of simple integrands and elementary integrals against a process

Two simple integrands with a common final partition point multiply to a simple integrand carried
on their common refinement, whose evaluation is the pointwise product of the evaluations and
whose adaptedness is inherited; summing the increments of the elementary integral of one against
the coefficients of the other is the elementary integral of that product, and the difference
between an elementary integral and an `L²` Itô integral obeys the Itô isometry.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- Adaptedness passes to the product on the common refinement. -/
theorem SimplePredictable.mul_on_common_adapt
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (h_adapt₁ : ∀ i : Fin H₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₁.partition i.castSucc)) (H₁.ξ i))
    (h_adapt₂ : ∀ i : Fin H₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₂.partition i.castSucc)) (H₂.ξ i)) :
    ∀ j : Fin (H₁.mul_on_common H₂ h_eq).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((H₁.mul_on_common H₂ h_eq).partition j.castSucc))
        ((H₁.mul_on_common H₂ h_eq).ξ j) := by
  intro j
  have h₁ := (h_adapt₁ (H₁.mergedIdxMap_left H₂ h_eq j)).mono
    (ℱ.mono (H₁.mergedIdxMap_left_idx_le H₂ h_eq j))
  have h₂ := (h_adapt₂ (H₁.mergedIdxMap_right H₂ h_eq j)).mono
    (ℱ.mono (H₁.mergedIdxMap_right_idx_le H₂ h_eq j))
  exact h₁.mul h₂
/-- The elementary integral of a simple integrand against an arbitrary process. -/
noncomputable def SimplePredictable.integralAgainst {T : ℝ} (G : SimplePredictable Ω T)
    (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin G.N, G.ξ i ω *
    (M (min (G.partition i.succ) t) ω - M (min (G.partition i.castSucc) t) ω)
/-- The zero-extension leaves the elementary integral against a process unchanged. -/
theorem SimplePredictable.appendInterval_integralAgainst
    {T : ℝ} (G : SimplePredictable Ω T) {T' : ℝ}
    (hlt : G.partition (Fin.last G.N) < T') (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (G.appendInterval hlt).integralAgainst M t ω = G.integralAgainst M t ω := by
  unfold SimplePredictable.integralAgainst
  rw [G.appendInterval_partition_eq hlt, G.appendInterval_xi_eq hlt]
  change (∑ i : Fin (G.N + 1),
      (Fin.snoc (α := fun _ => Ω → ℝ) G.ξ (fun _ : Ω => (0 : ℝ))) i ω
        * (M (min ((Fin.snoc (α := fun _ => ℝ) G.partition T') i.succ) t) ω
            - M (min ((Fin.snoc (α := fun _ => ℝ) G.partition T') i.castSucc) t) ω))
    = ∑ i : Fin G.N, G.ξ i ω
        * (M (min (G.partition i.succ) t) ω - M (min (G.partition i.castSucc) t) ω)
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_last, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (Fin.castSucc i).succ = Fin.castSucc i.succ from Fin.ext rfl]
  simp only [Fin.snoc_castSucc]
section SimpleVsGeneral

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ h_adapt in
/-- **Difference isometry between an elementary integral and an `L²` integral.** -/
theorem isometry_simple_sub_stochasticIntegralBrownian {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖simpleIntegral W G T ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖G.eval s ω - H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hiso := _root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8 W ℱ hℱ (fun ω s => G.eval s ω) H
    G.measurable_uncurry_eval hm (G.progressivelyMeasurable_eval ℱ h_adapt) hp
    ((_root_.Prove2MeSourceProof.h_1031d9d29bf1c82a34c725ef G) P) hq hT
  rw [← hiso]
  refine lintegral_congr_ae ?_
  filter_upwards [_root_.Prove2MeSourceProof.h_37464a1abdaa096cc46d9376 W ℱ hℱ G h_adapt
    G.measurable_uncurry_eval (G.progressivelyMeasurable_eval ℱ h_adapt)
    ((_root_.Prove2MeSourceProof.h_1031d9d29bf1c82a34c725ef G) P) hT.le] with ω hω
  rw [hω]
end SimpleVsGeneral

end LevyStochCalc.Brownian.Ito


