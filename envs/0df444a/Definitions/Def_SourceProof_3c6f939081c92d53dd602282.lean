-- Prove2me | Definitions.Def_SourceProof_3c6f939081c92d53dd602282
-- name    : SourceProof_3c6f939081c92d53dd602282
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:28:12.074821+00:00
-- url     : https://prove2.me/theorems/937be80f-7523-45bb-84c7-5953ccf89166
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.martingale_integralProcess_of_coefficients

import Definitions.Def_SourceProof_29d33b95cf42be6716ddb60d
import Definitions.Def_SourceProof_4a90e1998d81dac996f193f9
import Definitions.Def_SourceProof_5caa95db89fdd596c2cde105
import Definitions.Def_SourceProof_b8a5a233a0879d7b1a262eac
import Definitions.Def_SourceProof_d33983359663d20877640616
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Martingale.Centering
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Moments.Variance

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bounded elementary integrands preserve martingales

Random endpoints need not be deterministically bounded. Conditional increments
are computed after raising each endpoint to the conditioning time. Coefficients
on empty cells are normalized only when deducing a coefficient bound from a
process bound. The initial coefficient and initial martingale value are retained.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
  {X : ℝ≥0 → Ω → ℝ}

namespace SimplePredictableRep
theorem _root_.Prove2MeSourceProof.h_3c6f939081c92d53dd602282
    (H : SimplePredictableRep F) (hX : Martingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (C : ℝ)
    (hinit : ∀ᵐ ω ∂P, ‖H.initial ω‖ ≤ C)
    (hb : ∀ i, ∀ᵐ ω ∂P, ‖H.coefficient i ω‖ ≤ C) :
    Martingale (H.integralProcess X) F P := by
  classical
  have hiStop (a : ProbabilityTheory.FiniteStoppingTime F) (T : ℝ≥0) :
      Integrable (fun ω ↦ X (min (a ω) T) ω) P :=
    integrable_condExp.congr
      ((_root_.Prove2MeSourceProof.h_29d33b95cf42be6716ddb60d hX) hF hr a T).symm
  have hmC (i : Fin H.partition.size) : Measurable (H.coefficient i) :=
    (H.measurable_coefficient i).mono (_root_.Prove2MeSourceProof.h_4a90e1998d81dac996f193f9 (H.partition.point i.castSucc)) le_rfl
  have hiJ (T : ℝ≥0) : Integrable (H.integralProcess X T) P := by
    have hi0 : Integrable (fun ω ↦ H.initial ω * X 0 ω) P :=
      (hX.integrable 0).bdd_smul C
        (H.measurable_initial.mono (F.le 0) le_rfl).aestronglyMeasurable hinit
    have hiterm (i : Fin H.partition.size) : Integrable (fun ω ↦ H.coefficient i ω *
        (X (min (H.partition.point i.succ ω) T) ω -
          X (min (H.partition.point i.castSucc ω) T) ω)) P :=
      ((hiStop (H.partition.point i.succ) T).sub
        (hiStop (H.partition.point i.castSucc) T)).bdd_smul C (hmC i).aestronglyMeasurable (hb i)
    have his : Integrable (fun ω ↦ ∑ i, H.coefficient i ω *
        (X (min (H.partition.point i.succ ω) T) ω -
          X (min (H.partition.point i.castSucc ω) T) ω)) P := by
      rw [show (fun ω ↦ ∑ i, H.coefficient i ω *
          (X (min (H.partition.point i.succ ω) T) ω -
            X (min (H.partition.point i.castSucc ω) T) ω)) =
          ∑ i : Fin H.partition.size, (fun ω ↦ H.coefficient i ω *
            (X (min (H.partition.point i.succ ω) T) ω -
              X (min (H.partition.point i.castSucc ω) T) ω)) by
        funext ω
        simp only [Finset.sum_apply]]
      exact integrable_finsetSum' _ (fun i _ ↦ hiterm i)
    convert! hi0.add his using 1
    funext ω
    exact (_root_.Prove2MeSourceProof.h_5caa95db89fdd596c2cde105 H) X T ω
  have haJ := ((_root_.Prove2MeSourceProof.h_d33983359663d20877640616 H) hX.stronglyAdapted.adapted hF hr).stronglyAdapted
  refine ⟨haJ, fun s t hst ↦ ?_⟩
  let a (i : Fin H.partition.size) :=
    (H.partition.point i.castSucc).max (ProbabilityTheory.FiniteStoppingTime.const F s)
  let b (i : Fin H.partition.size) := (H.partition.point i.succ).max (ProbabilityTheory.FiniteStoppingTime.const F s)
  let U (i : Fin H.partition.size) : Ω → ℝ := fun ω ↦ H.coefficient i ω *
    (X (min (b i ω) t) ω - X (min (a i ω) t) ω)
  have hiU (i : Fin H.partition.size) : Integrable (U i) P :=
    ((hiStop (b i) t).sub (hiStop (a i) t)).bdd_smul C (hmC i).aestronglyMeasurable (hb i)
  have hzU (i : Fin H.partition.size) : P[U i | F s] =ᵐ[P] 0 := by
    have hca : Measurable[(a i).measurableSpace] (H.coefficient i) :=
      (H.measurable_coefficient i).mono
        ((H.partition.point i.castSucc).isStoppingTime.measurableSpace_mono
          (a i).isStoppingTime (fun ω ↦ WithTop.coe_le_coe.mpr (le_max_left _ _))) le_rfl
    exact (_root_.Prove2MeSourceProof.h_b8a5a233a0879d7b1a262eac hX) hF hr (a i) (b i)
      (fun ω ↦ max_le_max_right s (H.partition.monotone_point ω (Fin.castSucc_le_succ i)))
      t hca C (hb i) (fun _ ↦ le_max_right _ _)
  have heq : H.integralProcess X t - H.integralProcess X s = fun ω ↦ ∑ i, U i ω := by
    funext ω
    change H.integralProcess X t ω - H.integralProcess X s ω = _
    rw [(_root_.Prove2MeSourceProof.h_5caa95db89fdd596c2cde105 H), (_root_.Prove2MeSourceProof.h_5caa95db89fdd596c2cde105 H), add_sub_add_left_eq_sub,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hmin (v : ℝ≥0) : X (min v t) ω - X (min v s) ω =
        X (min (max v s) t) ω - X s ω := by
      by_cases hv : v ≤ s
      · simp only [min_eq_left hv, min_eq_left (hv.trans hst), max_eq_right hv,
          min_eq_left hst, sub_self]
      · simp only [min_eq_right (le_of_not_ge hv), max_eq_left (le_of_not_ge hv)]
    change H.coefficient i ω * (X (min (H.partition.point i.succ ω) t) ω -
        X (min (H.partition.point i.castSucc ω) t) ω) -
      H.coefficient i ω * (X (min (H.partition.point i.succ ω) s) ω -
        X (min (H.partition.point i.castSucc ω) s) ω) = _
    rw [← mul_sub]
    change H.coefficient i ω * _ = H.coefficient i ω *
      (X (min (max (H.partition.point i.succ ω) s) t) ω -
        X (min (max (H.partition.point i.castSucc ω) s) t) ω)
    congr 1
    calc
      _ = (X (min (H.partition.point i.succ ω) t) ω -
          X (min (H.partition.point i.succ ω) s) ω) -
        (X (min (H.partition.point i.castSucc ω) t) ω -
          X (min (H.partition.point i.castSucc ω) s) ω) := by ring
      _ = _ := by rw [hmin, hmin]; ring
  have hz : P[H.integralProcess X t - H.integralProcess X s | F s] =ᵐ[P] 0 := by
    rw [heq]
    rw [show (fun ω ↦ ∑ i, U i ω) = ∑ i, U i by
      funext ω
      simp only [Finset.sum_apply]]
    have hsum := condExp_finsetSum (fun i (_ : i ∈ (Finset.univ : Finset (Fin H.partition.size))) ↦
      hiU i) (F s)
    filter_upwards [hsum, ae_all_iff.mpr hzU] with ω hsumω hω
    rw [hsumω]
    simp only [Finset.sum_apply, hω, Pi.zero_apply, Finset.sum_const_zero]
  have hself : P[H.integralProcess X s | F s] = H.integralProcess X s :=
    condExp_of_stronglyMeasurable (F.le s) (haJ s) (hiJ s)
  filter_upwards [condExp_sub (hiJ t) (hiJ s) (F s), hz] with ω hsub hzω
  rw [hself] at hsub
  change P[H.integralProcess X t - H.integralProcess X s | F s] ω =
    P[H.integralProcess X t | F s] ω - H.integralProcess X s ω at hsub
  exact sub_eq_zero.mp (hsub.symm.trans hzω)
end SimplePredictableRep

end ProbabilityTheory


