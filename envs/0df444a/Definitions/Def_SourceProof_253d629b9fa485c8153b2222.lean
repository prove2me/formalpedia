-- Prove2me | Definitions.Def_SourceProof_253d629b9fa485c8153b2222
-- name    : SourceProof_253d629b9fa485c8153b2222
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:57:49.677914+00:00
-- url     : https://prove2.me/theorems/a8489abf-bfaf-4db1-a20b-cac72d9aa6ba
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.stoppedValue_min_ae_eq_condExp_of_ae_finite_continuous

import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_SourceProof_4f5bf6289f5ec1ba588efedb
import Definitions.Def_SourceProof_ad82fe9256ceb51c8ea7695a
import Definitions.Def_SourceProof_e2b6e4c8b89a0b17690a85de

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Unbounded, almost-surely finite optional sampling

Bounded truncations converge eventually pointwise on the finite event. The
actual UI stopping families supply L1 convergence; conditional expectation
is an L1 contraction. Uniqueness of limits in measure gives the minimum
formula, and AE ordering gives optional sampling.

This is the AE-finite terminal case of Protter I.16. A possibly infinite
terminal stopping time needs an explicitly supplied terminal process value;
Mathlib's totalized evaluation at infinity is not that value.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]


theorem _root_.Prove2MeSourceProof.h_253d629b9fa485c8153b2222 (hX : Martingale X F P)
    (hu : UniformIntegrable X 1 P) (hp : IsStronglyProgressive F X)
    (hr : HasRightContinuousPaths X P) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    stoppedValue X (fun ω ↦ min (σ ω) (τ ω)) =ᵐ[P]
      P[stoppedValue X τ | hσ.measurableSpace] := by
  let τn : ℕ → Ω → WithTop ℝ≥0 := fun n ω ↦ min (τ ω) (n : ℝ≥0)
  let ρ : ℕ → Ω → WithTop ℝ≥0 := fun n ω ↦ min (σ ω) (τn n ω)
  have hτn (n) : IsStoppingTime F (τn n) := hτ.min_const (n : ℝ≥0)
  have hρ (n) : IsStoppingTime F (ρ n) := hσ.min (hτn n)
  have hb (n) (ω) : τn n ω ≤ (n : ℝ≥0) := min_le_right _ _
  have hV := (_root_.Prove2MeSourceProof.h_e2b6e4c8b89a0b17690a85de hX) hu hp hr hτn
    (fun n ↦ ⟨(n : ℝ≥0), hb n⟩)
  have hU := (_root_.Prove2MeSourceProof.h_e2b6e4c8b89a0b17690a85de hX) hu hp hr hρ
    (fun n ↦ ⟨(n : ℝ≥0), fun _ ↦ (min_le_right _ _).trans (hb n _)⟩)
  have hVlim := _root_.Prove2MeSourceProof.h_ad82fe9256ceb51c8ea7695a (X := X) hfinite
  have hminfinite : ∀ᵐ ω ∂P, min (σ ω) (τ ω) ≠ ⊤ :=
    hfinite.mono (fun _ h ↦ ne_top_of_le_ne_top h (min_le_right _ _))
  have hUlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ stoppedValue X (ρ n) ω) atTop
      (𝓝 (stoppedValue X (fun ω ↦ min (σ ω) (τ ω)) ω)) := by
    simpa only [ρ, τn, min_assoc] using
      (_root_.Prove2MeSourceProof.h_ad82fe9256ceb51c8ea7695a (X := X) hminfinite)
  have hi := hV.integrable_of_ae_tendsto hVlim
  have hVL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    hV.1 (hV.memLp_of_ae_tendsto hVlim) hV.2.1 hVlim
  have hbounded (n) : stoppedValue X (ρ n) =ᵐ[P]
      P[stoppedValue X (τn n) | hσ.measurableSpace] :=
    (_root_.Prove2MeSourceProof.h_4f5bf6289f5ec1ba588efedb hX) hp hr hσ (hτn n) (hb n)
  have hnorm (n) : eLpNorm
      (stoppedValue X (ρ n) - P[stoppedValue X τ | hσ.measurableSpace]) 1 P ≤
      eLpNorm (stoppedValue X (τn n) - stoppedValue X τ) 1 P := by
    calc
      _ = eLpNorm (P[stoppedValue X (τn n) - stoppedValue X τ | hσ.measurableSpace]) 1 P := by
        apply eLpNorm_congr_ae
        exact ((hbounded n).sub EventuallyEq.rfl).trans
          (condExp_sub (memLp_one_iff_integrable.mp (hV.memLp n)) hi _).symm
      _ ≤ _ := eLpNorm_condExp_le_eLpNorm _ le_rfl
  have hUL1 : Tendsto (fun n ↦ eLpNorm
      (stoppedValue X (ρ n) - P[stoppedValue X τ | hσ.measurableSpace]) 1 P) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hVL1
      (fun _ ↦ zero_le) hnorm
  exact tendstoInMeasure_ae_unique (tendstoInMeasure_of_tendsto_ae hU.1 hUlim)
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hU.1
      integrable_condExp.aestronglyMeasurable hUL1)
end MeasureTheory.Martingale


