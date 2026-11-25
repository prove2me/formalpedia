-- Prove2me | Definitions.Def_SourceProof_cbee470a0aa2199fb74e9ccf
-- name    : SourceProof_cbee470a0aa2199fb74e9ccf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:09:02.972202+00:00
-- url     : https://prove2.me/theorems/5b387b89-9e0c-4056-84eb-e08eb5d7cd9e
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_ae_finite_usual

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_SourceProof_0f93b663621787fcc9aa0ad4
import Definitions.Def_SourceProof_3ff229e536baf2ccfe183e11
import Definitions.Def_SourceProof_4a9b239e53ad8f8a45b491f1
import Definitions.Def_SourceProof_dd5d93162907f5e6520ec487

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

theorem _root_.Prove2MeSourceProof.h_cbee470a0aa2199fb74e9ccf (hX : Martingale X F P)
    (hu : UniformIntegrable X 1 P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    stoppedValue X σ =ᵐ[P] P[stoppedValue X τ | hσ.measurableSpace] := by
  obtain ⟨Y, heq, hp, hreg⟩ :=
    (_root_.Prove2MeSourceProof.h_dd5d93162907f5e6520ec487 hX.stronglyAdapted) hF hr
  have hY := hX.congr hp.stronglyAdapted (_root_.Prove2MeSourceProof.h_4a9b239e53ad8f8a45b491f1 heq)
  exact ((_root_.Prove2MeSourceProof.h_0f93b663621787fcc9aa0ad4 heq) σ).trans
    (((_root_.Prove2MeSourceProof.h_3ff229e536baf2ccfe183e11 hY) (hu.ae_eq (_root_.Prove2MeSourceProof.h_4a9b239e53ad8f8a45b491f1 heq))
      hp (ae_of_all _ hreg) hσ hτ hle hfinite).trans
        (condExp_congr_ae ((_root_.Prove2MeSourceProof.h_0f93b663621787fcc9aa0ad4 heq) τ)).symm)
end MeasureTheory.Martingale


