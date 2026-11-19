-- Prove2me | Definitions.Def_BrownianMotion_Gaussian_GaussianProcess_F000
-- name    : BrownianMotion_Gaussian_GaussianProcess_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:08:24.347518+00:00
-- url     : https://prove2.me/theorems/e5129d6e-6fcd-43ca-8da8-b19639bb8b64
-- title:
--   Source declarations: BrownianMotion.Gaussian.GaussianProcess
-- statement:
--   Source-preserving Lean declaration bundle from BrownianMotion.Gaussian.GaussianProcess, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/

/-!
# Gaussian processes

-/

@[expose] public section

open MeasureTheory InnerProductSpace Finset
open scoped ENNReal NNReal RealInnerProductSpace

namespace ProbabilityTheory

variable {S T Ω E F : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : T → Ω → E}

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

variable [SecondCountableTopology E]

lemma IsGaussianProcess.indepFun'' {X : S → Ω → ℝ} {Y : T → Ω → ℝ}
    (h : IsGaussianProcess (Sum.elim X Y) P) (hX : ∀ s, Measurable (X s))
    (hY : ∀ t, Measurable (Y t)) (h' : ∀ s t, cov[X s, Y t; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P :=
  h.indepFun_of_covariance_inner (fun _ ↦ (hX _).aemeasurable) (fun _ ↦ (hY _).aemeasurable)
    fun _ _ _ _ ↦ by
    simp [mul_comm, covariance_const_mul_left, covariance_const_mul_right, h']
lemma IsGaussianProcess.iIndepFun'' {S : T → Type*}
    {X : (t : T) → (s : S t) → Ω → ℝ}
    (h : IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P)
    (hX : ∀ t s, Measurable (X t s))
    (h' : ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂), cov[X t₁ s₁, X t₂ s₂; P] = 0) :
    ProbabilityTheory.iIndepFun (fun t ω s ↦ X t s ω) P :=
  h.iIndepFun_of_covariance_inner (fun t s ↦ (hX t s).aemeasurable) fun _ _ h'' _ _ _ _ ↦ by
    simp [mul_comm, covariance_const_mul_left, covariance_const_mul_right, h' _ _ h'']
end ProbabilityTheory


