-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Learner_Bayesian
-- name    : LeanPool_FormalLearningTheory_Learner_Bayesian
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:31:53.206851+00:00
-- url     : https://prove2.me/theorems/c2786be0-051b-47fd-80d3-72057b3b34f1
-- title:
--   Bayesian
-- statement:
--   Definitions and structural lemmas for Bayesian, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Bayesian.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
structure BayesianInference (X : Type u) (Y : Type v) [MeasurableSpace X] where
  /-- Prior distribution over hypotheses -/
  prior : Concept X Y → ℝ
  /-- Likelihood: probability of data given hypothesis -/
  likelihood : Concept X Y → X × Y → ℝ
  /-- Posterior: prior(h) × ∏ likelihood(h, dᵢ). Unnormalized; the normalization
      constant Z = Σ_h' prior(h') × ∏ likelihood(h', dᵢ) is omitted because
      computing it requires summing over all hypotheses (which may be uncountable).
      Downstream definitions that need a proper probability must normalize explicitly.
      This is the standard "unnormalized posterior" used in computational Bayesian inference. -/
  posterior (h : Concept X Y) (data : List (X × Y)) : ℝ :=
    prior h * (data.map (likelihood h)).prod
structure BayesianLearner (X : Type u) (Y : Type v) [MeasurableSpace X] where
  /-- The hypothesis space -/
  hypotheses : HypothesisSpace X Y
  /-- Bayesian inference engine -/
  inference : BayesianInference X Y
  /-- MAP learner: output the maximum a posteriori hypothesis -/
  learnMAP : {m : ℕ} → (Fin m → X × Y) → Concept X Y
  /-- Output is in hypothesis space -/
  output_in_H : ∀ {m : ℕ} (S : Fin m → X × Y), learnMAP S ∈ hypotheses
structure GibbsPosterior (X : Type u) (Y : Type v) [MeasurableSpace X] where
  /-- Base Bayesian learner -/
  base : BayesianLearner X Y
  /-- Temperature parameter (inverse) -/
  lambda : ℝ
  /-- Temperature is positive -/
  lambda_pos : 0 < lambda


