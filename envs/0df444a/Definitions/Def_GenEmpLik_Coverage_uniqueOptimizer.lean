-- Prove2me | Definitions.Def_GenEmpLik_Coverage_uniqueOptimizer
-- name    : GenEmpLik_Coverage_uniqueOptimizer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:04:22.982709+00:00
-- url     : https://prove2.me/theorems/55275ae6-e0c6-4810-91a4-4a04f0d91764
-- title:
--   Unique population optimizer
-- statement:
--   The population problem has a **unique optimizer** when there is exactly one $x^\star\in\mathcal X$ such that
--
--   $$\mathbb E_{P_0}[\ell(x^\star;\xi)]\le\mathbb E_{P_0}[\ell(y;\xi)]\quad\text{for every }y\in\mathcal X.$$
--
--   The chosen optimizer is determined by this uniqueness assertion and is used in the influence function and its variance. It is not an independently supplied decision.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 8, Theorem 3, unique optimizer hypothesis

import Mathlib

namespace GenEmpLik.Coverage

/-- The unique population optimizer assumed in Theorem 3, p. 8. -/
def HasUniqueOptimizer {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (P : MeasureTheory.Measure Ξ) : Prop :=
  ∃! xs, xs ∈ X ∧ ∀ y ∈ X, (∫ z, ℓ xs z ∂P) ≤ (∫ z, ℓ y z ∂P)

/-- The optimizer selected from the unique optimizer assertion. -/
noncomputable def uniqueOptimizer {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (P : MeasureTheory.Measure Ξ) (h : HasUniqueOptimizer X ℓ P) :
    EuclideanSpace ℝ (Fin d) := Classical.choose h.exists

end GenEmpLik.Coverage


