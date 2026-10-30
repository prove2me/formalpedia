-- Prove2me | Definitions.Def_BasisWeightLearning_Exact_VectorFrontier
-- name    : BasisWeightLearning_Exact_VectorFrontier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:19:54.755716+00:00
-- url     : https://prove2.me/theorems/41093ab1-e860-46fe-a07e-fbc54dc720e6
-- title:
--   Definition 2 — positive-normal extreme points of vectors
-- statement:
--   For a set $Z\subseteq\mathbb R^n$, its positive-normal frontier contains exactly those $z\in Z$ strictly exposed by a nonnegative normalized vector: there is $\rho\in\mathbb R^n$, $\rho_i\ge0$, $\sum_i\rho_i=1$, such that $\rho^T y<\rho^T z$ for every distinct $y\in Z$. The strict comparison excludes ties; zero coordinates of the normal are permitted. Input collections are sets, so repetitions are removed. The intended uses have finite $Z$ and positive dimension.
-- source:
--   Hao Zhang, Dynamic Learning and Decision Making via Basis Weight Vectors, Operations Research (2022), DOI 10.1287/opre.2021.2240, supplied PDF p. 10 (printed p. 10), Definition 2.

import Mathlib
open scoped BigOperators

namespace BasisWeightLearning.Exact
noncomputable def vectorFrontier {n : ℕ} (Z : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {z | z ∈ Z ∧ ∃ ρ : Fin n → ℝ,
    (∀ i, 0 ≤ ρ i) ∧ (∑ i, ρ i) = 1 ∧
    ∀ y ∈ Z, y ≠ z → (∑ i, ρ i * y i) < ∑ i, ρ i * z i}
end BasisWeightLearning.Exact


