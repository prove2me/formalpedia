-- Prove2me | Definitions.Def_ChenCheckout_Protection_Choice
-- name    : ChenCheckout_Protection_Choice
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T06:47:50.639978+00:00
-- url     : https://prove2.me/theorems/6c23999b-c489-46c7-a174-43995fcb23a0
-- title:
--   Downward-closed substitutable single-purchase choice systems
-- statement:
--   A finite product set has a nonempty downward-closed family of feasible assortments, including the empty set. For each feasible assortment A, the real probability q(A,j) is nonnegative, vanishes outside A and has sum at most one. Each customer chooses zero or one product; the residual mass means no purchase. For feasible A⊆B and j∈A, q(B,j)≤q(A,j). No regularity condition is imposed on the no-purchase probability. This standalone choice object is independent of prices, inventory and the checkout primary.
-- source:
--   Chen, Ma, Simchi-Levi and Xin (2024), Mathematics of Operations Research 49(1), 297–325, https://doi.org/10.1287/moor.2023.1357, Definition 1(1)–(2), printed p. 303 / PDF 7

import Mathlib

namespace ChenCheckout.Protection

/-- A substitutable single-purchase choice system on a downward-closed feasible
family. No regularity of the residual no-purchase probability is required. -/
structure ChoiceSystem (n : ℕ) where
  feasible : Finset (Finset (Fin n))
  empty_mem : ∅ ∈ feasible
  downward : ∀ A ∈ feasible, ∀ B, B ⊆ A → B ∈ feasible
  q : Finset (Fin n) → Fin n → ℝ
  nonneg : ∀ A ∈ feasible, ∀ j, 0 ≤ q A j
  outside : ∀ A ∈ feasible, ∀ j, j ∉ A → q A j = 0
  mass : ∀ A ∈ feasible, ∑ j ∈ A, q A j ≤ 1
  substitutes : ∀ A ∈ feasible, ∀ B ∈ feasible, A ⊆ B → ∀ j ∈ A, q B j ≤ q A j

end ChenCheckout.Protection


