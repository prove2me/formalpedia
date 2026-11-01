-- Prove2me | Definitions.Def_SubmodOrder_Subadditive
-- name    : SubmodOrder_Subadditive
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:53.44374+00:00
-- url     : https://prove2.me/theorems/c462714e-63d3-49e4-a1ba-42f8e7ce5ce1
-- title:
--   Subadditive set function
-- statement:
--   A set function $f:2^N\to\mathbb R$ is **subadditive** if
--
--   $$
--   f(A)+f(B)\ \ge\ f(A\cup B)\qquad\text{for all } A,B\subseteq N.
--   $$
--
--   Every nonnegative submodular function is subadditive, and so are the revenue functions of assortment optimization for a broad family of random-utility choice models. Monotone subadditive maximization under a cardinality constraint is the problem that Theorem 2 of the paper solves when a weak submodular order is known.
--
--   **Formalization Note** Neither monotonicity nor $f(\emptyset)=0$ is part of this predicate; both are separate hypotheses where they are used.
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, p.2, "Subadditivity: f(A) + f(B) ≥ f(A ∪ B) ∀A, B ⊆ N."

import Mathlib

namespace SubmodOrder

/-- Subadditivity of a set function (Udwani, arXiv:2107.02743v5, p.2: "Subadditivity:
f(A) + f(B) ≥ f(A ∪ B) ∀A, B ⊆ N.").

**Formalization Note.** Neither monotonicity nor `f ∅ = 0` is part of this predicate; they are
separate hypotheses wherever the paper assumes them. -/
def Subadditive {α : Type*} [DecidableEq α] (f : Finset α → ℝ) : Prop :=
  ∀ A B : Finset α, f (A ∪ B) ≤ f A + f B

end SubmodOrder


