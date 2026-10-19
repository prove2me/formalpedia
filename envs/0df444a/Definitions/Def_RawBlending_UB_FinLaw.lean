-- Prove2me | Definitions.Def_RawBlending_UB_FinLaw
-- name    : RawBlending_UB_FinLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:47.446686+00:00
-- url     : https://prove2.me/theorems/fc4365e9-158b-4844-b072-351efb09318f
-- title:
--   Finite-support probability law
-- statement:
--   A finite-support weight table on a set $A$ consists of a finite set $S\subseteq A$ and a real weight $p(a)$ for each $a\in A$. The separate predicate `IsProb` says that the weights on $S$ are nonnegative and normalized:
--
--   $$
--   p(a)\ge0\quad(a\in S),\qquad \sum_{a\in S}p(a)=1.
--   $$
--
--   The expectation operation is the finite sum $\mathbb E_p[f]=\sum_{a\in S}p(a)f(a)$. Thus a table satisfying `IsProb` represents the finite distributions of demand, capacity, and material availability used in the model. Weights outside $S$ do not enter these sums.
-- source:
--   Chen, Duenyas & Jasin, Optimal use and replenishment of two substitutable raw materials, SSRN working paper 2801786 (version of 2016-06-28), §3, p. 7 (PDF 7), finite-support random variables

import Mathlib

namespace RawBlending.UB

/-- A finite discrete law, represented by its support and probability weights. -/
structure FinLaw (α : Type*) where
  supp : Finset α
  weight : α → ℝ

def FinLaw.IsProb {α : Type*} (μ : FinLaw α) : Prop :=
  (∀ a ∈ μ.supp, 0 ≤ μ.weight a) ∧ (∑ a ∈ μ.supp, μ.weight a) = 1

def FinLaw.expect {α : Type*} (μ : FinLaw α) (f : α → ℝ) : ℝ :=
  ∑ a ∈ μ.supp, μ.weight a * f a

end RawBlending.UB


