-- Prove2me | Definitions.Def_PolyClinch_TwoSided_Polymatroid
-- name    : PolyClinch_TwoSided_Polymatroid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:47.358255+00:00
-- url     : https://prove2.me/theorems/b34ea798-a4fb-4e72-9244-6b160017e67a
-- title:
--   pp. 3–4 — monotone submodular functions (1), the polymatroid P(f), and points of maximum coordinate sum (base polytope)
-- statement:
--   Let $S$ be a finite ground set. A **monotone submodular function** on $S$ is a set function $f:2^S\to\mathbb R_+$ with
--   $$
--   f(\emptyset)=0,\qquad f(A)\le f(B)\ (A\subseteq B\subseteq S),\qquad f(A\cup B)+f(A\cap B)\le f(A)+f(B)\ (A,B\subseteq S),
--   $$
--   which is condition (1) of Hirai and Sato (the page states the third inequality in the equivalent diminishing-returns form). Nonnegativity follows from the first two conditions.
--
--   The **polymatroid** of $f$ is
--   $$
--   P(f)=\{x\in\mathbb R^S_+ \mid x(F)\le f(F)\ (F\subseteq S)\},\qquad x(F)=\sum_{e\in F}x_e .
--   $$
--   The file also defines, for a set $Q\subseteq\mathbb R^\iota$ over a finite index set $\iota$, the points $y\in Q$ whose coordinate sum $y(\iota)$ is the largest over $Q$. For a polymatroid $Q=P(g)$ these are exactly the points of the **base polytope** $B=\{x\in P\mid x(\iota)=g(\iota)\}$, because $g(\iota)=\max_{x\in P(g)}x(\iota)$.
--
--   These are the usual polymatroid notions (the same notion as the platform definition `Disjunctive_Polymatroids_Basic`, which is stated on $\mathrm{Fin}\,n$ only); here they are needed on each seller's edge set and on the buyer set.
--
--   **Formalization Note** The functions are real valued on `Finset α`, and condition (1) is imposed only on subsets of `S`; values on other sets are irrelevant. `polymatroidOn S f` is a set of vectors on the whole ambient type that constrains only the coordinates in `S`, so membership says that the restriction $x|_S$ lies in $P(f)$.
-- source:
--   Hirai & Sato, Polyhedral Clinching Auctions for Two-sided Markets, arXiv:1708.04881v2, pp. 3–4, (1) and the definitions of P(f) and B

import Mathlib

namespace PolyClinch.TwoSided

open Finset

variable {α : Type*}

/-- Condition (1) of Hirai–Sato (arXiv:1708.04881v2, pp. 3–4) on the subsets of a finite ground set
`S`: `f ∅ = 0`, `f` is monotone on subsets of `S`, and `f` is submodular on subsets of `S`
(the page states the equivalent diminishing-returns form). Nonnegativity on subsets of `S`
follows from the first two clauses. Values of `f` on sets not contained in `S` are irrelevant. -/
def IsMonoSubmodOn [DecidableEq α] (S : Finset α) (f : Finset α → ℝ) : Prop :=
  f ∅ = 0 ∧ (∀ A B, A ⊆ B → B ⊆ S → f A ≤ f B) ∧
    (∀ A B, A ⊆ S → B ⊆ S → f (A ∪ B) + f (A ∩ B) ≤ f A + f B)

/-- The polymatroid `P(f) = {x ∈ ℝ^S_+ | x(F) ≤ f(F) (F ⊆ S)}` (p. 4), as a set of vectors on the
ambient type `α`: only the coordinates in `S` are constrained, so `x ∈ polymatroidOn S f` says
exactly that the restriction `x|_S` lies in `P(f)`. -/
def polymatroidOn (S : Finset α) (f : Finset α → ℝ) : Set (α → ℝ) :=
  {x | (∀ e ∈ S, 0 ≤ x e) ∧ ∀ F ⊆ S, ∑ e ∈ F, x e ≤ f F}

/-- A point of a set `Q ⊆ ℝ^ι` (`ι` finite) whose coordinate sum is the largest over `Q`. For a
polymatroid `Q = P(g)` this is exactly the base polytope `{x ∈ P | x(ι) = g(ι)}` of p. 4, since
`g(ι) = max_{x ∈ P(g)} x(ι)`. -/
def IsMaxSumPoint {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) (y : ι → ℝ) : Prop :=
  y ∈ Q ∧ ∀ z ∈ Q, ∑ i, z i ≤ ∑ i, y i

end PolyClinch.TwoSided


