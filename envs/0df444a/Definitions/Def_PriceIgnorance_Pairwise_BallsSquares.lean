-- Prove2me | Definitions.Def_PriceIgnorance_Pairwise_BallsSquares
-- name    : PriceIgnorance_Pairwise_BallsSquares
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:12:23.15772+00:00
-- url     : https://prove2.me/theorems/86fbf8a6-2480-413f-87dc-0c9df84f1efe
-- title:
--   Balls and squares in uniformly random order: the event $G$ of Lemma C.4
-- statement:
--   There are $C$ colors. Each color has $K$ disjoint triples of balls, so ball $(c,t,a)$ is ball $a\in\{0,1,2\}$ of triple $t$ of color $c$. There are also $n$ squares. All $3CK+n$ objects arrive in **uniformly random order**: a uniformly random bijection $e$ from the objects to the arrival positions $\{0,\dots,3CK+n-1\}$.
--
--   $G$ is the event that every color has at least one complete triple arriving before any square:
--   $$G=\Big\{\forall c\ \exists t\ \forall a\ \forall q:\ e(c,t,a)<e(\square_q)\Big\},\qquad \mathrm{probG}(C,K,n)=\mathbb P[G]=\frac{\#\{e\in G\}}{\#\{e\}} .$$
--
--   In Theorem 3.19 the triples are the masked copies that reveal a hidden sample, and the squares are the values of interest. $G$ is the event that a correlation-aware algorithm has decoded everything before the first value of interest arrives.
--
--   **Formalization Note** The uniformly random order is the uniform distribution on the finite set of bijections `BSObj C K n ≃ Fin (3CK+n)`.
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 30, Lemma C.4

import Mathlib

/-!
# Balls and squares in uniformly random order (Lemma C.4)

Abdallah, Wajc, *Price of Ignorance in Pairwise-Independent Prophet Inequalities*, STOC 2027
submission (manuscript sha256 c79626fd…), p. 30, Lemma C.4.

There are `C` colors, with `K` disjoint triples of balls of each color (ball `(c, t, a)` is ball
`a ∈ {0, 1, 2}` of triple `t` of color `c`), and `n` squares. All `3CK + n` objects arrive in a
uniformly random order: a uniformly random bijection `e` from the objects to the arrival
positions `0, …, 3CK + n − 1`. `G` is the event that every color has at least one complete triple
all of whose balls arrive before every square; `probG C K n = P[G]`.
-/

namespace PriceIgnorance.Pairwise

/-- The objects: balls `(color, triple, ball)` and squares. -/
abbrev BSObj (C K n : ℕ) : Type :=
  (Fin C × Fin K × Fin 3) ⊕ Fin n

/-- An arrival order: a bijection from the objects to the arrival positions. -/
abbrev ArrivalOrder (C K n : ℕ) : Type :=
  BSObj C K n ≃ Fin (Fintype.card (BSObj C K n))

/-- The event `G`: for every color `c` some triple `t` of color `c` has all three balls arriving
before every square. -/
def EventG {C K n : ℕ} (e : ArrivalOrder C K n) : Prop :=
  ∀ c : Fin C, ∃ t : Fin K, ∀ a : Fin 3, ∀ q : Fin n, e (Sum.inl (c, t, a)) < e (Sum.inr q)

open Classical in
/-- `P[G]` under a uniformly random arrival order. -/
noncomputable def probG (C K n : ℕ) : ℝ :=
  ((Finset.univ.filter (fun e : ArrivalOrder C K n => EventG e)).card : ℝ) /
    (Fintype.card (ArrivalOrder C K n) : ℝ)

end PriceIgnorance.Pairwise


