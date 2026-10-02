-- Prove2me | Definitions.Def_Disjunctive_IntroDuality_OptimalValue
-- name    : Disjunctive_IntroDuality_OptimalValue
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:04:18.345976+00:00
-- url     : https://prove2.me/theorems/c5e727d1-9bc4-416c-a9f8-ab092f681e1c
-- title:
--   "No finite optimum": unboundedness of a linear objective on a feasible set
-- statement:
--   This definition captures, in the exact sense Theorem 1.5 needs, what it means for a linear
--   program to be feasible yet have "no finite optimum".
--
--   For a nonempty set $S$ and a real-valued function $f$ on $S$: $S$ is
--   **unbounded below on $f$** if $S \ne \emptyset$ and for every real number $M$ there is a point
--   $x \in S$ with $f(x) < M$ — i.e. the infimum of $f$ over $S$ is $-\infty$, so the minimization
--   problem $\min\{f(x): x \in S\}$ has no finite optimal value even though it is feasible.
--   Symmetrically, $S$ is **unbounded above on $f$** if for every $M$ there is $x \in S$ with
--   $f(x) > M$, so $\max\{f(x): x \in S\}$ has no finite optimal value.
--
--   These are the two senses (for the primal minimization and dual maximization directions,
--   respectively) in which Theorem 1.5's dichotomy statement "the other one either is infeasible
--   or has no finite optimum" is made precise.
--
--   **Formalization Note.** Both definitions require nonemptiness of $S$ explicitly, since
--   "no finite optimum" presupposes feasibility — an infeasible problem is a separate case in
--   Theorem 1.5's statement, not folded into unboundedness.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 13, Section 1.5, Theorem 1.5

import Mathlib

namespace Disjunctive.IntroDuality

/-- `S` is nonempty and `f` has no finite lower bound on `S`: the minimization problem
`min {f x : x ∈ S}` "has no finite optimum" in the sense of Balas §1.5, Theorem 1.5(2). -/
def UnboundedBelowOn {α : Type*} (S : Set α) (f : α → ℝ) : Prop :=
  S.Nonempty ∧ ∀ M : ℝ, ∃ x ∈ S, f x < M

/-- `S` is nonempty and `f` has no finite upper bound on `S`: the maximization problem
`max {f x : x ∈ S}` "has no finite optimum" in the sense of Balas §1.5, Theorem 1.5(2). -/
def UnboundedAboveOn {α : Type*} (S : Set α) (f : α → ℝ) : Prop :=
  S.Nonempty ∧ ∀ M : ℝ, ∃ x ∈ S, M < f x

end Disjunctive.IntroDuality


