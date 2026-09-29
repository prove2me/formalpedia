-- Prove2me | Definitions.Def_ResourceScheduling_Chain_ThreePartition
-- name    : ResourceScheduling_Chain_ThreePartition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:23:46.17945+00:00
-- url     : https://prove2.me/theorems/8899499b-178e-4fbd-83cc-713ce7cb832b
-- title:
--   3-PARTITION with $\frac14 b < a_j < \frac12 b$
-- statement:
--   The paper states the problem as follows: "3-PARTITION: Given a set $S = \{1,\dots,3t\}$ and positive integers $a_1,\dots,a_{3t}, b$ with $\sum_{j\in S} a_j = tb$, can $S$ be partitioned into $t$ disjoint 3-element subsets $S_i$ such that $\sum_{j\in S_i} a_j = b$ $(i = 1,\dots,t)$?" In the proof of Theorem 7 the authors "assume without loss of generality that $\tfrac14 b < a_j < \tfrac12 b$ for all $j\in S$".
--
--   An instance consists of $t, b \in \mathbb{N}$ and numbers $a_j$ for $j \in S$. It is **valid** when $b > 0$,
--   $$\sum_{j\in S} a_j = tb, \qquad \tfrac14 b < a_j < \tfrac12 b \quad (j \in S),$$
--   which forces every $a_j$ to be positive. A **solution** is a map $\sigma : S \to \{1,\dots,t\}$ whose fibres $S_i = \sigma^{-1}(i)$ all have exactly three elements and satisfy $\sum_{j\in S_i} a_j = b$; the fibres are then $t$ disjoint 3-element subsets partitioning $S$. The yes-instances are the valid instances that have a solution, and an instance is described by the numbers $t, b, a_1, \dots, a_{3t}$.
--
--   This is Garey and Johnson's problem SP15, "the first number problem proved to be NP-complete in the strong sense" (p. 16). It is the source problem of the reductions for Theorems 4 and 7.
--
--   **Formalization Note.** Indices are 0-based: $S$ is `Fin (3 * t)` and the parts are indexed by `Fin t`. The bounds are stated without division as $b < 4a_j$ and $2a_j < b$.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 16, proof of Theorem 4 (definition of 3-PARTITION); p. 18, proof of Theorem 7 (the bounds ¼b < a_j < ½b)

import Mathlib

/-!
# 3-PARTITION

Błażewicz, Lenstra & Rinnooy Kan (1983), p. 16 (proof of Theorem 4), with the bounds
`¼b < a_j < ½b` assumed in the proof of Theorem 7 (p. 18); this is Garey & Johnson's SP15.
Indices are 0-based: `S = Fin (3t)` and the parts are indexed by `Fin t`.
-/

namespace ResourceScheduling.Chain

/-- An instance of 3-PARTITION: `t`, `b` and numbers `a_j` for `j ∈ S = {0, …, 3t − 1}`. -/
structure ThreePartition where
  /-- the number of parts -/
  t : ℕ
  /-- the target sum of each part -/
  b : ℕ
  /-- the numbers `a_j` -/
  a : Fin (3 * t) → ℕ

namespace ThreePartition

variable (P : ThreePartition)

/-- The instance is well formed: `b` is positive, `∑_{j ∈ S} a_j = t b`, and `¼b < a_j < ½b` for
every `j` (so every `a_j` is positive). -/
def Valid : Prop :=
  0 < P.b ∧ (∑ j, P.a j = P.t * P.b) ∧ ∀ j, P.b < 4 * P.a j ∧ 2 * P.a j < P.b

/-- `σ` assigns each index to a part `S_i = σ⁻¹(i)`; it is a solution when every part has exactly
three elements and sums to `b`. -/
def IsSolution (σ : Fin (3 * P.t) → Fin P.t) : Prop :=
  ∀ i, (Finset.univ.filter fun j => σ j = i).card = 3 ∧
    ∑ j ∈ Finset.univ.filter (fun j => σ j = i), P.a j = P.b

/-- `S` can be partitioned into `t` disjoint 3-element subsets, each summing to `b`. -/
def HasSolution : Prop := ∃ σ, P.IsSolution σ

/-- Yes-instances of 3-PARTITION. -/
def IsYes : Prop := P.Valid ∧ P.HasSolution

/-- The numbers of the instance: `t`, `b`, `a_0, …, a_{3t−1}`. -/
def code : List ℕ := [P.t, P.b] ++ List.ofFn P.a

end ThreePartition

end ResourceScheduling.Chain


