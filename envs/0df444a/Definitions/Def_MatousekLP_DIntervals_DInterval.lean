-- Prove2me | Definitions.Def_MatousekLP_DIntervals_DInterval
-- name    : MatousekLP_DIntervals_DInterval
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T13:50:26.464215+00:00
-- url     : https://prove2.me/theorems/1e412a3d-e89b-428f-ba8d-100a2c83d166
-- title:
--   §8.6 — d-intervals, their endpoints, and pairwise intersecting families
-- statement:
--   Fix an integer $d \ge 1$. A **$d$-interval** is the union of $d$ closed intervals on the real line:
--   $$
--   J \;=\; [a_1,b_1] \cup [a_2,b_2] \cup \dots \cup [a_d,b_d], \qquad a_k \le b_k \ (k = 1,\dots,d).
--   $$
--   The component intervals may coincide or overlap, so a $d$-interval is the same thing as a union of at most $d$ closed intervals.
--
--   1. The **endpoints** of $J$ are the $2d$ numbers $a_1,\dots,a_d,b_1,\dots,b_d$ (with repetitions merged).
--   2. For a finite family $\mathcal J$ of $d$-intervals, $P$ denotes the set of all endpoints of all members of $\mathcal J$.
--   3. A finite family $\mathcal J$ is **pairwise intersecting** if $J_1 \cap J_2 \ne \emptyset$ for every $J_1, J_2 \in \mathcal J$.
--
--   These are the objects of the whole section: the capstone theorem asks for a small set of points meeting every member of a pairwise intersecting family, and the lemmas leading to it put weights on the endpoint set $P$.
--
--   **Formalization Note** A $d$-interval is stored as data: the two functions $k \mapsto a_k$, $k \mapsto b_k$ on `Fin d` (the book's $k = 1,\dots,d$ are `0, …, d-1`) together with $a_k \le b_k$; the set it denotes is `toSet`. Its endpoints are those of the given components, so they depend on the chosen representation (for $[0,2]\cup[1,3]$ they are $0,1,2,3$), exactly as in the book's proofs, which use the left endpoints of the given intervals. A family is a `Finset` of such data; the pairwise condition includes $J_1 = J_2$.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, §8.6, p. 178 (definition of a d-interval, Theorem 8.6.1 hypothesis), p. 179 (Lemma 8.6.3, set P of endpoints)

import Mathlib

namespace MatousekLP.DIntervals

/-- A `d`-interval, given by its `d` component intervals `[left k, right k]`, `k : Fin d`
(Matoušek–Gärtner, §8.6, p. 178: "the union of d closed intervals on the real line").
Every component is a genuine closed interval, `left k ≤ right k`; components may coincide or
overlap. The book's components `1, …, d` are `0, …, d-1`. -/
structure DInterval (d : ℕ) where
  /-- The left endpoint `a_k` of the `k`-th component interval. -/
  left : Fin d → ℝ
  /-- The right endpoint `b_k` of the `k`-th component interval. -/
  right : Fin d → ℝ
  /-- Each component `[a_k, b_k]` is a closed interval: `a_k ≤ b_k`. -/
  left_le_right : ∀ k, left k ≤ right k

namespace DInterval

variable {d : ℕ}

/-- The subset of `ℝ` that the `d`-interval `J` is: the union `⋃_k [a_k, b_k]` of its
components. -/
def toSet (J : DInterval d) : Set ℝ := ⋃ k, Set.Icc (J.left k) (J.right k)

/-- The endpoints of `J`: all left endpoints `a_k` and all right endpoints `b_k` of its
component intervals (at most `2d` real numbers). -/
noncomputable def endpoints (J : DInterval d) : Finset ℝ :=
  Finset.univ.image J.left ∪ Finset.univ.image J.right

end DInterval

/-- The set `P` of endpoints of the `d`-intervals of a finite family `𝒥` (Lemma 8.6.3, p. 179):
the union of the endpoint sets of all members. -/
noncomputable def endpointSet {d : ℕ} (𝒥 : Finset (DInterval d)) : Finset ℝ :=
  𝒥.biUnion DInterval.endpoints

/-- A finite family `𝒥` of `d`-intervals is pairwise intersecting if `J₁ ∩ J₂ ≠ ∅` for every
`J₁, J₂ ∈ 𝒥` (Theorem 8.6.1, p. 178); the case `J₁ = J₂` is included. -/
def PairwiseIntersecting {d : ℕ} (𝒥 : Finset (DInterval d)) : Prop :=
  ∀ J₁ ∈ 𝒥, ∀ J₂ ∈ 𝒥, (J₁.toSet ∩ J₂.toSet).Nonempty

end MatousekLP.DIntervals


