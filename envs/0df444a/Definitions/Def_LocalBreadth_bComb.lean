-- Prove2me | Definitions.Def_LocalBreadth_bComb
-- name    : LocalBreadth_bComb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:14.620088+00:00
-- url     : https://prove2.me/theorems/4230f246-91be-418b-8349-746d88916464
-- title:
--   The combinatorial value b_n and the limit b
-- statement:
--   For $K\in\mathcal X$ and $n\ge1$,
--   $$b_n(K)=\inf_{\substack{T\text{ admissible}\\\text{root label }K}}\ \sup_{H\text{ a root-to-leaf path of }T}c_n(H),\qquad b(K)=\lim_{n\to\infty}b_n(K).$$
--   The scores lie in $[0,1/2]$ and $b_n$ increases with $n$. The value $b(K)$ is purely structural: it involves neither generators nor enumerations.
--
--   **Formalization Note** $b(K)$ is written as $\sup_{n\ge1}b_n(K)$; that this is the limit is a clause of the goal theorem.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), eq. (4), p.6; eq. (9), p.16

import Mathlib
import Definitions.Def_LocalBreadth_cScore
import Definitions.Def_LocalBreadth_ObsTree

namespace LocalBreadth

/-- The combinatorial value, eq. (4), p.6, and eq. (9), p.16:
`b_n^comb(K) = inf_{T admissible, root label K} sup_{H a root-to-leaf path of T} c_n(H)`.
Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…).

**Formalization Note.** For `K ∈ X` the single-vertex tree makes the infimum's index nonempty, and
every tree has a path; scores lie in `[0, 1/2]` for infinite languages and `n ≥ 1`. -/
noncomputable def bComb (X : Set (Set ℤ)) (n : ℕ) (K : Set ℤ) : ℝ :=
  ⨅ T : {T : ObsTree // T.Admissible X ∧ T.label = K}, ⨆ p : {p // p ∈ T.1.paths}, cScore n p.1

/-- `b(K) = lim_{n→∞} b_n(K)`, eq. (9), p.16.

**Formalization Note.** `b_n` increases with `n`, so the limit is this supremum over `n ≥ 1`; that it
is the limit is a clause of `theorem_1_5`, not an assumption hidden in a `limUnder`. -/
noncomputable def b (X : Set (Set ℤ)) (K : Set ℤ) : ℝ := ⨆ n : ℕ, bComb X (n + 1) K

end LocalBreadth


