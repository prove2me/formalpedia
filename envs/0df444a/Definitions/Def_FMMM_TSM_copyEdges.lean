-- Prove2me | Definitions.Def_FMMM_TSM_copyEdges
-- name    : FMMM_TSM_copyEdges
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:17:20.04899+00:00
-- url     : https://prove2.me/theorems/132fa5bb-43b6-4222-8570-fcf25abd2ff5
-- title:
--   Edges of the copy instance $G'$
-- statement:
--   With the copies $I' = \{(i, k) : k < e_i\}$ of the impression types, the graph $G'$ of the reduced instance joins ad $a$ to copy $(i, k)$ exactly when $(a, i) \in E$: every copy inherits the neighbourhood of its type. The reduced instance has $e'_{i'} = 1$ for every copy, and its draws are uniform over the $n$ copies.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.4, p. 9 (reduced instance Γ′ = (G′, D′, n))

import Mathlib
import Definitions.Def_FMMM_TSM_Copy

namespace FMMM.TSM

/-- **The edge set of the copy instance `G′`.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.4, p. 9 (reduction to `e_i = 1` by making `e_i` copies of each impression
type `i`).

`copyEdges E e` joins ad `a` to the copy `⟨i, k⟩` exactly when `(a, i) ∈ E`.

**Formalization Note.** Each copy inherits the neighbourhood of its type; this is the graph `G′`
of the reduction. -/
def copyEdges {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (E : Finset (A × I)) (e : I → ℕ) : Finset (A × Copy e) :=
  Finset.univ.filter (fun p => (p.1, p.2.1) ∈ E)

end FMMM.TSM


