-- Prove2me | Definitions.Def_LowErrExt_IsCoset
-- name    : LowErrExt_IsCoset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:30.21662+00:00
-- url     : https://prove2.me/theorems/18c9ff2c-3136-48d4-acd3-f3f738091518
-- title:
--   Coset $V=b+K$ of a finite abelian group
-- statement:
--   A subset $V$ of an abelian group $G$ is a **coset** if $V=b+K=\{b+u: u\in K\}$ for some $b\in G$ and some subgroup $K\le G$. Over $\mathbb F_2^n$ the cosets are exactly the affine subspaces.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Definitions 6.2–6.4, pp.37–38

import Mathlib

namespace LowErrExt

/-- **Coset.** `V ⊆ G` is a coset if `V = b + K` for some `b ∈ G` and some subgroup `K ≤ G`.
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definitions 6.2–6.4, pp.37–38 ("let V ⊆ G be a coset").

**Formalization Note.** Written as `x ∈ V ↔ x − b ∈ K`; a coset is nonempty (it contains `b`). Over
`𝔽₂ⁿ` the cosets are exactly the affine subspaces. -/
def IsCoset {G : Type*} [AddCommGroup G] (V : Set G) : Prop :=
  ∃ (b : G) (K : AddSubgroup G), ∀ x, x ∈ V ↔ x - b ∈ K

end LowErrExt


