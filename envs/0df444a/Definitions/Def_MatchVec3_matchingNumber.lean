-- Prove2me | Definitions.Def_MatchVec3_matchingNumber
-- name    : MatchVec3_matchingNumber
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:40:54.658906+00:00
-- url     : https://prove2.me/theorems/c39d2618-8975-486d-a017-87d0a59038ae
-- title:
--   The matching number $\nu(F)$
-- statement:
--   For a hypergraph $F$ on the vertex set $[K]$, the **matching number** $\nu(F)$ is the largest size of a subfamily of $F$ whose members are pairwise disjoint.
--
--   **Formalization Note** The vertices are `Fin K`, and the empty subfamily is always admissible.
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), proof of Theorem 5.2, p.14

import Mathlib

namespace MatchVec3

/-- **The matching number `ν(F)`** of a hypergraph `F` on `[K]` (Aggarwal, Obremski, STOC 2027
submission (manuscript sha256 44199413…), proof of Theorem 5.2, p.14): the largest size of a
pairwise-disjoint subfamily of `F`.

**Formalization Note** The empty subfamily is always pairwise disjoint, so the maximum is over a
nonempty set. An empty edge, were one present, is disjoint from itself but counts once. -/
def matchingNumber {K : ℕ} (F : Finset (Finset (Fin K))) : ℕ :=
  (F.powerset.filter fun M => ∀ A ∈ M, ∀ B ∈ M, A ≠ B → Disjoint A B).sup Finset.card

end MatchVec3


