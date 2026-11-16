-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_contrParts
-- name    : AgnosticTNS_Supplement_contrParts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:26:41.112253+00:00
-- url     : https://prove2.me/theorems/f0e8d8cf-5df6-4289-b7d4-b0dfc75e35b5
-- title:
--   Current parts of a contraction sequence
-- statement:
--   During a contraction sequence on a graph with vertex set $[n]$, every current vertex represents the set of original vertices merged into it. Starting from the partition of $[n]$ into singletons, a step merging the current vertices representing $A$ and $B$ replaces the parts $A$ and $B$ by $A\cup B$. This definition returns the partition reached after a given list of merges.
--
--   **Formalization Note** A contraction sequence is stored as the list of pairs $(A,B)$ of vertex sets it merges, in order.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definition 5.4 and the paragraph after it, p.41

import Mathlib

namespace AgnosticTNS.Supplement

/-- **The current vertices of a contraction sequence**, Definition 5.4, p.41 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).
Each current vertex represents the set of original vertices merged into it; starting from the
singletons, a step `(A, B)` replaces the parts `A` and `B` by `A ∪ B`. This is the partition after
the given steps.

**Formalization Note** A contraction sequence is stored as the list of the pairs of vertex sets it
merges (see `IsContractionSeq`). -/
def contrParts {n : ℕ} (steps : List (Finset (Fin n) × Finset (Fin n))) : Finset (Finset (Fin n)) :=
  steps.foldl (fun P s => insert (s.1 ∪ s.2) ((P.erase s.1).erase s.2))
    (Finset.univ.image fun v => ({v} : Finset (Fin n)))

end AgnosticTNS.Supplement


