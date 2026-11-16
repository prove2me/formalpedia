-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_IsContractionSeq
-- name    : AgnosticTNS_Supplement_IsContractionSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:27:08.201936+00:00
-- url     : https://prove2.me/theorems/fef83148-2448-459e-bfcf-c28f1af32d1e
-- title:
--   Contraction sequence of a graph
-- statement:
--   A **contraction sequence** of a graph $G$ starts from $G$ and repeatedly chooses a non-loop edge of the current multigraph and identifies its endpoints, until every connected component has been contracted to a single vertex; parallel edges are retained and loops created by an identification are deleted. On vertex sets: each step merges two distinct current parts $A\neq B$ that are joined by at least one edge of $G$, and at the end every part is a union of connected components (closed under reachability in $G$), hence a single component.
--
--   **Formalization Note** The list entry $(A,B)$ at position $k$ is the $k$-th merge; the current parts before it are those reached after the first $k$ merges. Contracting one edge between $A$ and $B$ and deleting the resulting loops is the same as merging $A$ and $B$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definition 5.4, p.41

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_contrParts

namespace AgnosticTNS.Supplement

/-- **A contraction sequence of `G`**, Definition 5.4, p.41 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
starting from `G`, repeatedly choose a non-loop edge of the current multigraph and identify its
endpoints, until every connected component has been contracted to a single vertex (parallel edges
retained, loops deleted). On vertex sets: each step merges two distinct current parts `A`, `B`
joined by at least one edge of `G`, and at the end every part is closed under reachability in `G`.

**Formalization Note** `steps[k] = (A, B)` is the `k`-th merge; `contrParts (steps.take k)` is the
partition before it. Choosing an edge between `A` and `B` and contracting it is the same as merging
`A` and `B`, since the loops it creates are deleted. -/
def IsContractionSeq {n : ℕ} (G : SimpleGraph (Fin n))
    (steps : List (Finset (Fin n) × Finset (Fin n))) : Prop :=
  (∀ (k : ℕ) (hk : k < steps.length),
      steps[k].1 ∈ contrParts (steps.take k) ∧ steps[k].2 ∈ contrParts (steps.take k) ∧
      steps[k].1 ≠ steps[k].2 ∧ ∃ u ∈ steps[k].1, ∃ v ∈ steps[k].2, G.Adj u v) ∧
    ∀ S ∈ contrParts steps, ∀ u ∈ S, ∀ v, G.Reachable u v → v ∈ S

end AgnosticTNS.Supplement


