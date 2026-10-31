-- Prove2me | Definitions.Def_CutSetEnum_Coll
-- name    : CutSetEnum_Coll
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:55.738197+00:00
-- url     : https://prove2.me/theorems/1e3474a3-7b66-4f9d-a19d-6230bda8b41c
-- title:
--   The collection $\mathcal C$ of sets cheaper than $U$ with a different cut-set
-- statement:
--   Let $(U,\bar U)$ be a 2-partition of $V$. The collection
--   $$
--   \mathcal C=\{Q\subseteq V:\ \bar U\subsetneq Q,\ d(Q)\le d(U),\ \delta(Q)\ne\delta(U)\}
--   $$
--   consists of the vertex sets that strictly contain $\bar U$, have cut value at most $d(U)$, and have a cut-set different from $\delta(U)$.
--
--   A transversal of $\mathcal C$ inside $U$ is the source terminal set of Theorem 2.1.
--
--   **Formalization Note** $\bar U$ is `Uᶜ`, cut-sets are compared with `cutSet` (multiset equality), and $\mathcal C$ is a `Set (Finset V)`.
-- source:
--   Beideman, Chandrasekaran & Wang, Counting and enumerating optimum cut sets for hypergraph k-partitioning problems for fixed k, arXiv:2204.09178v2, Theorem 2.1, proof, p.10 (PDF 11)

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Definitions.Def_CutSetEnum_cutSet

open HyperKCut.Structure

namespace CutSetEnum

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The collection `C` of the proof of Theorem 2.1.**
Beideman, Chandrasekaran & Wang, arXiv:2204.09178v2, Theorem 2.1, proof, p.10 (PDF 11):
"C := {Q ⊆ V : Ū ⊊ Q, d(Q) ≤ d(U), and δ(Q) ≠ δ(U)}".

`Coll H U` is the set of vertex sets `Q` that strictly contain the complement `Uᶜ`, have cut value
at most `d(U)`, and have a cut-set different from `δ(U)`.

**Formalization Note.** `Ū` is `Uᶜ`, `d` is the published cut value and `δ` is `cutSet`
(multiset equality). The collection is a `Set (Finset V)`. -/
def Coll (H : HyperKCut.Structure.Hypergraph V) (U : Finset V) : Set (Finset V) :=
  {Q | Uᶜ ⊂ Q ∧ d H Q ≤ d H U ∧ cutSet H Q ≠ cutSet H U}

end CutSetEnum


