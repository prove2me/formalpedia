-- Prove2me | Definitions.Def_CutSetEnum_cutSet
-- name    : CutSetEnum_cutSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:12.499003+00:00
-- url     : https://prove2.me/theorems/b3885985-128e-4f21-b669-5672189b1b1c
-- title:
--   Cut-set $\delta(A)$ of a hypergraph
-- statement:
--   Let $G=(V,E)$ be a finite hypergraph with unit costs, in which parallel hyperedges are allowed. For a set $A\subseteq V$ write $\bar A=V\setminus A$. The **cut-set** of $A$ is the set of hyperedges crossing the cut $(A,\bar A)$:
--   $$
--   \delta(A)=\{e\in E:\ e\cap A\ne\emptyset\ \text{and}\ e\cap\bar A\ne\emptyset\}.
--   $$
--   Its size is the cut value $d(A)=|\delta(A)|$, and $\delta(A)=\delta(\bar A)$.
--
--   The paper's structural theorem recovers cut-sets, not cuts: two different cuts can have the same cut-set, and the theorems of this mission compare cut-sets.
--
--   **Formalization Note** The hypergraph is the published `HyperKCut.Structure.Hypergraph V`, whose hyperedges form a multiset of vertex sets, so $\delta(A)$ is the sub-multiset of crossing hyperedges and equality of cut-sets is multiset equality. Parallel copies cross together, so this is equality of the sets of crossing hyperedges. The size of `cutSet H A` is the published `d H A` by definition.
-- source:
--   Beideman, Chandrasekaran & Wang, Counting and enumerating optimum cut sets for hypergraph k-partitioning problems for fixed k, arXiv:2204.09178v2, §1.2, p.4 (PDF 5)

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model

open HyperKCut.Structure

namespace CutSetEnum

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The cut-set `δ(A)`.**
Beideman, Chandrasekaran & Wang, *Counting and enumerating optimum cut sets for hypergraph
k-partitioning problems for fixed k*, arXiv:2204.09178v2, §1.2, p.4 (PDF 5): "For a non-empty
proper subset U of vertices, we will use Ū to denote V \ U, δ(U) to denote the set of hyperedges
crossing the cut (U, Ū), and d(U) := |δ(U)| to denote the cut value of U."

`cutSet H A` is the multiset of hyperedges of `H` that meet both `A` and its complement `Aᶜ`.

**Formalization Note.** The hypergraph is the published `HyperKCut.Structure.Hypergraph V`, a
multiset of vertex sets over a finite type `V` (unit costs, parallel hyperedges allowed, as on
p.4). A cut-set is therefore a sub-multiset of `H.edges`, and two cut-sets are equal as
multisets. Parallel copies of the same vertex set either all cross a cut or none does, so this is
exactly equality of the sets of crossing hyperedges. The cardinality of `cutSet H A` is the
published cut value `d H A`. The definition makes sense for every `A`; for `A = ∅` or `A = V` it
is empty. -/
def cutSet (H : HyperKCut.Structure.Hypergraph V) (A : Finset V) : Multiset (Finset V) :=
  H.edges.filter (fun e => Meets e A ∧ Meets e Aᶜ)

end CutSetEnum


