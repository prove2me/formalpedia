-- Prove2me | Definitions.Def_SparseDisc_Supplement_incidenceGraph
-- name    : SparseDisc_Supplement_incidenceGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:01:45.944204+00:00
-- url     : https://prove2.me/theorems/8caa6e0a-3fed-4e1a-bcfb-fbfbfbdd5185
-- title:
--   Bundle incidence graph
-- statement:
--   The **incidence graph** is the bipartite graph between functions and non-private bundle hyperedges, with incidence given by membership. Omitting private bundles does not change acyclicity because they are leaves in the paper's full incidence graph.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Definition 2.3, p.12

import Mathlib
import Definitions.Def_SparseDisc_Supplement_bundleEdges

namespace SparseDisc.Supplement

/-- The bipartite incidence graph between functions and non-private bundle hyperedges
(Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission
manuscript (sha256 0f09ec60…25b81), Definition 2.3, p.12).

**Formalization Note** Private bundles are omitted. The source says they are leaves of the full
incidence graph and hence do not affect whether it is a forest. -/
noncomputable def incidenceGraph {V ι : Type} [Fintype V] [DecidableEq V] [Fintype ι]
    (U : V → Finset ι) : SimpleGraph (V ⊕ Finset V) :=
  SimpleGraph.fromRel (fun a b => match a, b with
    | Sum.inl v, Sum.inr S => S ∈ bundleEdges U ∧ v ∈ S
    | Sum.inr S, Sum.inl v => S ∈ bundleEdges U ∧ v ∈ S
    | _, _ => False)

end SparseDisc.Supplement


