-- Prove2me | Definitions.Def_SparseDisc_Supplement_bundleEdges
-- name    : SparseDisc_Supplement_bundleEdges
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:01:13.706165+00:00
-- url     : https://prove2.me/theorems/5e652db1-8565-49d6-801b-707cc548db16
-- title:
--   Bundle hyperedges
-- statement:
--   For declared supports $(U_v)$, a set $S$ of at least two functions is a **bundle hyperedge** when some item has reader set exactly $S$. Private singleton bundles are not hyperedges.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Definition 2.3, p.12

import Mathlib

namespace SparseDisc.Supplement

open Classical in
/-- The non-private hyperedges of the bundle hypergraph: a set `S` of at least two functions is an
edge exactly when some item has declared reader set exactly `S` (Zeng–Cao–Dai–Wang–Liao,
*Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission manuscript (sha256
0f09ec60…25b81), Definition 2.3, p.12). -/
noncomputable def bundleEdges {V ι : Type} [Fintype V] [DecidableEq V] [Fintype ι]
    (U : V → Finset ι) : Finset (Finset V) :=
  (Finset.univ : Finset (Finset V)).filter (fun S =>
    2 ≤ S.card ∧ ∃ j : ι, Finset.univ.filter (fun v => j ∈ U v) = S)

end SparseDisc.Supplement


