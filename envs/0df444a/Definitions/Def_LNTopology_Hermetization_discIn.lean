-- Prove2me | Definitions.Def_LNTopology_Hermetization_discIn
-- name    : LNTopology_Hermetization_discIn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:18:59.225456+00:00
-- url     : https://prove2.me/theorems/25b9e0a6-5d68-422c-abbf-16d9ea3408a1
-- title:
--   Discrepancy $\mathrm{disc}(U)$ of a node set
-- statement:
--   For a cost function $c$ and a node set $U$, the **discrepancy of $U$** is the largest ratio between the costs of the largest and the smallest channel of a node, in the sub-network induced on $U$:
--
--   $$\mathrm{disc}(U)=\max_{v\in U,\ d_U(v)\ne 0}\frac{c(S_U(v))}{c(s_U(v))}.$$
--
--   This is Lemma B.2's $\mathrm{disc}(U)$. The maximum runs over the nodes of $U$ that have a channel into $U$, the only nodes for which $s_U(v)$, and hence the ratio, is defined; when every node of $U$ has such a channel it is the paper's maximum over all of $U$.
--
--   **Formalization Note** The maximum is a real supremum over a finite set, attained when the set is nonempty. When no node of $U$ has a channel into $U$ the supremum over the empty set returns $0$.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Definition 3.5, p. 7 (PDF p. 8)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_degIn
import Definitions.Def_LNTopology_Hermetization_sIn
import Definitions.Def_LNTopology_Hermetization_SIn__3548ff

namespace LNTopology.Hermetization

/-- **Discrepancy, inside a node set.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Definition 3.5, p. 7: "Define the discrepancy of G as disc(G) = max_{v∈V} c(S(v))/c(s(v))".

`discIn c lam U` is the maximum of `c (SIn lam U v) / c (sIn lam U v)` over the nodes `v ∈ U`
that have a channel into `U`. Lemma B.2's `disc(U)` is `discIn c lam U` (reading R2).

**Formalization Note.** The maximum runs over nodes with a channel, the only nodes for which
`s(v)` and hence the ratio are defined (readings R3, G2); when every node of `U` has a channel
into `U` this is the paper's maximum over all of `U`. The index is finite, so the `⨆` is
attained when it is nonempty; when no node of `U` has a channel into `U` the real `⨆` over the
empty index returns `0`. -/
noncomputable def discIn {V : Type*} (c : ℝ → ℝ) (lam : V → V → ℝ) (U : Finset V) : ℝ :=
  ⨆ v : {v : V // v ∈ U ∧ degIn lam U v ≠ 0}, c (SIn lam U v) / c (sIn lam U v)

end LNTopology.Hermetization


