-- Prove2me | Definitions.Def_LNTopology_Hermetization_SIn__3548ff
-- name    : LNTopology_Hermetization_SIn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:18:22.38082+00:00
-- url     : https://prove2.me/theorems/3548ffc5-b15b-4fc7-b555-71d9d68ad7ff
-- title:
--   Largest channel flow $S(v)$ inside a node set
-- statement:
--   For a node $v$ and a node set $U$, $S_U(v)$ is the largest absolute flow between $v$ and a node of $U$:
--
--   $$S_U(v)=\max_{j\in U}|\lambda_{v,j}|.$$
--
--   For $U=V$ it is the paper's $S(v)$; Lemmas B.1–B.2 use it for the sub-network induced on $U$.
--
--   **Formalization Note** The maximum is a real supremum over a finite set of nonnegative numbers, attained when $U$ is nonempty; for $U=\emptyset$ the supremum over the empty set returns $0$.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Definition 3.5, p. 7 (PDF p. 8)

import Mathlib

namespace LNTopology.Hermetization

/-- **Largest channel flow S(v), inside a node set.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Definition 3.5, p. 7: "S(v) be the largest, that is … S(v) = max_{j∈V} |λv,j|".

`SIn lam U v` is the maximum of `|lam v w|` over `w ∈ U`. For `U = univ` it is the paper's
`S(v)`; Lemmas B.1–B.2 use it for the induced sub-network on `U` (reading R2).

**Formalization Note.** The supremum runs over a finite set of nonnegative reals, so it is
attained when `U` is nonempty; for `U = ∅` the real `⨆` over the empty index returns `0`. -/
noncomputable def SIn {V : Type*} (lam : V → V → ℝ) (U : Finset V) (v : V) : ℝ :=
  ⨆ w : {w : V // w ∈ U}, |lam v w|

end LNTopology.Hermetization


