-- Prove2me | Definitions.Def_LNTopology_Hermetization_sIn
-- name    : LNTopology_Hermetization_sIn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:18:06.554411+00:00
-- url     : https://prove2.me/theorems/145d02ea-4f66-478a-b718-56be94203070
-- title:
--   Smallest channel flow $s(v)$ inside a node set
-- statement:
--   For a node $v$ and a node set $U$, $s_U(v)$ is the smallest absolute flow on a channel between $v$ and $U$:
--
--   $$s_U(v)=\min\{|\lambda_{v,j}|: j\in U,\ \lambda_{v,j}\ne 0\}.$$
--
--   For $U=V$ it is the paper's $s(v)$ ("the smallest flow of a channel adjacent to $v$"); Lemmas B.1–B.2 use it for the sub-network induced on $U$. When $v$ has a channel into $U$ this is a positive number.
--
--   **Formalization Note** The minimum is a real infimum over a finite index set, attained when the set is nonempty. When $v$ has no channel into $U$ the paper's $s(v)$ is undefined and the infimum over the empty set returns $0$; every statement of the mission uses $s_U(v)$ only for nodes with $d_U(v)>0$.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Definition 3.5, p. 7 (PDF p. 8)

import Mathlib

namespace LNTopology.Hermetization

/-- **Smallest channel flow s(v), inside a node set.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Definition 3.5, p. 7: "let s(v) be the smallest flow of a channel adjacent to v …, that
is s(v) = min{|λv,j| : j ∈ V : λv,j ≠ 0}".

`sIn lam U v` is the minimum of `|lam v w|` over the nodes `w ∈ U` with `lam v w ≠ 0`. For
`U = univ` it is the paper's `s(v)`; Lemmas B.1–B.2 use it for the induced sub-network on `U`
(reading R2).

**Formalization Note.** The infimum runs over a finite set, so when `v` has a channel into `U`
it is attained and is the paper's minimum, a positive number. When `v` has no channel into `U`
the paper's `s(v)` is undefined and the real `⨅` over the empty index returns `0`; every
statement of the mission uses `sIn lam U v` only for nodes with `0 < degIn lam U v`. -/
noncomputable def sIn {V : Type*} (lam : V → V → ℝ) (U : Finset V) (v : V) : ℝ :=
  ⨅ w : {w : V // w ∈ U ∧ lam v w ≠ 0}, |lam v w|

end LNTopology.Hermetization


