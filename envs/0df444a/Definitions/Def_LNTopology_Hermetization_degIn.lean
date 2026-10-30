-- Prove2me | Definitions.Def_LNTopology_Hermetization_degIn
-- name    : LNTopology_Hermetization_degIn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:16:44.744185+00:00
-- url     : https://prove2.me/theorems/3d5be570-871a-41df-b7c3-51a4b4e7ef4e
-- title:
--   Degree $d(v)$ of a node inside a node set $U$
-- statement:
--   For a network with flows $\Lambda$, a node set $U$ and a node $v$, the **degree of $v$ in $U$** is the number of channels between $v$ and nodes of $U$:
--
--   $$d_U(v)=\bigl|\{w\in U:\lambda_{v,w}\neq 0\}\bigr|.$$
--
--   For $U=V$ this is the paper's degree $d(v)=|\{w\in V:\lambda_{v,w}\ne0\}|$ (Definition 3.4). For $v\in U$ it is the degree of $v$ in the sub-network induced on $U$, which is how Lemmas B.1 and B.2 use $d(i)$: their proofs treat $U$ as the whole network.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Definition 3.4, p. 7 (PDF p. 8)

import Mathlib

namespace LNTopology.Hermetization

/-- **Degree of a node inside a node set.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Definition 3.4, p. 7: "d(v) = |{w ∈ V : λv,w ≠ 0}|".

`degIn lam U v` is the number of nodes `w ∈ U` with `lam v w ≠ 0`, the number of channels
between `v` and `U`. For `U = V` it is the paper's `d(v)` (see `deg`); for `v ∈ U` it is the
degree of `v` in the sub-network induced on `U`, which is how Lemmas B.1–B.2 use `d(i)`.

**Formalization Note.** Reading R2: in Lemmas B.1 and B.2 the paper treats `U` as the whole
network, so `d(i)` there is `degIn lam U i`. -/
noncomputable def degIn {V : Type*} (lam : V → V → ℝ) (U : Finset V) (v : V) : ℕ :=
  (U.filter fun w => lam v w ≠ 0).card

end LNTopology.Hermetization


