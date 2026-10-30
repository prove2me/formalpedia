-- Prove2me | Definitions.Def_LNTopology_Hermetization_IsLN
-- name    : LNTopology_Hermetization_IsLN
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:15:52.925681+00:00
-- url     : https://prove2.me/theorems/28946f6b-6d9e-4a90-b77a-a85ced91df57
-- title:
--   Lightning Network: antisymmetric matrix of net channel flows
-- statement:
--   A **Lightning Network** (LN) on a node set $V$ is described by its matrix of net channel flows $\Lambda=(\lambda_{i,j})_{i,j\in V}$, where $\lambda_{u,v}$ is the net flow from $u$ to $v$ in the channel between them. The matrix is anti-symmetric:
--
--   $$\lambda_{u,v}=-\lambda_{v,u}\qquad\text{for all } u,v\in V,$$
--
--   and $\lambda_{u,v}=0$ means that there is no channel between $u$ and $v$ (a channel with zero net flow is treated as absent). In particular $\lambda_{v,v}=0$.
--
--   This predicate is the standing hypothesis "G is a LN" of every result of the mission.
--
--   **Formalization Note** The node set is an arbitrary type; the paper's $V=\{1,\dots,n\}$ is `Fin n`.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), §2.1, p. 4 (PDF p. 5)

import Mathlib

namespace LNTopology.Hermetization

/-- **Lightning Network (net-flow matrix).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), §2.1, unnumbered, p. 4.

A Lightning Network (LN) on the node set `V` is given by its matrix of net channel flows
`lam i j` (the net flow from `i` to `j`); the paper's "the matrix Λ = (λi,j) is by definition
anti-symmetric, as λu,v = −λv,u". A channel between `u` and `v` exists exactly when
`lam u v ≠ 0` ("If there is no channel between u and v, then λu,v = 0").

**Formalization Note.** The node set is any type `V`; the paper's `V = {1, …, n}` is
`Fin n`. Antisymmetry forces `lam v v = 0`. -/
def IsLN {V : Type*} (lam : V → V → ℝ) : Prop :=
  ∀ i j, lam i j = - lam j i

end LNTopology.Hermetization


