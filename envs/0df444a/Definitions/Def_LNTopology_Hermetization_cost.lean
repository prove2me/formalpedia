-- Prove2me | Definitions.Def_LNTopology_Hermetization_cost
-- name    : LNTopology_Hermetization_cost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:16:14.694224+00:00
-- url     : https://prove2.me/theorems/c11baea7-72f9-4966-88f2-aa0e4bd245ea
-- title:
--   Cost $c(G)$ of a Lightning Network
-- statement:
--   Let $c:\mathbb R\to\mathbb R$ be the channel cost function and $\Lambda=(\lambda_{i,j})$ the flows of a network on a finite node set $V$. The **cost of the network** is the sum of the costs of its channels,
--
--   $$c(G)=\sum_{i>j}c(\lambda_{i,j})=\frac12\sum_{i,j\in V}c(\lambda_{i,j}).$$
--
--   The definition uses the second expression, the half-sum over all ordered pairs of nodes. It applies verbatim to the hermetized network, whose node set is $V$ plus one new node.
--
--   **Formalization Note** Under symmetry (SY), costless inaction (CI) and antisymmetry of $\Lambda$ the two expressions agree; the second needs no order on $V$.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), §2.2, unnumbered display, p. 5 (PDF p. 6)

import Mathlib

namespace LNTopology.Hermetization

/-- **Cost of a Lightning Network.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), §2.2, unnumbered display, p. 5:
"c(G) = Σ_{i>j} c(λi,j) = 1/2 Σ_{i,j=1}^n c(λi,j)".

`cost c lam` is `(1/2) * Σ_i Σ_j c (lam i j)`, the paper's second expression, over all ordered
pairs of nodes of the finite type `V`.

**Formalization Note.** The second expression is used because it needs no order on `V` and
applies verbatim to the hermetized network on `Option V`. Under (SY), (CI) and antisymmetry it
equals the first. -/
noncomputable def cost {V : Type*} [Fintype V] (c : ℝ → ℝ) (lam : V → V → ℝ) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, c (lam i j)

end LNTopology.Hermetization


