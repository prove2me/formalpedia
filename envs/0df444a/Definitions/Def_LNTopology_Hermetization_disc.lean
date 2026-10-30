-- Prove2me | Definitions.Def_LNTopology_Hermetization_disc
-- name    : LNTopology_Hermetization_disc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:19:35.713131+00:00
-- url     : https://prove2.me/theorems/aa6f2baf-a5ca-426e-9475-c17b503755ce
-- title:
--   Discrepancy $\mathrm{disc}(G)$ of a Lightning Network
-- statement:
--   The **discrepancy** of a network is
--
--   $$\mathrm{disc}(G)=\max_{v\in V,\ d(v)\ne0}\frac{c(S(v))}{c(s(v))},$$
--
--   the discrepancy of the whole node set. It appears in the hypothesis $\bar d(G)>2g_+^{-1}(2\,\mathrm{disc}(G))$ of Theorem 3.8.
--
--   **Formalization Note** The paper's maximum is over all nodes and is defined only when every node has a channel ($s(v)$ is undefined for an isolated node); this definition takes the maximum over nodes with a channel, which is the paper's value whenever the paper's is defined. If no node has a channel the value is $0$.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Definition 3.5, p. 7 (PDF p. 8)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_discIn

namespace LNTopology.Hermetization

/-- **Discrepancy disc(G) of a Lightning Network.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Definition 3.5, p. 7: "disc(G) = max_{v∈V} c(S(v))/c(s(v))".

`disc c lam` is `discIn c lam univ`: the maximum of `c(S(v)) / c(s(v))` over the nodes `v` with
at least one channel.

**Formalization Note.** Generalization G2: the paper's maximum is over every node and is defined
only when every node has a channel (an isolated node has no `s(v)`); on such networks the two
agree. If no node has a channel the value is `0` (empty `⨆`). -/
noncomputable def disc {V : Type*} [Fintype V] (c : ℝ → ℝ) (lam : V → V → ℝ) : ℝ :=
  discIn c lam Finset.univ

end LNTopology.Hermetization


