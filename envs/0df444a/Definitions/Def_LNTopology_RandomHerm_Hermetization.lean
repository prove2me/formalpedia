-- Prove2me | Definitions.Def_LNTopology_RandomHerm_Hermetization
-- name    : LNTopology_RandomHerm_Hermetization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T10:14:23.466761+00:00
-- url     : https://prove2.me/theorems/88ddd245-2f84-4ca9-92a9-e1e2571aefeb
-- title:
--   Definitions 3.6–3.7 — hermetizing a set of nodes U through a new hub v₀, and hermetizable sets and networks
-- statement:
--   Let $\Lambda=(\lambda_{i,j})$ be a Lightning Network on the finite node set $V$ and let $U\subseteq V$.
--
--   **Hermetization (Definition 3.6).** The *hermetization* of $U$ is the network on $V\cup\{v_0\}$, with a new node $v_0$, obtained by
--   1. deleting all channels among nodes of $U$;
--   2. adding the new node $v_0$;
--   3. connecting every $i\in U$ to $v_0$ by a channel that summarizes its flows towards the other nodes of $U$.
--
--   Its flows $\lambda'$ are
--   $$\lambda'_{i,v_0}=\sum_{j\in U}\lambda_{i,j}=-\lambda'_{v_0,i}\quad(i\in U),\qquad \lambda'_{i,j}=0\quad(i,j\in U),$$
--   $\lambda'_{i,j}=\lambda_{i,j}$ whenever $i\notin U$ or $j\notin U$, and $\lambda'_{i,v_0}=0$ for $i\notin U$.
--
--   **Hermetizable sets (Definition 3.7).** The set $U$ is *hermetizable* if hermetizing it strictly reduces the cost,
--   $$c(\Lambda')<c(\Lambda),$$
--   and the LN is *hermetizable* if some set of its nodes is hermetizable.
--
--   Hermetization is the cost-reducing operation of §3.2: a hub replaces the direct channels inside a group of nodes, and subadditivity of the channel cost is what can make this cheaper.
--
--   **Formalization Note** The new node $v_0$ is `none : Option V`, and an old node $i$ is `some i`; both costs are the $\tfrac12\sum_{i,j}$ form of the file `ChannelCost`. The hermetized network is anti-symmetric whenever $\Lambda$ is. For $U=\emptyset$ the hermetization adds an isolated node and never reduces the cost.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), pp. 7–8 (PDF 8–9), Definitions 3.6 and 3.7; λ′ as in the proof of Lemma B.1, p. 11 (PDF 12)

import Mathlib
import Definitions.Def_LNTopology_RandomHerm_ChannelCost

namespace LNTopology.RandomHerm

/-- The hermetization of the node set `U` in the LN `Λ` (Definition 3.6, pp. 7–8), on the node
set `Option V` with the new node `v₀ = none`: (i) every channel among nodes of `U` is deleted,
(ii) the node `v₀` is added, and (iii) every `i ∈ U` is joined to `v₀` by a channel carrying
`Σ_{j ∈ U} λ_{i,j}`, its net flow towards the other nodes of `U`. Channels between `U` and the
rest of the network, and among nodes outside `U`, are untouched. -/
def hermetize {V : Type*} [DecidableEq V] (Λ : V → V → ℝ) (U : Finset V) :
    Option V → Option V → ℝ
  | some i, some j => if i ∈ U ∧ j ∈ U then 0 else Λ i j
  | some i, none => if i ∈ U then ∑ j ∈ U, Λ i j else 0
  | none, some j => if j ∈ U then -∑ i ∈ U, Λ j i else 0
  | none, none => 0

/-- Definition 3.7 (p. 8): the node set `U` is hermetizable if hermetizing it strictly reduces
the cost of the LN. -/
def IsHermetizable {V : Type*} [Fintype V] [DecidableEq V] (c : ℝ → ℝ) (Λ : V → V → ℝ)
    (U : Finset V) : Prop :=
  LNTopology.Local.cost c (hermetize Λ U) < LNTopology.Local.cost c Λ

/-- Definition 3.7 (p. 8): the LN is hermetizable if some set of its nodes is hermetizable. -/
def IsHermetizableLN {V : Type*} [Fintype V] [DecidableEq V] (c : ℝ → ℝ)
    (Λ : V → V → ℝ) : Prop :=
  ∃ U : Finset V, IsHermetizable c Λ U

end LNTopology.RandomHerm


