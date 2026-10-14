-- Prove2me | Definitions.Def_LNTopology_Hermetic_Hermetization
-- name    : LNTopology_Hermetic_Hermetization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:36.97885+00:00
-- url     : https://prove2.me/theorems/051989eb-6ca8-4aea-937b-435ca4edb8ef
-- title:
--   Hermetization of a set of nodes and hermetizable sets and networks
-- statement:
--   Let $\Lambda=(\lambda_{i,j})$ be a Lightning Network on $V$ and $U\subseteq V$. The **hermetization** of $U$ is the network on $V\cup\{v_0\}$, with a new node $v_0$, obtained by
--
--   1. deleting all channels among nodes in $U$;
--   2. adding the new node $v_0$; and
--   3. connecting every $i\in U$ to $v_0$ by a channel that summarizes its flows towards the other nodes of $U$.
--
--   Explicitly, its flows $\lambda'$ are $\lambda'_{i,j}=0$ for $i,j\in U$, $\lambda'_{i,j}=\lambda_{i,j}$ for all other pairs of old nodes, and
--
--   $$\lambda'_{i,v_0}=\sum_{j\in U}\lambda_{i,j}=-\lambda'_{v_0,i}\quad(i\in U),\qquad \lambda'_{v_0,w}=\lambda'_{w,v_0}=0\quad(w\notin U\cup\{v_0\}).$$
--
--   The set $U$ is **hermetizable** if hermetizing it reduces the cost, $c(G')<c(G)$, where $c(G)=\tfrac12\sum_{i,j}c(\lambda_{i,j})$. The network is **hermetizable** if some set of its nodes is hermetizable.
--
--   These are Definitions 3.6 and 3.7; Theorem 3.8 gives a sufficient condition for a network to be hermetizable.
--
--   **Formalization Note** The new node $v_0$ is `none : Option V` and the old nodes are `some v`. Channels from $U$ to nodes outside $U$ are kept unchanged, so every old node keeps its net flow. The comparison is strict and between the full networks, as in Definition 3.7. The paper remarks that an existing node could serve as hub; that variant is not formalized.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), pp. 7–8 (PDF pp. 8–9), Definitions 3.6 and 3.7; λ′ of the proof of Lemma B.1, p. 11

import Mathlib
import Definitions.Def_LNTopology_Hermetic_Model

namespace LNTopology.Hermetic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The hermetization of `U` (Definition 3.6) on the node set `Option V`, where `none` is the new
node `v₀`: channels among nodes of `U` are deleted, every other channel is kept, and each `i ∈ U`
is joined to `v₀` by a channel carrying `∑_{j ∈ U} λ_{i,j}`, its net flow towards `U`. -/
def hermetize (Λ : V → V → ℝ) (U : Finset V) : Option V → Option V → ℝ
  | some i, some j => if i ∈ U ∧ j ∈ U then 0 else Λ i j
  | some i, none   => if i ∈ U then ∑ j ∈ U, Λ i j else 0
  | none,   some j => if j ∈ U then -∑ i ∈ U, Λ j i else 0
  | none,   none   => 0

/-- `U` is hermetizable (Definition 3.7): hermetizing it strictly reduces the cost of the network. -/
def IsHermetizable (c : ℝ → ℝ) (Λ : V → V → ℝ) (U : Finset V) : Prop :=
  LNTopology.Local.cost c (hermetize Λ U) < LNTopology.Local.cost c Λ

/-- A network is hermetizable (Definition 3.7) if some set of its nodes is hermetizable. -/
def IsHermetizableLN (c : ℝ → ℝ) (Λ : V → V → ℝ) : Prop :=
  ∃ U : Finset V, IsHermetizable c Λ U

end LNTopology.Hermetic


