-- Prove2me | Definitions.Def_RoundedPotentials_Main_Supplement_Broadcast
-- name    : RoundedPotentials_Main_Supplement_Broadcast
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:04:14.941594+00:00
-- url     : https://prove2.me/theorems/b15861d1-b10d-4e08-9854-ae55f37c3fe0
-- title:
--   Networks, local views and one-round broadcast proof-labeling schemes (§4.2)
-- statement:
--   This file defines the one-round broadcast proof-labeling model of [KKP10], as described in §4.2.
--
--   1. A **network** on $[n]$ has a loopless arc set, natural capacities on its arcs (zero allowed), an identifier `id v` for every vertex, and terminals $s,t$. It is **valid** when the identifiers are distinct, $s\ne t$, and the communication graph is connected. The communication graph joins $u\ne v$ when there is an arc between them in either direction.
--   2. An **undirected** network is encoded as one in which every arc has its reverse, with the same capacity.
--   3. $\mathrm{MaxFlow}(s,t)=p$ is the base mission's `MaxValue` for the arc instance.
--   4. Under a labelling $\ell$, the **local view** of $v$ consists of its identifier, whether it is $s$, whether it is $t$, the claimed value $p$, its own label, and, for every neighbour $u$, the tuple
--   $$(\mathrm{id}\,u,\ c(v\to u)\text{ if that arc exists},\ c(u\to v)\text{ if that arc exists},\ \ell(u)).$$
--   The vertex does not know $n$ or anything else about the graph. A scheme is a local decision rule $D$ applied to every view. `AllAccept` means that every vertex accepts.
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 21, §4.2 (Model paragraph), Corollary 4.5

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Supplement_Graphs

namespace RoundedPotentials.Main.Supplement

open RoundedPotentials.Main

/-! # One-round broadcast proof-labeling schemes (§4.2, model of [KKP10])

A network on `[n]` has a loopless arc set, natural capacities on its arcs (zero allowed), an
identifier for every vertex and two terminals. The communication graph is the underlying
undirected graph of the arcs; messages travel both ways along every arc. A vertex knows its
identifier, its terminal role, the claimed value `p`, and for every neighbour that neighbour's
identifier and the directions and capacities of the arcs between them; it receives the label of
every neighbour (the same label is broadcast to all neighbours). It does not know `n` or
anything else about the graph. An undirected network is encoded as a network in which every arc
has its reverse with the same capacity. -/

/-- A capacitated network on `[n]` with identifiers and terminals. -/
structure BNet (n : ℕ) where
  arcs : Finset (Fin n × Fin n)
  loopless : ∀ e ∈ arcs, e.1 ≠ e.2
  cap : Fin n → Fin n → ℕ
  id : Fin n → ℕ
  s : Fin n
  t : Fin n

namespace BNet

variable {n : ℕ} (G : BNet n)

/-- `u` and `v` are joined by an arc in some direction. -/
def Adj (u v : Fin n) : Prop := u ≠ v ∧ ((u, v) ∈ G.arcs ∨ (v, u) ∈ G.arcs)

instance (u v : Fin n) : Decidable (G.Adj u v) := by unfold Adj; infer_instance

/-- The communication graph: `u ~ v` iff `u ≠ v` and there is an arc between them in some
direction (adjacency is `Adj`, by `SimpleGraph.fromRel_adj`). -/
def commGraph : SimpleGraph (Fin n) := SimpleGraph.fromRel (fun u v => (u, v) ∈ G.arcs)

/-- The standing assumptions of the model: distinct identifiers, distinct terminals, a
connected communication graph. -/
def Valid : Prop := Function.Injective G.id ∧ G.s ≠ G.t ∧ G.commGraph.Connected

/-- An undirected network: every arc has its reverse, with the same capacity. -/
def Undirected : Prop := ∀ u v, (u, v) ∈ G.arcs → (v, u) ∈ G.arcs ∧ G.cap u v = G.cap v u

/-- `MaxFlow(s, t) = p` for the network (the base mission's `MaxValue`). -/
def MaxFlowIs (p : ℕ) : Prop :=
  MaxValue (arcInstance G.arcs G.loopless G.cap) G.s G.t (p : ℝ)

/-- The capacity of the arc `(u, v)`, or `none` if there is no such arc. -/
def arcCap (u v : Fin n) : Option ℕ := if (u, v) ∈ G.arcs then some (G.cap u v) else none

end BNet

/-- What a vertex sees in one round: its identifier, whether it is `s`, whether it is `t`, the
claimed value, its own label, and for every neighbour `u` the tuple
`(id u, capacity of the arc to u, capacity of the arc from u, label of u)`. -/
structure LocalView where
  id : ℕ
  isSource : Bool
  isSink : Bool
  claim : ℕ
  label : List Bool
  nbrs : Finset (ℕ × Option ℕ × Option ℕ × List Bool)

/-- The view of vertex `v` under the labelling `ℓ` and the claim `p`. -/
def view {n : ℕ} (G : BNet n) (p : ℕ) (ℓ : Fin n → List Bool) (v : Fin n) : LocalView where
  id := G.id v
  isSource := decide (v = G.s)
  isSink := decide (v = G.t)
  claim := p
  label := ℓ v
  nbrs := (Finset.univ.filter (fun u => G.Adj v u)).image
    (fun u => (G.id u, G.arcCap v u, G.arcCap u v, ℓ u))

/-- Every vertex accepts under the local decision rule `D`. -/
def AllAccept {n : ℕ} (D : LocalView → Bool) (G : BNet n) (p : ℕ) (ℓ : Fin n → List Bool) :
    Prop :=
  ∀ v, D (view G p ℓ v) = true

end RoundedPotentials.Main.Supplement


