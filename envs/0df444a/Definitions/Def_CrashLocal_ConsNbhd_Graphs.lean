-- Prove2me | Definitions.Def_CrashLocal_ConsNbhd_Graphs
-- name    : CrashLocal_ConsNbhd_Graphs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:57:35.424201+00:00
-- url     : https://prove2.me/theorems/23d0d0ef-9023-4afc-83f7-971607186d96
-- title:
--   Balls, induced reachability, identifier conventions and labeled views on identifiers
-- statement:
--   Graph notions of §3.1 and the output format of Definition 3. ballIn G U v r is the set of nodes reachable from v by a walk of G of length ≤ r whose nodes all lie in U, i.e. the ball B_{G[U]}(v, r) for v ∈ U; gBall G v r is an alias of the published LocalLLL.Main.ball, namely B_G(v, r) = {u : dist_G(u, v) ≤ r}, with extended distance ∞ across components; ReachIn G U u w says u and w are in the same connected component of G[U]. StandingGraph n c_ID id: at most n nodes and distinct identifiers in {1, …, max{2, n}^{c_ID}}. MaxDegLe G Δ: every node has at most Δ neighbors. A View L is a labeled graph written on identifiers (a node set and an edge set of identifiers and an optional label per identifier); H.ballSet a r = B_H(a, r) with distances measured inside H; H.compSet R a b = B_H(a, R−1) ∪ B_H(b, R−1) is the comparison set of Definition 2; H.induce s = H[s]; LabEq is equality as labeled graphs (same nodes, same edges, same labels at every node). Represents id lab H K: the view H is the labeled subgraph K of G written through the identifiers, its nodes the identifiers of K's nodes, its edges the images of K's edges, each node labeled by its input label.
-- source:
--   Ghinea, Kuhn, Liu-Zhang, Parsaeian 2026, arXiv:2611.04898, §3.1–3.2 and Definition 2, pp. 13–14, 17

import Mathlib
import Definitions.Def_LocalLLL_Main_GraphModel

noncomputable section
open Classical

namespace CrashLocal.ConsNbhd

/-- `ballIn G U v r` is the set of nodes `u` reachable from `v` by a walk of `G` of length at most
`r` all of whose nodes lie in `U`; for `v ∈ U` this is the ball `B_{G[U]}(v, r)` of the induced
subgraph `G[U]` (§3.1). It is empty when `v ∉ U`. -/
def ballIn {V : Type} (G : SimpleGraph V) (U : Set V) (v : V) (r : ℕ) : Set V :=
  {u | ∃ p : G.Walk v u, p.length ≤ r ∧ ∀ y ∈ p.support, y ∈ U}

/-- The radius-`r` ball `B_G(v, r) = {u : dist_G(u, v) ≤ r}` (§3.1), reusing the
published closed ball with extended distance (infinite across components). -/
abbrev gBall {V : Type} (G : SimpleGraph V) (v : V) (r : ℕ) : Set V :=
  LocalLLL.Main.ball G v r

/-- `u` and `w` lie in the same connected component of the induced subgraph `G[U]`
(both in `U`, joined by a walk inside `U`). -/
def ReachIn {V : Type} (G : SimpleGraph V) (U : Set V) (u w : V) : Prop :=
  ∃ p : G.Walk u w, ∀ y ∈ p.support, y ∈ U

/-- Standing assumptions of §3.1–3.2 on the graph and its identifiers: at most `n` nodes, and
distinct identifiers in `{1, …, max{2, n}^{c_ID}}`. -/
def StandingGraph {V : Type} [Fintype V] (n cID : ℕ) (id : V → ℕ) : Prop :=
  Fintype.card V ≤ n ∧ Function.Injective id ∧ ∀ v, 1 ≤ id v ∧ id v ≤ (max 2 n) ^ cID

/-- Maximum degree at most `Δ`. -/
def MaxDegLe {V : Type} (G : SimpleGraph V) (Δ : ℕ) : Prop :=
  ∀ v, (G.neighborSet v).ncard ≤ Δ

/-- A labeled graph written on identifiers, as a node can output it: a node set, an edge set and
the input label carried by each node (`none` = no label recorded). -/
structure View (L : Type) where
  nodes : Set ℕ
  edges : Set (Sym2 ℕ)
  label : ℕ → Option L

namespace View

variable {L : Type}

/-- `H.ballSet a r = B_H(a, r)`: the nodes of `H` at distance at most `r` from `a`, distances
measured inside `H` (empty when `a` is not a node of `H`). -/
def ballSet (H : View L) (a : ℕ) : ℕ → Set ℕ
  | 0 => {b | b = a ∧ a ∈ H.nodes}
  | r + 1 => H.ballSet a r ∪ {b | b ∈ H.nodes ∧ ∃ c ∈ H.ballSet a r, s(c, b) ∈ H.edges}

/-- Comparison set of Definition 2, computed in `H` for the edge `{a, b}` and radius `R`:
`B_H(a, R − 1) ∪ B_H(b, R − 1)`. -/
def compSet (H : View L) (R a b : ℕ) : Set ℕ :=
  H.ballSet a (R - 1) ∪ H.ballSet b (R - 1)

/-- The labeled subgraph `H[s]` induced on `s`. -/
def induce (H : View L) (s : Set ℕ) : View L where
  nodes := H.nodes ∩ s
  edges := {e | e ∈ H.edges ∧ ∀ a ∈ e, a ∈ s}
  label := H.label

/-- Equality as labeled graphs (§3.1): same node set, same edge set, same labels at every node. -/
def LabEq (H₁ H₂ : View L) : Prop :=
  H₁.nodes = H₂.nodes ∧ H₁.edges = H₂.edges ∧ ∀ a ∈ H₁.nodes, H₁.label a = H₂.label a

end View

/-- The view `H` (on identifiers) is the labeled subgraph `K` of `G`, written through the
identifier map `id`: its nodes are the identifiers of `K`'s nodes, its edges the images of `K`'s
edges, and each node of `K` carries its input label. -/
def Represents {V L : Type} {G : SimpleGraph V} (id : V → ℕ) (lab : V → L) (H : View L)
    (K : G.Subgraph) : Prop :=
  H.nodes = id '' K.verts ∧ H.edges = Sym2.map id '' K.edgeSet ∧
    ∀ u ∈ K.verts, H.label (id u) = some (lab u)

end CrashLocal.ConsNbhd


