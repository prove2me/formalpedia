-- Prove2me | Definitions.Def_PottsRapidMixing_Exploration
-- name    : PottsRapidMixing_Exploration
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:25.523602+00:00
-- url     : https://prove2.me/theorems/693d9259-d1ad-49b0-b052-25d6ab059ddb
-- title:
--   The exploration of Algorithm 1 and good tests
-- statement:
--   Fix orderings $\ell_V,\ell_E$ of the vertices and edges of $G$. Algorithm 1 reveals the components of an edge set $A$ one edge at a time. It keeps a remaining graph $G^{\mathrm{rem}}$, a current vertex set $U$ and a record of pairs $(e,\mathbf 1\{e\in A\})$. While $G^{\mathrm{rem}}\neq\emptyset$, it seeds $U=\{u\}$ with the vertex of least label. While the edge boundary $\partial^{\mathrm{rem}}U$ is nonempty, it tests the edge $e=yv$ of least label, with $y\in U$, $v\notin U$: on success $v$ joins $U$, on failure $e$ leaves $G^{\mathrm{rem}}$. It then removes $U$ from $G^{\mathrm{rem}}$.
--
--   For an integer $R\ge1$, the *forward region* of a test of $yv$ is
--   $$F=\{w\in V(G^{\mathrm{rem}}):\ \mathrm{dist}_{G^{\mathrm{rem}}\setminus\{yv\}}(v,w)\le R\}.$$
--   The test is *good* if $F\cap U=\emptyset$ and the ball of radius $R+1$ about $v$ in $G^{\mathrm{rem}}$ is a tree. Then $F^+$, the subgraph of $G^{\mathrm{rem}}$ of edges with an endpoint in $F$, is the *forward tree*, a tree with $V(F^+)=F\cup\partial F^+$, $\partial F^+=\{y\}\cup\{w:\mathrm{dist}_{G^{\mathrm{rem}}-yv}(v,w)=R+1\}$, in which vertices of $F$ have at most $d$ children.
--
--   The exploration is the coarse-grained revealing procedure of the shattering–escape dichotomy.
--
--   **Formalization Note** The next edge is a deterministic function of the record, so the state after a record is computed by replaying it (`rawCfg`, `cfgOf`). `settleStep` performs the moves that need no test. A complete record is the record of some $A$ (`recordOf`). Line 3 may be passed several times after one history, because a vertex isolated in $G^{\mathrm{rem}}$ is a component found with no test; `AtLine3` records the number of finished components. `IsForwardTree` lists the shape of a forward tree with no reference to a run. A verification file runs the algorithm on the one-edge graph.
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Definitions 3.1–3.2 and Algorithm 1, pp.15–16

import Mathlib

open scoped Classical

namespace PottsRapidMixing

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The fixed orderings `ℓ_V`, `ℓ_E` of Definition 3.1 (Blanca, Gheissari, Park, Zhang,
arXiv:2610.42059, p.15), as injective labels. -/
structure ExplOrder (G : SimpleGraph V) where
  labelV : V → ℕ
  labelE : G.edgeSet → ℕ
  injV : Function.Injective labelV
  injE : Function.Injective labelE

/-- The state of Algorithm 1 (arXiv:2610.42059, p.15): the vertices and edges of `G_rem`, the current
`U`, and the finished components in order. `U = ∅` stands for "no component being explored". -/
structure Cfg (G : SimpleGraph V) where
  remV : Finset V
  remE : Finset G.edgeSet
  U : Finset V
  done : List (Finset V)

/-- The state at line 1: `G_rem = G`. -/
noncomputable def Cfg.init (G : SimpleGraph V) : Cfg G := ⟨Finset.univ, Finset.univ, ∅, []⟩

/-- `G_rem` as a graph on `V`; removed vertices are isolated. -/
def Cfg.graph {G : SimpleGraph V} (c : Cfg G) : SimpleGraph V :=
  SimpleGraph.fromRel (fun a b => a ∈ c.remV ∧ b ∈ c.remV ∧ ∃ h : G.Adj a b, ⟨s(a, b), h⟩ ∈ c.remE)

/-- `∂_rem U`: the edges of `G_rem` from `U` to its complement, oriented as `y ∈ U`, `v ∉ U`. -/
noncomputable def Cfg.bdry {G : SimpleGraph V} (c : Cfg G) : Finset G.Dart :=
  Finset.univ.filter (fun d => d.fst ∈ c.U ∧ d.snd ∉ c.U ∧ c.graph.Adj d.fst d.snd)

/-- The edge of an oriented edge, in the coordinate type `G.edgeSet`. -/
def dartEdge {G : SimpleGraph V} (d : G.Dart) : G.edgeSet := ⟨d.edge, d.edge_mem⟩

/-- Line 6 of Algorithm 1: the edge of `∂_rem U` of least label, if there is one. -/
noncomputable def nextDart {G : SimpleGraph V} (ord : ExplOrder G) (c : Cfg G) : Option G.Dart :=
  if h : c.bdry.Nonempty then
    some (Classical.choose (Finset.exists_min_image c.bdry (fun d => ord.labelE (dartEdge d)) h))
  else none

/-- The moves of Algorithm 1 that involve no test. With a component open and `∂_rem U = ∅`, line 13
closes it. With no component open and `G_rem ≠ ∅`, lines 3–4 seed the vertex of least label.
Otherwise the state is a fixed point: a test is pending, or the run is over. -/
noncomputable def settleStep {G : SimpleGraph V} (ord : ExplOrder G) (c : Cfg G) : Cfg G :=
  if c.U.Nonempty then
    if c.bdry = ∅ then ⟨c.remV \ c.U, c.remE, ∅, c.done ++ [c.U]⟩ else c
  else if h : c.remV.Nonempty then
    ⟨c.remV, c.remE, {Classical.choose (Finset.exists_min_image c.remV ord.labelV h)}, c.done⟩
  else c

/-- Run `settleStep` until a test is pending or the run is over; `2|V| + 1` steps suffice. -/
noncomputable def settle {G : SimpleGraph V} (ord : ExplOrder G) (c : Cfg G) : Cfg G :=
  (settleStep ord)^[2 * Fintype.card V + 1] c

/-- Lines 7–11 of Algorithm 1: the outcome `b` of the pending test. On success `v` joins `U`, on
failure `e` leaves `G_rem`. -/
noncomputable def applyTest {G : SimpleGraph V} (ord : ExplOrder G) (c : Cfg G) (b : Bool) : Cfg G :=
  match nextDart ord c with
  | none => c
  | some d =>
    if b = true then ⟨c.remV, c.remE, insert d.snd c.U, c.done⟩
    else ⟨c.remV, c.remE.erase (dartEdge d), c.U, c.done⟩

/-- The state immediately after replaying the record `h`, before any untested move. The next edge is
a deterministic function of the record (p.16), so a record is the list of pairs
`(e, 1{e ∈ A})` of line 7. -/
noncomputable def rawCfg {G : SimpleGraph V} (ord : ExplOrder G) (h : List (G.edgeSet × Bool)) :
    Cfg G :=
  h.foldl (fun c t => applyTest ord (settle ord c) t.2) (Cfg.init G)

/-- The state after the record `h` once the untested moves are done. -/
noncomputable def cfgOf {G : SimpleGraph V} (ord : ExplOrder G) (h : List (G.edgeSet × Bool)) :
    Cfg G :=
  settle ord (rawCfg ord h)

/-- The record of Algorithm 1 on the edge set `A` (arXiv:2610.42059, p.15). Each edge is tested at
most once, so `|E|` rounds finish the run. -/
noncomputable def recordOf {G : SimpleGraph V} (ord : ExplOrder G) (A : G.edgeSet → Bool) :
    List (G.edgeSet × Bool) :=
  (fun h => match nextDart ord (cfgOf ord h) with
    | none => h
    | some d => h ++ [(dartEdge d, A (dartEdge d))])^[Fintype.card G.edgeSet] []

/-- The complete records of Algorithm 1: the sample space of the laws `P` and `Q`. -/
noncomputable def completeRecords {G : SimpleGraph V} (ord : ExplOrder G) :
    Finset (List (G.edgeSet × Bool)) :=
  Finset.univ.image (recordOf ord)

/-- Algorithm 1 is at line 3 after the history `h`, for the pass with `i` finished components
(arXiv:2610.42059, pp.21, 24). A history can be at line 3 for several passes, since a vertex isolated in
`G_rem` is a component found with no test. -/
def AtLine3 {G : SimpleGraph V} (ord : ExplOrder G) (h : List (G.edgeSet × Bool)) (i : ℕ) : Prop :=
  ∃ t : ℕ, ((settleStep ord)^[t] (rawCfg ord h)).U = ∅ ∧
    ((settleStep ord)^[t] (rawCfg ord h)).remV.Nonempty ∧
    ((settleStep ord)^[t] (rawCfg ord h)).done.length = i

/-- The `i`-th explored component of a complete record, `C_{u_i}` (arXiv:2610.42059, p.23). -/
noncomputable def compOf {G : SimpleGraph V} (ord : ExplOrder G) (R : List (G.edgeSet × Bool))
    (i : ℕ) : Finset V :=
  (cfgOf ord R).done.getD i ∅

/-- The forward region of a test of `yv`, Definition 3.2 (arXiv:2610.42059, p.16):
`F = {w : dist_{K∖{yv}}(v, w) ≤ R}`, for `K = G_rem`.

**Formalization Note.** `edist` is `⊤` between disconnected vertices, so removed vertices of `G_rem`
never enter `F`. -/
noncomputable def forwardRegion (K : SimpleGraph V) (y v : V) (R : ℕ) : Finset V :=
  Finset.univ.filter (fun w => (K.deleteEdges {s(y, v)}).edist v w ≤ (R : ℕ∞))

/-- A test of `yv` is good, Definition 3.2 (arXiv:2610.42059, p.16): `F ∩ U = ∅`, and the ball of radius
`R + 1` about `v` in `K = G_rem` is a tree. -/
def IsGoodTest (K : SimpleGraph V) (U : Finset V) (y v : V) (R : ℕ) : Prop :=
  Disjoint (forwardRegion K y v R) U ∧
    (K.induce {w | K.edist v w ≤ ((R + 1 : ℕ) : ℕ∞)}).IsTree

/-- `F⁺` as a graph on `V`: the edges of `K = G_rem` with at least one endpoint in `F`
(arXiv:2610.42059, p.16). -/
def forwardGraph (K : SimpleGraph V) (F : Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun a b => K.Adj a b ∧ (a ∈ F ∨ b ∈ F))

/-- The shape of the forward tree of a good test (arXiv:2610.42059, p.16): `T = F⁺` is a tree with the
edge `yv`; `F` is the set of vertices at distance at most `R` from `v` in `T − yv`; every other
vertex is `y` or at distance exactly `R + 1`, that is `V(F⁺) = F ∪ ∂F⁺`; every edge has an endpoint in
`F`; and vertices of `F` have at most `d = Δ − 1` children, that is degree at most `Δ`.

**Formalization Note.** Every forward tree of a good test has this shape, and vertices of `F` may have
fewer than `d` children, since edges tested closed have left `G_rem`. No run of Algorithm 1 is
mentioned, so Lemmas 3.4–3.5 are stated for all such trees. -/
structure IsForwardTree {W : Type*} [Fintype W] [DecidableEq W] (T : SimpleGraph W) (Δ R : ℕ)
    (y v : W) (F : Finset W) : Prop where
  isTree : T.IsTree
  adj : T.Adj y v
  mem_iff : ∀ w, w ∈ F ↔ (T.deleteEdges {s(y, v)}).edist v w ≤ (R : ℕ∞)
  boundary : ∀ w, w ∉ F → w = y ∨ (T.deleteEdges {s(y, v)}).edist v w = ((R + 1 : ℕ) : ℕ∞)
  edge_meets : ∀ a b, T.Adj a b → a ∈ F ∨ b ∈ F
  degree_le : ∀ w ∈ F, T.degree w ≤ Δ

end PottsRapidMixing


