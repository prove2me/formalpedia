-- Prove2me | Definitions.Def_GMSTFramework_LocalStructure_ColourExplorers
-- name    : GMSTFramework_LocalStructure_ColourExplorers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:02:11.018212+00:00
-- url     : https://prove2.me/theorems/d7308685-b99d-469c-ba5b-05b0717ed065
-- title:
--   Boundaried graphs, $(b,q,p)$-colour-explorers, protrusions, $I$-blank renditions, orientation-equivalence, hosting and representation (§3)
-- statement:
--   A **$q$-colorful boundaried graph** is $(H,B,A,\psi,\rho)$: $(H,\psi)$ $q$-colorful, $A\subsetneq B\subseteq V(H)$, $\rho:B\to[|B|]$ a bijection listing $B\setminus A$ first; $\mathcal B^q_b$ is the class of those with $|B|\in[b]$. $\varphi:\mathcal B^q_b\to 2^{[p]}$ ($p\ge q$, $b\ge1$) is a **$(b,q,p)$-colour-explorer** if it is computable, satisfies the **singleton axiom** $\varphi((\{v\},\emptyset),\{v\},\emptyset,\{v\mapsto\psi(v)\},\{v\mapsto1\})=\psi(v)$, and the **preservation axiom**: for every $q$-colorful $(F,\zeta)$ on $[m]$, $m\in[b-1]$, and $S\subseteq[m]$ there is a bijection $\mathrm{recolor}_S$ of $[p]$ such that for every $H\in\mathcal B^q_b$ with $|A|=m$ whose enumeration $a_1,\dots,a_m$ of $A$ (by $\rho$) is a colour-preserving isomorphism $(F,\zeta)\to(H[A],\psi)$, if $N_H(Z_S)\subseteq A$ for $Z_S=\{a_i:i\in S\}$ then $\varphi(H-Z_S)=\mathrm{recolor}_S(\varphi(H))$.
--
--   The **protrusion** at a simple cell $c$ of a rendition of $G-A$ w.r.t. $A'\subseteq A$ is $(G[V(\sigma(c))\cup A'],A'\cup N(c),A',\chi)$ with $\rho_{\mathrm{label}}$. $\rho$ is **$I$-blank** w.r.t. $\varphi$ and $A'$ if $\varphi(\mathrm{protrusion}(c))\subseteq I$ for every simple $c$. Two simple cells are **orientation-equivalent** if they have the same number $k$ of nodes and $k\le2$, or $k=3$ and $\mathrm{orient}(c,\Delta)=\mathrm{orient}(c',\Delta)$ for every closed disk $\Delta$ disjoint from $\bar c\cup\bar c'$ (admissible orientations: positively ordered $y_1,y_2,y_3\in\mathrm{bd}(\Delta)$, disjoint arcs $x_iy_i$ from the label-ordered nodes, all inside a closed disk). A flap-segment **hosts** a simple cell $c$ if $\pi(N(c))$ is the set of ends of its hyperedge and $c$ lies in the interior of the disk bounded by the trace of its pocket that avoids the simple cycle. $D$ **represents** $J$ with strength $r$ if (i) every flap-segment hosts a simple cell whose colours meet $J$ and (ii) there are pairwise disjoint families $F_{j,o}$ of $r$ flap-segments, for each $j\in J$ and each orientation class $o$ containing a cell with colour $j$, each segment hosting a cell of $o$ with colour $j$.
--
--   **Formalization Note.** Colour-explorers act on boundaried graphs with vertices in $\mathbb N$ (`BGraph`, its conditions in `Valid`); the boundaried subgraphs of a labelled $G$ are passed with every vertex named by its label in $[|V(G)|]$ (`vName`). Computability is not required. Colours are 1-based ($[q]=\{1..q\}$); $F$ in the preservation axiom is on `Fin m`. Orientations of $\Delta$ are boundary parametrisations $S^1\to\mathrm{bd}(\Delta)$, so `orientSet` compares sets of parametrisations (equal iff the admissible orientations agree). `Represents` is stated for every $J$, including $J=\emptyset$; the families $F_{j,o}$ are indexed by a colour and a representative cell of $o$.
-- source:
--   Gorsky, Protopapas, Wiederrecht, A unifying framework for Graph Minor Structure Theorems with polynomial bounds, STOC 2027 submission (manuscript sha256 b2ee466d…), p. 24–28 (PDF 27–31), §3.1–3.3

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_Renditions
import Definitions.Def_GMSTFramework_LocalStructure_SurfaceWalls

open scoped Classical

noncomputable section

namespace GMSTFramework.LocalStructure

/-!
# Boundaried graphs, colour-explorers, protrusions, blank renditions, representation

Gorsky, Protopapas, Wiederrecht, *A unifying framework for Graph Minor Structure Theorems with
polynomial bounds*, STOC 2027 submission (manuscript sha256 b2ee466d…), §3.1 p. 24–26
(PDF 27–29), §3.2 p. 26–27 (PDF 29–30), §3.3 p. 27–28 (PDF 30–31).

* `BGraph`: a boundaried graph `(H, B, A, ψ, ρ)` whose vertices are natural numbers: vertex set `V`,
  adjacency `adj`, colours `ψ`, boundary `B`, distinguished set `A`, and the bijection
  `ρ : B → [|B|]` given as the list `ord = ρ⁻¹(1), …, ρ⁻¹(|B|)`. `BGraph.Valid` collects the
  conditions (`A ⊊ B ⊆ V`, edges and colours only on `V`, `ord` lists `B` once, `B \ A` before
  `A`). `InClass q b X`: `X ∈ B^q_b` (`q`-colorful, `|B| ∈ [b]`).
  Colour-explorers are functions on **all** boundaried graphs, which carry concrete vertex sets;
  here they act on boundaried graphs with vertex set in `ℕ`. A boundaried subgraph of a host graph
  `G` is passed to `φ` with every vertex `v` named by its label `label(v) ∈ [|V(G)|]`; since `G`
  comes with a fixed labelling (p. 24) and the axioms are invariant under renaming vertices, this
  covers every colour-explorer of the paper (see the moderation notes).
* `IsColourExplorer b q p φ` (p. 25): `p ≥ q`, `b ≥ 1`, `φ(X) ⊆ [p]` on `B^q_b`, the singleton axiom
  and the preservation axiom (the bijection `recolor_S` depends only on `(F, ζ)` and `S`). The
  paper also requires `φ` to be computable; that requirement is dropped (a generalization).
* `protrusion` (p. 26): `(G[V(σ(c)) ∪ A'], A' ∪ N(c), A', χ)` with `ρ_label` (`B \ A` by increasing
  label, then `A` by increasing label).
* `IsIBlank` (p. 26): `φ(protrusion_{ρ,A'}(c)) ⊆ I` for every simple cell `c`.
* Orientation-equivalence of simple cells (p. 27): orientations of a closed disk `Δ` are its
  boundary parametrisations `S¹ → bd(Δ)` (two parametrisations give the same orientation iff they
  induce the same cyclic order); `orient(c, Δ)` is the set of admissible ones.
* `Hosts` and `Represents` (p. 28), stated for every set of colours `J` (for `J = ∅` condition i)
  says that `D` has no flap-segment, the stronger reading of "`D` represents `φ`" when `I = ∅`).
-/

/-- A boundaried graph with vertices in `ℕ` (raw data; see `BGraph.Valid`). -/
structure BGraph where
  /-- vertex set -/
  V : Finset ℕ
  /-- adjacency -/
  adj : SimpleGraph ℕ
  /-- colours -/
  ψ : ℕ → Finset ℕ
  /-- boundary -/
  B : Finset ℕ
  /-- distinguished boundary vertices -/
  A : Finset ℕ
  /-- `ρ⁻¹(1), …, ρ⁻¹(|B|)` -/
  ord : List ℕ

namespace BGraph

/-- The conditions of a boundaried graph (p. 24). -/
def Valid (X : BGraph) : Prop :=
  (∀ u v, X.adj.Adj u v → u ∈ X.V ∧ v ∈ X.V) ∧ (∀ v, v ∉ X.V → X.ψ v = ∅) ∧
    X.A ⊂ X.B ∧ X.B ⊆ X.V ∧ X.ord.Nodup ∧ (∀ v, v ∈ X.ord ↔ v ∈ X.B) ∧
    ∀ (i j : ℕ) (hi : i < X.ord.length) (hj : j < X.ord.length), i < j →
      X.ord[i] ∈ X.A → X.ord[j] ∈ X.A

/-- `X ∈ B^q_b`: a valid `q`-colorful `b'`-boundaried graph with `b' ∈ [b]`. -/
def InClass (q b : ℕ) (X : BGraph) : Prop :=
  X.Valid ∧ (∀ v, X.ψ v ⊆ Finset.Icc 1 q) ∧ 1 ≤ X.B.card ∧ X.B.card ≤ b

/-- The singleton boundaried graph `(({v}, ∅), {v}, ∅, {v ↦ s}, {v ↦ 1})`. -/
def single (v : ℕ) (s : Finset ℕ) : BGraph where
  V := {v}
  adj := ⊥
  ψ := fun w => if w = v then s else ∅
  B := {v}
  A := ∅
  ord := [v]

/-- The adjacency with the vertices of `Z` removed. -/
def adjDel (X : BGraph) (Z : Finset ℕ) : SimpleGraph ℕ where
  Adj u w := X.adj.Adj u w ∧ u ∉ Z ∧ w ∉ Z
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun u h => X.adj.loopless.irrefl u h.1⟩

/-- `H - Z = (H - Z, B \ Z, A \ Z, ψ, ρ_Z)`, the remaining boundary labels compressed in their
original order. -/
def deleteSet (X : BGraph) (Z : Finset ℕ) : BGraph where
  V := X.V \ Z
  adj := X.adjDel Z
  ψ := fun w => if w ∈ Z then ∅ else X.ψ w
  B := X.B \ Z
  A := X.A \ Z
  ord := X.ord.filter fun w => w ∉ Z

/-- `A = {a₁, …, a_m}` listed in increasing order under `ρ`. -/
def aList (X : BGraph) : List ℕ := X.ord.filter fun w => w ∈ X.A

end BGraph

/-- `φ` is a `(b, q, p)`-colour-explorer (without the computability requirement). -/
def IsColourExplorer (b q p : ℕ) (φ : BGraph → Finset ℕ) : Prop :=
  q ≤ p ∧ 1 ≤ b ∧
  (∀ X, X.InClass q b → φ X ⊆ Finset.Icc 1 p) ∧
  -- singleton axiom
  (∀ (v : ℕ) (s : Finset ℕ), s ⊆ Finset.Icc 1 q → φ (BGraph.single v s) = s) ∧
  -- preservation axiom
  (∀ m, 1 ≤ m → m ≤ b - 1 → ∀ (F : SimpleGraph (Fin m)) (ζ : Fin m → Finset ℕ),
    (∀ i, ζ i ⊆ Finset.Icc 1 q) → ∀ S : Finset (Fin m),
    ∃ recolor : ℕ → ℕ, Set.BijOn recolor (Finset.Icc 1 p : Set ℕ) (Finset.Icc 1 p : Set ℕ) ∧
      ∀ X : BGraph, X.InClass q b → X.A.card = m →
        (∀ i j : Fin m, F.Adj i j ↔ X.adj.Adj (X.aList.getD i 0) (X.aList.getD j 0)) →
        (∀ i : Fin m, ζ i = X.ψ (X.aList.getD i 0)) →
        (∀ z ∈ S.image (fun i : Fin m => X.aList.getD i 0), ∀ w, X.adj.Adj z w → w ∈ X.A) →
        φ (X.deleteSet (S.image fun i : Fin m => X.aList.getD i 0)) = (φ X).image recolor)

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {X : Type} [TopologicalSpace X]

/-- The name of a vertex: its label in `[|V(G)|]` (`label` is a bijection `V(G) → [|V(G)|]`). -/
def vName (label : V ≃ Fin (Fintype.card V)) (v : V) : ℕ := (label v : ℕ) + 1

/-- The boundaried subgraph `(G[W], B, A, χ, ρ_label)` of the labelled colorful graph `(G, χ)`, with
vertices named by their labels. -/
def boundariedSub (G : SimpleGraph V) (χ : V → Finset ℕ) (label : V ≃ Fin (Fintype.card V))
    (W Bd Ad : Finset V) : BGraph where
  V := W.image (vName label)
  adj := SimpleGraph.fromRel fun u w => ∃ x ∈ W, ∃ y ∈ W, vName label x = u ∧ vName label y = w ∧
    G.Adj x y
  ψ := fun u => if h : ∃ x ∈ W, vName label x = u then χ (Classical.choose h) else ∅
  B := Bd.image (vName label)
  A := Ad.image (vName label)
  ord := ((Bd \ Ad).image (vName label)).sort (· ≤ ·) ++ (Ad.image (vName label)).sort (· ≤ ·)

/-- The protrusion at the cell `c` with respect to `A'`:
`(G[V(σ(c)) ∪ A'], A' ∪ N(c), A', χ)`. -/
def protrusion (G : SimpleGraph V) (χ : V → Finset ℕ) (label : V ≃ Fin (Fintype.card V))
    (A' : Finset V) {H : G.Subgraph} (ρ : Rendition X H) (c : Set X) : BGraph :=
  boundariedSub G χ label (Finset.univ.filter fun v => v ∈ (ρ.σ c).verts ∨ v ∈ A')
    (Finset.univ.filter fun v => v ∈ A' ∨ v ∈ ρ.cellNodeVerts c) A'

/-- `ρ` is `I`-blank with respect to `φ` and `A'`. -/
def IsIBlank (φ : BGraph → Finset ℕ) (G : SimpleGraph V) (χ : V → Finset ℕ)
    (label : V ≃ Fin (Fintype.card V)) (A' : Finset V) {H : G.Subgraph} (ρ : Rendition X H)
    (I : Finset ℕ) : Prop :=
  ∀ c, ρ.IsSimple c → φ (protrusion G χ label A' ρ c) ⊆ I

/-! ### Orientation-equivalence -/

/-- The nodes `x₁, x₂, x₃` of a cell, in increasing order of the labels of their vertices. -/
def orderedNodes (label : V ≃ Fin (Fintype.card V)) {H : G.Subgraph} (ρ : Rendition X H)
    (c : Set X) (xs : Fin 3 → X) : Prop :=
  (∀ i, xs i ∈ ρ.nodesOf c) ∧ Set.range xs = ρ.nodesOf c ∧
    StrictMono fun i => vName label (ρ.π (xs i))

/-- The orientation of `Δ` given by the boundary parametrisation `o` is admissible for the simple
cell `c` with `|N(c)| = 3`. -/
def IsAdmissible (label : V ≃ Fin (Fintype.card V)) {H : G.Subgraph} (ρ : Rendition X H)
    (c Δ : Set X) (o : C(Circle, X)) : Prop :=
  ∃ xs : Fin 3 → X, orderedNodes label ρ c xs ∧
    ∃ z : Fin 3 → Circle, Function.Injective z ∧ CyclicPositive (z 0) (z 1) (z 2) ∧
      ∃ L : Fin 3 → Set X, (∀ i, IsArc (L i) (xs i) (o (z i))) ∧
        (Pairwise fun i j => Disjoint (L i) (L j)) ∧
        (∃ Δ' : Set X, IsClosedDisk Δ' ∧ closure c ∪ Δ ∪ (⋃ i, L i) ⊆ Δ') ∧
        ∀ i, L i ∩ (closure c ∪ Δ) = {xs i, o (z i)}

/-- `orient_ρ(c, Δ)`: the boundary parametrisations of `Δ` whose orientation is admissible for `c`. -/
def orientSet (label : V ≃ Fin (Fintype.card V)) {H : G.Subgraph} (ρ : Rendition X H)
    (c Δ : Set X) : Set C(Circle, X) :=
  {o | Function.Injective o ∧ IsDiskWithBoundary Δ (Set.range o) ∧ IsAdmissible label ρ c Δ o}

/-- Simple cells `c`, `c'` are orientation-equivalent. -/
def OrientEquiv (label : V ≃ Fin (Fintype.card V)) {H : G.Subgraph} (ρ : Rendition X H)
    (c c' : Set X) : Prop :=
  ρ.IsSimple c ∧ ρ.IsSimple c' ∧ (ρ.nodesOf c).ncard = (ρ.nodesOf c').ncard ∧
    ((ρ.nodesOf c).ncard ≤ 2 ∨
      ((ρ.nodesOf c).ncard = 3 ∧ ∀ Δ : Set X, IsClosedDisk Δ →
        Disjoint Δ (closure c ∪ closure c') → orientSet label ρ c Δ = orientSet label ρ c' Δ))

/-! ### Hosting and representation -/

/-- The flap-segment `i` of `D` hosts the simple cell `c`: `π(N(c))` is the set of ends of its
hyperedge, and `c` lies in the interior of the disk bounded by the trace of its pocket that avoids
(a trace of) the simple cycle of `D`. -/
def Hosts {n : ℕ} {H : G.Subgraph} (ρ : Rendition X H) (D : SurfaceWall G n)
    (i : Fin D.kinds.length) (c : Set X) : Prop :=
  D.IsFlapSeg i ∧ ρ.IsSimple c ∧ ρ.cellNodeVerts c = (D.zs i : Set V) ∧
    ∃ Tp Dk Ts : Set X, ρ.IsTraceCycle (D.pocket i) Tp ∧ IsDiskWithBoundary Dk Tp ∧
      ρ.IsTraceCycle D.simpleCycle Ts ∧ Disjoint Dk Ts ∧ c ⊆ Dk \ Tp

/-- `D` represents the colour set `J` with respect to `A'` in `ρ` with strength `r`: i) every
flap-segment hosts a simple cell whose protrusion has a colour in `J`; ii) pairwise disjoint families
`F_{j,o}` of `r` flap-segments, one for each colour `j ∈ J` and each orientation class `o` containing
a cell with colour `j`, each segment of `F_{j,o}` hosting a cell of `o` with colour `j`. The family
`F j c` is indexed by a representative `c` of the class. -/
def Represents (φ : BGraph → Finset ℕ) (G : SimpleGraph V) (χ : V → Finset ℕ)
    (label : V ≃ Fin (Fintype.card V)) (A' : Finset V) {n : ℕ} {H : G.Subgraph}
    (ρ : Rendition X H) (D : SurfaceWall G n) (J : Finset ℕ) (r : ℕ) : Prop :=
  let col := fun c => φ (protrusion G χ label A' ρ c)
  (∀ i, D.IsFlapSeg i → ∃ c, Hosts ρ D i c ∧ (col c ∩ J).Nonempty) ∧
  ∃ F : ℕ → Set X → Finset (Fin D.kinds.length),
    (∀ j ∈ J, ∀ c, ρ.IsSimple c → j ∈ col c →
      (F j c).card = r ∧ ∀ i ∈ F j c, ∃ c', OrientEquiv label ρ c c' ∧ j ∈ col c' ∧ Hosts ρ D i c') ∧
    (∀ j ∈ J, ∀ c c', ρ.IsSimple c → ρ.IsSimple c' → j ∈ col c → j ∈ col c' →
      OrientEquiv label ρ c c' → F j c = F j c') ∧
    (∀ j ∈ J, ∀ j' ∈ J, ∀ c c', ρ.IsSimple c → ρ.IsSimple c' → j ∈ col c → j' ∈ col c' →
      (j ≠ j' ∨ ¬ OrientEquiv label ρ c c') → Disjoint (F j c) (F j' c'))

end GMSTFramework.LocalStructure


