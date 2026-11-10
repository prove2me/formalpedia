-- Prove2me | Definitions.Def_TwMSOCount_Main_BGraph
-- name    : TwMSOCount_Main_BGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:39:57.671325+00:00
-- url     : https://prove2.me/theorems/ef554098-eed6-418d-aa20-567a6f524963
-- title:
--   Colored boundaried graphs with output labels, the operations of Table 2, isomorphisms and the partial weight
-- statement:
--   Let $\Lambda_k$ be the ordered pool of $7(k+1)+1$ **boundary labels** (here $\{0,\dots,7(k+1)\}$). A **colored $B$-boundaried graph** $(H,\chi,\iota_B)$ consists of a finite simple graph $H$, a coloring $\chi$, a set $B \subseteq \Lambda_k$ and a **boundary map** $\iota_B : B \to V(H)$; its **boundary** is $\partial H = \iota(B)$, its **internal vertices** are $H^\circ = V(H) \setminus \partial H$ and its internal size is $m = |H^\circ|$. Internal vertices carry **output labels**; $\min H^\circ$ is the internal vertex with the least output label. It is **well formed** when $\iota$ is injective and internal output labels are distinct.
--
--   The **partial weight** (1) is $W_B(H,\chi) = \prod_{v\in H^\circ} \lambda_{\chi(v)} \cdot \omega_\chi(E(H))$.
--
--   Operations (Table 2): **introduce** $(b,c)$ adds a fresh isolated vertex of color $c$ labeled $b$ (defined for $b \notin B$); **forget** $b$ removes $b$ from the boundary map (also batched as $\mathrm{forget}_N$); **relabel** by $\pi$ replaces $\iota$ by $\iota\circ\pi^{-1}$ on $\pi(B)$ (defined for $\pi$ injective on $B$); **add edges** inserts $\{\iota(a),\iota(b)\}$ for the label pairs of a pattern $F$ (defined when the pairs are distinct labels of $B$ with nonadjacent images; a single AddEdge is $F = \{\{a,b\}\}$); **glue** takes disjoint copies and identifies $\iota_1(b)$ with $\iota_2(b)$ for the common labels $Q = B_1\cap B_2$, giving label set $B_1\cup B_2$ (defined when colors agree at identified vertices and no pair of $Q$ is an edge in both operands).
--
--   Two boundaried graphs are **isomorphic** (`IsoBL`) when a bijection preserves adjacency, colors and every boundary label; `IsoOut` also preserves the output labels of internal vertices. The **stored graph** on $V_B \sqcup [m]$ (Appendix B.2) has boundary vertices $v_b$ with $\iota(b) = v_b$ and internal vertices $0,\dots,m-1$ carrying themselves as output labels; $H_{B,F}$ is the graph on the boundary vertices alone with edge pattern $F$. Finally $G - D$ is represented by isolating the vertices of $D$, and `comps G D` lists the vertex sets of the components of $G - D$.
--
--   **Formalization Note.** `BGraph r k` bundles the vertex type `V` (finite, decidable equality); `ι : B → V` is defined on the subtype of `B`.
--
--   `BoundaryWF` requires only an injective boundary map, as in the structural graph algebra. `WF` additionally requires distinct internal output labels for descriptions. State maps and construction terms ignore output labels.
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), §3.1, pp. 4–5 (PDF 5–6), eq. (1); §4.1, p. 8 (PDF 9); Table 2, p. 27 (PDF 28); Appendix B.2, p. 19 (PDF 20)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights

namespace TwMSOCount.Main

/-- The ordered pool `Λ_k` of `7(k+1)+1` boundary labels (Section 3.1). -/
abbrev Lab (k : ℕ) := Fin (7 * (k + 1) + 1)

/-- A colored `B`-boundaried graph `(H, χ, ι_B)` (Section 3.1): a finite simple graph on a vertex
type `V`, a coloring `col : V → Fin r`, a set `B ⊆ Λ_k` of boundary labels with boundary map
`ι : B → V`, and output labels `out : V → ℕ`, which are meaningful on internal vertices only
(least output label = least `out`). Well-formedness (`WF`) asks `ι` injective and `out` injective on
internal vertices. -/
structure BGraph (r k : ℕ) where
  V : Type
  [fin : Fintype V]
  [dec : DecidableEq V]
  G : SimpleGraph V
  col : V → Fin r
  B : Finset (Lab k)
  ι : B → V
  out : V → ℕ

attribute [instance] BGraph.fin BGraph.dec

namespace BGraph

variable {r k : ℕ}

/-- The boundary `∂H = ι(B)`. -/
def bdry (H : BGraph r k) : Finset H.V := Finset.univ.image H.ι

/-- The internal vertex set `H° = V(H) \ ∂H`. -/
def int (H : BGraph r k) : Finset H.V := Finset.univ \ H.bdry

/-- A boundaried graph as a structural object: the boundary map is injective. Output labels
are ignored by the state map and by the operations of Table 2. -/
def BoundaryWF (H : BGraph r k) : Prop := Function.Injective H.ι

/-- Well-formed: the boundary map is an injection and internal output labels are distinct. -/
def WF (H : BGraph r k) : Prop := Function.Injective H.ι ∧ Set.InjOn H.out H.int

/-- Image `ι(Q)` of a set of labels (labels outside `B` are ignored). -/
def img (H : BGraph r k) (Q : Finset (Lab k)) : Finset H.V :=
  (Finset.univ.filter (fun b : H.B => b.1 ∈ Q)).image H.ι

/-- Constant interpretation `b ↦ ι(b)` for `b ∈ B`, uninterpreted otherwise. -/
def κ (H : BGraph r k) (b : Lab k) : Option H.V :=
  if h : b ∈ H.B then some (H.ι ⟨b, h⟩) else none

/-- `I(H, χ, ι_B) ⊨ φ` for a sentence over `V_{C,B}` (constants `c_b` interpreted as `ι(b)`). -/
def Models (H : BGraph r k) (φ : Formula r (Lab k)) : Prop := Formula.Models H.G H.col H.κ φ

/-- Treewidth of the underlying graph. -/
noncomputable def tw (H : BGraph r k) : ℕ := PlantedSubgraphLD.tw H.G

open Classical in
/-- Partial weight (1): `W_B(H, χ) = ∏_{v ∈ H°} λ_{χ(v)} · ω_χ(E(H))`. -/
noncomputable def pw (w : Weights r) (H : BGraph r k) : ℚ≥0 :=
  (∏ v ∈ H.int, w.vtx (H.col v)) * w.omega H.col H.G.edgeFinset

/-- Isomorphism preserving adjacency, colors and boundary labels (Definition 4.1(i)). -/
def IsoBL (H H' : BGraph r k) : Prop :=
  H.B = H'.B ∧ ∃ e : H.V ≃ H'.V, (∀ u v, H'.G.Adj (e u) (e v) ↔ H.G.Adj u v) ∧
    (∀ v, H'.col (e v) = H.col v) ∧
    ∀ (b : Lab k) (h : b ∈ H.B) (h' : b ∈ H'.B), e (H.ι ⟨b, h⟩) = H'.ι ⟨b, h'⟩

/-- Isomorphism that also preserves the output labels of internal vertices ("output labels
included", Lemma 3.1(i)). -/
def IsoOut (H H' : BGraph r k) : Prop :=
  H.B = H'.B ∧ ∃ e : H.V ≃ H'.V, (∀ u v, H'.G.Adj (e u) (e v) ↔ H.G.Adj u v) ∧
    (∀ v, H'.col (e v) = H.col v) ∧
    (∀ (b : Lab k) (h : b ∈ H.B) (h' : b ∈ H'.B), e (H.ι ⟨b, h⟩) = H'.ι ⟨b, h'⟩) ∧
    ∀ v ∈ H.int, H'.out (e v) = H.out v

/-! ### The operations of Table 2 -/

/-- Introduce `(b, c)`: a fresh isolated vertex of color `c` carrying label `b`. Defined when
`b ∉ B`. -/
def introduce (H : BGraph r k) (b : Lab k) (c : Fin r) : BGraph r k where
  V := Option H.V
  G := H.G.map (Function.Embedding.some)
  col := fun v => match v with | none => c | some u => H.col u
  B := insert b H.B
  ι := fun x => if h : x.1 ∈ H.B then some (H.ι ⟨x.1, h⟩) else none
  out := fun v => match v with | none => 0 | some u => H.out u

/-- Forget a label: restrict the boundary map to `B \ {b}`, keeping every vertex and edge. -/
def forget (H : BGraph r k) (b : Lab k) : BGraph r k where
  V := H.V
  G := H.G
  col := H.col
  B := H.B.erase b
  ι := fun x => H.ι ⟨x.1, Finset.mem_of_mem_erase x.2⟩
  out := H.out

/-- Forget a set `N` of labels (the batched `forget_N`). -/
def forgetSet (H : BGraph r k) (N : Finset (Lab k)) : BGraph r k where
  V := H.V
  G := H.G
  col := H.col
  B := H.B \ N
  ι := fun x => H.ι ⟨x.1, (Finset.mem_sdiff.mp x.2).1⟩
  out := H.out

/-- Relabel by `π`: boundary map `ι ∘ π⁻¹` on `π(B)`. Defined when `π` is injective on `B`. -/
noncomputable def relabel (H : BGraph r k) (π : Lab k → Lab k) : BGraph r k where
  V := H.V
  G := H.G
  col := H.col
  B := H.B.image π
  ι := fun y => H.ι ⟨(Finset.mem_image.mp y.2).choose, (Finset.mem_image.mp y.2).choose_spec.1⟩
  out := H.out

/-- Insert the edges `{ι(a), ι(b)}` for the label pairs `{a, b} ∈ F` with `a, b ∈ B` (the batched
`add_F`; a single `AddEdge (a, b)` is `F = {{a, b}}`). -/
def addEdges (H : BGraph r k) (F : Finset (Sym2 (Lab k))) : BGraph r k where
  V := H.V
  G := H.G ⊔ SimpleGraph.fromEdgeSet
    {e | ∃ (a b : H.B), s(a.1, b.1) ∈ F ∧ e = s(H.ι a, H.ι b)}
  col := H.col
  B := H.B
  ι := H.ι
  out := H.out

/-- `AddEdge (a, b)` is defined: `a ≠ b`, both in `B`, images nonadjacent. -/
def AddEdgeOK (H : BGraph r k) (a b : Lab k) : Prop :=
  ∃ (ha : a ∈ H.B) (hb : b ∈ H.B), a ≠ b ∧ ¬ H.G.Adj (H.ι ⟨a, ha⟩) (H.ι ⟨b, hb⟩)

/-- The batched `add_F` is defined: every pair of `F` is a pair of distinct labels of `B` whose
images are nonadjacent. -/
def AddEdgesOK (H : BGraph r k) (F : Finset (Sym2 (Lab k))) : Prop :=
  ∀ a b, s(a, b) ∈ F → H.AddEdgeOK a b

/-- Vertices of the second operand that are not identified with a vertex of the first. -/
def glueRest (H₁ H₂ : BGraph r k) : Type :=
  {v : H₂.V // ¬ ∃ b : H₂.B, b.1 ∈ H₁.B ∧ H₂.ι b = v}

noncomputable instance (H₁ H₂ : BGraph r k) : Fintype (glueRest H₁ H₂) := by
  unfold glueRest
  classical
  infer_instance

noncomputable instance (H₁ H₂ : BGraph r k) : DecidableEq (glueRest H₁ H₂) := by
  unfold glueRest
  classical
  infer_instance

open Classical in
/-- Where a vertex of the second operand lands in the glued graph: `ι₂(b) ↦ ι₁(b)` for a common
label `b`, every other vertex is kept. -/
noncomputable def glueMap (H₁ H₂ : BGraph r k) (v : H₂.V) : H₁.V ⊕ glueRest H₁ H₂ :=
  if h : ∃ b : H₂.B, b.1 ∈ H₁.B ∧ H₂.ι b = v then
    Sum.inl (H₁.ι ⟨h.choose.1, h.choose_spec.1⟩)
  else Sum.inr ⟨v, h⟩

/-- Glue along the common labels `Q = B₁ ∩ B₂` (Table 2): disjoint copies with `ι₁(b)` and
`ι₂(b)` identified for `b ∈ Q`; label set `B₁ ∪ B₂`. -/
noncomputable def glue (H₁ H₂ : BGraph r k) : BGraph r k where
  V := H₁.V ⊕ glueRest H₁ H₂
  G := SimpleGraph.fromRel (fun x y =>
    (∃ a b, x = Sum.inl a ∧ y = Sum.inl b ∧ H₁.G.Adj a b) ∨
    (∃ a b, x = glueMap H₁ H₂ a ∧ y = glueMap H₁ H₂ b ∧ H₂.G.Adj a b))
  col := fun x => match x with | Sum.inl a => H₁.col a | Sum.inr v => H₂.col v.1
  B := H₁.B ∪ H₂.B
  ι := fun x => if h : x.1 ∈ H₁.B then Sum.inl (H₁.ι ⟨x.1, h⟩)
    else glueMap H₁ H₂ (H₂.ι ⟨x.1, (Finset.mem_union.mp x.2).resolve_left h⟩)
  out := fun x => match x with | Sum.inl a => H₁.out a | Sum.inr v => H₂.out v.1

/-- Gluing is defined: colors agree at identified vertices, and no label pair of `Q = B₁ ∩ B₂`
has images forming an edge in both operands. -/
def GlueOK (H₁ H₂ : BGraph r k) : Prop :=
  (∀ (b : Lab k) (h₁ : b ∈ H₁.B) (h₂ : b ∈ H₂.B), H₁.col (H₁.ι ⟨b, h₁⟩) = H₂.col (H₂.ι ⟨b, h₂⟩)) ∧
  ∀ (a b : Lab k) (ha₁ : a ∈ H₁.B) (ha₂ : a ∈ H₂.B) (hb₁ : b ∈ H₁.B) (hb₂ : b ∈ H₂.B),
    ¬ (H₁.G.Adj (H₁.ι ⟨a, ha₁⟩) (H₁.ι ⟨b, hb₁⟩) ∧ H₂.G.Adj (H₂.ι ⟨a, ha₂⟩) (H₂.ι ⟨b, hb₂⟩))

/-- A graph consisting of boundary vertices alone: vertex set `B`, boundary map the identity,
colors `χB`, edges `{a, b}` for the label pairs of `F` (the graph `H_{B,F}` of (3)). -/
def boundaryOnly (B : Finset (Lab k)) (χB : B → Fin r) (F : Finset (Sym2 (Lab k))) :
    BGraph r k where
  V := B
  G := SimpleGraph.fromEdgeSet {e | ∃ a b : B, s(a.1, b.1) ∈ F ∧ e = s(a, b)}
  col := χB
  B := B
  ι := id
  out := fun _ => 0

/-- The stored `B`-boundaried graph on `V_B ⊔ [m]` (Appendix B.2): boundary vertices `v_b`
(`Sum.inl b`), internal vertices `Fin m` with output labels `0, …, m-1`. -/
def stored (B : Finset (Lab k)) (m : ℕ) (G : SimpleGraph (B ⊕ Fin m)) (χ : B ⊕ Fin m → Fin r) :
    BGraph r k where
  V := B ⊕ Fin m
  G := G
  col := χ
  B := B
  ι := Sum.inl
  out := fun v => match v with | Sum.inl _ => 0 | Sum.inr i => i.val

/-- Deleting a vertex set `D` from the graph: the vertices of `D` become isolated (paths in
`G − D` are walks of this graph that start outside `D`). -/
def delV {V : Type} (G : SimpleGraph V) (D : Set V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => G.Adj u v ∧ u ∉ D ∧ v ∉ D)

/-- The component vertex set of `v` in `G − D` (empty when `v ∈ D`). -/
noncomputable def comp {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (D : Finset V) (v : V) :
    Finset V := by
  classical
  exact Finset.univ.filter (fun u => v ∉ D ∧ u ∉ D ∧ (delV G ↑D).Reachable v u)

/-- The vertex sets of the components of `G − D`. -/
noncomputable def comps {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (D : Finset V) : Finset (Finset V) := by
  classical
  exact (Finset.univ.filter (fun v => v ∉ D)).image (comp G D)

end BGraph

end TwMSOCount.Main


