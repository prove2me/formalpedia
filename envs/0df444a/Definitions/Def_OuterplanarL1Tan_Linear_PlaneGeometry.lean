-- Prove2me | Definitions.Def_OuterplanarL1Tan_Linear_PlaneGeometry
-- name    : OuterplanarL1Tan_Linear_PlaneGeometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:06:46.026775+00:00
-- url     : https://prove2.me/theorems/d8c75e5f-acfa-412b-986f-bd2657496675
-- title:
--   Actual outer faces, geometric peeling and cyclic facial walks
-- statement:
--   A plane drawing assigns distinct points in $\mathbb R^2$ to vertices and simple continuous arcs to edges. Opposite orientations traverse the same arc in reverse; interiors contain no vertices and different unoriented edges have disjoint interiors. This general drawing is imported from the published Robertson–Seymour definition.
--
--   For a vertex set $S$, the drawing is structurally restricted to the actual induced graph on the subtype $S$. The trace $K_S$ and its outer face reuse the published Tait–Tobin definitions, including isolated vertices. Faces are the connected components of $\mathbb R^2\setminus K_S$. The outer face is the unbounded complementary component, and $\partial_D S$ consists of vertices of $S$ whose points lie in its closure. The residuals and layers are
--
--   $$R_0=V,\qquad L_{n+1}=\partial_D R_n,\qquad R_{n+1}=R_n\setminus L_{n+1}.$$
--
--   A graph is $k$-outerplanar when some drawing satisfies $R_k=\varnothing$. A cyclic outer facial walk lists boundary visits, allowing repeated vertices, and uses each oriented boundary edge at most once. Its geometric order is witnessed by an exterior collar: nested simple closed curves in the outer face enclose the drawing and converge to the edge traversal on the outer boundary. The one-vertex graph has a single stationary visit.
--
--   This supplies geometric incidence and peeling independently of distances and metric inequalities. It imposes no connectedness or distance-preservation condition on residuals.
--
--   **Formalization Note** The plane uses the usual product topology; its bounded sets are the usual bounded subsets of the Euclidean plane. An alias reuses the imported drawing without changing its fields; structural field proofs construct its restriction. The published drawing image and outer face are reused on that restriction. Complement components and closure, rather than an asserted nonalternation property, determine the boundary. Walk positions use `Fin m`, with $m>0$ for a nonempty component and cyclic successor modulo $m$. Existence of collars/facial walks is an ordinary topological obligation for future proofs; no existence theorem or metric assertion is hidden in this definition file.
-- source:
--   Zihan Tan, Improved Embedding of k-Outerplanar Metrics into ℓ₁, STOC 2027 submission #262 (October 2026), p. 2–3, 7–8, §§1.2, 2.1, 3.3 and Appendix A (PDF p. 3–4, 8–9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/262.pdf; SHA256 0ec64e77e85f536fdf7dc42bb8fdeedaf8861f751861d02b2d5edbdef75ee0ab

import Definitions.Def_OuterplanarL1Tan_Linear_WeightedGraph
import Definitions.Def_TaitTobin_Outerplanar_Setting

namespace OuterplanarL1Tan.Linear

abbrev Plane := ℝ × ℝ

/-- Alias of the published continuous-arc drawing, with coherent reversal.
No polygonal, straight-line, or metric assumptions are added. -/
abbrev PlaneDrawing {V : Type} (G : SimpleGraph V) :=
  RobertsonSeymour1986.GM5.PlaneDrawing G

/-- Restrict the published drawing to the actual induced graph on a subtype.
All proofs below are structural restrictions of the drawing fields. -/
def PlaneDrawing.induced {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G)
    (S : Set V) : PlaneDrawing (G.induce S) where
  vertex := fun v => D.vertex v.val
  vertex_injective := D.vertex_injective.comp Subtype.val_injective
  arc := fun h => D.arc h
  arc_injective := fun h => D.arc_injective h
  arc_reverse := fun h => D.arc_reverse h
  arc_avoids_vertices := by
    intro v w h t x hx
    rcases D.arc_avoids_vertices h t x.val hx with hv | hw
    · exact Or.inl (Subtype.ext hv)
    · exact Or.inr (Subtype.ext hw)
  arcs_meet_only_at_endpoints := by
    intro v w x y h k s t heq
    rcases D.arcs_meet_only_at_endpoints h k s t heq with he | he | he
    · exact Or.inl ⟨Subtype.ext he.1, Subtype.ext he.2⟩
    · exact Or.inr (Or.inl ⟨Subtype.ext he.1, Subtype.ext he.2⟩)
    · exact Or.inr (Or.inr he)

/-- Reuse the published geometric image on the induced drawing,
including isolated vertices. -/
def PlaneDrawing.trace {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G)
    (S : Set V) : Set Plane :=
  TaitTobin.Outerplanar.drawingImage (D.induced S)

/-- Faces are the connected components of the complement of the actual trace. -/
def PlaneDrawing.faces {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G)
    (S : Set V) : Set (Set Plane) :=
  {F | ∃ p ∉ D.trace S, F = connectedComponentIn (D.trace S)ᶜ p}

/-- Reuse the published unbounded complementary component on an induced
subdrawing. This also has the correct empty-drawing meaning. -/
def PlaneDrawing.outerFace {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G)
    (S : Set V) : Set Plane :=
  TaitTobin.Outerplanar.outerFace (D.induced S)

/-- Vertices incident to the unbounded face in the inherited induced drawing. -/
def PlaneDrawing.boundary {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G)
    (S : Set V) : Set V :=
  {v | v ∈ S ∧ D.vertex v ∈ closure (D.outerFace S)}

/-- Zero-based residuals: `remaining 0` is the source's `H₁`. -/
def PlaneDrawing.remaining {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G) :
    ℕ → Set V
  | 0 => Set.univ
  | n + 1 => D.remaining n \ D.boundary (D.remaining n)

/-- The source's `L_(n+1)`. Residuals need not be connected or isometric. -/
def PlaneDrawing.layer {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G)
    (n : ℕ) : Set V :=
  D.boundary (D.remaining n)

/-- The source's union of all layers preceding `L_(n+1)`. -/
def PlaneDrawing.earlierLayers {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G)
    (n : ℕ) : Set V :=
  (D.remaining n)ᶜ

/-- Exhaustion after at most `k` geometric peeling rounds. At `k = 0`
this permits exactly the empty graph. -/
def IsKOuterplanar {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ D : PlaneDrawing G, D.remaining k = ∅

/-- The successor of a visit in a nonempty cyclic walk. -/
def cyclicNext {m : ℕ} (hm : 0 < m) (j : Fin m) : Fin m :=
  ⟨(j.val + 1) % m, Nat.mod_lt _ hm⟩

/-- A geometric exterior collar for a boundary traversal. For positive radius,
the parameter gives nested simple closed curves in the outer face enclosing
the whole graph. At radius zero it is the prescribed boundary traversal.
This is topological incidence data, with no metric inequalities built in. -/
def IsExteriorCollar {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G)
    (c : ℝ → ℝ → Plane) : Prop :=
  ContinuousOn (Function.uncurry c) (Set.Icc (0, 0) (1, 1)) ∧
  (∀ r ∈ Set.Icc (0 : ℝ) 1, c r 0 = c r 1) ∧
  (∀ r ∈ Set.Ioc (0 : ℝ) 1, Set.InjOn (c r) (Set.Ico 0 1)) ∧
  (∀ r ∈ Set.Ioc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    c r t ∈ D.outerFace Set.univ) ∧
  (∀ r ∈ Set.Ioc (0 : ℝ) 1, ∀ s ∈ Set.Ioc (0 : ℝ) 1,
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ u ∈ Set.Ico (0 : ℝ) 1,
      c r t = c s u → r = s ∧ t = u) ∧
  (∀ r ∈ Set.Ioc (0 : ℝ) 1, ∀ p ∈ D.trace Set.univ,
    Bornology.IsBounded
      (connectedComponentIn ((c r) '' Set.Icc (0 : ℝ) 1)ᶜ p)) ∧
  (c 0) '' Set.Icc (0 : ℝ) 1 = frontier (D.outerFace Set.univ)

/-- One turn around the actual outer facial walk. Repeated vertices are allowed;
each oriented edge is used at most once. An exterior collar fixes the facial
order geometrically, rather than by any distance-difference conclusion.
A one-vertex graph has one stationary boundary visit. -/
structure OuterFacialWalk {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G) where
  size : ℕ
  positive : 0 < size
  vertex : Fin size → V
  covers_boundary : Set.range vertex = D.boundary Set.univ
  steps : ∀ j, G.Adj (vertex j) (vertex (cyclicNext positive j)) ∨
    (∀ v : V, v = vertex j)
  once : ∀ i j, vertex i = vertex j →
    vertex (cyclicNext positive i) = vertex (cyclicNext positive j) → i = j
  collar : ℝ → ℝ → Plane
  exterior : IsExteriorCollar D collar
  traces_edges : ∀ j (h : G.Adj (vertex j) (vertex (cyclicNext positive j)))
    (s : unitInterval),
    collar 0 (((j.val : ℝ) + (s : ℝ)) / (size : ℝ)) =
      D.arc h s
  traces_singleton : ∀ j, (∀ v : V, v = vertex j) →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, collar 0 t = D.vertex (vertex j)

end OuterplanarL1Tan.Linear


