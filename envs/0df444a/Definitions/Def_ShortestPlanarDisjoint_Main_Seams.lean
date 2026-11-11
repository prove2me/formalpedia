-- Prove2me | Definitions.Def_ShortestPlanarDisjoint_Main_Seams
-- name    : ShortestPlanarDisjoint_Main_Seams
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:23.073469+00:00
-- url     : https://prove2.me/theorems/8798afcc-de59-4e08-9168-e9be2784dea6
-- title:
--   Finite polygonal seams and their geometric disk-cut specification
-- statement:
--   The surface of a signed rotation system is the quotient of its barycentric flag triangles, gluing the side opposite color i by flip i. Isolated capped components are two-spheres. In a connected nontrivial cellular input, replacing each used face by a boundary removes the interior of a polygonal neighbourhood of its face-center star. A spike ends at each assigned terminal corner; distinct occurrences on a repeated boundary walk remain distinct. Isolated corners use a hemisphere meeting their single graph vertex on its boundary.
--
--   A gap is represented by a designated terminal and one side of its spike, covering every terminal-free boundary interval. Finite curves are lists of affine segments with rational barycentric coordinates. The definition of a seam code contains curves, disk-side order, terminal-block lists and gluing bits only. All simplicity, continuity, disjointness, vertex avoidance, transversality, endpoint-gap conditions and disk topology are conclusions in RealizesCut.
--
--   RealizesCut requires a continuous map of a closed triangle onto the punctured surface, mapping its interior bijectively onto the complement of the boundary and seam images, with exactly two preimages on seam interiors and one on other boundary points. Boundary intervals give the two copies of every seam, their identification direction and the actual order of terminal occurrences. PlanarOrder states the source root-track endpoint pattern and exact boundary word (1) after face relabelling. The computed crossing lists contain precisely the transverse junctions through graph-edge interiors. The triangle is a closed disk; this is a topological cut, without a cut-existence field in the input embedding. All runtime outputs are finite codes; the mathematical parametrization is not supplied to a machine.
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Sections 5.1 and 6.1, Lemmas 5.1 and 6.2, p. 30 (PDF p. 32)

import Definitions.Def_ShortestPlanarDisjoint_Main_Embedding
import Definitions.Def_ShortestPlanarDisjoint_Main_StateSignature

set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main
noncomputable section

/-- Closed barycentric triangle, homeomorphic to the closed disk. -/
def TrianglePoint := {x : Fin 3 → ℝ // (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}
instance : TopologicalSpace TrianglePoint := inferInstanceAs (TopologicalSpace {x : Fin 3 → ℝ // (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1})

def triangleInterior : Set TrianglePoint := {p | ∀ i, 0 < p.val i}
def triangleBoundary : Set TrianglePoint := {p | ∃ i, p.val i = 0}

abbrev SpherePoint := {x : EuclideanSpace ℝ (Fin 3) // ‖x‖ = 1}
def sphereNorth : SpherePoint := ⟨PiLp.single 2 (2 : Fin 3) (1 : ℝ), by simp⟩
def sphereSouth : SpherePoint := ⟨PiLp.single 2 (2 : Fin 3) (-1 : ℝ), by simp⟩

namespace RibbonEmbedding
variable {n k : ℕ} {I : RoutingInput n k}

/-- Barycentric triangles are glued along the side opposite color i by flip i.
This constructs the actual topological surface of the signed rotation system. -/
def pointStep (E : RibbonEmbedding I)
    (p q : Fin E.flags × TrianglePoint) : Prop :=
  ∃ i : Fin 3, p.2.val i = 0 ∧ q.1 = E.flip i p.1 ∧ q.2 = p.2

def pointSetoid (E : RibbonEmbedding I) : Setoid (Fin E.flags × TrianglePoint) :=
  Relation.EqvGen.setoid E.pointStep

abbrev Carrier (E : RibbonEmbedding I) :=
  (Quotient E.pointSetoid) ⊕ ({v : Fin n // ∀ u, ¬ I.graph.Adj v u} × SpherePoint)

def point (E : RibbonEmbedding I) (flag : Fin E.flags) (p : TrianglePoint) : E.Carrier :=
  Sum.inl (Quotient.mk _ (flag,p))

end RibbonEmbedding

/-- Rational coordinates make every output curve a finite binary object. -/
structure RationalTrianglePoint where
  coordinate : Fin 3 → ℚ
  nonnegative : ∀ i, 0 ≤ coordinate i
  sum_one : ∑ i, coordinate i = 1

def RationalTrianglePoint.real (p : RationalTrianglePoint) : TrianglePoint :=
  ⟨fun i => p.coordinate i, (fun i => by
    change (0 : ℝ) ≤ (p.coordinate i : ℝ)
    exact_mod_cast p.nonnegative i), by
      change (∑ i, (p.coordinate i : ℝ)) = 1
      exact_mod_cast p.sum_one⟩

def rationalBits (q : ℚ) : List Bool :=
  (decide (q < 0)) :: (numberBits q.num.natAbs ++ numberBits q.den)

def RationalTrianglePoint.bits (p : RationalTrianglePoint) : List Bool :=
  (List.ofFn p.coordinate).flatMap rationalBits

structure SurfaceSegment {n k : ℕ} {I : RoutingInput n k} (E : RibbonEmbedding I) where
  flag : Fin E.flags
  first : RationalTrianglePoint
  last : RationalTrianglePoint

def SurfaceSegment.eval {n k : ℕ} {I : RoutingInput n k} {E : RibbonEmbedding I}
    (s : SurfaceSegment E) (t : unitInterval) : E.Carrier :=
  E.point s.flag ⟨fun i => (1 - (t : ℝ)) * s.first.real.val i + (t : ℝ) * s.last.real.val i,
    (fun i => add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (s.first.real.property.1 i))
      (mul_nonneg t.property.1 (s.last.real.property.1 i))), by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [s.first.real.property.2, s.last.real.property.2]
        ring⟩

structure SurfaceCurve {n k : ℕ} {I : RoutingInput n k} (E : RibbonEmbedding I) where
  length : ℕ
  positive : 0 < length
  segment : Fin length → SurfaceSegment E

/-- Piecewise affine evaluation. All continuity, simplicity and properness
conditions are conclusions in RealizesCut, rather than fields of curve data. -/
def SurfaceCurve.eval {n k : ℕ} {I : RoutingInput n k} {E : RibbonEmbedding I}
    (c : SurfaceCurve E) (t : unitInterval) : E.Carrier :=
  let i : Fin c.length := ⟨min ⌊(t : ℝ) * c.length⌋₊ (c.length-1), by have := c.positive; omega⟩
  let u := max 0 (min 1 ((t : ℝ) * c.length - i.val))
  (c.segment i).eval ⟨u, le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

def SurfaceCurve.bits {n k : ℕ} {I : RoutingInput n k} {E : RibbonEmbedding I}
    (c : SurfaceCurve E) : List Bool :=
  numberBits c.length ++ (List.ofFn c.segment).flatMap fun s =>
    numberBits s.flag.val ++ s.first.bits ++ s.last.bits

namespace FaceInput
variable {n k f : ℕ} {I : RoutingInput n k}

/-- Regular polygonal neighbourhood of the face-center star. A selected corner
adds a triangular spike ending exactly at its assigned terminal. Across a side
opposite color 0 the selected and unselected inequalities agree. Thus repeated
vertices on a facial walk cause no identification of distinct corner spikes. -/
def puncture (E : FaceInput I f) (j : Fin f) : Set E.embedding.Carrier := by
  classical
  exact {x | ∃ flag p, E.embedding.point flag p = x ∧
    (∃ i, E.label i = j ∧ E.embedding.face (E.corner i) = E.embedding.face (.inl flag)) ∧
    (if (∃ i, E.corner i = .inl flag ∨ E.corner i = .inl (E.embedding.flip 1 flag))
      then p.val 1 ≤ p.val 2 else (1/2 : ℝ) ≤ p.val 2)} ∪
    {x | ∃ v : {v : Fin n // ∀ u, ¬ I.graph.Adj v u}, ∃ p : SpherePoint,
      x = .inr (v,p) ∧ 0 ≤ p.val 0 ∧ ∃ i, E.label i = j ∧ E.corner i = .inr v}

def surface (E : FaceInput I f) : Set E.embedding.Carrier :=
  (⋃ j, interior (E.puncture j))ᶜ

def boundary (E : FaceInput I f) : Set E.embedding.Carrier :=
  ⋃ j, frontier (E.puncture j)

def terminalPoint (E : FaceInput I f) (i : Fin (2*k)) (x : E.embedding.Carrier) : Prop :=
  (∃ flag, E.corner i = .inl flag ∧
    x = E.embedding.point flag ⟨![1,0,0], by simp [Fin.forall_fin_succ, Fin.sum_univ_succ]⟩) ∨
    ∃ v, E.corner i = .inr v ∧ x = .inr (v,sphereNorth)

/-- One side of the spike at a designated terminal specifies each terminal-free
boundary gap. Every gap is adjacent to an assigned terminal. -/
structure GapChoice (E : FaceInput I f) where
  terminal : Fin f → Fin (2*k)
  label : ∀ j, E.label (terminal j) = j
  side : Fin f → Bool

def GapChoice.bits {E : FaceInput I f} (gaps : E.GapChoice) : List Bool :=
  (List.finRange f).flatMap fun j => numberBits (gaps.terminal j).val ++ [gaps.side j]

def GapChoice.point {E : FaceInput I f} (gaps : E.GapChoice) (j : Fin f) :
    Option E.embedding.Carrier :=
  match E.corner (gaps.terminal j) with
  | .inr v => some (.inr (v,sphereSouth))
  | .inl flag => some (E.embedding.point
      (if gaps.side j then E.embedding.flip 1 flag else flag)
      ⟨![1/2,1/4,1/4], by norm_num [Fin.forall_fin_succ, Fin.sum_univ_succ]⟩)

/-- A directed facial boundary walk, stopped on its first return. -/
def faceWalk (E : FaceInput I f) (start : Fin E.embedding.flags) :
    ℕ → Fin E.embedding.flags → List (Fin E.embedding.flags)
  | 0, _ => []
  | t+1, current =>
    let next := E.embedding.flip 1 (E.embedding.flip 0 current)
    current :: (if next = start then [] else E.faceWalk start t next)

/-- Terminal order starting just after the selected gap. Each corner is the pair
of flags interchanged by flip 1; repeated vertex occurrences stay distinct. -/
def blockOrder (E : FaceInput I f) (gaps : E.GapChoice) (j : Fin f) : List (Fin (2*k)) := by
  classical
  exact match E.corner (gaps.terminal j) with
  | .inr _ => [gaps.terminal j]
  | .inl flag =>
    let start := if gaps.side j then E.embedding.flip 1 flag else flag
    let flags := E.faceWalk start (E.embedding.flags+1) start
    (flags.tail ++ [start]).filterMap fun flag =>
      (List.finRange (2*k)).find? fun i => E.label i = j ∧
        (E.corner i = .inl flag ∨ E.corner i = .inl (E.embedding.flip 1 flag))

def InGap (E : FaceInput I f) (gaps : E.GapChoice) (j : Fin f)
    (p : E.embedding.Carrier) : Prop :=
  ∃ key, gaps.point j = some key ∧ ∃ S : Set E.embedding.Carrier,
    IsPreconnected S ∧ S ⊆ frontier (E.puncture j) ∧
    (∀ x ∈ S, ∀ i, ¬ E.terminalPoint i x) ∧ key ∈ S ∧ p ∈ S

end FaceInput

/-- Finite output data only. Topology, crossings, gluing, pairing and complexity
are absent from the fields; the source lemmas establish them in RealizesCut. -/
structure SeamCode {n k f : ℕ} {I : RoutingInput n k} (E : FaceInput I f) (r : ℕ) where
  curve : Fin r → SurfaceCurve E.embedding
  layout : DiskLayout k f r
  sameOrder : Fin r → Bool

def SeamCode.bits {n k f r : ℕ} {I : RoutingInput n k} {E : FaceInput I f}
    (S : SeamCode E r) : List Bool :=
  numberBits r ++ (List.ofFn S.curve).flatMap SurfaceCurve.bits ++
  numbersBits (S.layout.sideOrder.flatMap fun side => match side with
    | .inl j => [0,j.val]
    | .inr (s,e) => [1,s.val,if e then 1 else 0]) ++
  (List.finRange f).flatMap (fun j => numbersBits ((S.layout.block j).map Fin.val)) ++
  List.ofFn S.sameOrder

/-- A crossing is a transverse junction of two affine segments across the
opposite-color-2 side. Its coordinates lie strictly inside a primal half-edge. -/
def TransverseJunction {n k : ℕ} {I : RoutingInput n k} {E : RibbonEmbedding I}
    (a b : SurfaceSegment E) : Prop :=
  b.flag = E.flip 2 a.flag ∧ a.last = b.first ∧
  a.last.coordinate 2 = 0 ∧ 0 < a.last.coordinate 0 ∧ 0 < a.last.coordinate 1 ∧
  0 < a.first.coordinate 2 ∧ 0 < b.last.coordinate 2

/-- The ordered lists are computed from the actual curve segments. -/
def SeamCode.crossings {n k f r : ℕ} {I : RoutingInput n k} {E : FaceInput I f}
    (S : SeamCode E r) (s : Fin r) : List (SurfaceSegment E.embedding) := by
  classical
  let segments := List.ofFn (S.curve s).segment
  exact (segments.zip segments.tail).filterMap fun ab =>
    if TransverseJunction ab.1 ab.2 then some ab.1 else none

def SeamCode.crossingCount {n k f r : ℕ} {I : RoutingInput n k} {E : FaceInput I f}
    (S : SeamCode E r) : ℕ := ∑ s, (S.crossings s).length

def GraphEdgeInterior {n k : ℕ} {I : RoutingInput n k} (E : RibbonEmbedding I)
    (x : E.Carrier) : Prop :=
  ∃ flag p, E.point flag p = x ∧ p.val 2 = 0 ∧ p.val 1 > 0

def GraphVertex {n k : ℕ} {I : RoutingInput n k} (E : RibbonEmbedding I)
    (x : E.Carrier) : Prop :=
  (∃ flag, x = E.point flag ⟨![1,0,0], by simp [Fin.forall_fin_succ, Fin.sum_univ_succ]⟩) ∨
    ∃ v, x = .inr (v,sphereNorth)

/-- A mathematical parametrization of the cut. Its existence is a conclusion;
these maps are never supplied to the algorithm. -/
structure CutParameters {n k f : ℕ} {I : RoutingInput n k} (E : FaceInput I f) (r : ℕ) where
  map : TrianglePoint → E.embedding.Carrier
  walk : unitInterval → TrianglePoint
  interval : DiskSide f r → ℝ × ℝ
  direction : Fin r → Bool → Bool

def SeamCode.BoundaryValid {n k f r : ℕ} {I : RoutingInput n k} {E : FaceInput I f}
    (S : SeamCode E r) (W : CutParameters E r) : Prop :=
  let F := W.map
  let walk := W.walk
  let interval := W.interval
  let direction := W.direction
  Continuous F ∧ Set.range F = E.surface ∧
  F ⁻¹' (E.surface \ (E.boundary ∪ ⋃ s, Set.range (S.curve s).eval)) = triangleInterior ∧
  Set.BijOn F triangleInterior
    (E.surface \ (E.boundary ∪ ⋃ s, Set.range (S.curve s).eval)) ∧
  Continuous walk ∧ Set.range walk = triangleBoundary ∧
  walk 0 = walk 1 ∧ Set.InjOn walk {t | (t : ℝ) < 1} ∧
  (∀ side, 0 ≤ (interval side).1 ∧ (interval side).1 < (interval side).2 ∧
    (interval side).2 ≤ 1) ∧
  (∀ side other, S.layout.sideOrder.idxOf side < S.layout.sideOrder.idxOf other →
    (interval side).2 ≤ (interval other).1) ∧
  (∀ j i, i ∈ S.layout.block j ↔ E.label i = j) ∧
  (∀ j i t, E.terminalPoint i (F (walk t)) →
    (E.label i = j ↔ (interval (.inl j)).1 ≤ (t : ℝ) ∧ (t : ℝ) ≤ (interval (.inl j)).2)) ∧
  (∀ j i u t v, E.terminalPoint i (F (walk t)) → E.terminalPoint u (F (walk v)) →
    E.label i = j → E.label u = j →
    ((S.layout.block j).idxOf i < (S.layout.block j).idxOf u ↔ (t : ℝ) < (v : ℝ))) ∧
  (∀ s e (t : unitInterval), ∃ u : unitInterval,
    (u : ℝ) = (1 - (t : ℝ)) * (interval (.inr (s,e))).1 +
      (t : ℝ) * (interval (.inr (s,e))).2 ∧
    F (walk u) = (S.curve s).eval (if direction s e then t else unitInterval.symm t)) ∧
  (∀ s, S.sameOrder s = decide (direction s false = direction s true)) ∧
  (∀ s (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
    (F ⁻¹' {(S.curve s).eval t}).ncard = 2) ∧
  (∀ x ∈ E.boundary \ (⋃ s, {(S.curve s).eval 0, (S.curve s).eval 1}),
    (F ⁻¹' {x}).ncard = 1)

def SeamCode.RealizesCut {n k f r : ℕ} {I : RoutingInput n k} {E : FaceInput I f}
    (S : SeamCode E r) (gaps : E.GapChoice) : Prop :=
  (∀ s, Continuous (S.curve s).eval ∧ Function.Injective (S.curve s).eval ∧
    (∀ t, (S.curve s).eval t ∈ E.surface ∧ ¬ GraphVertex E.embedding ((S.curve s).eval t)) ∧
    (∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → (S.curve s).eval t ∉ E.boundary) ∧
    (∃ j, E.InGap gaps j ((S.curve s).eval 0)) ∧
    (∃ j, E.InGap gaps j ((S.curve s).eval 1)) ∧
    (∀ t, GraphEdgeInterior E.embedding ((S.curve s).eval t) ↔
      ∃ a ∈ S.crossings s, (S.curve s).eval t = a.eval 1)) ∧
  (∀ s u, s ≠ u → Disjoint (Set.range (S.curve s).eval) (Set.range (S.curve u).eval)) ∧
  ∃ W : CutParameters E r, S.BoundaryValid W

/-- The planar root-track construction, including the exact boundary order
(1) after relabelling used faces. It is a conclusion of Lemma 5.1. -/
def SeamCode.PlanarOrder {n k f : ℕ} {I : RoutingInput n k} {E : FaceInput I f}
    (S : SeamCode E (f-1)) (gaps : E.GapChoice) : Prop :=
  ∃ hf : 0 < f, ∃ faceOrder : Equiv.Perm (Fin f),
    (faceOrder ⟨0,hf⟩).val = f-1 ∧
    S.layout.sideOrder = [.inl (faceOrder ⟨0,hf⟩)] ++
      (List.finRange (f-1)).flatMap (fun s =>
        [.inr (s,false), .inl (faceOrder ⟨s.val+1, by omega⟩), .inr (s,true)]) ∧
    ∀ s : Fin (f-1),
      E.InGap gaps (faceOrder ⟨s.val+1, by omega⟩) ((S.curve s).eval 0) ∧
      E.InGap gaps (faceOrder ⟨0,hf⟩) ((S.curve s).eval 1)

/-- Conditional choice asserts neither existence nor computational cost.
The query theorem supplies meaning and computability as conclusions. -/
def SeamCode.parameters {n k f r : ℕ} {I : RoutingInput n k} {E : FaceInput I f}
    (S : SeamCode E r) : Option (CutParameters E r) := by
  classical
  exact if h : ∃ W, S.BoundaryValid W then some (Classical.choose h) else none

end
end ShortestPlanarDisjoint.Main


