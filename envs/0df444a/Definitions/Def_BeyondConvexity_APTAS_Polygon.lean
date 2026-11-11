-- Prove2me | Definitions.Def_BeyondConvexity_APTAS_Polygon
-- name    : BeyondConvexity_APTAS_Polygon
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:07:31.116981+00:00
-- url     : https://prove2.me/theorems/121f4d26-477f-41fe-8f8b-e44ab913ac9c
-- title:
--   Rational polygonal regions with holes
-- statement:
--   A polygonal region is specified by one rational outer boundary cycle and a finite list of rational inner boundary cycles. Every cycle is simple and has at least three distinct vertices. The closed inner regions are pairwise disjoint and lie in the interior of the outer region. The region retains all boundaries and removes precisely the interiors of the holes. Valid regions are compact, connected, have nonempty interior, and are the closure of their interiors.
--
--   The boundary is a union of line segments. Filling uses the bounded complementary component of this boundary, so nonconvex regions and holes are retained. No bound is imposed on the number of vertices or holes. Normalized input regions have minimum coordinates zero and lie in the unit square. Area is planar Lebesgue measure; diameter is Euclidean and span is the larger coordinate span. Translation containment means that some translation of the first region is a subset of the second.
--
--   These definitions provide the geometric objects shared by all packing statements. **Formalization Note** The ambient product type has the sup metric, so Euclidean distance is defined explicitly by the square-root formula before taking diameter.
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/890.pdf, Section 2, printed p.5 / PDF p.6, equations (1)–(2); Appendix D.3, printed p.28 / PDF p.29 (closure of interior).

import Mathlib

noncomputable section

namespace BeyondConvexity.APTAS

abbrev QPoint := ℚ × ℚ
abbrev Point := ℝ × ℝ

def QPoint.real (p : QPoint) : Point := (p.1, p.2)

/-- A boundary cycle, stored without a repeated closing vertex. -/
abbrev Cycle := List QPoint

def Cycle.vertex (c : Cycle) (i : ℕ) : Point :=
  (c.getD (i % c.length) (0, 0)).real

def Cycle.edge (c : Cycle) (i : ℕ) : Set Point :=
  segment ℝ (c.vertex i) (c.vertex (i + 1))

def Cycle.boundary (c : Cycle) : Set Point :=
  ⋃ i ∈ Finset.range c.length, c.edge i

/-- Simple closed polygonal boundary: distinct vertices and no extra edge intersections. -/
def Cycle.Simple (c : Cycle) : Prop :=
  3 ≤ c.length ∧ c.Nodup ∧
    ∀ i < c.length, ∀ j < c.length, i ≠ j →
      c.edge i ∩ c.edge j ⊆
        ({c.vertex i, c.vertex (i + 1)} ∩ {c.vertex j, c.vertex (j + 1)})

/-- Fill the bounded complementary component of a simple cycle, retaining its boundary.
This uses the actual polygonal curve, not its convex hull. -/
def Cycle.filled (c : Cycle) : Set Point :=
  c.boundary ∪ {x | x ∉ c.boundary ∧
    Bornology.IsBounded (connectedComponentIn c.boundaryᶜ x)}

/-- Raw finite rational polygonal boundary representation; holes have no fixed bound. -/
structure Polygon where
  outer : Cycle
  holes : List Cycle
  deriving Inhabited

def Polygon.region (P : Polygon) : Set Point :=
  P.outer.filled \ ⋃ c ∈ P.holes, interior c.filled

/-- Section 2's compact, connected, non-degenerate polygonal region with simple,
pairwise disjoint holes strictly inside its outer boundary. -/
def Polygon.Valid (P : Polygon) : Prop :=
  P.outer.Simple ∧ (∀ c ∈ P.holes, c.Simple) ∧
    P.holes.Pairwise (fun c d => Disjoint c.filled d.filled) ∧
    (∀ c ∈ P.holes, c.filled ⊆ interior P.outer.filled) ∧
    IsCompact P.region ∧ IsConnected P.region ∧
    (interior P.region).Nonempty ∧ closure (interior P.region) = P.region

def square (a : ℝ) : Set Point := Set.Icc 0 a ×ˢ Set.Icc 0 a

def translate (v : Point) (S : Set Point) : Set Point :=
  (fun x => x + v) '' S

def Polygon.Normalized (P : Polygon) : Prop :=
  P.region ⊆ {p | 0 ≤ p.1 ∧ 0 ≤ p.2} ∧
    (∃ p ∈ P.region, p.1 = 0) ∧ (∃ p ∈ P.region, p.2 = 0)

def Polygon.InputValid (P : Polygon) : Prop :=
  P.Valid ∧ P.Normalized ∧ P.region ⊆ square 1

def area (S : Set Point) : ℝ := (MeasureTheory.volume S).toReal

/-- Euclidean distance, explicitly distinct from the sup metric on the product type. -/
def euclideanDistance (p q : Point) : ℝ :=
  Real.sqrt ((p.1 - q.1)^2 + (p.2 - q.2)^2)

def Polygon.diameter (P : Polygon) : ℝ :=
  sSup {d | ∃ p ∈ P.region, ∃ q ∈ P.region, d = euclideanDistance p q}

def Polygon.span (P : Polygon) : ℝ :=
  max (sSup (Prod.fst '' P.region) - sInf (Prod.fst '' P.region))
    (sSup (Prod.snd '' P.region) - sInf (Prod.snd '' P.region))

def Polygon.ContainsTranslate (P Q : Polygon) : Prop :=
  ∃ v : Point, translate v P.region ⊆ Q.region

end BeyondConvexity.APTAS


