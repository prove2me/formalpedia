-- Prove2me | Definitions.Def_BeyondConvexity_APTAS_Supplement_PolyhedralRegion
-- name    : BeyondConvexity_APTAS_Supplement_PolyhedralRegion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:11:24.590809+00:00
-- url     : https://prove2.me/theorems/0fdfc6f7-b9a2-4b16-af4b-387a28560448
-- title:
--   Rational polyhedral regions in Euclidean space
-- statement:
--   Fix a dimension $d$. A point has $d$ rational coordinates and a simplex has $d+1$ rational vertices. A region is a finite list of these closed simplices, interpreted by their convex hulls and union in Euclidean $\mathbb R^d$. Validity requires full-dimensional simplices, distinct simplices with disjoint interiors meeting in a common face, and a nonempty connected region interior. There is no convexity, boundary manifold, topological or complexity restriction. In particular, cavities and tunnels are allowed.
--
--   The coordinate span $b(P)$ is the maximum coordinate range, $D(P)$ is Euclidean diameter, volume is actual Lebesgue $d$-volume, and translation containment means containment after an arbitrary real translation. A valid class input is a list of normalized regions with coordinate minima zero, each contained in the exact unit hypercube. List positions label occurrences, preserving repeated geometries. Fixed binary natural/list/rational encoders serialize every coordinate, simplex and occurrence; $L$ is the maximum of two and the complete input length, including the dimension. The class is a promise, without a membership algorithm.
--
--   This supplies the dimensional geometric denotations and binary input model; no optimization value is an input.
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), Section 2, printed p.5 / PDF p.6; Section 7, printed p.16 / PDF p.17

import Mathlib
import Definitions.Def_BeyondConvexity_APTAS_PolynomialOn

noncomputable section

open scoped ENNReal

namespace BeyondConvexity.APTAS.Supplement

abbrev RPoint (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev QPoint (d : ℕ) := Fin d → ℚ

def realPoint {d : ℕ} (v : QPoint d) : RPoint d := WithLp.toLp 2 (fun i => (v i : ℝ))

/-- A full-dimensional simplex has d+1 rational vertices; validity is checked below. -/
abbrev QSimplex (d : ℕ) := Fin (d + 1) → QPoint d

def simplexSet {d : ℕ} (s : QSimplex d) : Set (RPoint d) :=
  convexHull ℝ (Set.range fun i => realPoint (s i))

/-- Faces include the empty face and the whole simplex. -/
def IsSimplexFace {d : ℕ} (s : QSimplex d) (F : Set (RPoint d)) : Prop :=
  ∃ A : Finset (Fin (d + 1)), F = convexHull ℝ {realPoint (s i) | i ∈ A}

/-- Raw simplicial input, without any geometric or algorithmic certificate. -/
structure PolyhedralRegion (d : ℕ) where
  simplices : List (QSimplex d)
  deriving Inhabited

def PolyhedralRegion.region {d : ℕ} (P : PolyhedralRegion d) : Set (RPoint d) :=
  ⋃ s ∈ P.simplices, simplexSet s

/-- Ordinary finite simplicial decomposition: full-dimensional simplices,
disjoint interiors, and a common face at every intersection. No boundary
manifold, convexity, topology or complexity restriction is imposed. -/
def PolyhedralRegion.Valid {d : ℕ} (P : PolyhedralRegion d) : Prop :=
  P.simplices.Nodup ∧
  (∀ s ∈ P.simplices, (interior (simplexSet s)).Nonempty) ∧
  (∀ s ∈ P.simplices, ∀ t ∈ P.simplices, s ≠ t →
    Disjoint (interior (simplexSet s)) (interior (simplexSet t)) ∧
    IsSimplexFace s (simplexSet s ∩ simplexSet t) ∧
    IsSimplexFace t (simplexSet s ∩ simplexSet t)) ∧
  IsConnected (interior P.region)

def translate {d : ℕ} (v : RPoint d) (S : Set (RPoint d)) : Set (RPoint d) :=
  (fun x => x + v) '' S

def unitCube (d : ℕ) : Set (RPoint d) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

def PolyhedralRegion.Normalized {d : ℕ} (P : PolyhedralRegion d) : Prop :=
  ∀ i : Fin d, IsLeast ((fun x : RPoint d => x i) '' P.region) 0

def PolyhedralRegion.span {d : ℕ} (P : PolyhedralRegion d) : ℝ :=
  sSup {s | ∃ i : Fin d,
    s = sSup ((fun x : RPoint d => x i) '' P.region) -
      sInf ((fun x : RPoint d => x i) '' P.region)}

/-- Metric.diam here is Euclidean, because RPoint uses EuclideanSpace. -/
def PolyhedralRegion.diameter {d : ℕ} (P : PolyhedralRegion d) : ℝ :=
  Metric.diam P.region

/-- Lebesgue d-volume, kept extended to avoid default real values. -/
def vol {d : ℕ} (S : Set (RPoint d)) : ℝ≥0∞ := MeasureTheory.volume S

def PolyhedralRegion.ContainsTranslate {d : ℕ} (P Q : PolyhedralRegion d) : Prop :=
  ∃ v : RPoint d, translate v P.region ⊆ Q.region

abbrev Instance (d : ℕ) := List (PolyhedralRegion d)

/-- List positions are occurrence labels, including repeated geometries. -/
def InClass {d : ℕ} (I : Instance d) (P : Set (PolyhedralRegion d)) : Prop :=
  ∀ Q ∈ I, Q ∈ P ∧ Q.Valid ∧ Q.Normalized ∧ Q.region ⊆ unitCube d

open RSListDecodingCapacity.AllRates (encNat encList)

def encPoint {d : ℕ} (v : QPoint d) : List Bool :=
  encList AbelianCayleyHDX.encRat (List.ofFn v)

def encSimplex {d : ℕ} (s : QSimplex d) : List Bool :=
  encList encPoint (List.ofFn s)

def encRegion {d : ℕ} (P : PolyhedralRegion d) : List Bool :=
  encList encSimplex P.simplices

def encInstance {d : ℕ} (I : Instance d) : List Bool :=
  encNat d ++ encList encRegion I

def inputLength {d : ℕ} (I : Instance d) : ℕ := max 2 (encInstance I).length

end BeyondConvexity.APTAS.Supplement


