-- Prove2me | Definitions.Def_TriangularCovering
-- name    : TriangularCovering
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:34.875229+00:00
-- url     : https://prove2.me/theorems/4b4bb154-a592-48fc-909b-6ee372a60a99
-- statement:
--   Working in Euclidean 3-space, H=√2 and point(x,y,t) is the vector (x,y,Ht). K is the solid set of all point(x,y,t) with 0≤t≤1, |x|≤1−t and |y|≤t. For a unit vector u, projection(u,z) is z minus its component along u, i.e. orthogonal projection onto the plane perpendicular to u. Area is the real value of 2-dimensional Hausdorff measure, shadowArea(u) is the area of the projection of K along u, and A_min is the infimum of shadowArea(u) over all unit vectors u. A TriCylinder consists of a unit axis vector and a base set whose points are all perpendicular to the axis, where the base is the convex hull of three affinely independent points (a nondegenerate triangle), is compact, convex and measurable, and has finite 2-dimensional Hausdorff measure; its carrier is the infinite cylinder of all points b+r·axis with b in the base and r real. A family of m tri-cylinders Covers if every point of K lies in the carrier of at least one member. totalArea is the sum of the base areas, and relativeCost is the sum over members of base area divided by shadowArea of that member's axis. With n(ε)=⌈2/ε²⌉, the defined proposition MainAsymptotic says there exist δ>0 and C>0 such that for every 0<ε<δ there is a covering family of 2n(ε) tri-cylinders with |totalArea/H − (1/2 − (13/6000)ε²)| ≤ Cε⁴ and totalArea < A_min/2. The defined proposition NormalizedCounterexample says that for some m there is a covering family of m tri-cylinders with relativeCost < 1/2. Both are propositions, not established theorems.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TriangularCovering.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TriangularCovering.lean; bytes 16..2015
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

abbrev Space := EuclideanSpace ℝ (Fin 3)

def H : ℝ := Real.sqrt 2

def point (x y t : ℝ) : Space := !₂[x, y, H * t]

def K : Set Space :=
  {z | ∃ x y t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ |x| ≤ 1 - t ∧ |y| ≤ t ∧ z = point x y t}

def projection (u z : Space) : Space := z - (inner ℝ u z) • u

def area (B : Set Space) : ℝ := (Measure.euclideanHausdorffMeasure 2 B).toReal

def shadowArea (u : Space) : ℝ := area (projection u '' K)

def A_min : ℝ := sInf {a : ℝ | ∃ u : Space, ‖u‖ = 1 ∧ a = shadowArea u}

structure TriCylinder where
  axis : Space
  base : Set Space
  unit_axis : ‖axis‖ = 1
  perpendicular : ∀ z ∈ base, inner ℝ axis z = 0
  triangular : ∃ v : Fin 3 → Space, AffineIndependent ℝ v ∧
    base = convexHull ℝ (Set.range v)
  compact : IsCompact base
  convex : Convex ℝ base
  measurable : MeasurableSet base
  finite_area : Measure.euclideanHausdorffMeasure 2 base ≠ ⊤

def TriCylinder.carrier (c : TriCylinder) : Set Space :=
  {z | ∃ b ∈ c.base, ∃ r : ℝ, z = b + r • c.axis}

def Covers {m : ℕ} (c : Fin m → TriCylinder) : Prop :=
  ∀ z ∈ K, ∃ i : Fin m, z ∈ (c i).carrier

def totalArea {m : ℕ} (c : Fin m → TriCylinder) : ℝ :=
  ∑ i : Fin m, area (c i).base

def relativeCost {m : ℕ} (c : Fin m → TriCylinder) : ℝ :=
  ∑ i : Fin m, area (c i).base / shadowArea (c i).axis

def n (ε : ℝ) : ℕ := ⌈2 / ε ^ 2⌉₊

def MainAsymptotic : Prop :=
  ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
    ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ c : Fin (2 * n ε) → TriCylinder,
        Covers c ∧
        |totalArea c / H - (1 / 2 - (13 / 6000 : ℝ) * ε ^ 2)| ≤ C * ε ^ 4 ∧
        totalArea c < A_min / 2

def NormalizedCounterexample : Prop :=
  ∃ m : ℕ, ∃ c : Fin m → TriCylinder, Covers c ∧ relativeCost c < 1 / 2



end TriangularCovering
end
end OAI


