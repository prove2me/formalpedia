-- Prove2me | Definitions.Def_HeilbronnTriangle
-- name    : HeilbronnTriangle
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:14.01302+00:00
-- url     : https://prove2.me/theorems/7251c89e-65af-48d7-8840-bab9d032443a
-- statement:
--   This block works in the plane ℝ², with points as pairs of reals. triangleArea(p,q,r) is the usual area |(q₁−p₁)(r₂−p₂)−(q₂−p₂)(r₁−p₁)|/2 of the triangle with vertices p, q, r. pointInUnitSquare(p) means 0≤p₁≤1 and 0≤p₂≤1, and pointsInUnitSquare(P) means every point of the finite set P lies in the closed unit square. triangleAreasAtLeast(P,a) says every triangle formed by three pairwise distinct points of P has area at least a, while hasTriangleAreaAtMost(P,a) says some three pairwise distinct points of P form a triangle of area at most a. Next come constants built from d=41: M=C(4d−1,d)=C(163,41), T=C(M,3), K=T²+1, and heilbronnExponent=1/(100000·K), a tiny positive real number; these are defined but not used in the later predicate. Finally, eventualAlmostUpperBound(ε) is a defined proposition, not an established theorem, for a real ε (with no range restriction imposed). It asserts that there exist a constant C>0 and a threshold n₀ such that for every integer n with n≥n₀ and n≥3, every set P of exactly n points in the unit square contains three distinct points forming a triangle of area at most C·n^(−2+ε). This is a Heilbronn-type upper bound on the smallest triangle area, up to an n^ε loss.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HeilbronnTriangle.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HeilbronnTriangle.lean; bytes 16..1460
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

namespace Problem355

abbrev Point := ℝ × ℝ

def triangleArea (p q r : Point) : ℝ :=
  abs ((q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)) / 2

def pointInUnitSquare (p : Point) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1

def pointsInUnitSquare (P : Finset Point) : Prop := by
  classical
  exact ∀ p, p ∈ P → pointInUnitSquare p

def triangleAreasAtLeast (P : Finset Point) (a : ℝ) : Prop := by
  classical
  exact ∀ p, p ∈ P → ∀ q, q ∈ P → ∀ r, r ∈ P →
    p ≠ q → p ≠ r → q ≠ r → a ≤ triangleArea p q r

def hasTriangleAreaAtMost (P : Finset Point) (a : ℝ) : Prop := by
  classical
  exact ∃ p, p ∈ P ∧ ∃ q, q ∈ P ∧ ∃ r, r ∈ P ∧
    p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ triangleArea p q r ≤ a

def heilbronnD : ℕ := 41

def heilbronnM : ℕ := Nat.choose (4 * heilbronnD - 1) heilbronnD

def heilbronnT : ℕ := Nat.choose heilbronnM 3

def heilbronnK : ℕ := heilbronnT ^ 2 + 1

def heilbronnExponent : ℝ :=
  1 / (100000 * (heilbronnK : ℝ))

def eventualAlmostUpperBound (epsilon : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → 3 ≤ n →
    ∀ P : Finset Point, P.card = n → pointsInUnitSquare P →
      hasTriangleAreaAtMost P
        (C * Real.rpow (n : ℝ) (-2 + epsilon))

attribute [local irreducible] Problem355.heilbronnT
  Problem355.heilbronnM



end Problem355
end
end OAI


