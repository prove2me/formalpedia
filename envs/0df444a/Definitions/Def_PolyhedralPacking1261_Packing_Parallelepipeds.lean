-- Prove2me | Definitions.Def_PolyhedralPacking1261_Packing_Parallelepipeds
-- name    : PolyhedralPacking1261_Packing_Parallelepipeds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:28.220352+00:00
-- url     : https://prove2.me/theorems/408578ed-252a-4934-b1ff-4eb1604866e5
-- title:
--   Section 2 — centered bc-parallelepipeds, shadow classes and fan translations
-- statement:
--   For common b,c>0, an object has real a,u,v with a>0 and an integer k. Its centered representative consists of s(a,0,0)+t(u,b,0)+w(v,kb,c), with all three coefficients in the closed interval [-1/2,1/2]. Its shadow class is k, and the shear distance of two objects is |u_i-u_j|+|v_i-v_j|; distinct objects may have zero distance. The standing individual-fit assumptions are a+|u|+|v|≤1, (1+|k|)b≤1, and c≤1. They do not assert simultaneous unit-cube packability.
--   The fan translation of an object in integer block ell, at any real horizontal offset x, is (x,(ell-1+k/2)b,0). Subtraction is real subtraction, and both block and shadow labels may be negative. A translated body is the image under addition of the translation. These are concrete generating-set definitions, without assumed separation properties.
-- source:
--   Simon Bartlmae, Anders Aamand, Mikkel Abrahamsen, Polylogarithmic Approximation for Packing Convex Polyhedra, STOC 2027 submission #1261 (October 2026), canonical PDF SHA-256 b915da2d5fece730ea9946885b05ad09e10e575374e6a1df96e8a6149cb0e67e, §2, PDF pp.6–8 = printed pp.5–7; definitions preceding Lemmas 5 and 6

import Definitions.Def_PolyhedralPacking1261_Packing_Geometry

set_option autoImplicit false

namespace PolyhedralPacking1261.Packing

structure BCParameters where
  a : ℝ
  u : ℝ
  v : ℝ
  k : ℤ

/-- The standing assumptions of Section 2: positive thickness and individual
unit-cube fit. Positive b,c are asserted separately for a common type. -/
def IndividuallyFits (b c : ℝ) (p : BCParameters) : Prop :=
  0 < p.a ∧ p.a + |p.u| + |p.v| ≤ 1 ∧
    (1 + |(p.k : ℝ)|) * b ≤ 1 ∧ c ≤ 1

/-- Centered representative of the source's bc-parallelepiped; all three
coefficients range over the closed interval [-1/2,1/2]. -/
def bcBody (b c : ℝ) (p : BCParameters) : Set Point3 :=
  {x | ∃ s t w : ℝ, |s| ≤ (1 / 2 : ℝ) ∧ |t| ≤ (1 / 2 : ℝ) ∧
    |w| ≤ (1 / 2 : ℝ) ∧
    x = ![s * p.a + t * p.u + w * p.v,
      t * b + w * (p.k : ℝ) * b, w * c]}

def shearDistance (p q : BCParameters) : ℝ :=
  |p.u - q.u| + |p.v - q.v|

def shiftSet (translation : Point3) (S : Set Point3) : Set Point3 :=
  (fun x => x + translation) '' S

noncomputable def fanTranslation (b : ℝ) (p : BCParameters) (x : ℝ) (block : ℤ) : Point3 :=
  ![x, ((block : ℝ) - 1 + (p.k : ℝ) / 2) * b, 0]

end PolyhedralPacking1261.Packing


