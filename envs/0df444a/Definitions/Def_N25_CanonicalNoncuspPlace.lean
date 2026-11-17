-- Prove2me | Definitions.Def_N25_CanonicalNoncuspPlace
-- name    : N25_CanonicalNoncuspPlace
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:19:33.103862+00:00
-- url     : https://prove2.me/theorems/4c40fd4f-4edc-4b9c-a33c-71382765de00
-- title:
--   The place attached to a noncuspidal rational canonical point
-- statement:
--   This file packages the coordinate and denominator conditions that distinguish the five rational cusps from the dense birational open. For a rational canonical point $[x:y:z:w]$ outside those cusp classes, it defines the associated place by the plane coordinates $$u=x/(y+z-w),   v=x^2/(z(y+z-w))$$ and transports the resulting plane place through the canonical function-field equivalence. This converts a hypothetical noncuspidal rational point into the place used by the modular endgame.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_RationalPointsN25CanonicalPoints
import Definitions.Def_N25_CanonicalUnitPlane
import Definitions.Def_N25_UnitPlanePointPlace
/-! Rational noncuspidal canonical points define places through the explicit birational map.

A rational point of the canonical model outside the five cusp classes has all coordinates nonzero and nonzero
denominators of the birational map; these facts are proved here because the place is defined through that map. -/

/-! ### Boundary points of the canonical model are cusps -/
noncomputable section

/-! Proofs of the lemmas stated in `Theorems.Thm_CanonicalLevelTwentyFive_BoundaryPoints` and their helpers. -/

namespace MazurProof.RationalPointsN25CanonicalPoints

open Polynomial

/-- The canonical cubic is linear in `y` with the displayed coefficient and
constant term. -/
theorem canonicalCubic25_eq_linear (x y z w : ℚ) :
    canonicalCubic25 x y z w =
      y * projectionDenominator25 x z w + projectionNumerator25 x z w := by
  simp only [canonicalCubic25, projectionDenominator25, projectionNumerator25]
  ring

/-- Exact elimination identity behind the plane sextic projection. -/
theorem canonical_elimination_identity25 (x y z w : ℚ) :
    canonicalPlaneSextic25 x z w =
      projectionDenominator25 x z w ^ 2 * canonicalQuadric25 x y z w +
      (projectionNumerator25 x z w -
          projectionDenominator25 x z w * y -
          z * projectionDenominator25 x z w) *
        canonicalCubic25 x y z w := by
  simp only [canonicalPlaneSextic25, projectionDenominator25,
    projectionNumerator25, canonicalQuadric25, canonicalCubic25]
  ring

/-- Every point on the canonical complete intersection projects to the plane
sextic. -/
theorem canonical_point_projects_to_plane_sextic {x y z w : ℚ}
    (hQ : canonicalQuadric25 x y z w = 0)
    (hC : canonicalCubic25 x y z w = 0) :
    canonicalPlaneSextic25 x z w = 0 := by
  rw [canonical_elimination_identity25, hQ, hC]
  ring

/-- Conversely, away from the linear-projection denominator, every rational
point on the plane sextic lifts to the canonical complete intersection. -/
theorem plane_sextic_lifts_to_canonical {x z w : ℚ}
    (hD : projectionDenominator25 x z w ≠ 0)
    (hF : canonicalPlaneSextic25 x z w = 0) :
    canonicalQuadric25 x (recoveredY25 x z w) z w = 0 ∧
      canonicalCubic25 x (recoveredY25 x z w) z w = 0 := by
  have hC : canonicalCubic25 x (recoveredY25 x z w) z w = 0 := by
    rw [canonicalCubic25_eq_linear]
    unfold recoveredY25
    field_simp [hD]
    ring
  refine ⟨?_, hC⟩
  have hid := canonical_elimination_identity25 x (recoveredY25 x z w) z w
  rw [hF, hC, mul_zero, add_zero] at hid
  exact (mul_eq_zero.mp hid.symm).resolve_left (pow_ne_zero 2 hD)

/-- The eliminated coordinate is uniquely recovered from any canonical point
on the nonexceptional projection locus. -/
theorem recoveredY25_eq_of_canonical {x y z w : ℚ}
    (hD : projectionDenominator25 x z w ≠ 0)
    (hC : canonicalCubic25 x y z w = 0) :
    y = recoveredY25 x z w := by
  rw [canonicalCubic25_eq_linear] at hC
  unfold recoveredY25
  field_simp [hD]
  linarith

/-! ## Elementary projective-coordinate helpers -/

private theorem cusp0001_of_coordinates {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hx : x = 0) (hy : y = 0) (hz : z = 0) :
    IsCanonicalCusp25 x y z w := by
  subst x
  subst y
  subst z
  have hw : w ≠ 0 := by simpa [NonzeroQuadruple] using hnz
  exact Or.inl ⟨w, hw, by norm_num, by norm_num, by norm_num, by ring⟩

private theorem cusp0m110_of_coordinates {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hx : x = 0) (hyz : y = -z) (hw : w = 0) :
    IsCanonicalCusp25 x y z w := by
  subst x
  subst y
  subst w
  have hz : z ≠ 0 := by simpa [NonzeroQuadruple] using hnz
  exact Or.inr <| Or.inl ⟨z, hz, by norm_num, by ring, by ring, by norm_num⟩

private theorem cusp1101_of_coordinates {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hy : y = x) (hz : z = 0) (hw : w = x) :
    IsCanonicalCusp25 x y z w := by
  subst y
  subst z
  subst w
  have hx : x ≠ 0 := by simpa [NonzeroQuadruple] using hnz
  exact Or.inr <| Or.inr <| Or.inl
    ⟨x, hx, by ring, by ring, by norm_num, by ring⟩

private theorem cusp0010_of_coordinates {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hx : x = 0) (hy : y = 0) (hw : w = 0) :
    IsCanonicalCusp25 x y z w := by
  subst x
  subst y
  subst w
  have hz : z ≠ 0 := by simpa [NonzeroQuadruple] using hnz
  exact Or.inr <| Or.inr <| Or.inr <| Or.inl
    ⟨z, hz, by norm_num, by norm_num, by ring, by norm_num⟩

private theorem cusp1000_of_coordinates {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hy : y = 0) (hz : z = 0) (hw : w = 0) :
    IsCanonicalCusp25 x y z w := by
  subst y
  subst z
  subst w
  have hx : x ≠ 0 := by simpa [NonzeroQuadruple] using hnz
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr
    ⟨x, hx, by ring, by norm_num, by norm_num, by norm_num⟩

/-! ## The cubic obstruction in the `y = 0` chart -/

/-- The monic cubic `T^3 - T - 1` has no rational root. -/
theorem plastic_cubic_ne_zero (t : ℚ) : t ^ 3 - t - 1 ≠ 0 := by
  intro ht
  let p : ℤ[X] := X ^ 3 - X - 1
  have hp : p.Monic := by
    dsimp [p]
    monicity
    all_goals norm_num
  have heval : Polynomial.aeval t p = 0 := by
    norm_num [p, Polynomial.aeval_def]
    exact ht
  obtain ⟨n, hn, hndvd⟩ :=
    exists_integer_of_is_root_of_monic hp heval
  have hunit : IsUnit n := by
    apply isUnit_of_dvd_one
    have hneg : n ∣ (-1 : ℤ) := by simpa [p] using hndvd
    simpa using hneg.neg_right
  rcases Int.isUnit_iff.mp hunit with hnone | hnneg
  · have htone : t = 1 := by simpa [hnone] using hn
    rw [htone] at ht
    norm_num at ht
  · have htneg : t = -1 := by simpa [hnneg] using hn
    rw [htneg] at ht
    norm_num at ht

/-- A second monic cubic occurring in the exceptional projection locus has no
rational root. -/
theorem projection_cubic_ne_zero (t : ℚ) :
    t ^ 3 - 2 * t ^ 2 + 3 * t - 1 ≠ 0 := by
  intro ht
  let p : ℤ[X] := X ^ 3 - 2 * X ^ 2 + 3 * X - 1
  have hp : p.Monic := by
    dsimp [p]
    monicity
    all_goals norm_num
  have heval : Polynomial.aeval t p = 0 := by
    norm_num [p, Polynomial.aeval_def]
    exact ht
  obtain ⟨n, hn, hndvd⟩ :=
    exists_integer_of_is_root_of_monic hp heval
  have hunit : IsUnit n := by
    apply isUnit_of_dvd_one
    have hneg : n ∣ (-1 : ℤ) := by simpa [p] using hndvd
    simpa using hneg.neg_right
  rcases Int.isUnit_iff.mp hunit with hnone | hnneg
  · have htone : t = 1 := by simpa [hnone] using hn
    rw [htone] at ht
    norm_num at ht
  · have htneg : t = -1 := by simpa [hnneg] using hn
    rw [htneg] at ht
    norm_num at ht

/-! ## Classification on the four coordinate hyperplanes -/

/-- Every rational canonical point on the hyperplane `w = 0` is a cusp. -/
theorem canonical_point_w_zero_is_cusp {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hQ : canonicalQuadric25 x y z w = 0)
    (hC : canonicalCubic25 x y z w = 0)
    (hw : w = 0) :
    IsCanonicalCusp25 x y z w := by
  subst w
  have hxyz : x * y * z = 0 := by
    simpa [canonicalCubic25] using hC
  rcases mul_eq_zero.mp hxyz with hxy | hz
  · rcases mul_eq_zero.mp hxy with hx | hy
    · have hyfac : y * (y + z) = 0 := by
        simp only [canonicalQuadric25, hx, zero_mul, neg_zero] at hQ
        nlinarith
      rcases mul_eq_zero.mp hyfac with hy | hyz
      · exact cusp0010_of_coordinates hnz hx hy rfl
      · have hyneg : y = -z := by linarith
        exact cusp0m110_of_coordinates hnz hx hyneg rfl
    · have hxz : x * z = 0 := by
        simp only [canonicalQuadric25, hy, zero_mul, add_zero] at hQ
        nlinarith
      rcases mul_eq_zero.mp hxz with hx | hz
      · exact cusp0010_of_coordinates hnz hx hy rfl
      · exact cusp1000_of_coordinates hnz hy hz rfl
  · have hy : y = 0 := by
      simp only [canonicalQuadric25, hz, mul_zero, add_zero] at hQ
      nlinarith [sq_nonneg y]
    exact cusp1000_of_coordinates hnz hy hz rfl

/-- Every rational canonical point on the hyperplane `z = 0` is a cusp. -/
theorem canonical_point_z_zero_is_cusp {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hQ : canonicalQuadric25 x y z w = 0)
    (hC : canonicalCubic25 x y z w = 0)
    (hz : z = 0) :
    IsCanonicalCusp25 x y z w := by
  subst z
  have hC' : x ^ 2 * w - x * y * w = 0 := by
    simpa [canonicalCubic25] using hC
  have hprod : x * w * (x - y) = 0 := by
    linear_combination hC'
  rcases mul_eq_zero.mp hprod with hxw | hxy
  · rcases mul_eq_zero.mp hxw with hx | hw
    · have hy : y = 0 := by
        simp only [canonicalQuadric25, hx, zero_mul, neg_zero] at hQ
        nlinarith [sq_nonneg y]
      exact cusp0001_of_coordinates hnz hx hy rfl
    · have hy : y = 0 := by
        simp only [canonicalQuadric25, hw, mul_zero, add_zero] at hQ
        nlinarith [sq_nonneg y]
      exact cusp1000_of_coordinates hnz hy rfl hw
  · have hy : y = x := by linarith
    have hxw : x * (x - w) = 0 := by
      simp only [canonicalQuadric25, hy] at hQ
      nlinarith
    rcases mul_eq_zero.mp hxw with hx | hxw
    · have hy0 : y = 0 := by rw [hy, hx]
      exact cusp0001_of_coordinates hnz hx hy0 rfl
    · have hw : w = x := by linarith
      exact cusp1101_of_coordinates hnz hy rfl hw

/-- Every rational canonical point on the hyperplane `x = 0` is a cusp. -/
theorem canonical_point_x_zero_is_cusp {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hQ : canonicalQuadric25 x y z w = 0)
    (hC : canonicalCubic25 x y z w = 0)
    (hx : x = 0) :
    IsCanonicalCusp25 x y z w := by
  subst x
  have hC' : y * z * w + z ^ 2 * w - z * w ^ 2 = 0 := by
    simpa [canonicalCubic25] using hC
  have hprod : z * w * (y + z - w) = 0 := by
    linear_combination hC'
  rcases mul_eq_zero.mp hprod with hzw | hyzw
  · rcases mul_eq_zero.mp hzw with hz | hw
    · have hy : y = 0 := by
        simp only [canonicalQuadric25, hz, mul_zero, add_zero] at hQ
        nlinarith [sq_nonneg y]
      exact cusp0001_of_coordinates hnz rfl hy hz
    · have hyfac : y * (y + z) = 0 := by
        simp only [canonicalQuadric25, hw, mul_zero, add_zero] at hQ
        nlinarith
      rcases mul_eq_zero.mp hyfac with hy | hyz
      · exact cusp0010_of_coordinates hnz rfl hy hw
      · have hyneg : y = -z := by linarith
        exact cusp0m110_of_coordinates hnz rfl hyneg hw
  · have hwzero : w = 0 := by
      have hyzw' : y + z = w := by linarith
      have hQ' : y ^ 2 + y * z + z * w = 0 := by
        simpa [canonicalQuadric25] using hQ
      rw [← hyzw'] at hQ'
      have hsum : y + z = 0 := by nlinarith [sq_nonneg (y + z)]
      linarith
    have hyfac : y * (y + z) = 0 := by
      simp only [canonicalQuadric25, hwzero, mul_zero, add_zero] at hQ
      nlinarith
    rcases mul_eq_zero.mp hyfac with hy | hyz
    · exact cusp0010_of_coordinates hnz rfl hy hwzero
    · have hyneg : y = -z := by linarith
      exact cusp0m110_of_coordinates hnz rfl hyneg hwzero

/-- Every rational canonical point on the hyperplane `y = 0` is a cusp.

After the easy component `w = 0`, elimination of `x` from the two equations
gives

`z * (z^3 - w^2*z - w^3) = 0`.

The second factor would make `z/w` a rational root of `T^3 - T - 1`. -/
theorem canonical_point_y_zero_is_cusp {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hQ : canonicalQuadric25 x y z w = 0)
    (hC : canonicalCubic25 x y z w = 0)
    (hy : y = 0) :
    IsCanonicalCusp25 x y z w := by
  subst y
  by_cases hw : w = 0
  · exact canonical_point_w_zero_is_cusp hnz hQ hC hw
  have hQ' : -x * z - x * w + z * w = 0 := by
    simpa [canonicalQuadric25] using hQ
  have hC' : x ^ 2 * w - x * z * w + z ^ 2 * w - z * w ^ 2 = 0 := by
    simpa [canonicalCubic25] using hC
  have hinner : x ^ 2 - x * z + z ^ 2 - z * w = 0 := by
    have hfactor : w * (x ^ 2 - x * z + z ^ 2 - z * w) = 0 := by
      linear_combination hC'
    exact (mul_eq_zero.mp hfactor).resolve_left hw
  have hres : z * (z ^ 3 - w ^ 2 * z - w ^ 3) = 0 := by
    linear_combination
      ((w + z) * x - z ^ 2) * hQ' + (w + z) ^ 2 * hinner
  rcases mul_eq_zero.mp hres with hz | hhom
  · have hx : x = 0 := by
      rw [hz] at hQ'
      norm_num at hQ'
      exact hQ'.resolve_right hw
    exact cusp0001_of_coordinates hnz hx rfl hz
  · have hroot : (z / w) ^ 3 - z / w - 1 = 0 := by
      field_simp [hw]
      nlinarith
    exact False.elim ((plastic_cubic_ne_zero (z / w)) hroot)

/-- A rational point on the canonical model with a zero homogeneous
coordinate is one of the five rational cusps. -/
theorem canonical_point_with_zero_coordinate_is_cusp {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hQ : canonicalQuadric25 x y z w = 0)
    (hC : canonicalCubic25 x y z w = 0)
    (hzero : x = 0 ∨ y = 0 ∨ z = 0 ∨ w = 0) :
    IsCanonicalCusp25 x y z w := by
  rcases hzero with hx | hy | hz | hw
  · exact canonical_point_x_zero_is_cusp hnz hQ hC hx
  · exact canonical_point_y_zero_is_cusp hnz hQ hC hy
  · exact canonical_point_z_zero_is_cusp hnz hQ hC hz
  · exact canonical_point_w_zero_is_cusp hnz hQ hC hw

/-- Contrapositive form used by later affine/descent reductions: every
noncuspidal rational point has all four coordinates nonzero. -/
theorem all_coordinates_ne_zero_of_not_cusp {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hQ : canonicalQuadric25 x y z w = 0)
    (hC : canonicalCubic25 x y z w = 0)
    (hncusp : ¬ IsCanonicalCusp25 x y z w) :
    x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ w ≠ 0 := by
  constructor
  · intro hx
    exact hncusp (canonical_point_with_zero_coordinate_is_cusp hnz hQ hC (Or.inl hx))
  constructor
  · intro hy
    exact hncusp (canonical_point_with_zero_coordinate_is_cusp hnz hQ hC (Or.inr (Or.inl hy)))
  constructor
  · intro hz
    exact hncusp
      (canonical_point_with_zero_coordinate_is_cusp hnz hQ hC (Or.inr (Or.inr (Or.inl hz))))
  · intro hw
    exact hncusp
      (canonical_point_with_zero_coordinate_is_cusp hnz hQ hC (Or.inr (Or.inr (Or.inr hw))))

/-- The plane-sextic projection denominator cannot vanish at a noncuspidal
rational point.  Indeed, simultaneous vanishing of the denominator and the
canonical cubic eliminates `x` to

`z * (z^3 - 2*w*z^2 + 3*w^2*z - w^3) = 0`.

On the dense torus the first factor is nonzero, while the second factor would
give a rational root of `T^3 - 2*T^2 + 3*T - 1`. -/
theorem projectionDenominator25_ne_zero_of_not_cusp {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hQ : canonicalQuadric25 x y z w = 0)
    (hC : canonicalCubic25 x y z w = 0)
    (hncusp : ¬ IsCanonicalCusp25 x y z w) :
    projectionDenominator25 x z w ≠ 0 := by
  obtain ⟨_hx, _hy, hz, hw⟩ :=
    all_coordinates_ne_zero_of_not_cusp hnz hQ hC hncusp
  intro hD
  have hD' : x * z - x * w + z * w = 0 := by
    simpa [projectionDenominator25] using hD
  have hdecomp :
      y * projectionDenominator25 x z w +
        w * (x ^ 2 - x * z + z ^ 2 - z * w) = 0 := by
    change y * projectionDenominator25 x z w +
      projectionNumerator25 x z w = 0
    rw [← canonicalCubic25_eq_linear]
    exact hC
  have hwi : w * (x ^ 2 - x * z + z ^ 2 - z * w) = 0 := by
    simpa only [hD, mul_zero, zero_add] using hdecomp
  have hinner : x ^ 2 - x * z + z ^ 2 - z * w = 0 :=
    (mul_eq_zero.mp hwi).resolve_left hw
  have hres :
      z * (z ^ 3 - 2 * w * z ^ 2 + 3 * w ^ 2 * z - w ^ 3) = 0 := by
    linear_combination
      ((w - z) * x + z ^ 2) * hD' + (w - z) ^ 2 * hinner
  have hhom : z ^ 3 - 2 * w * z ^ 2 + 3 * w ^ 2 * z - w ^ 3 = 0 :=
    (mul_eq_zero.mp hres).resolve_left hz
  have hroot :
      (z / w) ^ 3 - 2 * (z / w) ^ 2 + 3 * (z / w) - 1 = 0 := by
    field_simp [hw]
    nlinarith
  exact (projection_cubic_ne_zero (z / w)) hroot

/-- Dense-open birational reduction: every hypothetical noncuspidal canonical
point projects to the plane sextic on its nonexceptional locus, and its fourth
coordinate `y` is recovered by the explicit rational formula. -/
theorem noncuspidal_point_to_plane_sextic {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hQ : canonicalQuadric25 x y z w = 0)
    (hC : canonicalCubic25 x y z w = 0)
    (hncusp : ¬ IsCanonicalCusp25 x y z w) :
    canonicalPlaneSextic25 x z w = 0 ∧
      projectionDenominator25 x z w ≠ 0 ∧
      y = recoveredY25 x z w := by
  have hD := projectionDenominator25_ne_zero_of_not_cusp hnz hQ hC hncusp
  exact ⟨canonical_point_projects_to_plane_sextic hQ hC, hD,
    recoveredY25_eq_of_canonical hD hC⟩

end MazurProof.RationalPointsN25CanonicalPoints

end

/-! ### Denominators of the birational map at noncuspidal points -/
noncomputable section

/-! Noncuspidal rational canonical points lie in the open used by the birational formulas. -/
namespace N25
open Polynomial

/-- The first birational denominator cannot vanish when x and z are nonzero. -/
theorem canonicalDenominator_ne_zero {k : Type*} [Field k] {x y z w : k}
    (hx : x ≠ 0) (hz : z ≠ 0)
    (hq : canonicalQuadric x y z w = 0) (hc : canonicalCubic x y z w = 0) :
    canonicalDenominator y z w ≠ 0 := by
  intro ha
  unfold canonicalDenominator at ha
  have hw : w = y+z := by linear_combination -ha
  rw [hw] at hq hc
  unfold canonicalQuadric at hq
  unfold canonicalCubic at hc
  have hxy : x*z*(x-y) = 0 := by linear_combination -x*hq-hc
  have hxy' : x = y := sub_eq_zero.mp ((mul_eq_zero.mp hxy).resolve_left (mul_ne_zero hx hz))
  subst y
  have hz2 : z^2 = 0 := by linear_combination hq
  exact (pow_ne_zero 2 hz) hz2

/-- The reverse-composition multiplier is nonzero at rational points with x,z nonzero. -/
theorem canonicalMultiplier_ne_zero {x y z w : ℚ}
    (hx : x ≠ 0) (hz : z ≠ 0)
    (hq : canonicalQuadric x y z w = 0) (hc : canonicalCubic x y z w = 0) :
    canonicalMultiplier x y z w ≠ 0 := by
  have ha := canonicalDenominator_ne_zero hx hz hq hc
  intro hb
  let a := canonicalDenominator y z w
  have hid : z*(x^2-z*a+a^2) - y*canonicalMultiplier x y z w =
      -x*canonicalQuadric x y z w-canonicalCubic x y z w := by
    dsimp [a, canonicalMultiplier, canonicalDenominator, canonicalQuadric, canonicalCubic]
    ring
  rw [hb, hq, hc] at hid
  have hpoly : x^2-z*a+a^2 = 0 := by
    have hm : z*(x^2-z*a+a^2) = 0 := by simpa using hid
    exact (mul_eq_zero.mp hm).resolve_left hz
  have hb' : x*z+z*a+x*a = 0 := hb
  have hcum : x^3+x^2*a+2*x*a^2+a^3 = 0 := by
    linear_combination (x+a)*hpoly+a*hb'
  apply planeCubicBranch_ne_zero (x/a)
  have ha' : a ≠ 0 := ha
  field_simp [ha']
  linear_combination hcum

/-- The September noncusp classification supplies every denominator of the canonical open. -/
theorem canonical_noncuspidal_denominators {x y z w : ℚ}
    (hnz : MazurProof.RationalPointsN25CanonicalPoints.NonzeroQuadruple x y z w)
    (hq : canonicalQuadric x y z w = 0) (hc : canonicalCubic x y z w = 0)
    (hnc : ¬ MazurProof.RationalPointsN25CanonicalPoints.IsCanonicalCusp25 x y z w) :
    x ≠ 0 ∧ z ≠ 0 ∧ canonicalDenominator y z w ≠ 0 ∧ canonicalMultiplier x y z w ≠ 0 := by
  have h := MazurProof.RationalPointsN25CanonicalPoints.all_coordinates_ne_zero_of_not_cusp
    hnz hq hc hnc
  exact ⟨h.1, h.2.2.1, canonicalDenominator_ne_zero h.1 h.2.2.1 hq hc,
    canonicalMultiplier_ne_zero h.1 h.2.2.1 hq hc⟩

end N25

end

/-! ### The place -/
noncomputable section
namespace N25

/-- The place of a rational canonical point outside the five cusp classes. -/
def canonicalNoncuspPlace25 (x y z w : ℚ)
    (hnz : MazurProof.RationalPointsN25CanonicalPoints.NonzeroQuadruple x y z w)
    (hq : canonicalQuadric x y z w = 0) (hc : canonicalCubic x y z w = 0)
    (hnc : ¬ MazurProof.RationalPointsN25CanonicalPoints.IsCanonicalCusp25 x y z w) :
    AlgebraicCurve.Place ℚ (CanonicalFF25 ℚ) :=
  let h := canonical_noncuspidal_denominators hnz hq hc hnc
  canonicalPointPlaceOfUnitPlane25 (x/canonicalDenominator y z w)
    (x^2/(z*canonicalDenominator y z w))
    (canonical_maps_to_plane x y z w h.1 h.2.2.1 h.2.1 hq hc)
    (div_ne_zero h.1 h.2.2.1)

end N25


