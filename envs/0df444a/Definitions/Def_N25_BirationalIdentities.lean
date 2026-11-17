-- Prove2me | Definitions.Def_N25_BirationalIdentities
-- name    : N25_BirationalIdentities
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:55.161588+00:00
-- url     : https://prove2.me/theorems/7f0791ca-3861-48cc-ac57-923ab460e968
-- title:
--   Polynomial certificates for the canonical–plane birational maps
-- statement:
--   This file is principally a certificate suite rather than a new carrier definition. It records the pullbacks of the canonical quadric and cubic under the plane parametrization, denominator and coordinate identities, homogeneous scaling laws, and the cleared reverse-substitution formulas over commutative rings and fields. These identities certify that the plane and canonical rational maps are mutually inverse on their common principal open.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalUnitPlane
/-! Integral certificates and inverse formulas for the canonical and plane models. -/
namespace N25

section Ring
variable {k : Type*} [CommRing k]

/-- The plane relation pulls back the canonical quadric with the indicated factor. -/
theorem plane_quadric (u v : k) :
    canonicalQuadric (planeX u v) (planeY u v) (planeZ u v) (planeW u v) =
      u * planeRelation u v := by
  unfold canonicalQuadric planeX planeY planeZ planeW planeDenominator planeRelation
  ring

/-- The plane relation pulls back the canonical cubic with the indicated factor. -/
theorem plane_cubic (u v : k) :
    canonicalCubic (planeX u v) (planeY u v) (planeZ u v) (planeW u v) =
      -u^2*v*planeDenominator u v*planeRelation u v := by
  unfold canonicalCubic planeX planeY planeZ planeW planeDenominator planeRelation
  ring

theorem plane_denominator (u v : k) :
    canonicalDenominator (planeY u v) (planeZ u v) (planeW u v) =
      v * planeDenominator u v := by
  unfold canonicalDenominator planeY planeZ planeW planeDenominator
  ring

theorem plane_x_certificate (u v : k) :
    planeX u v = u * canonicalDenominator (planeY u v) (planeZ u v) (planeW u v) := by
  rw [plane_denominator]; unfold planeX; ring

theorem plane_v_certificate (u v : k) :
    (planeX u v)^2 = v * planeZ u v *
      canonicalDenominator (planeY u v) (planeZ u v) (planeW u v) := by
  rw [plane_denominator]; unfold planeX planeZ; ring

theorem reverse_y_certificate (x y z w : k) :
    reverseY x y z w - y * canonicalMultiplier x y z w =
      -x * canonicalQuadric x y z w - canonicalCubic x y z w := by
  unfold reverseY canonicalMultiplier canonicalDenominator canonicalQuadric canonicalCubic
  ring

theorem reverse_w_certificate (x y z w : k) :
    reverseW x y z w - w * canonicalMultiplier x y z w =
      -x * canonicalQuadric x y z w - canonicalCubic x y z w := by
  unfold reverseW canonicalMultiplier canonicalDenominator canonicalQuadric canonicalCubic
  ring

theorem reverse_x_certificate (x y z w : k) :
    reverseX x y z w - x * canonicalMultiplier x y z w = 0 := by
  unfold reverseX; ring

theorem reverse_z_certificate (x y z w : k) :
    reverseZ x y z w - z * canonicalMultiplier x y z w = 0 := by
  unfold reverseZ; ring

theorem canonicalQuadric_smul (t x y z w : k) :
    canonicalQuadric (t*x) (t*y) (t*z) (t*w) = t^2*canonicalQuadric x y z w := by
  unfold canonicalQuadric; ring

theorem plane_maps_to_canonical (u v : k) (h : planeRelation u v = 0) :
    canonicalQuadric (planeX u v) (planeY u v) (planeZ u v) (planeW u v) = 0 ∧
    canonicalCubic (planeX u v) (planeY u v) (planeZ u v) (planeW u v) = 0 := by
  rw [plane_quadric, plane_cubic, h]; simp

/-- Reverse substitution over a ring, with an explicitly specified inverse of z. -/
theorem canonical_substitution_of_inverse (x y z w r : k)
    (ha : canonicalDenominator y z w = 1) (hz : z*r = 1) :
    let u := x
    let v := x^2*r
    let s := x^3*r^2
    planeX u v = s*reverseX x y z w ∧
    planeY u v = s*reverseY x y z w ∧
    planeZ u v = s*reverseZ x y z w ∧
    planeW u v = s*reverseW x y z w := by
  have hd : planeDenominator x (x^2*r) = x*r*canonicalMultiplier x y z w := by
    unfold planeDenominator canonicalMultiplier
    rw [ha]
    linear_combination -(x^2+x)*hz
  dsimp only
  constructor
  · unfold planeX reverseX
    rw [hd]
    ring
  constructor
  · unfold planeY reverseY
    rw [ha]
    linear_combination x^3*(z*r+1-r*(x^2+1))*hz
  constructor
  · unfold planeZ reverseZ
    rw [hd]
    linear_combination -x^3*r*canonicalMultiplier x y z w*hz
  · unfold planeW reverseW
    rw [ha]
    linear_combination -x^4*(z*r+1+x*r)*hz

/-- The reverse substitution satisfies R without any domain assumption. -/
theorem canonical_maps_to_plane_of_inverse (x y z w r i : k)
    (ha : canonicalDenominator y z w = 1) (hz : z*r = 1) (hx : x*i = 1)
    (hq : canonicalQuadric x y z w = 0) (hc : canonicalCubic x y z w = 0) :
    planeRelation x (x^2*r) = 0 := by
  have hy := reverse_y_certificate x y z w
  have hw := reverse_w_certificate x y z w
  rw [hq, hc] at hy hw
  have hy' : reverseY x y z w = y*canonicalMultiplier x y z w := by linear_combination hy
  have hw' : reverseW x y z w = w*canonicalMultiplier x y z w := by linear_combination hw
  have h := canonical_substitution_of_inverse x y z w r ha hz
  dsimp only at h
  rcases h with ⟨hX,hY,hZ,hW⟩
  rw [hy'] at hY
  rw [hw'] at hW
  unfold reverseX at hX
  unfold reverseZ at hZ
  have heX : planeX x (x^2*r) = (x^3*r^2*canonicalMultiplier x y z w)*x := by rw [hX]; ring
  have heY : planeY x (x^2*r) = (x^3*r^2*canonicalMultiplier x y z w)*y := by rw [hY]; ring
  have heZ : planeZ x (x^2*r) = (x^3*r^2*canonicalMultiplier x y z w)*z := by rw [hZ]; ring
  have heW : planeW x (x^2*r) = (x^3*r^2*canonicalMultiplier x y z w)*w := by rw [hW]; ring
  have hp := plane_quadric x (x^2*r)
  rw [heX,heY,heZ,heW,canonicalQuadric_smul,hq,mul_zero] at hp
  calc
    planeRelation x (x^2*r) = (x*i)*planeRelation x (x^2*r) := by rw [hx,one_mul]
    _ = i*(x*planeRelation x (x^2*r)) := by ring
    _ = 0 := by rw [← hp,mul_zero]

/-- The cubic scales by the third power of a common coordinate factor. -/
theorem canonicalCubic_smul (t x y z w : k) :
    canonicalCubic (t*x) (t*y) (t*z) (t*w) = t^3*canonicalCubic x y z w := by
  unfold canonicalCubic; ring

/-- Normalizing A=1 preserves both canonical equations on the plane open. -/
theorem plane_normalized_equations (u v h : k)
    (hi : u*v*planeDenominator u v*h = 1) (hr : planeRelation u v = 0) :
    let s := u*h
    let y := s*planeY u v
    let z := s*planeZ u v
    let w := s*planeW u v
    canonicalQuadric u y z w = 0 ∧ canonicalCubic u y z w = 0 ∧
    canonicalDenominator y z w = 1 ∧
    canonicalMultiplier u y z w = u^2*(planeDenominator u v)^2*h := by
  have hx : (u*h)*planeX u v = u := by
    unfold planeX
    linear_combination u*hi
  have hq := plane_quadric u v
  have hc := plane_cubic u v
  rw [hr,mul_zero] at hq hc
  dsimp only
  constructor
  · conv_lhs => arg 1; rw [← hx]
    rw [canonicalQuadric_smul,hq,mul_zero]
  constructor
  · conv_lhs => arg 1; rw [← hx]
    rw [canonicalCubic_smul,hc,mul_zero]
  have ha : canonicalDenominator ((u*h)*planeY u v) ((u*h)*planeZ u v)
      ((u*h)*planeW u v) = 1 := by
    unfold canonicalDenominator planeY planeZ planeW planeDenominator at *
    linear_combination hi
  constructor
  · exact ha
  · unfold canonicalMultiplier
    rw [ha]
    unfold planeZ planeDenominator at *
    linear_combination -u*hi

/-- Normalization of the reverse composition is the identity in every commutative ring. -/
theorem canonical_normalized_inverse (x y z w r s : k)
    (ha : canonicalDenominator y z w = 1) (hz : z*r = 1)
    (hq : canonicalQuadric x y z w = 0) (hc : canonicalCubic x y z w = 0)
    (hs : x*(x^2*r)*planeDenominator x (x^2*r)*s = 1) :
    x*s*planeY x (x^2*r) = y ∧ x*s*planeZ x (x^2*r) = z ∧
    x*s*planeW x (x^2*r) = w := by
  have hd : planeDenominator x (x^2*r) = x*r*canonicalMultiplier x y z w := by
    unfold planeDenominator canonicalMultiplier
    rw [ha]
    linear_combination -(x^2+x)*hz
  rw [hd] at hs
  have hy := reverse_y_certificate x y z w
  have hw := reverse_w_certificate x y z w
  rw [hq,hc] at hy hw
  have hy' : reverseY x y z w = y*canonicalMultiplier x y z w := by linear_combination hy
  have hw' : reverseW x y z w = w*canonicalMultiplier x y z w := by linear_combination hw
  have h := canonical_substitution_of_inverse x y z w r ha hz
  dsimp only at h
  rw [hy'] at h
  rw [hw'] at h
  rcases h with ⟨_,hY,hZ,hW⟩
  unfold reverseZ at hZ
  constructor
  · linear_combination x*s*hY + y*hs
  constructor
  · linear_combination x*s*hZ + z*hs
  · linear_combination x*s*hW + w*hs

end Ring

section Field
variable {k : Type*} [Field k]

/-- The two rational functions recover the plane coordinates on their common open. -/
theorem plane_inverse (u v : k) (hu : u ≠ 0) (hv : v ≠ 0)
    (hd : planeDenominator u v ≠ 0) :
    planeX u v / canonicalDenominator (planeY u v) (planeZ u v) (planeW u v) = u ∧
    (planeX u v)^2 / (planeZ u v *
      canonicalDenominator (planeY u v) (planeZ u v) (planeW u v)) = v := by
  rw [plane_denominator]
  unfold planeX planeZ
  constructor <;> field_simp [hu, hv, hd]

/-- Clearing the canonical denominators gives the four integral reverse numerators. -/
theorem canonical_substitution (x y z w : k)
    (ha : canonicalDenominator y z w ≠ 0) (hz : z ≠ 0) :
    let a := canonicalDenominator y z w
    let u := x/a
    let v := x^2/(z*a)
    let s := x^3/(z^2*a^4)
    planeX u v = s*reverseX x y z w ∧
    planeY u v = s*reverseY x y z w ∧
    planeZ u v = s*reverseZ x y z w ∧
    planeW u v = s*reverseW x y z w := by
  dsimp only
  unfold planeX planeY planeZ planeW planeDenominator reverseX reverseY reverseZ reverseW
    canonicalMultiplier
  generalize canonicalDenominator y z w = a at *
  constructor
  · field_simp [ha, hz]
  constructor
  · field_simp [ha, hz]
  constructor <;> field_simp [ha, hz]

/-- The reverse map is projectively the identity on the canonical complete intersection. -/
theorem canonical_inverse (x y z w : k)
    (ha : canonicalDenominator y z w ≠ 0) (hz : z ≠ 0)
    (hq : canonicalQuadric x y z w = 0) (hc : canonicalCubic x y z w = 0) :
    let a := canonicalDenominator y z w
    let u := x/a
    let v := x^2/(z*a)
    let t := x^3*canonicalMultiplier x y z w/(z^2*a^4)
    planeX u v = t*x ∧ planeY u v = t*y ∧
    planeZ u v = t*z ∧ planeW u v = t*w := by
  have hy := reverse_y_certificate x y z w
  have hw := reverse_w_certificate x y z w
  rw [hq, hc] at hy hw
  have hy' : reverseY x y z w = y*canonicalMultiplier x y z w := by linear_combination hy
  have hw' : reverseW x y z w = w*canonicalMultiplier x y z w := by linear_combination hw
  have h := canonical_substitution x y z w ha hz
  dsimp only at h ⊢
  rcases h with ⟨hX, hY, hZ, hW⟩
  rw [hy'] at hY
  rw [hw'] at hW
  unfold reverseX at hX
  unfold reverseZ at hZ
  constructor
  · rw [hX]; ring
  constructor
  · rw [hY]; ring
  constructor
  · rw [hZ]; ring
  · rw [hW]; ring

/-- A canonical point with nonzero x, z and denominator satisfies the plane relation. -/
theorem canonical_maps_to_plane (x y z w : k) (hx : x ≠ 0)
    (ha : canonicalDenominator y z w ≠ 0) (hz : z ≠ 0)
    (hq : canonicalQuadric x y z w = 0) (hc : canonicalCubic x y z w = 0) :
    planeRelation (x/canonicalDenominator y z w)
      (x^2/(z*canonicalDenominator y z w)) = 0 := by
  have h := canonical_inverse x y z w ha hz hq hc
  dsimp only at h
  rcases h with ⟨hX, hY, hZ, hW⟩
  have hp := plane_quadric (x/canonicalDenominator y z w)
    (x^2/(z*canonicalDenominator y z w))
  rw [hX, hY, hZ, hW, canonicalQuadric_smul, hq, mul_zero] at hp
  exact (mul_eq_zero.mp hp.symm).resolve_left (div_ne_zero hx ha)

end Field
end N25


