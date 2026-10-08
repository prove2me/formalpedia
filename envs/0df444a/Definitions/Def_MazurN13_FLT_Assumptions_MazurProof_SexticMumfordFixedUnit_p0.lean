-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordFixedUnit_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_SexticMumfordFixedUnit_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:08:27.162596+00:00
-- url     : https://prove2.me/theorems/b056096b-0aae-42b7-8ac7-b7c6b129b7f0
-- title:
--   FLT.Assumptions.MazurProof.SexticMumfordFixedUnit source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.SexticMumfordFixedUnit

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordFixedUnit
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordNorm_p0

set_option autoImplicit false




/-!
# Units fixed by hyperelliptic conjugation

In the affine coordinate ring of a smooth monic sextic, a unit fixed by
hyperelliptic conjugation is a scalar.  This is the structural unit lemma
needed to make the fake Mumford--Kummer value independent of principal
ideal representatives.

The proof uses the rank-two basis `p(X) + q(X)Y`.  Conjugation changes the
sign of `q`, so characteristic zero forces `q = 0`.  Applying the same
basis to the inverse of the unit then shows that `p` is already a unit of
the polynomial ring, hence a nonzero constant.
-/

open Polynomial

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

variable (M : Model K)

theorem conjugate_eq_coeffs (z : CoordinateRing M) :
    conjugate M z =
      xClass M (coeff0 M z) -
        xClass M (coeffY M z) * yClass M := by
  conv_lhs =>
    rw [← recompose M z]
  simp only [map_add, map_mul, conjugate_xClass, conjugate_yClass]
  ring

@[simp] theorem coeffY_conjugate (z : CoordinateRing M) :
    coeffY M (conjugate M z) = -(coeffY M z) := by
  rw [conjugate_eq_coeffs]
  simp

variable [CharZero K]

/-- A coordinate-ring unit fixed by hyperelliptic conjugation is induced
by a unique nonzero scalar of the ground field. -/
theorem fixed_coordinate_unit_is_scalar
    (epsilon : (CoordinateRing M)ˣ)
    (hfix : conjugate M (epsilon : CoordinateRing M) = epsilon) :
    ∃ q : Kˣ,
      epsilon =
        Units.map
          (algebraMap K (CoordinateRing M)).toMonoidHom q := by
  let p : K[X] := coeff0 M (epsilon : CoordinateRing M)
  have hYeq := congrArg (coeffY M) hfix
  rw [coeffY_conjugate] at hYeq
  have hY : coeffY M (epsilon : CoordinateRing M) = 0 :=
    CharZero.neg_eq_self_iff.mp hYeq
  have hepsilon :
      (epsilon : CoordinateRing M) = xClass M p := by
    calc
      (epsilon : CoordinateRing M) =
          xClass M (coeff0 M (epsilon : CoordinateRing M)) +
            xClass M (coeffY M (epsilon : CoordinateRing M)) *
              yClass M :=
        (recompose M (epsilon : CoordinateRing M)).symm
      _ = xClass M p := by simp [p, hY]
  let epsilonInv : CoordinateRing M :=
    (epsilon⁻¹ : (CoordinateRing M)ˣ)
  let r : K[X] := coeff0 M epsilonInv
  have hprod :
      (epsilon : CoordinateRing M) * epsilonInv = 1 := by
    simp [epsilonInv]
  have hp : p ≠ 0 := by
    intro hp0
    exact epsilon.ne_zero (by
      rw [hepsilon, hp0, xClass_zero])
  have hinvY : coeffY M epsilonInv = 0 := by
    have hc := congrArg (coeffY M) hprod
    rw [hepsilon, coeffY_xClass_mul] at hc
    have hone :
        coeffY M (1 : CoordinateRing M) = 0 := by
      rw [← xClass_one M, coeffY_xClass]
    rw [hone] at hc
    exact (mul_eq_zero.mp hc).resolve_left hp
  have hepsilonInv :
      epsilonInv = xClass M r := by
    calc
      epsilonInv =
          xClass M (coeff0 M epsilonInv) +
            xClass M (coeffY M epsilonInv) * yClass M :=
        (recompose M epsilonInv).symm
      _ = xClass M r := by simp [r, hinvY]
  have hpr : p * r = 1 := by
    apply xClass_injective M
    calc
      xClass M (p * r) = xClass M p * xClass M r :=
        xClass_mul M p r
      _ = (epsilon : CoordinateRing M) * epsilonInv := by
        rw [hepsilon, hepsilonInv]
      _ = 1 := hprod
      _ = xClass M 1 := (xClass_one M).symm
  have hpunit : IsUnit p := by
    rw [isUnit_iff_exists]
    exact ⟨r, hpr, by simpa [mul_comm] using hpr⟩
  obtain ⟨a, ha, hCa⟩ := Polynomial.isUnit_iff.mp hpunit
  refine ⟨ha.unit, ?_⟩
  apply Units.ext
  change
    (epsilon : CoordinateRing M) =
      algebraMap K (CoordinateRing M) (ha.unit : K)
  rw [hepsilon, ← hCa]
  rw [IsUnit.unit_spec]
  rfl

end

end MazurProof.SexticMumford


