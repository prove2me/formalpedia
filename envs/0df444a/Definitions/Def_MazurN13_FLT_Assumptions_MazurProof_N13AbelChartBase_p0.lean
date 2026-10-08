-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13AbelChartBase_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13AbelChartBase_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:59:43.096102+00:00
-- url     : https://prove2.me/theorems/5cded6d4-58c0-4716-baa3-c7ce20eabeea
-- title:
--   FLT.Assumptions.MazurProof.N13AbelChartBase source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13AbelChartBase

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13AbelChartBase
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13AbelFiberTwoModel_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FormalAbelLinearization_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GeneralizedMumfordReduction_p0

set_option autoImplicit false




/-!
# The nonspecial base divisor for the N13 Abel chart

The integral divisor

`(0,0) + (-1,0)`

has generalized Mumford pair `u = X² + X`, `v = 0`.  Its reduction is the
unordered pair of the sheet-zero points over the distinct affine base
coordinates `0` and `1`.  A canonical hyperelliptic fibre contains one
point on each sheet, so this reduced divisor is noncanonical.

The same base pair satisfies a short Bézout identity.  Hence its graph ideal
is one of the smooth integral Mumford ideals already shown to commute with
reduction.
-/

open Polynomial

namespace MazurProof.N13AbelChartBase

noncomputable section

open N13AbelFiberTwoModel
open N13SymmetricSquareTwo

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  ℤ_[2]

abbrev K : Type :=
  N13AbelFiberTwoModel.K

/-- The special-fibre point `(0,0)`. -/
def p00 : N13AbelFiberTwoModel.CurvePoint :=
  curvePointEquiv.symm (Sum.inl 0, 0)

/-- The special-fibre point `(1,0)`, which is the reduction of `(-1,0)`. -/
def p10 : N13AbelFiberTwoModel.CurvePoint :=
  curvePointEquiv.symm (Sum.inl 1, 0)

/-- Reduction of the selected integral degree-two divisor. -/
def specialBaseDivisor :
    N13SymmetricSquareTwo.EffectiveDivisorTwo :=
  s(p00, p10)

private def sheet
    (P : N13AbelFiberTwoModel.CurvePoint) : K :=
  (curvePointEquiv P).2

@[simp] private theorem sheet_p00 :
    sheet p00 = 0 := by
  simp [sheet, p00]

@[simp] private theorem sheet_p10 :
    sheet p10 = 0 := by
  simp [sheet, p10]

@[simp] private theorem sheet_canonical_zero
    (b : BasePoint) :
    sheet (curvePointEquiv.symm (b, 0)) = 0 := by
  simp [sheet]

@[simp] private theorem sheet_canonical_one
    (b : BasePoint) :
    sheet (curvePointEquiv.symm (b, 1)) = 1 := by
  simp [sheet]

/-- The base divisor is outside the canonical hyperelliptic pencil.  The
proof only compares sheet coordinates; it does not enumerate curve points. -/
theorem specialBaseDivisor_not_canonical :
    ¬IsCanonical specialBaseDivisor := by
  rintro ⟨b, hb⟩
  change
    s(curvePointEquiv.symm (b, 0),
      curvePointEquiv.symm (b, 1)) =
        s(p00, p10) at hb
  rw [Sym2.eq_iff] at hb
  rcases hb with hb | hb
  · have hs := congrArg sheet hb.2
    simp at hs
  · have hs := congrArg sheet hb.2
    simp at hs

/-- Consequently its class in the nineteen-element Abel set is regular. -/
theorem abel_specialBaseDivisor_ne_canonicalClass :
    abel specialBaseDivisor ≠ canonicalClass := by
  intro h
  exact specialBaseDivisor_not_canonical
    ((abel_eq_canonicalClass_iff specialBaseDivisor).1 h)

/-- The smooth integral generalized Mumford datum of the selected base
divisor.  The Bézout certificate is

`(X-1)u + h + 2w = 1`.
-/
def baseSmoothMumford :
    N13GeneralizedMumfordReduction.SmoothMumford₂ where
  u := N13FormalAbelLinearization.uBase
  v := 0
  w := -X ^ 3
  u_monic := N13FormalAbelLinearization.uBase_monic
  curve_eq := by
    simp only [N13GeneralizedMumfordIntegral.hPoly,
      N13GeneralizedMumfordIntegral.rhsPoly,
      N13FormalAbelLinearization.uBase]
    ring
  bezout := by
    refine ⟨X - 1, 1, 2, ?_⟩
    simp only [N13FormalAbelLinearization.uBase,
      N13GeneralizedMumfordIntegral.hPoly]
    ring

@[simp] theorem baseSmoothMumford_u :
    baseSmoothMumford.u =
      N13FormalAbelLinearization.uBase := rfl

@[simp] theorem baseSmoothMumford_v :
    baseSmoothMumford.v = 0 := rfl

/-- The integral base graph reduces to the same polynomial pair
`(X²+X,0)` in characteristic two. -/
theorem reduce_baseSmoothMumford_u :
    (N13GeneralizedMumfordReduction.reduceSmoothMumford
      baseSmoothMumford).u =
        (X ^ 2 + X :
          N13GoodCoordinateRingTwo.K[X]) := by
  simp [baseSmoothMumford,
    N13FormalAbelLinearization.uBase,
    N13GeneralizedMumfordReduction.reducePoly,
    N13GeneralizedMumfordReduction.reduceBase]

@[simp] theorem reduce_baseSmoothMumford_v :
    (N13GeneralizedMumfordReduction.reduceSmoothMumford
      baseSmoothMumford).v = 0 := by
  simp [baseSmoothMumford,
    N13GeneralizedMumfordReduction.reducePoly]

end

end MazurProof.N13AbelChartBase


