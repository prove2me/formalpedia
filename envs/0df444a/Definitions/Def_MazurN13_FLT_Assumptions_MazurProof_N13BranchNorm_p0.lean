-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13BranchNorm_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13BranchNorm_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:06:25.673889+00:00
-- url     : https://prove2.me/theorems/5cea7597-8bf3-417a-92da-5102f8f13fcf
-- title:
--   FLT.Assumptions.MazurProof.N13BranchNorm source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13BranchNorm

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13BranchNorm
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityAPI_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityMinusAPI_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13LaurentPolynomialOrder_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordBasis_p0

set_option autoImplicit false




/-!
# The two infinity branches and the quadratic norm on `X₁(13)`

For an affine function `p(X) + q(X)Y`, the two Laurent embeddings differ
only in the sign of `Y`.  Their product is therefore the polynomial norm
`p² - q²f`.  This packages the structural reason that the two infinity
orders must be used together: cancellation at one branch is detected by
the other branch.
-/

open Polynomial
open scoped LaurentSeries

namespace MazurProof.N13BranchNorm

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

def evalPoly : K[X] →+* LaurentSeries K :=
  Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K))
    ((N13Infinity.parameter K)⁻¹)

omit [CharZero K] in
@[simp] theorem evalPoly_apply (p : K[X]) :
    evalPoly K p =
      p.eval₂ (algebraMap K (LaurentSeries K))
        ((N13Infinity.parameter K)⁻¹) := rfl

omit [CharZero K] in
theorem evalPoly_eq_evalAtInfinity (p : K[X]) :
    evalPoly K p =
      N13LaurentPolynomialOrder.evalAtInfinity K p := by
  rfl

omit [CharZero K] in
theorem evalPoly_ne_zero {p : K[X]} (hp : p ≠ 0) :
    evalPoly K p ≠ 0 := by
  rw [evalPoly_eq_evalAtInfinity,
    N13LaurentPolynomialOrder.evalAtInfinity_eq_reverse_mul]
  apply mul_ne_zero
  · rw [N13LaurentPolynomialOrder.eval_parameter_eq_ofPowerSeries]
    intro hzero
    apply hp
    apply Polynomial.reverse_eq_zero.mp
    apply Polynomial.coe_injective K
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa using hzero
  · exact pow_ne_zero _
      (inv_ne_zero (N13LaurentPolynomialOrder.parameter_ne_zero K))

omit [CharZero K] in
theorem evalPoly_order (p : K[X]) (hp : p ≠ 0) :
    (evalPoly K p).order = -(p.natDegree : ℤ) := by
  rw [evalPoly_eq_evalAtInfinity]
  exact N13LaurentPolynomialOrder.order_evalAtInfinity K p hp

@[simp] theorem coordinateToLaurent_yClass :
    N13Infinity.coordinateToLaurent K
      (SexticMumford.yClass (N13Mumford.model K)) =
      N13Infinity.ySeries K := by
  change N13Infinity.algebraicToLaurent K
    (N13Infinity.coordinateToAlgebraic K
      (AdjoinRoot.mk
        (SexticMumford.curvePoly (N13Mumford.model K)) X)) = _
  rw [N13Infinity.coordinateToAlgebraic_mk]
  simp only [Polynomial.map_X]
  exact AdjoinRoot.lift_root
    (N13Infinity.curvePolyRat_eval_ySeries K)

def linearFunction (p q : K[X]) : N13Mumford.CoordinateRing K :=
  SexticMumford.xClass (N13Mumford.model K) p +
    SexticMumford.xClass (N13Mumford.model K) q *
      SexticMumford.yClass (N13Mumford.model K)

@[simp] theorem coordinateToLaurent_linearFunction (p q : K[X]) :
    N13Infinity.coordinateToLaurent K (linearFunction K p q) =
      evalPoly K p + evalPoly K q * N13Infinity.ySeries K := by
  simp [linearFunction, coordinateToLaurent_yClass]

@[simp] theorem coordinateToLaurentMinus_linearFunction (p q : K[X]) :
    N13InfinityMinus.coordinateToLaurentMinus K (linearFunction K p q) =
      evalPoly K p - evalPoly K q * N13Infinity.ySeries K := by
  simp [linearFunction, N13InfinityMinus.ySeriesMinus_eq_neg]
  ring

def normNumerator (p q : K[X]) : K[X] :=
  p ^ 2 - q ^ 2 * N13Mumford.f K

theorem branch_product (p q : K[X]) :
    N13Infinity.coordinateToLaurent K (linearFunction K p q) *
        N13InfinityMinus.coordinateToLaurentMinus K
          (linearFunction K p q) =
      evalPoly K (normNumerator K p q) := by
  rw [coordinateToLaurent_linearFunction,
    coordinateToLaurentMinus_linearFunction]
  calc
    (evalPoly K p + evalPoly K q * N13Infinity.ySeries K) *
          (evalPoly K p - evalPoly K q * N13Infinity.ySeries K) =
        evalPoly K p ^ 2 -
          evalPoly K q ^ 2 * N13Infinity.ySeries K ^ 2 := by ring
    _ = evalPoly K p ^ 2 -
          evalPoly K q ^ 2 * evalPoly K (N13Mumford.f K) := by
            have hy :
                N13Infinity.ySeries K ^ 2 =
                  evalPoly K (N13Mumford.f K) := by
              simpa only [evalPoly_apply] using
                N13Infinity.ySeries_sq K
            rw [hy]
    _ = evalPoly K (normNumerator K p q) := by
      simp only [normNumerator, map_sub, map_mul, map_pow]

theorem branch_orders_add (p q : K[X])
    (hnorm : normNumerator K p q ≠ 0) :
    (N13Infinity.coordinateToLaurent K (linearFunction K p q)).order +
        (N13InfinityMinus.coordinateToLaurentMinus K
          (linearFunction K p q)).order =
      -((normNumerator K p q).natDegree : ℤ) := by
  have hproduct :
      N13Infinity.coordinateToLaurent K (linearFunction K p q) *
          N13InfinityMinus.coordinateToLaurentMinus K
            (linearFunction K p q) ≠ 0 := by
    rw [branch_product]
    exact evalPoly_ne_zero K hnorm
  have hplus :
      N13Infinity.coordinateToLaurent K (linearFunction K p q) ≠ 0 :=
    left_ne_zero_of_mul hproduct
  have hminus :
      N13InfinityMinus.coordinateToLaurentMinus K
          (linearFunction K p q) ≠ 0 :=
    right_ne_zero_of_mul hproduct
  calc
    (N13Infinity.coordinateToLaurent K (linearFunction K p q)).order +
          (N13InfinityMinus.coordinateToLaurentMinus K
            (linearFunction K p q)).order =
        (N13Infinity.coordinateToLaurent K (linearFunction K p q) *
          N13InfinityMinus.coordinateToLaurentMinus K
            (linearFunction K p q)).order :=
      (HahnSeries.order_mul hplus hminus).symm
    _ = (evalPoly K (normNumerator K p q)).order := by
      rw [branch_product]
    _ = -((normNumerator K p q).natDegree : ℤ) :=
      evalPoly_order K _ hnorm

theorem normNumerator_eq_coeff_norm
    (z : N13Mumford.CoordinateRing K) :
    normNumerator K
        (SexticMumford.coeff0 (N13Mumford.model K) z)
        (SexticMumford.coeffY (N13Mumford.model K) z) =
      SexticMumford.coeff0 (N13Mumford.model K)
        (SexticMumford.norm (N13Mumford.model K) z) := by
  let p := SexticMumford.coeff0 (N13Mumford.model K) z
  let q := SexticMumford.coeffY (N13Mumford.model K) z
  symm
  calc
    SexticMumford.coeff0 (N13Mumford.model K)
          (SexticMumford.norm (N13Mumford.model K) z) =
        SexticMumford.coeff0 (N13Mumford.model K)
          (SexticMumford.norm (N13Mumford.model K)
            (SexticMumford.xClass (N13Mumford.model K) p +
              SexticMumford.xClass (N13Mumford.model K) q *
                SexticMumford.yClass (N13Mumford.model K))) := by
                  simpa [p, q] using congrArg
                    (fun w => SexticMumford.coeff0
                      (N13Mumford.model K)
                      (SexticMumford.norm (N13Mumford.model K) w))
                    (SexticMumford.recompose
                      (N13Mumford.model K) z).symm
    _ = normNumerator K p q := by
      rw [SexticMumford.norm_recompose,
        SexticMumford.coeff0_xClass]
      rfl

end

end MazurProof.N13BranchNorm


