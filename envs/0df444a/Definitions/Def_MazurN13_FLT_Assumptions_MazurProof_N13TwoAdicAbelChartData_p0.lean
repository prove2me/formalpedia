-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicAbelChartData_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicAbelChartData_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:00:53.511001+00:00
-- url     : https://prove2.me/theorems/f3c15244-47ac-48f8-83be-a2d4ae9c64d2
-- title:
--   FLT.Assumptions.MazurProof.N13TwoAdicAbelChartData source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13TwoAdicAbelChartData

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TwoAdicAbelChartData
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GeneralizedMumfordReduction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FormalAbelLinearization_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicDisks_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicKernelChart_p0
import Mathlib.Algebra.Polynomial.RingDivision

set_option autoImplicit false




/-!
# Integral Mumford data on the nonspecial N13 two-adic Abel chart

A point in the residue disk of `(0,0)` and a point in the residue disk of
`(-1,0)` have distinct `x`-coordinates by a unit.  Lagrange interpolation
therefore gives an integral graph polynomial through the two points.

The product of the two linear factors divides the curve residual.  The same
interpolation argument, applied to the inverses of the two vertical
derivatives, gives the smoothness Bezout identity.  Thus every such pair
defines smooth generalized Mumford data over `ℤ₂`, without a search through
congruence classes.
-/

open Polynomial

namespace MazurProof.N13TwoAdicAbelChartData

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  ℤ_[2]

abbrev maximal : Ideal R₂ :=
  N13TwoAdicDisks.maximal

/-- A pair of points in the two residue disks used by the nonspecial chart.
The `y`-coordinates are the canonical Hensel lifts and are therefore not
stored separately. -/
structure DiskPair where
  x₀ : R₂
  x₁ : R₂
  x₀_mem : x₀ ∈ maximal
  x₁_add_one_mem : x₁ + 1 ∈ maximal

/-- The distinguished pair `(0,0)+(-1,0)`. -/
def basePair : DiskPair where
  x₀ := 0
  x₁ := -1
  x₀_mem := maximal.zero_mem
  x₁_add_one_mem := by simp

namespace DiskPair

variable (P : DiskPair)

theorem reduceBase_eq_zero_of_mem
    {a : R₂} (ha : a ∈ maximal) :
    N13GeneralizedMumfordReduction.reduceBase a = 0 := by
  apply RingHom.mem_ker.mp
  rw [N13GeneralizedMumfordReduction.reduceBase,
    PadicInt.ker_toZMod]
  exact ha

@[simp] theorem reduceBase_x₀ :
    N13GeneralizedMumfordReduction.reduceBase P.x₀ = 0 :=
  reduceBase_eq_zero_of_mem P.x₀_mem

@[simp] theorem reduceBase_x₁ :
    N13GeneralizedMumfordReduction.reduceBase P.x₁ = 1 := by
  have hsum :
    N13GeneralizedMumfordReduction.reduceBase P.x₁ + 1 = 0 := by
    simpa only [map_add, map_one] using
      reduceBase_eq_zero_of_mem P.x₁_add_one_mem
  simpa only [CharTwo.neg_eq] using
    eq_neg_of_add_eq_zero_left hsum

def y₀ : R₂ :=
  N13TwoAdicDisks.zeroDiskY P.x₀ P.x₀_mem

def y₁ : R₂ :=
  N13TwoAdicDisks.negOneDiskY P.x₁ P.x₁_add_one_mem

@[simp] theorem basePair_y₀ :
    basePair.y₀ = 0 :=
  N13TwoAdicDisks.zeroDiskY_zero

@[simp] theorem basePair_y₁ :
    basePair.y₁ = 0 :=
  N13TwoAdicDisks.negOneDiskY_negOne

theorem y₀_spec :
    N13GoodModelTwo.AffineEquation P.x₀ P.y₀ ∧
      P.y₀ ∈ maximal :=
  N13TwoAdicDisks.zeroDiskY_spec P.x₀ P.x₀_mem

theorem y₁_spec :
    N13GoodModelTwo.AffineEquation P.x₁ P.y₁ ∧
      P.y₁ ∈ maximal :=
  N13TwoAdicDisks.negOneDiskY_spec P.x₁ P.x₁_add_one_mem

@[simp] theorem reduceBase_y₀ :
    N13GeneralizedMumfordReduction.reduceBase P.y₀ = 0 :=
  reduceBase_eq_zero_of_mem P.y₀_spec.2

@[simp] theorem reduceBase_y₁ :
    N13GeneralizedMumfordReduction.reduceBase P.y₁ = 0 :=
  reduceBase_eq_zero_of_mem P.y₁_spec.2

theorem x₁_sub_x₀_isUnit :
    IsUnit (P.x₁ - P.x₀) := by
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_neg_one
  have h :=
    maximal.sub_mem P.x₁_add_one_mem P.x₀_mem
  convert h using 1
  ring

theorem cross_x₁_sub_x₀_isUnit (Q : DiskPair) :
    IsUnit (P.x₁ - Q.x₀) := by
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_neg_one
  have h :=
    maximal.sub_mem P.x₁_add_one_mem Q.x₀_mem
  convert h using 1
  ring

/-- The inverse of the unit separating the two `x`-coordinates. -/
def deltaInv : R₂ :=
  ↑((P.x₁_sub_x₀_isUnit).unit⁻¹)

theorem deltaInv_mul_delta :
    P.deltaInv * (P.x₁ - P.x₀) = 1 := by
  rw [← (P.x₁_sub_x₀_isUnit).unit_spec]
  exact Units.inv_mul _

/-- The integral linear interpolant taking values `a₀,a₁` at the two
selected `x`-coordinates. -/
def interpolate (a₀ a₁ : R₂) : R₂[X] :=
  C a₀ +
    C (P.deltaInv * (a₁ - a₀)) * (X - C P.x₀)

@[simp] theorem interpolate_eval_x₀ (a₀ a₁ : R₂) :
    (P.interpolate a₀ a₁).eval P.x₀ = a₀ := by
  simp [interpolate]

@[simp] theorem interpolate_eval_x₁ (a₀ a₁ : R₂) :
    (P.interpolate a₀ a₁).eval P.x₁ = a₁ := by
  simp only [interpolate, eval_add, eval_C, eval_mul, eval_sub,
    eval_X]
  calc
    a₀ + P.deltaInv * (a₁ - a₀) * (P.x₁ - P.x₀) =
        a₀ + (a₁ - a₀) *
          (P.deltaInv * (P.x₁ - P.x₀)) := by ring
    _ = a₁ := by rw [P.deltaInv_mul_delta]; ring

/-- The monic polynomial cutting out the two selected affine points. -/
def u : R₂[X] :=
  (X - C P.x₀) * (X - C P.x₁)

/-- The graph polynomial through the two selected affine points. -/
def v : R₂[X] :=
  P.interpolate P.y₀ P.y₁

@[simp] theorem basePair_u :
    basePair.u =
      N13FormalAbelLinearization.uBase := by
  simp [u, basePair, N13FormalAbelLinearization.uBase]
  ring

@[simp] theorem basePair_v :
    basePair.v = 0 := by
  change basePair.interpolate basePair.y₀ basePair.y₁ = 0
  rw [basePair_y₀, basePair_y₁]
  simp [interpolate]

theorem u_monic : P.u.Monic := by
  exact (monic_X_sub_C P.x₀).mul (monic_X_sub_C P.x₁)

@[simp] theorem u_eval_x₀ :
    P.u.eval P.x₀ = 0 := by
  simp [u]

@[simp] theorem u_eval_x₁ :
    P.u.eval P.x₁ = 0 := by
  simp [u]

@[simp] theorem v_eval_x₀ :
    P.v.eval P.x₀ = P.y₀ :=
  P.interpolate_eval_x₀ P.y₀ P.y₁

@[simp] theorem v_eval_x₁ :
    P.v.eval P.x₁ = P.y₁ :=
  P.interpolate_eval_x₁ P.y₀ P.y₁

/-- The generalized-hyperelliptic residual after restriction to the graph
`Y=v(X)`. -/
def curveError : R₂[X] :=
  P.v ^ 2 +
      N13GeneralizedMumfordIntegral.hPoly * P.v -
    N13GeneralizedMumfordIntegral.rhsPoly

@[simp] theorem curveError_eval_x₀ :
    P.curveError.eval P.x₀ = 0 := by
  have hcurve := P.y₀_spec.1
  rw [N13GoodModelTwo.affineEquation_iff_residual] at hcurve
  simpa [curveError, N13GoodModelTwo.affineResidual,
    N13GoodModelTwo.h, N13GoodModelTwo.rhs,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly] using hcurve

@[simp] theorem curveError_eval_x₁ :
    P.curveError.eval P.x₁ = 0 := by
  have hcurve := P.y₁_spec.1
  rw [N13GoodModelTwo.affineEquation_iff_residual] at hcurve
  simpa [curveError, N13GoodModelTwo.affineResidual,
    N13GoodModelTwo.h, N13GoodModelTwo.rhs,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly] using hcurve

theorem u_dvd_curveError :
    P.u ∣ P.curveError := by
  have h₀ : X - C P.x₀ ∣ P.curveError := by
    rw [dvd_iff_isRoot, IsRoot]
    exact P.curveError_eval_x₀
  have h₁ : X - C P.x₁ ∣ P.curveError := by
    rw [dvd_iff_isRoot, IsRoot]
    exact P.curveError_eval_x₁
  have hprod :=
    (isCoprime_X_sub_C_of_isUnit_sub
      P.x₁_sub_x₀_isUnit).mul_dvd h₁ h₀
  simpa [u, mul_comm] using hprod

def w : R₂[X] :=
  Classical.choose P.u_dvd_curveError

theorem curve_eq :
    P.v ^ 2 +
        N13GeneralizedMumfordIntegral.hPoly * P.v -
      N13GeneralizedMumfordIntegral.rhsPoly =
        P.u * P.w :=
  Classical.choose_spec P.u_dvd_curveError

/-- The vertical derivative `2v+h` restricted to the graph. -/
def verticalDerivative : R₂[X] :=
  2 * P.v + N13GeneralizedMumfordIntegral.hPoly

@[simp] theorem verticalDerivative_eval_x₀ :
    P.verticalDerivative.eval P.x₀ =
      2 * P.y₀ + N13GoodModelTwo.h P.x₀ := by
  simp [verticalDerivative, N13GeneralizedMumfordIntegral.hPoly,
    N13GoodModelTwo.h]

@[simp] theorem verticalDerivative_eval_x₁ :
    P.verticalDerivative.eval P.x₁ =
      2 * P.y₁ + N13GoodModelTwo.h P.x₁ := by
  simp [verticalDerivative, N13GeneralizedMumfordIntegral.hPoly,
    N13GoodModelTwo.h]

theorem verticalDerivative_eval_x₀_isUnit :
    IsUnit (P.verticalDerivative.eval P.x₀) := by
  rw [P.verticalDerivative_eval_x₀]
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal
    (N13TwoAdicDisks.h_isUnit_of_mem_zeroDisk P.x₀_mem)
  have h := maximal.mul_mem_left (2 : R₂) P.y₀_spec.2
  convert h using 1
  ring

theorem verticalDerivative_eval_x₁_isUnit :
    IsUnit (P.verticalDerivative.eval P.x₁) := by
  rw [P.verticalDerivative_eval_x₁]
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal
    (N13TwoAdicDisks.h_isUnit_of_mem_negOneDisk
      P.x₁_add_one_mem)
  have h := maximal.mul_mem_left (2 : R₂) P.y₁_spec.2
  convert h using 1
  ring

def derivativeInv₀ : R₂ :=
  ↑((P.verticalDerivative_eval_x₀_isUnit).unit⁻¹)

def derivativeInv₁ : R₂ :=
  ↑((P.verticalDerivative_eval_x₁_isUnit).unit⁻¹)

@[simp] theorem derivativeInv₀_mul :
    P.derivativeInv₀ * P.verticalDerivative.eval P.x₀ = 1 := by
  rw [← (P.verticalDerivative_eval_x₀_isUnit).unit_spec]
  exact Units.inv_mul _

@[simp] theorem derivativeInv₁_mul :
    P.derivativeInv₁ * P.verticalDerivative.eval P.x₁ = 1 := by
  rw [← (P.verticalDerivative_eval_x₁_isUnit).unit_spec]
  exact Units.inv_mul _

/-- Interpolate the inverses of the two vertical derivatives. -/
def derivativeInverse : R₂[X] :=
  P.interpolate P.derivativeInv₀ P.derivativeInv₁

@[simp] theorem derivativeInverse_mul_eval_x₀ :
    (P.derivativeInverse * P.verticalDerivative).eval P.x₀ = 1 := by
  rw [eval_mul, derivativeInverse, P.interpolate_eval_x₀,
    P.derivativeInv₀_mul]

@[simp] theorem derivativeInverse_mul_eval_x₁ :
    (P.derivativeInverse * P.verticalDerivative).eval P.x₁ = 1 := by
  rw [eval_mul, derivativeInverse, P.interpolate_eval_x₁,
    P.derivativeInv₁_mul]

theorem u_dvd_derivativeInverse_mul_sub_one :
    P.u ∣ P.derivativeInverse * P.verticalDerivative - 1 := by
  have h₀ :
      X - C P.x₀ ∣
        P.derivativeInverse * P.verticalDerivative - 1 := by
    rw [dvd_iff_isRoot, IsRoot]
    rw [eval_sub, P.derivativeInverse_mul_eval_x₀, eval_one,
      sub_self]
  have h₁ :
      X - C P.x₁ ∣
        P.derivativeInverse * P.verticalDerivative - 1 := by
    rw [dvd_iff_isRoot, IsRoot]
    rw [eval_sub, P.derivativeInverse_mul_eval_x₁, eval_one,
      sub_self]
  have hprod :=
    (isCoprime_X_sub_C_of_isUnit_sub
      P.x₁_sub_x₀_isUnit).mul_dvd h₁ h₀
  simpa [u, mul_comm] using hprod

def bezoutQuotient : R₂[X] :=
  Classical.choose P.u_dvd_derivativeInverse_mul_sub_one

theorem bezoutQuotient_spec :
    P.derivativeInverse * P.verticalDerivative - 1 =
      P.u * P.bezoutQuotient :=
  Classical.choose_spec P.u_dvd_derivativeInverse_mul_sub_one

/-- The two-disk divisor supplies smooth integral generalized Mumford data. -/
def smoothMumford :
    N13GeneralizedMumfordReduction.SmoothMumford₂ where
  u := P.u
  v := P.v
  w := P.w
  u_monic := P.u_monic
  curve_eq := P.curve_eq
  bezout := by
    refine
      ⟨-P.bezoutQuotient, P.derivativeInverse, 0, ?_⟩
    rw [show
      2 * P.v +
          N13GeneralizedMumfordIntegral.hPoly =
        P.verticalDerivative by rfl]
    have h := P.bezoutQuotient_spec
    have hb :
        P.derivativeInverse * P.verticalDerivative =
          P.u * P.bezoutQuotient + 1 :=
      sub_eq_iff_eq_add.mp h
    rw [hb]
    ring

@[simp] theorem smoothMumford_u :
    P.smoothMumford.u = P.u := rfl

@[simp] theorem smoothMumford_v :
    P.smoothMumford.v = P.v := rfl

@[simp] theorem reducePoly_u :
    N13GeneralizedMumfordReduction.reducePoly P.u =
      (X ^ 2 + X :
        N13GoodCoordinateRingTwo.K[X]) := by
  rw [N13GeneralizedMumfordReduction.reducePoly_apply]
  simp only [u, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C,
    P.reduceBase_x₀, P.reduceBase_x₁, C_0, C_1, sub_zero]
  rw [CharTwo.sub_eq_add]
  ring

@[simp] theorem reducePoly_v :
    N13GeneralizedMumfordReduction.reducePoly P.v = 0 := by
  rw [N13GeneralizedMumfordReduction.reducePoly_apply]
  simp [v, interpolate]

/-- Every divisor in the two-disk chart reduces to the fixed nonspecial
Mumford pair `(X²+X,0)`. -/
theorem reduce_smoothMumford :
    (N13GeneralizedMumfordReduction.reduceSmoothMumford
      P.smoothMumford).u =
        (X ^ 2 + X :
          N13GoodCoordinateRingTwo.K[X]) ∧
      (N13GeneralizedMumfordReduction.reduceSmoothMumford
        P.smoothMumford).v = 0 := by
  exact ⟨P.reducePoly_u, P.reducePoly_v⟩

/-- The monic divisor polynomial remembers the ordered pair because the two
roots lie in disjoint residue disks. -/
theorem u_injective :
    Function.Injective DiskPair.u := by
  intro P Q hPQ
  have hQ₀ : Q.u.eval P.x₀ = 0 := by
    rw [← hPQ]
    exact P.u_eval_x₀
  have hprod₀ :
      (P.x₀ - Q.x₀) * (P.x₀ - Q.x₁) = 0 := by
    simpa [u] using hQ₀
  have hright : P.x₀ - Q.x₁ ≠ 0 := by
    intro hzero
    apply (Q.cross_x₁_sub_x₀_isUnit P).ne_zero
    calc
      Q.x₁ - P.x₀ = -(P.x₀ - Q.x₁) := by ring
      _ = 0 := by rw [hzero]; simp
  have hx₀ : P.x₀ = Q.x₀ :=
    sub_eq_zero.mp
      ((mul_eq_zero.mp hprod₀).resolve_right hright)
  have hQ₁ : Q.u.eval P.x₁ = 0 := by
    rw [← hPQ]
    exact P.u_eval_x₁
  have hprod₁ :
      (P.x₁ - Q.x₀) * (P.x₁ - Q.x₁) = 0 := by
    simpa [u] using hQ₁
  have hleft : P.x₁ - Q.x₀ ≠ 0 :=
    (P.cross_x₁_sub_x₀_isUnit Q).ne_zero
  have hx₁ : P.x₁ = Q.x₁ :=
    sub_eq_zero.mp
      ((mul_eq_zero.mp hprod₁).resolve_left hleft)
  cases P
  cases Q
  simp_all

theorem smoothMumford_injective :
    Function.Injective DiskPair.smoothMumford := by
  intro P Q hPQ
  apply u_injective
  exact congrArg
    (fun D : N13GeneralizedMumfordReduction.SmoothMumford₂ => D.u)
    hPQ

/-- Coordinates centered at the distinguished pair. -/
def coord : DiskPair → Fin 2 → R₂ :=
  fun Q => ![Q.x₀, Q.x₁ + 1]

@[simp] theorem coord_zero (Q : DiskPair) :
    coord Q 0 = Q.x₀ := rfl

@[simp] theorem coord_one (Q : DiskPair) :
    coord Q 1 = Q.x₁ + 1 := rfl

@[simp] theorem coord_basePair :
    coord basePair = 0 := by
  funext i
  fin_cases i <;> simp [coord, basePair]

theorem coord_mem_maximal
    (Q : DiskPair) (i : Fin 2) :
    coord Q i ∈ maximal := by
  fin_cases i
  · exact Q.x₀_mem
  · exact Q.x₁_add_one_mem

theorem maximal_eq_powTwoIdeal_one :
    maximal =
      N13TwoAdicKernelChart.powTwoIdeal 1 := by
  change IsLocalRing.maximalIdeal R₂ = _
  rw [PadicInt.maximalIdeal_eq_span_p,
    N13TwoAdicKernelChart.powTwoIdeal, pow_one]
  norm_num

theorem coord_mem_two
    (Q : DiskPair) (i : Fin 2) :
    coord Q i ∈
      N13TwoAdicKernelChart.powTwoIdeal 1 := by
  rw [← maximal_eq_powTwoIdeal_one]
  exact coord_mem_maximal Q i

theorem coord_injective :
    Function.Injective coord := by
  intro P Q hPQ
  have hx₀ := congrFun hPQ (0 : Fin 2)
  have hx₁ := congrFun hPQ (1 : Fin 2)
  cases P
  cases Q
  simp_all [coord]

end DiskPair

end

end MazurProof.N13TwoAdicAbelChartData


