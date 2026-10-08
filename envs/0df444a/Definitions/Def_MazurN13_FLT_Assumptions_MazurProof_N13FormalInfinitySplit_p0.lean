-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FormalInfinitySplit_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13FormalInfinitySplit_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:46:50.990352+00:00
-- url     : https://prove2.me/theorems/2685b5db-0579-4a71-a70a-0b3d31b04ea2
-- title:
--   FLT.Assumptions.MazurProof.N13FormalInfinitySplit source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13FormalInfinitySplit

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13FormalInfinitySplit
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FormalInfinityBranches_p0

set_option autoImplicit false




/-!
# Splitting the N13 formal infinity chart

The two Hensel roots of the formal-infinity equation differ by a unit.
Evaluation on those roots therefore identifies every function in the
quadratic chart with its values on the two disjoint branches.  Injectivity
uses the normal form `a + bv`; surjectivity is explicit two-point
interpolation.
-/

open Polynomial

namespace MazurProof.N13FormalInfinitySplit

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev Power : Type :=
  N13FormalInfinityChart.Power

abbrev InfinityCurve : Type :=
  N13FormalInfinityChart.InfinityCurve

open N13FormalInfinityBranches

theorem eval₂_branchZero :
    N13FormalInfinityChart.infinityCurvePoly.eval₂
        (RingHom.id Power) branchZero = 0 := by
  simpa using branchZero_isRoot

theorem eval₂_branchOne :
    N13FormalInfinityChart.infinityCurvePoly.eval₂
        (RingHom.id Power) branchOne = 0 := by
  simpa using branchOne_isRoot

/-- Evaluation on the branch reducing to `v = 0`. -/
def evalBranchZero : InfinityCurve →+* Power :=
  AdjoinRoot.lift (RingHom.id Power) branchZero
    eval₂_branchZero

/-- Evaluation on the branch reducing to `v = 1`. -/
def evalBranchOne : InfinityCurve →+* Power :=
  AdjoinRoot.lift (RingHom.id Power) branchOne
    eval₂_branchOne

@[simp] theorem evalBranchZero_of
    (f : Power) :
    evalBranchZero
        (AdjoinRoot.of
          N13FormalInfinityChart.infinityCurvePoly f) = f := by
  exact AdjoinRoot.lift_of eval₂_branchZero

@[simp] theorem evalBranchOne_of
    (f : Power) :
    evalBranchOne
        (AdjoinRoot.of
          N13FormalInfinityChart.infinityCurvePoly f) = f := by
  exact AdjoinRoot.lift_of eval₂_branchOne

@[simp] theorem evalBranchZero_vClass :
    evalBranchZero N13FormalInfinityChart.vClass =
      branchZero := by
  exact AdjoinRoot.lift_root eval₂_branchZero

@[simp] theorem evalBranchOne_vClass :
    evalBranchOne N13FormalInfinityChart.vClass =
      branchOne := by
  exact AdjoinRoot.lift_root eval₂_branchOne

/-- Simultaneous evaluation on the two disjoint Hensel branches. -/
def branchEval : InfinityCurve →+* Power × Power :=
  evalBranchZero.prod evalBranchOne

@[simp] theorem branchEval_ofPowerPair
    (z : Power × Power) :
    branchEval (N13FormalInfinityChart.ofPowerPair z) =
      (z.1 + z.2 * branchZero,
        z.1 + z.2 * branchOne) := by
  simp [branchEval, N13FormalInfinityChart.ofPowerPair]

theorem branchEval_eq_coeff
    (z : InfinityCurve) :
    branchEval z =
      (N13FormalInfinityChart.coeff0 z +
          N13FormalInfinityChart.coeffV z * branchZero,
        N13FormalInfinityChart.coeff0 z +
          N13FormalInfinityChart.coeffV z * branchOne) := by
  calc
    branchEval z =
        branchEval
          (algebraMap Power InfinityCurve
              (N13FormalInfinityChart.coeff0 z) +
            algebraMap Power InfinityCurve
                (N13FormalInfinityChart.coeffV z) *
              N13FormalInfinityChart.vClass) := by
          exact congrArg branchEval
            (N13FormalInfinityChart.recompose z).symm
    _ = _ := by simp [branchEval]

theorem branchEval_injective :
    Function.Injective branchEval := by
  intro z w hzw
  rw [branchEval_eq_coeff, branchEval_eq_coeff] at hzw
  simp only [Prod.mk.injEq] at hzw
  rcases hzw with ⟨hzero, hone⟩
  have hvprod :
      (N13FormalInfinityChart.coeffV z -
          N13FormalInfinityChart.coeffV w) *
        (branchZero - branchOne) = 0 := by
    linear_combination hzero - hone
  have hvsub :
      N13FormalInfinityChart.coeffV z -
          N13FormalInfinityChart.coeffV w = 0 := by
    apply branch_difference_isUnit.mul_right_cancel
    simpa using hvprod
  have hv :
      N13FormalInfinityChart.coeffV z =
        N13FormalInfinityChart.coeffV w :=
    sub_eq_zero.mp hvsub
  have hzero' := hzero
  rw [hv] at hzero'
  have hcoeff0 :
      N13FormalInfinityChart.coeff0 z =
        N13FormalInfinityChart.coeff0 w :=
    add_right_cancel hzero'
  rw [← N13FormalInfinityChart.recompose z,
    ← N13FormalInfinityChart.recompose w, hcoeff0, hv]

/-- The unit represented by the difference of the two branches. -/
def branchDifferenceUnit : Powerˣ :=
  branch_difference_isUnit.unit

@[simp] theorem branchDifferenceUnit_coe :
    (branchDifferenceUnit : Power) =
      branchZero - branchOne :=
  IsUnit.unit_spec branch_difference_isUnit

theorem branchDifferenceUnit_inv_mul :
    (↑(branchDifferenceUnit⁻¹) : Power) *
        (branchZero - branchOne) = 1 := by
  rw [← branchDifferenceUnit_coe]
  exact Units.inv_mul branchDifferenceUnit

/-- Lagrange interpolation between the two Hensel branches. -/
def interpolate (z : Power × Power) : InfinityCurve :=
  let b :=
    (z.1 - z.2) *
      (↑(branchDifferenceUnit⁻¹) : Power)
  N13FormalInfinityChart.ofPowerPair
    (z.1 - b * branchZero, b)

theorem branchEval_interpolate
    (z : Power × Power) :
    branchEval (interpolate z) = z := by
  rcases z with ⟨x, y⟩
  apply Prod.ext
  · simp [interpolate]
  · simp only [interpolate, branchEval_ofPowerPair]
    let b : Power :=
      (x - y) *
        (↑(branchDifferenceUnit⁻¹) : Power)
    change x - b * branchZero + b * branchOne = y
    calc
      x - b * branchZero + b * branchOne =
          x - b * (branchZero - branchOne) := by ring
      _ = x - (x - y) := by
        unfold b
        rw [mul_assoc,
          branchDifferenceUnit_inv_mul, mul_one]
      _ = y := by ring

theorem branchEval_surjective :
    Function.Surjective branchEval :=
  fun z => ⟨interpolate z, branchEval_interpolate z⟩

theorem branchEval_bijective :
    Function.Bijective branchEval :=
  ⟨branchEval_injective, branchEval_surjective⟩

/-- The complete formal infinity chart is the product of its two Hensel
branches. -/
def infinityCurveEquivBranches :
    InfinityCurve ≃+* Power × Power :=
  RingEquiv.ofBijective branchEval branchEval_bijective

@[simp] theorem infinityCurveEquivBranches_apply
    (z : InfinityCurve) :
    infinityCurveEquivBranches z = branchEval z :=
  rfl

@[simp] theorem infinityCurveEquivBranches_symm_apply
    (z : Power × Power) :
    infinityCurveEquivBranches.symm z = interpolate z := by
  apply infinityCurveEquivBranches.injective
  rw [RingEquiv.apply_symm_apply,
    infinityCurveEquivBranches_apply,
    branchEval_interpolate]

end

end MazurProof.N13FormalInfinitySplit


