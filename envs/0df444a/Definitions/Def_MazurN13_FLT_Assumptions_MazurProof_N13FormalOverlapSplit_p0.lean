-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FormalOverlapSplit_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13FormalOverlapSplit_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:49:05.161986+00:00
-- url     : https://prove2.me/theorems/090a8b9d-3080-406e-ae2e-c284af4eaa46
-- title:
--   FLT.Assumptions.MazurProof.N13FormalOverlapSplit source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13FormalOverlapSplit

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13FormalOverlapSplit
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FormalInfinitySplit_p0

set_option autoImplicit false




/-!
# Splitting the punctured N13 formal overlap

The two Hensel branches remain disjoint after passing from power series to
Laurent series.  Evaluation therefore splits the actual quadratic
punctured-overlap algebra as a product of two Laurent-series rings.  The
explicit interpolation inverse is compatible with restriction from the
complete formal-infinity chart.
-/

open Polynomial

namespace MazurProof.N13FormalOverlapSplit

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev Power : Type :=
  N13FormalInfinityChart.Power

abbrev Laurent : Type :=
  N13FormalCurveOverlap.Laurent

abbrev InfinityCurve : Type :=
  N13FormalInfinityChart.InfinityCurve

abbrev FormalCurve : Type :=
  N13FormalCurveOverlap.FormalCurve

open N13FormalInfinityBranches

/-- The zero branch restricted to the punctured formal chart. -/
def branchZeroLaurent : Laurent :=
  N13FormalInfinityChart.includePowerRing branchZero

/-- The one branch restricted to the punctured formal chart. -/
def branchOneLaurent : Laurent :=
  N13FormalInfinityChart.includePowerRing branchOne

theorem branchZeroLaurent_relation :
    branchZeroLaurent ^ 2 +
        N13FormalLineBundleCech.hInfinity *
          branchZeroLaurent -
      N13FormalLineBundleCech.rhsInfinity = 0 := by
  have h := congrArg
    N13FormalInfinityChart.includePowerRing branchZero_relation
  simp only [map_sub, map_add, map_pow, map_mul, map_zero] at h
  simpa [branchZeroLaurent] using h

theorem branchOneLaurent_relation :
    branchOneLaurent ^ 2 +
        N13FormalLineBundleCech.hInfinity *
          branchOneLaurent -
      N13FormalLineBundleCech.rhsInfinity = 0 := by
  have h := congrArg
    N13FormalInfinityChart.includePowerRing
      (show branchOne ^ 2 +
          N13FormalInfinityChart.hPower * branchOne -
        N13FormalInfinityChart.rhsPower = 0 by
        simpa [N13FormalInfinityChart.infinityCurvePoly] using
          branchOne_isRoot)
  simp only [map_sub, map_add, map_pow, map_mul, map_zero] at h
  simpa [branchOneLaurent] using h

theorem eval₂_branchZeroLaurent :
    N13FormalCurveOverlap.formalCurvePoly.eval₂
        (RingHom.id Laurent) branchZeroLaurent = 0 := by
  simpa [N13FormalCurveOverlap.formalCurvePoly] using
    branchZeroLaurent_relation

theorem eval₂_branchOneLaurent :
    N13FormalCurveOverlap.formalCurvePoly.eval₂
        (RingHom.id Laurent) branchOneLaurent = 0 := by
  simpa [N13FormalCurveOverlap.formalCurvePoly] using
    branchOneLaurent_relation

theorem branchLaurent_difference_isUnit :
    IsUnit (branchZeroLaurent - branchOneLaurent) := by
  simpa [branchZeroLaurent, branchOneLaurent] using
    branch_difference_isUnit.map
      N13FormalInfinityChart.includePowerRing

def evalBranchZeroLaurent : FormalCurve →+* Laurent :=
  AdjoinRoot.lift (RingHom.id Laurent) branchZeroLaurent
    eval₂_branchZeroLaurent

def evalBranchOneLaurent : FormalCurve →+* Laurent :=
  AdjoinRoot.lift (RingHom.id Laurent) branchOneLaurent
    eval₂_branchOneLaurent

@[simp] theorem evalBranchZeroLaurent_of
    (f : Laurent) :
    evalBranchZeroLaurent
        (AdjoinRoot.of
          N13FormalCurveOverlap.formalCurvePoly f) = f := by
  exact AdjoinRoot.lift_of eval₂_branchZeroLaurent

@[simp] theorem evalBranchOneLaurent_of
    (f : Laurent) :
    evalBranchOneLaurent
        (AdjoinRoot.of
          N13FormalCurveOverlap.formalCurvePoly f) = f := by
  exact AdjoinRoot.lift_of eval₂_branchOneLaurent

@[simp] theorem evalBranchZeroLaurent_vClass :
    evalBranchZeroLaurent N13FormalCurveOverlap.vClass =
      branchZeroLaurent := by
  exact AdjoinRoot.lift_root eval₂_branchZeroLaurent

@[simp] theorem evalBranchOneLaurent_vClass :
    evalBranchOneLaurent N13FormalCurveOverlap.vClass =
      branchOneLaurent := by
  exact AdjoinRoot.lift_root eval₂_branchOneLaurent

def formalBranchEval : FormalCurve →+* Laurent × Laurent :=
  evalBranchZeroLaurent.prod evalBranchOneLaurent

@[simp] theorem formalBranchEval_ofOverlap
    (z : Laurent × Laurent) :
    formalBranchEval (N13FormalCurveOverlap.ofOverlap z) =
      (z.1 + z.2 * branchZeroLaurent,
        z.1 + z.2 * branchOneLaurent) := by
  simp [formalBranchEval, N13FormalCurveOverlap.ofOverlap]

theorem formalBranchEval_eq_coeff
    (z : FormalCurve) :
    formalBranchEval z =
      (N13FormalCurveOverlap.coeff0 z +
          N13FormalCurveOverlap.coeffV z *
            branchZeroLaurent,
        N13FormalCurveOverlap.coeff0 z +
          N13FormalCurveOverlap.coeffV z *
            branchOneLaurent) := by
  calc
    formalBranchEval z =
        formalBranchEval
          (N13FormalCurveOverlap.ofOverlap
            (N13FormalCurveOverlap.toOverlap z)) := by
          exact congrArg formalBranchEval
            (N13FormalCurveOverlap.ofOverlap_toOverlap z).symm
    _ = _ := by
      simp [N13FormalCurveOverlap.toOverlap]

theorem formalBranchEval_injective :
    Function.Injective formalBranchEval := by
  intro z w hzw
  rw [formalBranchEval_eq_coeff,
    formalBranchEval_eq_coeff] at hzw
  simp only [Prod.mk.injEq] at hzw
  rcases hzw with ⟨hzero, hone⟩
  have hvprod :
      (N13FormalCurveOverlap.coeffV z -
          N13FormalCurveOverlap.coeffV w) *
        (branchZeroLaurent - branchOneLaurent) = 0 := by
    linear_combination hzero - hone
  have hvsub :
      N13FormalCurveOverlap.coeffV z -
          N13FormalCurveOverlap.coeffV w = 0 := by
    apply branchLaurent_difference_isUnit.mul_right_cancel
    simpa using hvprod
  have hv :
      N13FormalCurveOverlap.coeffV z =
        N13FormalCurveOverlap.coeffV w :=
    sub_eq_zero.mp hvsub
  have hzero' := hzero
  rw [hv] at hzero'
  have hcoeff0 :
      N13FormalCurveOverlap.coeff0 z =
        N13FormalCurveOverlap.coeff0 w :=
    add_right_cancel hzero'
  calc
    z = N13FormalCurveOverlap.ofOverlap
        (N13FormalCurveOverlap.toOverlap z) :=
      (N13FormalCurveOverlap.ofOverlap_toOverlap z).symm
    _ = N13FormalCurveOverlap.ofOverlap
        (N13FormalCurveOverlap.toOverlap w) := by
      congr 1
      exact Prod.ext hcoeff0 hv
    _ = w :=
      N13FormalCurveOverlap.ofOverlap_toOverlap w

def branchLaurentDifferenceUnit : Laurentˣ :=
  branchLaurent_difference_isUnit.unit

@[simp] theorem branchLaurentDifferenceUnit_coe :
    (branchLaurentDifferenceUnit : Laurent) =
      branchZeroLaurent - branchOneLaurent :=
  IsUnit.unit_spec branchLaurent_difference_isUnit

theorem branchLaurentDifferenceUnit_inv_mul :
    (↑(branchLaurentDifferenceUnit⁻¹) : Laurent) *
        (branchZeroLaurent - branchOneLaurent) = 1 := by
  rw [← branchLaurentDifferenceUnit_coe]
  exact Units.inv_mul branchLaurentDifferenceUnit

def formalInterpolate
    (z : Laurent × Laurent) : FormalCurve :=
  let b :=
    (z.1 - z.2) *
      (↑(branchLaurentDifferenceUnit⁻¹) : Laurent)
  N13FormalCurveOverlap.ofOverlap
    (z.1 - b * branchZeroLaurent, b)

theorem formalBranchEval_formalInterpolate
    (z : Laurent × Laurent) :
    formalBranchEval (formalInterpolate z) = z := by
  rcases z with ⟨x, y⟩
  apply Prod.ext
  · simp [formalInterpolate]
  · simp only [formalInterpolate, formalBranchEval_ofOverlap]
    let b : Laurent :=
      (x - y) *
        (↑(branchLaurentDifferenceUnit⁻¹) : Laurent)
    change x - b * branchZeroLaurent +
        b * branchOneLaurent = y
    calc
      x - b * branchZeroLaurent +
            b * branchOneLaurent =
          x - b *
            (branchZeroLaurent - branchOneLaurent) := by
        ring
      _ = x - (x - y) := by
        unfold b
        rw [mul_assoc,
          branchLaurentDifferenceUnit_inv_mul, mul_one]
      _ = y := by ring

theorem formalBranchEval_surjective :
    Function.Surjective formalBranchEval :=
  fun z =>
    ⟨formalInterpolate z,
      formalBranchEval_formalInterpolate z⟩

theorem formalBranchEval_bijective :
    Function.Bijective formalBranchEval :=
  ⟨formalBranchEval_injective, formalBranchEval_surjective⟩

def formalCurveEquivBranches :
    FormalCurve ≃+* Laurent × Laurent :=
  RingEquiv.ofBijective formalBranchEval
    formalBranchEval_bijective

@[simp] theorem formalCurveEquivBranches_apply
    (z : FormalCurve) :
    formalCurveEquivBranches z = formalBranchEval z :=
  rfl

@[simp] theorem formalCurveEquivBranches_symm_apply
    (z : Laurent × Laurent) :
    formalCurveEquivBranches.symm z = formalInterpolate z := by
  apply formalCurveEquivBranches.injective
  rw [RingEquiv.apply_symm_apply,
    formalCurveEquivBranches_apply,
    formalBranchEval_formalInterpolate]

def includePowerBranches
    (z : Power × Power) : Laurent × Laurent :=
  (N13FormalInfinityChart.includePowerRing z.1,
    N13FormalInfinityChart.includePowerRing z.2)

@[simp] theorem infinityToFormalCurve_adjoinRootOf
    (f : Power) :
    N13FormalInfinityChart.infinityToFormalCurve
        (AdjoinRoot.of
          N13FormalInfinityChart.infinityCurvePoly f) =
      AdjoinRoot.of N13FormalCurveOverlap.formalCurvePoly
        (N13FormalInfinityChart.includePowerRing f) := by
  exact N13FormalInfinityChart.infinityToFormalCurve_of f

theorem formalBranchEval_infinityToFormalCurve
    (z : InfinityCurve) :
    formalBranchEval
        (N13FormalInfinityChart.infinityToFormalCurve z) =
      includePowerBranches
        (N13FormalInfinitySplit.branchEval z) := by
  calc
    formalBranchEval
        (N13FormalInfinityChart.infinityToFormalCurve z) =
      formalBranchEval
        (N13FormalInfinityChart.infinityToFormalCurve
          (algebraMap Power InfinityCurve
              (N13FormalInfinityChart.coeff0 z) +
            algebraMap Power InfinityCurve
                (N13FormalInfinityChart.coeffV z) *
              N13FormalInfinityChart.vClass)) := by
        exact congrArg
          (fun w =>
            formalBranchEval
              (N13FormalInfinityChart.infinityToFormalCurve w))
          (N13FormalInfinityChart.recompose z).symm
    _ =
      (N13FormalInfinityChart.includePowerRing
          (N13FormalInfinityChart.coeff0 z) +
        N13FormalInfinityChart.includePowerRing
            (N13FormalInfinityChart.coeffV z) *
          branchZeroLaurent,
       N13FormalInfinityChart.includePowerRing
          (N13FormalInfinityChart.coeff0 z) +
        N13FormalInfinityChart.includePowerRing
            (N13FormalInfinityChart.coeffV z) *
          branchOneLaurent) := by
        simp [formalBranchEval,
          N13FormalInfinityChart.infinityToFormalCurve_vClass]
    _ =
      includePowerBranches
        (N13FormalInfinitySplit.branchEval z) := by
      rw [N13FormalInfinitySplit.branchEval_eq_coeff]
      simp [includePowerBranches, branchZeroLaurent,
        branchOneLaurent]

end

end MazurProof.N13FormalOverlapSplit


