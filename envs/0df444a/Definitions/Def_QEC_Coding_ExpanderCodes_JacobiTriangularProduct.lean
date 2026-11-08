-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
-- name    : QEC_Coding_ExpanderCodes_JacobiTriangularProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:31:15.869587+00:00
-- url     : https://prove2.me/theorems/86cadc1b-6f1d-4e00-8730-2ec862c8d328
-- title:
--   Jacobi Triangular Product
-- statement:
--   Definitions and structural lemmas for Jacobi Triangular Product, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTriangularProduct.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.Topology.WithTopology
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_jtpPositiveTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeriesRaw
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedSquareSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSixProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSquareProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_integerTriangularRoots_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inl
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inr
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_integerTriangularRoots_iff
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jtpPositiveTerm
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_succ_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_right
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_succ
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeriesRaw
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedSquareSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSixProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSquareProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiThetaProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiTriangularProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.integerTriangularRoots_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inl
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inr
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace JacobiTriangularProduct
open JacobiGeneralCore.FormalPowerSeries
abbrev DiscreteRat := ULift.{0, 0} ℚ
local instance discreteRatUniformSpace : UniformSpace DiscreteRat := ⊥
attribute [local instance] discreteRatUniformSpace
local instance discreteRatTopologicalSpace : TopologicalSpace DiscreteRat :=
  UniformSpace.toTopologicalSpace
attribute [local instance] discreteRatTopologicalSpace
local instance discreteRatUniformity : DiscreteUniformity DiscreteRat := inferInstance
attribute [local instance] discreteRatUniformity
local instance discreteRatTopology : DiscreteTopology DiscreteRat := ⟨rfl⟩
attribute [local instance] discreteRatTopology
abbrev Target := PowerSeries DiscreteRat
abbrev DiscreteTarget := ULift.{0, 0} Target
abbrev Outer := PowerSeries DiscreteTarget
local instance discreteTargetUniformSpace : UniformSpace DiscreteTarget := ⊥
attribute [local instance] discreteTargetUniformSpace
local instance discreteTargetTopologicalSpace : TopologicalSpace DiscreteTarget :=
  UniformSpace.toTopologicalSpace
attribute [local instance] discreteTargetTopologicalSpace
local instance discreteTargetUniformity : DiscreteUniformity DiscreteTarget := inferInstance
attribute [local instance] discreteTargetUniformity
local instance discreteTargetTopology : DiscreteTopology DiscreteTarget := ⟨rfl⟩
attribute [local instance] discreteTargetTopology
noncomputable def wrapTarget : Target →+* DiscreteTarget where
  toFun := ULift.up
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
noncomputable def unwrapTarget : DiscreteTarget →+* Target where
  toFun := ULift.down
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
@[simp] theorem unwrapTarget_wrapTarget (f : Target) :
    unwrapTarget (wrapTarget f) = f := rfl
theorem continuous_unwrapTarget : Continuous unwrapTarget :=
  continuous_of_discreteTopology
theorem hasEval_X_sq : PowerSeries.HasEval (PowerSeries.X ^ 2 : Target) :=
  by
    simpa [pow_two] using
      (PowerSeries.HasEval.X.mul_right (PowerSeries.X : Target))
noncomputable def evalOuter : Outer →+* Target :=
  PowerSeries.eval₂Hom continuous_unwrapTarget hasEval_X_sq
@[simp] theorem evalOuter_C (f : Target) :
    evalOuter (PowerSeries.C (wrapTarget f)) = f := by
  rw [evalOuter, PowerSeries.coe_eval₂Hom]
  rw [PowerSeries.eval₂_C]
  rfl
@[simp] theorem evalOuter_X :
    evalOuter (PowerSeries.X : Outer) =
      (PowerSeries.X : Target) ^ 2 := by
  rw [evalOuter, PowerSeries.coe_eval₂Hom]
  rw [PowerSeries.eval₂_X]
noncomputable def sourceQ : Outer :=
  PowerSeries.C (wrapTarget ((PowerSeries.X : Target) ^ 2))
noncomputable def sourceOne : Outer :=
  PowerSeries.C (wrapTarget 1)
@[simp] theorem evalOuter_sourceQ : evalOuter sourceQ =
    (PowerSeries.X : Target) ^ 2 := by
  simp [sourceQ]
@[simp] theorem evalOuter_sourceOne : evalOuter sourceOne = 1 := by
  simp [sourceOne]
noncomputable def baseQ : Target := (PowerSeries.X : Target) ^ 2
noncomputable def evaluatedPochhammerInf : Target :=
  evalOuter (qPochhammerInf (PowerSeries.X : Outer))
noncomputable def evaluatedPochhammerInv (n : ℕ) : Target :=
  evalOuter (qPochhammerInv (R := DiscreteTarget) n)
noncomputable def evaluatedTail (n : ℕ) : Target :=
  evalOuter (qPochhammerInf
    ((PowerSeries.X : Outer) * PowerSeries.X ^ n))
noncomputable def triangularLeftTerm (n : ℕ) : Target :=
  baseQ ^ n.choose 2 * baseQ ^ n * evaluatedTail n
noncomputable def triangularRightTerm (m : ℕ) : Target :=
  baseQ ^ m.choose 2 * evaluatedPochhammerInv m
noncomputable def triangularProductTerm (p : ℕ × ℕ) : Target :=
  triangularLeftTerm p.1 * triangularRightTerm p.2
def diagonalEquiv : ℕ × ℕ ≃ (ℕ × ℕ) ⊕ (ℕ × ℕ) where
  toFun p := if p.2 ≤ p.1 then
      Sum.inl (p.1 - p.2, p.2)
    else
      Sum.inr (p.2 - p.1 - 1, p.1)
  invFun s := match s with
    | Sum.inl (k, m) => (m + k, m)
    | Sum.inr (l, n) => (n, n + l + 1)
  left_inv := by
    intro ⟨n, m⟩
    simp only
    split_ifs with h <;> simp <;> omega
  right_inv := by
    intro s
    rcases s with ⟨k, m⟩ | ⟨l, n⟩ <;> simp
    omega
noncomputable def evaluatedTriangularSeries : Target :=
  ∑' n : ℕ, baseQ ^ (n + 1).choose 2
noncomputable def evaluatedEvenMinusProduct : Target :=
  ∏' n : ℕ, (1 - baseQ ^ (n + 1))
noncomputable def evaluatedEvenPlusProduct : Target :=
  ∏' n : ℕ, (1 + baseQ ^ (n + 1))
noncomputable def evaluatedTriangularProduct : Target :=
  ∏' n : ℕ,
    (1 - baseQ ^ (n + 1)) * (1 + baseQ ^ (n + 1)) ^ 2
noncomputable def unwrapRat : DiscreteRat →+* ℚ where
  toFun := ULift.down
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
noncomputable def mapToRat : Target →+* PowerSeries ℚ :=
  PowerSeries.map unwrapRat
@[simp] theorem mapToRat_X :
    mapToRat (PowerSeries.X : Target) =
      (PowerSeries.X : PowerSeries ℚ) := by
  simp [mapToRat]
@[simp] theorem mapToRat_baseQ :
    mapToRat baseQ = (PowerSeries.X : PowerSeries ℚ) ^ 2 := by
  simp [baseQ]
noncomputable def naturalTriangularRoots (d : ℕ) : Finset ℕ :=
  (Finset.range (d + 1)).filter fun n => n * (n + 1) = d
theorem mem_naturalTriangularRoots_iff (d n : ℕ) :
    n ∈ naturalTriangularRoots d ↔ n * (n + 1) = d := by
  rw [naturalTriangularRoots, Finset.mem_filter]
  refine and_iff_right_of_imp fun hn => ?_
  rw [Finset.mem_range]
  have hle : n ≤ n * (n + 1) := by nlinarith
  omega
def integerTriangularRootEquiv (d : ℕ) :
    {z : ℤ // z ∈ integerTriangularRoots d} ≃
      Bool × {n : ℕ // n ∈ naturalTriangularRoots d} where
  toFun z := if hz : 0 ≤ z.1 then
      (false, ⟨z.1.toNat, by
        rw [mem_naturalTriangularRoots_iff]
        have heq := (mem_integerTriangularRoots_iff d z.1).mp z.2
        have hcast : (z.1.toNat : ℤ) = z.1 := Int.toNat_of_nonneg hz
        rw [← hcast] at heq
        have hnat : z.1.toNat ^ 2 + z.1.toNat = d := by
          exact_mod_cast heq
        nlinarith⟩)
    else
      (true, ⟨(-z.1 - 1).toNat, by
        rw [mem_naturalTriangularRoots_iff]
        have heq := (mem_integerTriangularRoots_iff d z.1).mp z.2
        have hw : 0 ≤ -z.1 - 1 := by omega
        have hcast : (((-z.1 - 1).toNat : ℕ) : ℤ) = -z.1 - 1 :=
          Int.toNat_of_nonneg hw
        have heq' : (-z.1 - 1) ^ 2 + (-z.1 - 1) = (d : ℤ) := by
          nlinarith
        rw [← hcast] at heq'
        have hnat : (-z.1 - 1).toNat ^ 2 + (-z.1 - 1).toNat = d := by
          exact_mod_cast heq'
        nlinarith⟩)
  invFun p := match p with
    | (false, n) => ⟨(n.1 : ℤ), by
        rw [mem_integerTriangularRoots_iff]
        have hn := (mem_naturalTriangularRoots_iff d n.1).mp n.2
        have hn' : (n.1 : ℤ) * (n.1 + 1) = d := by exact_mod_cast hn
        nlinarith⟩
    | (true, n) => ⟨-(n.1 : ℤ) - 1, by
        rw [mem_integerTriangularRoots_iff]
        have hnNat := (mem_naturalTriangularRoots_iff d n.1).mp n.2
        have hn : (n.1 : ℤ) * (n.1 + 1) = d := by exact_mod_cast hnNat
        nlinarith⟩
  left_inv := by
    intro z
    simp only
    split_ifs with hz
    · apply Subtype.ext
      simp [Int.toNat_of_nonneg hz]
    · apply Subtype.ext
      have hw : 0 ≤ -z.1 - 1 := by omega
      change -((((-z.1 - 1).toNat : ℕ) : ℤ)) - 1 = z.1
      rw [Int.toNat_of_nonneg hw]
      omega
  right_inv := by
    rintro ⟨b, n⟩
    cases b
    · simp
    · simp
      omega
end JacobiTriangularProduct
end QEC.Coding.TannerLiftedProduct


