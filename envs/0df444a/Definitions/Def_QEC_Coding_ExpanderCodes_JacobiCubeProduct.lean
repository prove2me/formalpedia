-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
-- name    : QEC_Coding_ExpanderCodes_JacobiCubeProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:17:39.873653+00:00
-- url     : https://prove2.me/theorems/87e3cc80-842d-45ab-b0d9-1444968464f5
-- title:
--   Jacobi Cube Product
-- statement:
--   Definitions and structural lemmas for Jacobi Cube Product, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Mathlib
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_multipliable_one_sub_mul_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammerInf_eq_one_sub_mul
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
namespace JacobiCubeProduct
open JacobiGeneralCore.FormalPowerSeries
set_option linter.style.haveILetI false
abbrev LaurentQ := LaurentPolynomial ℚ
abbrev Bivariate := PowerSeries LaurentQ
noncomputable def evalNegOne : LaurentQ →+* ℚ :=
  LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1)
noncomputable def signedEulerCoeff : LaurentQ →+ ℚ where
  toFun f := f.coeff.sum fun m c => (m : ℚ) * c * ((-1 : ℚ) ^ m)
  map_zero' := Finsupp.sum_zero_index
  map_add' f g := Finsupp.sum_add_index'
    (fun _ => by simp) (fun _ a b => by ring)
noncomputable def signedEuler (F : Bivariate) : PowerSeries ℚ :=
  PowerSeries.mk fun n => signedEulerCoeff (PowerSeries.coeff n F)
noncomputable def evalNegOneSeries : Bivariate →+* PowerSeries ℚ :=
  PowerSeries.map evalNegOne
@[simp] theorem coeff_signedEuler (n : ℕ) (F : Bivariate) :
    PowerSeries.coeff n (signedEuler F) =
      signedEulerCoeff (PowerSeries.coeff n F) := by
  simp [signedEuler]
@[simp] theorem coeff_evalNegOneSeries (n : ℕ) (F : Bivariate) :
    PowerSeries.coeff n (evalNegOneSeries F) =
      evalNegOne (PowerSeries.coeff n F) := by
  simp [evalNegOneSeries]
@[simp] theorem evalNegOne_C_mul_T (c : ℚ) (m : ℤ) :
    evalNegOne (LaurentPolynomial.C c * LaurentPolynomial.T m) =
      c * ((-1 : ℚ) ^ m) := by
  simp [evalNegOne]
@[simp] theorem signedEulerCoeff_C_mul_T (c : ℚ) (m : ℤ) :
    signedEulerCoeff (LaurentPolynomial.C c * LaurentPolynomial.T m) =
      (m : ℚ) * c * ((-1 : ℚ) ^ m) := by
  show (LaurentPolynomial.C c * LaurentPolynomial.T m).coeff.sum
      (fun j d => (j : ℚ) * d * ((-1 : ℚ) ^ j)) = _
  rw [← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single,
    Finsupp.sum_single_index (by simp)]
@[simp] theorem signedEulerCoeff_C (c : ℚ) :
    signedEulerCoeff (LaurentPolynomial.C c) = 0 := by
  simpa using signedEulerCoeff_C_mul_T c 0
@[simp] theorem signedEulerCoeff_T (m : ℤ) :
    signedEulerCoeff (LaurentPolynomial.T m) =
      (m : ℚ) * ((-1 : ℚ) ^ m) := by
  simpa using signedEulerCoeff_C_mul_T 1 m
@[simp] theorem signedEulerCoeff_one : signedEulerCoeff 1 = 0 := by
  simpa using signedEulerCoeff_C 1
@[simp] theorem evalNegOne_C (c : ℚ) :
    evalNegOne (LaurentPolynomial.C c) = c := by
  simp [evalNegOne]
@[simp] theorem evalNegOne_T (m : ℤ) :
    evalNegOne (LaurentPolynomial.T m) = ((-1 : ℚ) ^ m) := by
  simpa using evalNegOne_C_mul_T 1 m
noncomputable def eulerProduct : PowerSeries ℚ :=
  ∏' n : ℕ, (1 - PowerSeries.X ^ (n + 1))
theorem continuous_evalNegOneSeries :
    letI : TopologicalSpace LaurentQ := ⊥
    Continuous evalNegOneSeries := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  rw [continuous_iff_continuousAt]
  intro F
  rw [ContinuousAt,
    PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  change Filter.Tendsto
    (fun G : Bivariate => evalNegOne (PowerSeries.coeff n G))
    (nhds F)
    (nhds (evalNegOne (PowerSeries.coeff n F)))
  exact (continuous_of_discreteTopology.comp
    (PowerSeries.WithPiTopology.continuous_coeff LaurentQ n)).continuousAt
theorem evalNegOneSeries_qPochhammerInf (a : Bivariate) :
    letI : TopologicalSpace LaurentQ := ⊥
    evalNegOneSeries (qPochhammerInf a) =
      ∏' n : ℕ,
        ((1 : PowerSeries ℚ) - evalNegOneSeries a * PowerSeries.X ^ n) := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  rw [qPochhammerInf]
  rw [(multipliable_one_sub_mul_pow a).map_tprod
    evalNegOneSeries continuous_evalNegOneSeries]
  simp only [map_sub, map_one, map_mul, map_pow,
    evalNegOneSeries, PowerSeries.map_X]
@[simp] theorem evalNegOneSeries_X :
    evalNegOneSeries (PowerSeries.X : Bivariate) = PowerSeries.X := by
  simp [evalNegOneSeries]
@[simp] theorem evalNegOneSeries_laurentZ :
    evalNegOneSeries laurentZ = -1 := by
  ext n
  cases n <;> simp [evalNegOneSeries, evalNegOne]
@[simp] theorem evalNegOneSeries_laurentZInv :
    evalNegOneSeries laurentZInv = -1 := by
  ext n
  cases n <;> simp [evalNegOneSeries, evalNegOne]
@[simp] theorem signedEuler_one_add_laurentZ :
    signedEuler (1 + laurentZ) = -1 := by
  ext n
  cases n <;> simp [signedEuler]
@[simp] theorem evalNegOneSeries_one_add_laurentZ :
    evalNegOneSeries (1 + laurentZ) = 0 := by
  rw [map_add, map_one, evalNegOneSeries_laurentZ]
  ring
@[simp] theorem evalNegOneSeries_qPochhammerInf_X :
    evalNegOneSeries (qPochhammerInf (PowerSeries.X : Bivariate)) =
      eulerProduct := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  rw [evalNegOneSeries_qPochhammerInf]
  rw [eulerProduct]
  apply tprod_congr
  intro n
  rw [evalNegOneSeries_X, pow_succ']
@[simp] theorem evalNegOneSeries_qPochhammerInf_neg_X_mul_laurentZInv :
    evalNegOneSeries (qPochhammerInf
        (-(PowerSeries.X : Bivariate) * laurentZInv)) =
      eulerProduct := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  rw [evalNegOneSeries_qPochhammerInf]
  rw [eulerProduct]
  apply tprod_congr
  intro n
  simp only [map_neg, map_mul, evalNegOneSeries_X,
    evalNegOneSeries_laurentZInv, mul_neg, mul_one, neg_neg]
  rw [pow_succ']
@[simp] theorem evalNegOneSeries_qPochhammerInf_neg_laurentZ :
    evalNegOneSeries (qPochhammerInf (-laurentZ)) = 0 := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  rw [qPochhammerInf_eq_one_sub_mul]
  have hfactor : (1 : Bivariate) - -laurentZ = 1 + laurentZ := by ring
  rw [hfactor, map_mul, evalNegOneSeries_one_add_laurentZ, zero_mul]
noncomputable def signedTriangularTerm (z : ℤ) : PowerSeries ℚ :=
  PowerSeries.C
      (jacobiParitySign z * (2 * (z : ℚ) + 1)) *
    PowerSeries.X ^ jacobiHalfTriangularDegree z
@[simp] theorem coeff_signedTriangularTerm (n : ℕ) (z : ℤ) :
    PowerSeries.coeff n (signedTriangularTerm z) =
      if jacobiHalfTriangularDegree z = n then
        jacobiParitySign z * (2 * (z : ℚ) + 1)
      else 0 := by
  rw [signedTriangularTerm, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow]
  split_ifs <;> simp_all
def triangularPairEquiv : ℕ ⊕ ℕ ≃ ℤ where
  toFun s := match s with
    | Sum.inl n => n
    | Sum.inr n => -(n : ℤ) - 1
  invFun z := if 0 ≤ z then Sum.inl z.toNat else Sum.inr (-z - 1).toNat
  left_inv := by
    rintro (n | n)
    · simp
    · change (if 0 ≤ (-(n : ℤ) - 1) then
          Sum.inl (-(n : ℤ) - 1).toNat
        else Sum.inr (-(-(n : ℤ) - 1) - 1).toNat) = Sum.inr n
      rw [if_neg (by omega)]
      congr 1
      rw [show -(-(n : ℤ) - 1) - 1 = (n : ℤ) by ring]
      simp
  right_inv := by
    intro z
    simp only
    by_cases hz : 0 ≤ z
    · rw [if_pos hz]
      simp [Int.toNat_of_nonneg hz]
    · rw [if_neg hz]
      have hz' : 0 ≤ -z - 1 := by omega
      change -(((-z - 1).toNat : ℕ) : ℤ) - 1 = z
      rw [Int.toNat_of_nonneg hz']
      omega
@[simp] theorem signedEuler_add (F G : Bivariate) :
    signedEuler (F + G) = signedEuler F + signedEuler G := by
  ext n
  simp [signedEuler]
noncomputable def signedEulerHom :
    Bivariate →+ PowerSeries ℚ where
  toFun := signedEuler
  map_zero' := by
    ext n
    simp [signedEuler]
  map_add' := signedEuler_add
noncomputable def jtpPositiveTerm (n : ℕ) : Bivariate :=
  PowerSeries.C (LaurentPolynomial.T (n : ℤ)) *
    PowerSeries.X ^ n.choose 2
noncomputable def jtpNegativeTerm (m : ℕ) : Bivariate :=
  PowerSeries.C (LaurentPolynomial.T (-(m : ℤ) - 1)) *
    PowerSeries.X ^ (m + 2).choose 2
noncomputable def jtpIntegerTerm (z : ℤ) : Bivariate :=
  if 0 ≤ z then jtpPositiveTerm z.toNat
  else jtpNegativeTerm (-z - 1).toNat
@[simp] theorem jtpIntegerTerm_nat (n : ℕ) :
    jtpIntegerTerm (n : ℤ) = jtpPositiveTerm n := by
  simp [jtpIntegerTerm]
@[simp] theorem jtpIntegerTerm_neg_sub_one (n : ℕ) :
    jtpIntegerTerm (-(n : ℤ) - 1) = jtpNegativeTerm n := by
  rw [jtpIntegerTerm, if_neg (by omega)]
  congr 1
  rw [show -(-(n : ℤ) - 1) - 1 = (n : ℤ) by ring]
  simp
@[simp] theorem signedEuler_C_T_mul_X_pow (z : ℤ) (e : ℕ) :
    signedEuler
        (PowerSeries.C (LaurentPolynomial.T z) * PowerSeries.X ^ e) =
      PowerSeries.C ((z : ℚ) * ((-1 : ℚ) ^ z)) *
        PowerSeries.X ^ e := by
  ext n
  rw [coeff_signedEuler, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul]
  rw [PowerSeries.coeff_X_pow]
  by_cases h : n = e
  · subst n
    simp
  · simp [h]
def cubePairEquiv : ℕ ⊕ ℕ ≃ ℤ where
  toFun s := match s with
    | Sum.inl t => (t : ℤ) + 1
    | Sum.inr t => -(t : ℤ)
  invFun z := if 0 < z then Sum.inl (z - 1).toNat else Sum.inr (-z).toNat
  left_inv := by
    rintro (t | t)
    · simp
    · change (if 0 < -(t : ℤ) then
          Sum.inl (-(t : ℤ) - 1).toNat
        else Sum.inr (-(-(t : ℤ))).toNat) = Sum.inr t
      rw [if_neg (by omega)]
      simp
  right_inv := by
    intro z
    simp only
    by_cases hz : 0 < z
    · rw [if_pos hz]
      change (((z - 1).toNat : ℕ) : ℤ) + 1 = z
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    · rw [if_neg hz]
      change -(((-z).toNat : ℕ) : ℤ) = z
      rw [Int.toNat_of_nonneg (by omega)]
      omega
end JacobiCubeProduct
end QEC.Coding.TannerLiftedProduct


