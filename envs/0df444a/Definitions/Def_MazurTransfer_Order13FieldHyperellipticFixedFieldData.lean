-- Prove2me | Definitions.Def_MazurTransfer_Order13FieldHyperellipticFixedFieldData
-- name    : MazurTransfer_Order13FieldHyperellipticFixedFieldData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T17:38:56.526373+00:00
-- url     : https://prove2.me/theorems/514f904c-a1c6-40de-8200-6414dfef68f7
-- title:
--   The actual hyperelliptic rational field is the diamond-cube fixed field over characteristic-zero fields
-- statement:
--   Over every characteristic-zero field K, the actual field K(x) equals the fixed field of the diamond cube and is rational over K, with the original quadratic and exact degree-two Galois extension, involution subgroup and rational function-field equivalence. Twenty-one original types, including the finite-group proof-instance type, five data values and eight current/dependency scalar algebra providers are compared. Named downstream consumer: geometric-field hyperelliptic arithmetic Picard trace.
-- source:
--   Complete original MazurTheorem Order13FieldHyperellipticFixedField, using the published actual general-field coordinate generators, exact diamond order and finite automorphism-subgroup degree theorem. Official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the actual hyperelliptic involution fixed field
with the rational field K(x), including its rationality and degree-two Galois extension.
Named downstream consumer: the Picard involution-negation relation used
with the order-three quotient trace in the nineteen-isogeny descent.
-/
import Definitions.Def_MazurTransfer_Order13FieldFunctionFieldGeneratorsData
import Definitions.Def_MazurTransfer_Order13FieldDiamondExactOrderData
import Theorems.Thm_MazurTransfer_FiniteAutomorphismSubgroupFixedFieldDegree_finrank_fixedField

noncomputable section
universe w
namespace MazurTransfer.Order13FieldHyperellipticFixedField
open Polynomial
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13FieldOrdinaryPolynomialTranscendence
open Order13FieldDiamondFunctionFieldAutomorphism Order13FieldDiamondExactOrder
open Order13FieldDiamondFunctionFieldMap Order13FieldFunctionFieldGenerators
open Order13PellChartCertificate
variable (K : Type w) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
local instance : CharZero (actualCurveFunctionField K) := Algebra.charZero_of_charZero K _

def xField : IntermediateField K (actualCurveFunctionField K) :=
  IntermediateField.adjoin K {xImage K}

theorem x_mem : xImage K ∈ (xField K) := IntermediateField.subset_adjoin K _ (by simp)

theorem sextic_mem : sextic (xImage K) ∈ (xField K) := by
  change Order13PellChartCertificate.sextic (xImage K) ∈ (xField K)
  unfold Order13PellChartCertificate.sextic
  exact (xField K).add_mem
    ((xField K).add_mem
      ((xField K).add_mem
        ((xField K).add_mem
          ((xField K).add_mem
            ((xField K).add_mem (pow_mem (x_mem K) 6)
              ((xField K).mul_mem ((xField K).natCast_mem 2) (pow_mem (x_mem K) 5)))
            (pow_mem (x_mem K) 4))
          ((xField K).mul_mem ((xField K).natCast_mem 2) (pow_mem (x_mem K) 3)))
        ((xField K).mul_mem ((xField K).natCast_mem 6) (pow_mem (x_mem K) 2)))
      ((xField K).mul_mem ((xField K).natCast_mem 4) (x_mem K)))
    (xField K).one_mem

theorem y_generates : IntermediateField.adjoin (xField K) {yImage K} = ⊤ := by
  apply IntermediateField.restrictScalars_injective K
  rw [IntermediateField.restrictScalars_top]
  apply (intermediateField_eq_top K)
  · exact (IntermediateField.adjoin (xField K) {yImage K}).algebraMap_mem ⟨xImage K, (x_mem K)⟩
  · exact IntermediateField.subset_adjoin (xField K) _ (by simp)

def quadratic : Polynomial (xField K) := X ^ 2 - C ⟨sextic (xImage K), (sextic_mem K)⟩

theorem quadratic_monic : (quadratic K).Monic := monic_X_pow_sub_C _ (by decide : 2 ≠ 0)
theorem quadratic_degree : (quadratic K).natDegree = 2 := by unfold quadratic; compute_degree!
theorem quadratic_root : aeval (yImage K) (quadratic K) = 0 := by
  simp only [quadratic, map_sub, map_pow, aeval_X, aeval_C]
  change yImage K ^ 2 - sextic (xImage K) = 0
  exact sub_eq_zero.mpr (yImage_sq K)

theorem y_integral : IsIntegral (xField K) (yImage K) := ⟨(quadratic K), (quadratic_monic K), (quadratic_root K)⟩
theorem curveField_finite : FiniteDimensional (xField K) (actualCurveFunctionField K) := by
  have := IntermediateField.adjoin.finiteDimensional (y_integral K)
  rw [(y_generates K)] at this
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

theorem curveField_degree_le_two : Module.finrank (xField K) (actualCurveFunctionField K) ≤ 2 := by
  have H := Polynomial.natDegree_le_natDegree (minpoly.min (xField K) (yImage K) (quadratic_monic K) (quadratic_root K))
  rw [(quadratic_degree K)] at H
  rw [← IntermediateField.finrank_top', ← (y_generates K), IntermediateField.adjoin.finrank (y_integral K)]
  exact H

def involutionGroup : Subgroup (actualCurveFunctionField K ≃ₐ[K] actualCurveFunctionField K) :=
  Subgroup.zpowers ((diamondAlgEquiv K) ^ 3)

theorem involutionGroup_card : Nat.card (involutionGroup K) = 2 := by
  rw [involutionGroup, Nat.card_zpowers,
    orderOf_pow' (x := (diamondAlgEquiv K)) (n := 3) (by decide), (diamondAlgEquiv_order K)]
  norm_num
instance : Finite (involutionGroup K) := Nat.finite_of_card_ne_zero (by rw [(involutionGroup_card K)]; decide)

def involutionFixedField : IntermediateField K (actualCurveFunctionField K) :=
  IntermediateField.fixedField (involutionGroup K)

theorem fixedField_degree : Module.finrank (involutionFixedField K) (actualCurveFunctionField K) = 2 := by
  rw [involutionFixedField, FiniteAutomorphismSubgroupFixedFieldDegree.finrank_fixedField,
    (involutionGroup_card K)]

theorem x_fixedField_mem : xImage K ∈ (involutionFixedField K) := by
  apply (IntermediateField.mem_fixedField_iff _ _).mpr
  intro f hf
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
  have H : xImage K ∈ MulAction.fixedBy (actualCurveFunctionField K) ((diamondAlgEquiv K) ^ 3) := by
    change (diamondThird K) (xImage K) = xImage K
    exact (diamondThird_x K)
  exact MulAction.mem_fixedBy_zpow H n

theorem actual_hyperelliptic_fixed_field : (xField K) = (involutionFixedField K) := by
  have hle : (xField K) ≤ (involutionFixedField K) := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    exact Set.mem_singleton_iff.mp hz ▸ (x_fixedField_mem K)
  letI := (curveField_finite K)
  apply IntermediateField.eq_of_le_of_finrank_le' hle
  rw [(fixedField_degree K)]
  exact (curveField_degree_le_two K)

theorem curveField_degree_two : Module.finrank (xField K) (actualCurveFunctionField K) = 2 := by
  rw [(actual_hyperelliptic_fixed_field K)]
  exact (fixedField_degree K)

local instance : Algebra K (xField K) := IntermediateField.algebra' (xField K)
local instance : Algebra K (RatFunc K) := RatFunc.instAlgebraOfPolynomial K K

def rationalInvolutionFieldEquiv : RatFunc K ≃ₐ[K] (xField K) :=
  RatFunc.algEquivOfTranscendental (xImage K) (xImage_transcendental K)

theorem curveField_galois : IsGalois (xField K) (actualCurveFunctionField K) := by
  rw [(actual_hyperelliptic_fixed_field K)]
  exact IsGalois.of_fixed_field (actualCurveFunctionField K) (involutionGroup K)

end MazurTransfer.Order13FieldHyperellipticFixedField
#print axioms MazurTransfer.Order13FieldHyperellipticFixedField.actual_hyperelliptic_fixed_field
#print axioms MazurTransfer.Order13FieldHyperellipticFixedField.rationalInvolutionFieldEquiv


