-- Prove2me | Definitions.Def_MazurTransfer_Order13FieldCurveInversePlaceSetData
-- name    : MazurTransfer_Order13FieldCurveInversePlaceSetData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T18:30:21.209843+00:00
-- url     : https://prove2.me/theorems/2b48232c-5814-41f1-bcbd-31270aa9640b
-- title:
--   Inverse curve pullback transports the actual closed-point place sets by the specified field action
-- statement:
--   Over every characteristic-zero field, membership in placesOf on the actual curve is characterized by its literal closed points, and inverse pullback by the original generic-compatible curve lift transports those place sets by the specified field automorphism. Both complete original types and the original local scalar algebra provider are compared. Named downstream consumer: full divisor-presentation pullback on the actual field curve.
-- source:
--   Complete original MazurTheorem geometric diamond/closed-point transport statements and proofs, with public original map and isomorphism constructors. The original base-map compatibility statement is a checked bridge from the accepted Cartesian-square theorem. Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: inverse-curve preimages of opens transport the literal
sets of closed-point valuation places by the field automorphism. Named
downstream consumer: the range condition for transformed divisor presentations.
-/
import Definitions.Def_MazurTransfer_Order13FieldDiamondGenericCurveOrderData
import Definitions.Def_AlgebraicCurve_PlacesOf

noncomputable section
universe u
namespace MazurTransfer.Order13FieldCurveInversePlaceSet
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13FieldCurveAutomorphismLift Order13FieldDiamondGenericCurveOrder
open CurveClosedPointImage
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local notation "C" => curveScheme K
local notation "F" => actualCurveFunctionField K
local instance : Algebra K F := actualCurveFunctionFieldAlgebra K

theorem mem_placesOf_actual_iff (U : (curveScheme K).Opens) (v : Place K F) :
    v ∈ placesOf (curveToBase K) U ↔
      ∃ x : closedPoints C, x.1 ∈ U ∧ actualPlaceOfPoint K x = v := by
  constructor
  · rintro ⟨x, hxU, hx, hv⟩
    refine ⟨⟨x, hx⟩, hxU, ?_⟩
    have hR : (actualPlaceOfPoint K ⟨x, hx⟩).toValuationSubring.toSubring =
        v.toValuationSubring.toSubring := (actualPlaceOfPoint_stalk_range K ⟨x, hx⟩).symm.trans hv
    apply Place.ext
    ext a
    exact Iff.of_eq (congrArg (fun R : Subring F => a ∈ R) hR)
  · rintro ⟨x, hxU, rfl⟩
    exact ⟨x.1, hxU, x.2, actualPlaceOfPoint_stalk_range K x⟩

theorem inverse_placesOf (σ : F ≃ₐ[K] F) (U : (curveScheme K).Opens) :
    placesOf (curveToBase K) ((fieldLift K σ).inv ⁻¹ᵁ U) =
      (fun v : Place K F => σ • v) '' placesOf (curveToBase K) U := by
  ext v
  constructor
  · intro hv
    obtain ⟨x, hx, rfl⟩ := (mem_placesOf_actual_iff K _ _).mp hv
    let y := closedPointImage (fieldLift K σ).symm x
    have hy : actualPlaceOfPoint K y = σ⁻¹ • actualPlaceOfPoint K x := by
      have h := fieldLift_place K σ⁻¹ x
      rw [fieldLift_inv K] at h
      exact h
    refine ⟨actualPlaceOfPoint K y, (mem_placesOf_actual_iff K U _).mpr ⟨y, hx, rfl⟩, ?_⟩
    change σ • actualPlaceOfPoint K y = actualPlaceOfPoint K x
    rw [hy, smul_inv_smul]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (mem_placesOf_actual_iff K U w).mp hw
    let x := closedPointImage (fieldLift K σ) y
    apply (mem_placesOf_actual_iff K _ _).mpr
    refine ⟨x, ?_, fieldLift_place K σ y⟩
    change (fieldLift K σ).inv ((fieldLift K σ).hom y.1) ∈ U
    have h : (fieldLift K σ).inv ((fieldLift K σ).hom y.1) = y.1 := by
      exact congrArg (fun f : C ⟶ C => f y.1) (fieldLift K σ).hom_inv_id
    rw [h]
    exact hy

end MazurTransfer.Order13FieldCurveInversePlaceSet
#print axioms MazurTransfer.Order13FieldCurveInversePlaceSet.inverse_placesOf


