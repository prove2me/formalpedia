-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualDiamondCurveAutomorphism
-- name    : MazurTransfer_Order13ActualDiamondCurveAutomorphism
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T11:29:45.83603+00:00
-- url     : https://prove2.me/theorems/15f677d3-9984-410c-9e19-2ae283ffc35d
-- title:
--   The actual diamond isomorphism of the literal rational curve
-- statement:
--   The specified diamond automorphism of the existing rational function field extends to an isomorphism $\delta:C\simeq C$ of the literal order-thirteen curve over $\mathbb Q$. It preserves the structure morphism, as does its inverse, and on every closed-point place satisfies $$p_{\delta(x)}=\sigma\cdot p_x.$$ This isomorphism supplies the actual re-rigidified Picard pullback action.
-- source:
--   Original complete constructors and certificates from MazurTheorem Order13ActualDiamondCurveAutomorphism.lean and the short original place-action congruence helper, Apache-2.0, Vas and contributors. Seven complete original closed types and two data values are kernel-compared. Uses the original Proved Anthropic FLT fixed-model extension theorem at pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Original bodies are retained. Named downstream consumer: actual re-rigidified Picard diamond action.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Uses original official Anthropic FLT at exact pin
6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: the specified diamond field automorphism induces an
isomorphism of the literal curve, with its action on every closed-point place.
Named downstream consumer: the actual re-rigidified Picard diamond action. -/
import Definitions.Def_MazurTransfer_Order13ActualCurveModel
import Definitions.Def_MazurTransfer_Order13ActualDiamondFunctionFieldAutomorphism
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_iso_comp_toBase_eq_placeOfPoint_congr_eq
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the original FLT place congruence for a field
algebra automorphism with its genuine place action. Named downstream
consumer: the actual diamond curve isomorphism and arithmetic Picard action.
-/

noncomputable section
universe u v
namespace MazurTransfer.FieldAutomorphismPlaceCongruence
open AlgebraicCurve
open scoped Pointwise
variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

theorem congrRingEquiv_eq_smul (σ : F ≃ₐ[K] F) (p : Place K F) :
    Place.congrRingEquiv σ.toRingEquiv σ.commutes p = σ • p := by
  apply Place.ext
  ext x
  change σ.symm x ∈ p.toValuationSubring ↔ x ∈ σ • p.toValuationSubring
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

end MazurTransfer.FieldAutomorphismPlaceCongruence
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The fixed-model isomorphism extension is the checked original Anthropic FLT
at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: an automorphism of the literal order-thirteen curve over Q,
with its action on all closed-point places, rather than a relabelled model.
Named downstream consumer: re-rigidified pullback on its represented Picard
scheme and comparison with the checked arithmetic diamond action.
-/

noncomputable section
namespace MazurTransfer.Order13ActualDiamondCurveAutomorphism
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualArithmeticCurveModel Order13ActualDiamondFunctionFieldAutomorphism
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ

def closedPointImage (e : curveScheme ℚ ≅ curveScheme ℚ)
    (x : closedPoints (curveScheme ℚ)) : closedPoints (curveScheme ℚ) :=
  ⟨e.hom.base x.1, by
    show IsClosed ({e.hom.base x.1} : Set (curveScheme ℚ))
    rw [← Set.image_singleton]
    exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isClosedMap _ x.2⟩

theorem exists_diamondCurveIso :
    ∃ e : curveScheme ℚ ≅ curveScheme ℚ,
      e.hom ≫ curveToBase ℚ = curveToBase ℚ ∧
      ∀ x : closedPoints (curveScheme ℚ),
        actualPlaceOfPoint ℚ (closedPointImage e x) =
          diamondAlgEquiv • actualPlaceOfPoint ℚ x := by
  obtain ⟨e, he, hp⟩ := CurveModel.exists_iso_comp_toBase_eq_placeOfPoint_congr_eq
    diamondAlgEquiv (actualCurveModel ℚ) (actualCurveModel ℚ)
  refine ⟨e, he, fun x => ?_⟩
  exact (hp x).trans
    (FieldAutomorphismPlaceCongruence.congrRingEquiv_eq_smul diamondAlgEquiv
      (actualPlaceOfPoint ℚ x))

def diamondCurveIso : curveScheme ℚ ≅ curveScheme ℚ := exists_diamondCurveIso.choose

theorem diamondCurveIso_over :
    diamondCurveIso.hom ≫ curveToBase ℚ = curveToBase ℚ :=
  exists_diamondCurveIso.choose_spec.1

theorem diamondCurveIso_place (x : closedPoints (curveScheme ℚ)) :
    actualPlaceOfPoint ℚ (closedPointImage diamondCurveIso x) =
      diamondAlgEquiv • actualPlaceOfPoint ℚ x :=
  exists_diamondCurveIso.choose_spec.2 x

theorem diamondCurveIso_inv_over :
    diamondCurveIso.inv ≫ curveToBase ℚ = curveToBase ℚ := by
  have h := congrArg (fun f => diamondCurveIso.inv ≫ f) diamondCurveIso_over
  exact h.symm.trans (Iso.inv_hom_id_assoc diamondCurveIso (curveToBase ℚ))

end MazurTransfer.Order13ActualDiamondCurveAutomorphism
#print axioms MazurTransfer.Order13ActualDiamondCurveAutomorphism.exists_diamondCurveIso
#print axioms MazurTransfer.Order13ActualDiamondCurveAutomorphism.diamondCurveIso_place
#print axioms MazurTransfer.Order13ActualDiamondCurveAutomorphism.diamondCurveIso_inv_over


