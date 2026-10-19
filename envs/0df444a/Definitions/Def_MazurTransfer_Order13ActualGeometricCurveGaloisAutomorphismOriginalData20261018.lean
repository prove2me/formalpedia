-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualGeometricCurveGaloisAutomorphismOriginalData20261018
-- name    : MazurTransfer_Order13ActualGeometricCurveGaloisAutomorphismOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T13:02:10.573988+00:00
-- url     : https://prove2.me/theorems/02de75b9-e636-4054-a3cd-5c807af13533
-- title:
--   Original Galois isomorphism of the literal actual curve
-- statement:
--   Preserve the original field-spectrum isomorphism, relative fibre automorphism and literal geometric curve Galois isomorphism, with all eight original declaration types and three nonproof values checked. The named downstream consumer is geometric Picard divisor-class Galois naturality.
-- source:
--   MazurTheorem original checked constructors and complete type/value audits; official FLT provenance retained where used.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a coefficient Galois automorphism induces a genuine
semilinear automorphism of the SAME literal extension-field curve through
the already checked rational-curve base-change isomorphism.
Named downstream consumer: geometric Picard divisor-class Galois naturality.
-/
import Definitions.Def_MazurTransfer_Order13GeometricRelativeCurveChangeData
import Definitions.Def_MazurTransfer_FieldPointActionsAndNormPreimageDifferenceData

noncomputable section
namespace MazurTransfer.Order13ActualGeometricCurveGaloisAutomorphism
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13GeometricRelativeCurveChange FieldAutomorphismOverPointAction
variable (K : Type) [Field K] [CharZero K]

def fieldSpectrumIso (σ : K ≃ₐ[ℚ] K) : Spec (CommRingCat.of K) ≅ Spec (CommRingCat.of K) where
  hom := (fieldAut ℚ K σ).left
  inv := (fieldAut ℚ K σ⁻¹).left
  hom_inv_id := by
    have h := congrArg (fun f => f.left) (fieldAut_mul ℚ K σ σ⁻¹)
    rw [mul_inv_cancel, fieldAut_one] at h
    exact h.symm
  inv_hom_id := by
    have h := congrArg (fun f => f.left) (fieldAut_mul ℚ K σ⁻¹ σ)
    rw [inv_mul_cancel, fieldAut_one] at h
    exact h.symm

theorem fieldSpectrumIso_over (σ : K ≃ₐ[ℚ] K) :
    (fieldSpectrumIso K σ).hom ≫ fieldBase ℚ K = fieldBase ℚ K :=
  Over.w (fieldAut ℚ K σ)

def relativeFibreAut (σ : K ≃ₐ[ℚ] K) :
    pullback (curveToBase ℚ) (fieldBase ℚ K) ⟶ pullback (curveToBase ℚ) (fieldBase ℚ K) :=
  pullback.map _ _ _ _ (𝟙 _) (fieldSpectrumIso K σ).hom (𝟙 _)
    (by simp) (by simpa using (fieldSpectrumIso_over K σ).symm)

instance relativeFibreAut_isIso (σ : K ≃ₐ[ℚ] K) : IsIso (relativeFibreAut K σ) := by
  unfold relativeFibreAut
  infer_instance

def geometricCurveGaloisIso (σ : K ≃ₐ[ℚ] K) : curveScheme K ≅ curveScheme K :=
  asIso (geometricCurveEmbedding K) ≪≫ asIso (relativeFibreAut K σ) ≪≫
    (asIso (geometricCurveEmbedding K)).symm

theorem geometricCurveGaloisIso_embedding (σ : K ≃ₐ[ℚ] K) :
    (geometricCurveGaloisIso K σ).hom ≫ geometricCurveEmbedding K =
      geometricCurveEmbedding K ≫ relativeFibreAut K σ := by
  simp only [geometricCurveGaloisIso, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  have h : (asIso (geometricCurveEmbedding K)).inv ≫ geometricCurveEmbedding K = 𝟙 _ :=
    (asIso (geometricCurveEmbedding K)).inv_hom_id
  simp only [Category.assoc, h, Category.comp_id]

theorem geometricCurveGaloisIso_toBase (σ : K ≃ₐ[ℚ] K) :
    (geometricCurveGaloisIso K σ).hom ≫ curveToBase K =
      curveToBase K ≫ (fieldSpectrumIso K σ).hom := by
  rw [← geometricCurveEmbedding_snd K, ← Category.assoc,
    geometricCurveGaloisIso_embedding]
  simp only [Category.assoc, relativeFibreAut, fieldBase, pullback.map, pullback.lift_snd]

theorem geometricCurveGaloisIso_curveMap (σ : K ≃ₐ[ℚ] K) :
    (geometricCurveGaloisIso K σ).hom ≫ Order13ActualCurveBaseChange.curveMap ℚ K =
      Order13ActualCurveBaseChange.curveMap ℚ K := by
  rw [← geometricCurveEmbedding_fst K, ← Category.assoc,
    geometricCurveGaloisIso_embedding]
  simp only [Category.assoc, relativeFibreAut, fieldBase, pullback.map, pullback.lift_fst, Category.comp_id]

end MazurTransfer.Order13ActualGeometricCurveGaloisAutomorphism
#print axioms MazurTransfer.Order13ActualGeometricCurveGaloisAutomorphism.geometricCurveGaloisIso_toBase
#print axioms MazurTransfer.Order13ActualGeometricCurveGaloisAutomorphism.geometricCurveGaloisIso_curveMap


