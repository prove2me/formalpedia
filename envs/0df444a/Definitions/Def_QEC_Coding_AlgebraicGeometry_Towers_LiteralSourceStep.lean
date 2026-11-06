-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_LiteralSourceStep
-- name    : QEC_Coding_AlgebraicGeometry_Towers_LiteralSourceStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:04:25.887061+00:00
-- url     : https://prove2.me/theorems/c169c1af-cda5-47c8-a283-0b6a73e8179c
-- title:
--   Literal Source Step
-- statement:
--   Definitions and structural lemmas for Literal Source Step, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/LiteralSourceStep.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
open Polynomial IntermediateField
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K E : Type*} [_root_.Field K] [_root_.Field E]
  [Algebra F256 K] [Algebra K E]
noncomputable def sourceStepLiteralAdjoinHom
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (y : E) (hy : y ^ 16 + y = algebraMap K E (sourceStepRhs x)) :
    SourceStepField P x hx →ₐ[K] K⟮y⟯ := by
  let z : K⟮y⟯ := AdjoinSimple.gen K y
  have hz : z ^ 16 + z = algebraMap K K⟮y⟯ (sourceStepRhs x) := by
    apply Subtype.ext
    exact hy
  have ha0 : sourceStepRhs x ≠ 0 := by
    intro h
    have ho := sourceStepRhs_order P x hx
    simp [h, GlobalPlace.order] at ho
  have haL : algebraMap K K⟮y⟯ (sourceStepRhs x) ≠ 0 := by
    simpa only [map_zero] using (algebraMap K K⟮y⟯).injective.ne ha0
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
    exact haL hz.symm
  have hroot : eval₂ (Algebra.ofId K K⟮y⟯) z⁻¹
      (sourceStepPolynomial P x hx) = 0 := by
    have hc : ((Algebra.ofId K K⟮y⟯ : K →+* K⟮y⟯).comp
        (algebraMap P.valuationRing K)) (sourceStepUniformizer P x hx) =
        (algebraMap K K⟮y⟯ (sourceStepRhs x))⁻¹ := by
      change algebraMap K K⟮y⟯ ((sourceStepUniformizer P x hx : P.valuationRing) : K) = _
      rw [coe_sourceStepUniformizer, map_inv₀]
    rw [sourceStepPolynomial, Polynomial.eval₂_map]
    simp only [sourceStepReciprocalPolynomial, eval₂_add,
      eval₂_X_pow, eval₂_mul, eval₂_C]
    rw [hc]
    change z⁻¹ ^ 16 + (algebraMap K K⟮y⟯ (sourceStepRhs x))⁻¹ * z⁻¹ ^ 15 +
      (algebraMap K K⟮y⟯ (sourceStepRhs x))⁻¹ = 0
    letI : CharP F256 2 :=
      charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
    letI : CharP K 2 :=
      charP_of_injective_algebraMap (algebraMap F256 K).injective 2
    letI : CharP K⟮y⟯ 2 :=
      charP_of_injective_algebraMap (algebraMap K K⟮y⟯).injective 2
    field_simp [hz0, haL]
    rw [← hz]
    calc
      z ^ 16 + z + z + z ^ 16 = (z ^ 16 + z ^ 16) + (z + z) := by ac_rfl
      _ = 0 := by simp only [CharTwo.add_self_eq_zero]
    all_goals simp
  exact AdjoinRoot.liftAlgHom _ (Algebra.ofId K K⟮y⟯) z⁻¹ hroot
theorem sourceStepLiteralAdjoinHom_apply_coordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (y : E) (hy : y ^ 16 + y = algebraMap K E (sourceStepRhs x)) :
    sourceStepLiteralAdjoinHom P x hx y hy (sourceStepCoordinate P x hx) =
      AdjoinSimple.gen K y := by
  simp only [sourceStepLiteralAdjoinHom, sourceStepCoordinate,
    sourceStepReciprocalRoot, map_inv₀, AdjoinRoot.liftAlgHom_root, inv_inv]
theorem sourceStepLiteralAdjoinHom_surjective
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (y : E) (hy : y ^ 16 + y = algebraMap K E (sourceStepRhs x)) :
    Function.Surjective (sourceStepLiteralAdjoinHom P x hx y hy) := by
  let f := sourceStepLiteralAdjoinHom P x hx y hy
  rintro ⟨z, hz⟩
  induction hz using IntermediateField.adjoin_induction with
  | mem v hv =>
      have h : v = y := Set.mem_singleton_iff.mp hv
      subst v
      exact ⟨sourceStepCoordinate P x hx,
        sourceStepLiteralAdjoinHom_apply_coordinate P x hx y hy⟩
  | algebraMap v =>
      refine ⟨algebraMap K (SourceStepField P x hx) v, ?_⟩
      exact f.commutes v
  | add v w _ _ hv hw =>
      obtain ⟨v', hv'⟩ := hv
      obtain ⟨w', hw'⟩ := hw
      refine ⟨v' + w', ?_⟩
      rw [map_add, hv', hw']
      rfl
  | inv v _ hv =>
      obtain ⟨v', hv'⟩ := hv
      refine ⟨v'⁻¹, ?_⟩
      rw [map_inv₀, hv']
      rfl
  | mul v w _ _ hv hw =>
      obtain ⟨v', hv'⟩ := hv
      obtain ⟨w', hw'⟩ := hw
      refine ⟨v' * w', ?_⟩
      rw [map_mul, hv', hw']
      rfl
noncomputable def sourceStepLiteralAdjoinEquiv
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (y : E) (hy : y ^ 16 + y = algebraMap K E (sourceStepRhs x)) :
    SourceStepField P x hx ≃ₐ[K] K⟮y⟯ :=
  AlgEquiv.ofBijective (sourceStepLiteralAdjoinHom P x hx y hy)
    ⟨(sourceStepLiteralAdjoinHom P x hx y hy).injective,
      sourceStepLiteralAdjoinHom_surjective P x hx y hy⟩
noncomputable def sourceStepLiteralQuadraticRefinementEquiv
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (y : E) (hy : y ^ 16 + y = algebraMap K E (sourceStepRhs x)) :
    QuadraticArtinSchreierTowerField P (sourceStepRhs x)
        (sourceStepRhs_order P x hx) 4 ≃ₐ[K] K⟮y⟯ :=
  (sourceStepQuadraticRefinementEquiv P x hx).symm.trans
    (sourceStepLiteralAdjoinEquiv P x hx y hy)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


