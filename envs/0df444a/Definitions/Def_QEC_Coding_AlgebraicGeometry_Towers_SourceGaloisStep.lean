-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisStep
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:51:18.64533+00:00
-- url     : https://prove2.me/theorems/ecab7244-3111-4d76-af48-741dc87cb575
-- title:
--   Source Galois Step
-- statement:
--   Definitions and structural lemmas for Source Galois Step, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisStep.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
import Mathlib.FieldTheory.Galois.Basic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ArtinSchreier_ker_card
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepCoordinate_equation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepReciprocalRoot_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStep_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
theorem sourceTranslation_rhs_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepRhs x ≠ 0 := by
  intro hzero
  have horder := sourceStepRhs_order P x hx
  rw [hzero] at horder
  simp [GlobalPlace.order] at horder
theorem sourceTranslation_kernel_equation
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    (algebraMap F256 (SourceStepField P x hx) (c : F256)) ^ 16 +
        algebraMap F256 (SourceStepField P x hx) (c : F256) = 0 := by
  have hc : (c : F256) ^ 16 + (c : F256) = 0 := by
    have hc' : f256ArtinSchreier (c : F256) = 0 :=
      LinearMap.mem_ker.mp c.property
    simpa only [f256ArtinSchreier_apply] using hc'
  simpa only [map_add, map_pow, map_zero] using
    congrArg (algebraMap F256 (SourceStepField P x hx)) hc
theorem sourceTranslatedCoordinate_equation
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    (sourceStepCoordinate P x hx +
          algebraMap F256 (SourceStepField P x hx) (c : F256)) ^ 16 +
        (sourceStepCoordinate P x hx +
          algebraMap F256 (SourceStepField P x hx) (c : F256)) =
      sourceStepEmbedding P x hx (sourceStepRhs x) := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP (SourceStepField P x hx) 2 :=
    charP_of_injective_algebraMap
      (algebraMap K (SourceStepField P x hx)).injective 2
  have hstep := sourceStepCoordinate_equation P x hx
  have hkernel := sourceTranslation_kernel_equation P x hx c
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, add_pow_char_pow]
  linear_combination hstep + hkernel
theorem sourceTranslatedCoordinate_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    sourceStepCoordinate P x hx +
        algebraMap F256 (SourceStepField P x hx) (c : F256) ≠ 0 := by
  intro hzero
  have hequation := sourceTranslatedCoordinate_equation P x hx c
  rw [hzero] at hequation
  simp only [zero_pow (by norm_num : (16 : ℕ) ≠ 0), zero_add] at hequation
  apply (sourceStepEmbedding P x hx).injective.ne
    (sourceTranslation_rhs_ne_zero P x hx)
  simp only [map_zero]
  exact hequation.symm
noncomputable def sourceTranslatedReciprocalRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) : SourceStepField P x hx :=
  (sourceStepCoordinate P x hx +
    algebraMap F256 (SourceStepField P x hx) (c : F256))⁻¹
theorem sourceStepPolynomial_eq_translation_explicit
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepPolynomial P x hx =
      X ^ 16 + C (sourceStepRhs x)⁻¹ * X ^ 15 +
        C (sourceStepRhs x)⁻¹ := by
  simp [sourceStepPolynomial, sourceStepReciprocalPolynomial,
    sourceStepUniformizer, coe_reciprocalUniformizer]
theorem sourceTranslatedReciprocalRoot_isRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    eval₂ (Algebra.ofId K (SourceStepField P x hx))
      (sourceTranslatedReciprocalRoot P x hx c)
      (sourceStepPolynomial P x hx) = 0 := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP (SourceStepField P x hx) 2 :=
    charP_of_injective_algebraMap
      (algebraMap K (SourceStepField P x hx)).injective 2
  let a := sourceStepEmbedding P x hx (sourceStepRhs x)
  let y := sourceStepCoordinate P x hx +
    algebraMap F256 (SourceStepField P x hx) (c : F256)
  have ha : a ≠ 0 := by
    have hport := (sourceStepEmbedding P x hx).injective.ne
      (sourceTranslation_rhs_ne_zero P x hx)
    simp only [a, map_zero] at hport ⊢
    exact hport
  have hy : y ≠ 0 := sourceTranslatedCoordinate_ne_zero P x hx c
  have hyAS : y ^ 16 + y = a :=
    sourceTranslatedCoordinate_equation P x hx c
  have htwo : (2 : SourceStepField P x hx) = 0 :=
    CharP.cast_eq_zero (SourceStepField P x hx) 2
  have hexplicit :
      y⁻¹ ^ 16 + a⁻¹ * y⁻¹ ^ 15 + a⁻¹ = 0 := by
    field_simp [ha, hy]
    linear_combination hyAS + a * htwo
  have hpoly := sourceStepPolynomial_eq_translation_explicit P x hx
  calc
    eval₂ (Algebra.ofId K (SourceStepField P x hx))
        (sourceTranslatedReciprocalRoot P x hx c)
        (sourceStepPolynomial P x hx) =
        eval₂ (Algebra.ofId K (SourceStepField P x hx))
          (sourceTranslatedReciprocalRoot P x hx c)
          (X ^ 16 + C (sourceStepRhs x)⁻¹ * X ^ 15 +
            C (sourceStepRhs x)⁻¹) :=
      congrArg
        (eval₂ (Algebra.ofId K (SourceStepField P x hx))
          (sourceTranslatedReciprocalRoot P x hx c)) hpoly
    _ = 0 := by
      rw [eval₂_add, eval₂_add, eval₂_X_pow,
        eval₂_mul, eval₂_C, eval₂_X_pow]
      simp only [sourceTranslatedReciprocalRoot, a, y,
        sourceStepEmbedding, map_inv₀] at hexplicit ⊢
      exact hexplicit
noncomputable def sourceStepTranslationHom
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    SourceStepField P x hx →ₐ[K] SourceStepField P x hx :=
  AdjoinRoot.liftAlgHom (sourceStepPolynomial P x hx)
    (Algebra.ofId K (SourceStepField P x hx))
    (sourceTranslatedReciprocalRoot P x hx c)
    (sourceTranslatedReciprocalRoot_isRoot P x hx c)
@[simp]
theorem sourceStepTranslationHom_apply_root
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    sourceStepTranslationHom P x hx c (sourceStepReciprocalRoot P x hx) =
      sourceTranslatedReciprocalRoot P x hx c := by
  simp only [sourceStepTranslationHom, sourceStepReciprocalRoot,
    AdjoinRoot.liftAlgHom_root]
theorem sourceStepTranslationHom_fixes_constant
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    sourceStepTranslationHom P x hx c
        (algebraMap F256 (SourceStepField P x hx) (c : F256)) =
      algebraMap F256 (SourceStepField P x hx) (c : F256) := by
  rw [IsScalarTower.algebraMap_apply F256 K (SourceStepField P x hx)]
  exact (sourceStepTranslationHom P x hx c).commutes _
theorem sourceStepTranslationHom_apply_coordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    sourceStepTranslationHom P x hx c (sourceStepCoordinate P x hx) =
      sourceStepCoordinate P x hx +
        algebraMap F256 (SourceStepField P x hx) (c : F256) := by
  rw [sourceStepCoordinate, map_inv₀,
    sourceStepTranslationHom_apply_root]
  simp only [sourceTranslatedReciprocalRoot,
    inv_inv, sourceStepCoordinate]
theorem sourceStepTranslationHom_apply_translatedReciprocalRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    sourceStepTranslationHom P x hx c
        (sourceTranslatedReciprocalRoot P x hx c) =
      sourceStepReciprocalRoot P x hx := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP (SourceStepField P x hx) 2 :=
    charP_of_injective_algebraMap
      (algebraMap K (SourceStepField P x hx)).injective 2
  have hw : sourceStepReciprocalRoot P x hx ≠ 0 :=
    sourceStepReciprocalRoot_ne_zero P x hx
  rw [sourceTranslatedReciprocalRoot, map_inv₀, map_add,
    sourceStepTranslationHom_apply_coordinate,
    sourceStepTranslationHom_fixes_constant,
    add_assoc, CharTwo.add_self_eq_zero, add_zero,
    sourceStepCoordinate]
  exact inv_inv _
theorem sourceStepTranslationHom_comp_self
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    (sourceStepTranslationHom P x hx c).comp
        (sourceStepTranslationHom P x hx c) =
      AlgHom.id K (SourceStepField P x hx) := by
  apply AdjoinRoot.algHom_ext
  change sourceStepTranslationHom P x hx c
      (sourceStepTranslationHom P x hx c
        (sourceStepReciprocalRoot P x hx)) =
    sourceStepReciprocalRoot P x hx
  rw [sourceStepTranslationHom_apply_root,
    sourceStepTranslationHom_apply_translatedReciprocalRoot]
noncomputable def sourceStepTranslation
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    SourceStepField P x hx ≃ₐ[K] SourceStepField P x hx :=
  AlgEquiv.ofAlgHom (sourceStepTranslationHom P x hx c)
    (sourceStepTranslationHom P x hx c)
    (sourceStepTranslationHom_comp_self P x hx c)
    (sourceStepTranslationHom_comp_self P x hx c)
theorem sourceStepTranslation_apply_coordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    sourceStepTranslation P x hx c (sourceStepCoordinate P x hx) =
      sourceStepCoordinate P x hx +
        algebraMap F256 (SourceStepField P x hx) (c : F256) :=
  sourceStepTranslationHom_apply_coordinate P x hx c
theorem sourceStepTranslation_injective
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Function.Injective (sourceStepTranslation P x hx) := by
  intro c d hcd
  have hcoordinate := congrArg
    (fun e : SourceStepField P x hx ≃ₐ[K] SourceStepField P x hx =>
      e (sourceStepCoordinate P x hx)) hcd
  change sourceStepTranslation P x hx c (sourceStepCoordinate P x hx) =
    sourceStepTranslation P x hx d (sourceStepCoordinate P x hx) at hcoordinate
  rw [sourceStepTranslation_apply_coordinate,
    sourceStepTranslation_apply_coordinate] at hcoordinate
  have hconstants :
      algebraMap F256 (SourceStepField P x hx) (c : F256) =
        algebraMap F256 (SourceStepField P x hx) (d : F256) :=
    add_left_cancel hcoordinate
  apply Subtype.ext
  exact (algebraMap F256 (SourceStepField P x hx)).injective hconstants
theorem sourceStepField_algEquiv_card
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Nat.card (SourceStepField P x hx ≃ₐ[K] SourceStepField P x hx) = 16 := by
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card (SourceStepField P x hx ≃ₐ[K] SourceStepField P x hx) ≤
          Module.finrank K (SourceStepField P x hx) := AlgEquiv.card_le
      _ = 16 := sourceStep_finrank P x hx
  · calc
      16 = Nat.card (LinearMap.ker f256ArtinSchreier) := by
        rw [Nat.card_eq_fintype_card, f256ArtinSchreier_ker_card]
      _ ≤ Nat.card
          (SourceStepField P x hx ≃ₐ[K] SourceStepField P x hx) :=
        Nat.card_le_card_of_injective (sourceStepTranslation P x hx)
          (sourceStepTranslation_injective P x hx)
noncomputable instance sourceStepField_isGalois
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsGalois K (SourceStepField P x hx) := by
  apply IsGalois.of_card_aut_eq_finrank
  rw [sourceStepField_algEquiv_card, sourceStep_finrank]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


