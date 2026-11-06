-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Translation
-- name    : QEC_Coding_AlgebraicGeometry_Towers_Translation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:51:41.132081+00:00
-- url     : https://prove2.me/theorems/1608c4f9-8c0b-4ec9-b589-630e9e03f830
-- title:
--   Translation
-- statement:
--   Definitions and structural lemmas for Translation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Translation.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryCoordinate_artinSchreier
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepReciprocalRoot_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
instance stepTranslationConstantScalarTower
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsScalarTower F256 K (StepField P x hx) :=
  IsScalarTower.of_algebraMap_eq' rfl
theorem translation_coordinate_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) : x ≠ 0 := by
  intro hzero
  subst x
  simp [GlobalPlace.order] at hx
theorem translation_embedded_coordinate_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    stepFieldEmbedding P x hx x ≠ 0 := by
  have hport := (stepFieldEmbedding P x hx).injective.ne
    (translation_coordinate_ne_zero P x hx)
  simp only [map_zero] at hport ⊢
  exact hport
theorem translation_kernel_equation
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    (algebraMap F256 (StepField P x hx) (c : F256)) ^ 16 +
        algebraMap F256 (StepField P x hx) (c : F256) = 0 := by
  have hc : (c : F256) ^ 16 + (c : F256) = 0 := by
    have hc' : f256ArtinSchreier (c : F256) = 0 :=
      LinearMap.mem_ker.mp c.property
    simpa only [f256ArtinSchreier_apply] using hc'
  simpa only [map_add, map_pow, map_zero] using
    congrArg (algebraMap F256 (StepField P x hx)) hc
theorem translatedAuxiliaryCoordinate_artinSchreier
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    (stepAuxiliaryCoordinate P x hx +
          algebraMap F256 (StepField P x hx) (c : F256)) ^ 16 +
        (stepAuxiliaryCoordinate P x hx +
          algebraMap F256 (StepField P x hx) (c : F256)) =
      stepFieldEmbedding P x hx x ^ 17 := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP (StepField P x hx) 2 :=
    charP_of_injective_algebraMap
      (algebraMap K (StepField P x hx)).injective 2
  have hstep := stepAuxiliaryCoordinate_artinSchreier P x hx
  have hkernel := translation_kernel_equation P x hx c
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, add_pow_char_pow]
  linear_combination hstep + hkernel
theorem translatedAuxiliaryCoordinate_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    stepAuxiliaryCoordinate P x hx +
        algebraMap F256 (StepField P x hx) (c : F256) ≠ 0 := by
  intro hzero
  have htranslated := translatedAuxiliaryCoordinate_artinSchreier P x hx c
  rw [hzero] at htranslated
  simp only [zero_pow (by norm_num : (16 : ℕ) ≠ 0), zero_add] at htranslated
  exact (pow_ne_zero 17 (translation_embedded_coordinate_ne_zero P x hx))
    htranslated.symm
noncomputable def translatedReciprocalRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) : StepField P x hx :=
  stepFieldEmbedding P x hx x /
    (stepAuxiliaryCoordinate P x hx +
      algebraMap F256 (StepField P x hx) (c : F256))
theorem translatedReciprocalRoot_isRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    eval₂ (Algebra.ofId K (StepField P x hx))
      (translatedReciprocalRoot P x hx c) (stepPolynomial P x hx) = 0 := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP (StepField P x hx) 2 :=
    charP_of_injective_algebraMap
      (algebraMap K (StepField P x hx)).injective 2
  let X₀ := stepFieldEmbedding P x hx x
  let y := stepAuxiliaryCoordinate P x hx +
    algebraMap F256 (StepField P x hx) (c : F256)
  have hX₀ : X₀ ≠ 0 := translation_embedded_coordinate_ne_zero P x hx
  have hy : y ≠ 0 := translatedAuxiliaryCoordinate_ne_zero P x hx c
  have hyAS : y ^ 16 + y = X₀ ^ 17 :=
    translatedAuxiliaryCoordinate_artinSchreier P x hx c
  have htwo : (2 : StepField P x hx) = 0 :=
    CharP.cast_eq_zero (StepField P x hx) 2
  have hexplicit :
      (X₀ / y) ^ 16 + X₀⁻¹ ^ 16 * (X₀ / y) ^ 15 + X₀⁻¹ = 0 := by
    field_simp [hX₀, hy]
    linear_combination hyAS + X₀ ^ 17 * htwo
  have hpoly : stepPolynomial P x hx =
      X ^ 16 + C (x⁻¹ ^ 16) * X ^ 15 + C x⁻¹ := by
    simp [stepPolynomial, reciprocalPolynomial,
      coe_reciprocalUniformizer]
    rw [← map_pow, inv_pow]
  calc
    eval₂ (Algebra.ofId K (StepField P x hx))
        (translatedReciprocalRoot P x hx c) (stepPolynomial P x hx) =
        eval₂ (Algebra.ofId K (StepField P x hx))
          (translatedReciprocalRoot P x hx c)
          (X ^ 16 + C (x⁻¹ ^ 16) * X ^ 15 + C x⁻¹) :=
      congrArg
        (eval₂ (Algebra.ofId K (StepField P x hx))
          (translatedReciprocalRoot P x hx c)) hpoly
    _ = 0 := by
      rw [eval₂_add, eval₂_add, eval₂_X_pow,
        eval₂_mul, eval₂_C, eval₂_X_pow, eval₂_C]
      have hport := hexplicit
      simp only [translatedReciprocalRoot, X₀, y, stepFieldEmbedding, map_pow, map_inv₀] at hport ⊢
      exact hport
noncomputable def stepTranslationHom
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    StepField P x hx →ₐ[K] StepField P x hx :=
  AdjoinRoot.liftAlgHom (stepPolynomial P x hx)
    (Algebra.ofId K (StepField P x hx))
    (translatedReciprocalRoot P x hx c)
    (translatedReciprocalRoot_isRoot P x hx c)
@[simp]
theorem stepTranslationHom_apply_root
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    stepTranslationHom P x hx c (stepReciprocalRoot P x hx) =
      translatedReciprocalRoot P x hx c := by
  simp only [stepTranslationHom, stepReciprocalRoot,
    AdjoinRoot.liftAlgHom_root]
theorem stepTranslationHom_fixes_constant
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    stepTranslationHom P x hx c
        (algebraMap F256 (StepField P x hx) (c : F256)) =
      algebraMap F256 (StepField P x hx) (c : F256) := by
  rw [IsScalarTower.algebraMap_apply F256 K (StepField P x hx)]
  exact (stepTranslationHom P x hx c).commutes _
theorem stepTranslationHom_fixes_base
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) (r : K) :
    stepTranslationHom P x hx c (stepFieldEmbedding P x hx r) =
      stepFieldEmbedding P x hx r := by
  change stepTranslationHom P x hx c
      (algebraMap K (StepField P x hx) r) =
    algebraMap K (StepField P x hx) r
  exact (stepTranslationHom P x hx c).commutes r
theorem stepTranslationHom_apply_auxiliaryCoordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    stepTranslationHom P x hx c (stepAuxiliaryCoordinate P x hx) =
      stepAuxiliaryCoordinate P x hx +
        algebraMap F256 (StepField P x hx) (c : F256) := by
  have hX₀ := translation_embedded_coordinate_ne_zero P x hx
  have hy := translatedAuxiliaryCoordinate_ne_zero P x hx c
  rw [stepAuxiliaryCoordinate,
    map_div₀ (stepTranslationHom P x hx c),
    stepTranslationHom_fixes_base,
    stepTranslationHom_apply_root]
  simp only [translatedReciprocalRoot]
  field_simp [hX₀, hy]
  rw [stepAuxiliaryCoordinate]
theorem stepTranslationHom_apply_translatedReciprocalRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    stepTranslationHom P x hx c (translatedReciprocalRoot P x hx c) =
      stepReciprocalRoot P x hx := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP (StepField P x hx) 2 :=
    charP_of_injective_algebraMap
      (algebraMap K (StepField P x hx)).injective 2
  have hX₀ := translation_embedded_coordinate_ne_zero P x hx
  have hw := stepReciprocalRoot_ne_zero P x hx
  rw [translatedReciprocalRoot,
    map_div₀ (stepTranslationHom P x hx c),
    stepTranslationHom_fixes_base,
    map_add, stepTranslationHom_apply_auxiliaryCoordinate,
    stepTranslationHom_fixes_constant]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero,
    stepAuxiliaryCoordinate]
  field_simp [hX₀, hw]
theorem stepTranslationHom_comp_self
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    (stepTranslationHom P x hx c).comp (stepTranslationHom P x hx c) =
      AlgHom.id K (StepField P x hx) := by
  apply AdjoinRoot.algHom_ext
  change stepTranslationHom P x hx c
      (stepTranslationHom P x hx c (stepReciprocalRoot P x hx)) =
    stepReciprocalRoot P x hx
  rw [stepTranslationHom_apply_root,
    stepTranslationHom_apply_translatedReciprocalRoot]
noncomputable def stepTranslation
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    StepField P x hx ≃ₐ[K] StepField P x hx :=
  AlgEquiv.ofAlgHom (stepTranslationHom P x hx c)
    (stepTranslationHom P x hx c)
    (stepTranslationHom_comp_self P x hx c)
    (stepTranslationHom_comp_self P x hx c)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


