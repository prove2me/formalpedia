-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionFields
-- name    : QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionFields
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:12:33.835137+00:00
-- url     : https://prove2.me/theorems/45e476fa-846a-47ed-8cb1-8c16628432ae
-- title:
--   Basic Projection Fields
-- statement:
--   Definitions and structural lemmas for Basic Projection Fields, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasicProjectionFields.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_LiteralSourceStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalRecursionOrders
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceBasicSourceCoordinate_transcendental
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceRecursion_equation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepLiteral_adjoin_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepDistinguishedCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepFieldEmbedding
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepReciprocalRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_comapAlgEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepDistinguishedCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepFieldEmbedding
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepReciprocalRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.comapAlgEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
open IntermediateField
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
noncomputable def sourceBasicRationalInfinityPlace
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    (x : E) (hx : Transcendental F256 x) :
    GlobalPlace F256 F256⟮x⟯ :=
  GlobalPlace.comapAlgEquiv
    (RatFunc.algEquivOfTranscendental x hx).symm
    (GlobalPlace.rationalInfinity F256)
theorem sourceBasicRationalInfinityPlace_order_gen
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    (x : E) (hx : Transcendental F256 x) :
    (sourceBasicRationalInfinityPlace x hx).order
      (AdjoinSimple.gen F256 x) = -1 := by
  have hX : (GlobalPlace.rationalInfinity F256).order
      (RatFunc.X : RatFunc F256) = -1 := by
    exact sourceDistinguishedCoordinate_order 0
  rw [sourceBasicRationalInfinityPlace, GlobalPlace.comapAlgEquiv_order,
    RatFunc.algEquivOfTranscendental_symm_gen]
  exact hX
abbrev SourceBasicForwardField (i : ℕ) : Type :=
  F256⟮sourceRecursionEmbedding i (sourceDistinguishedCoordinate i)⟯
theorem sourceBasicForward_root_equation (i : ℕ) :
    sourceDistinguishedCoordinate (i + 1) ^ 16 +
        sourceDistinguishedCoordinate (i + 1) =
      algebraMap (SourceBasicForwardField i) (SourceField (i + 1))
        (sourceStepRhs
          (AdjoinSimple.gen F256
            (sourceRecursionEmbedding i (sourceDistinguishedCoordinate i)))) := by
  change sourceDistinguishedCoordinate (i + 1) ^ 16 +
      sourceDistinguishedCoordinate (i + 1) =
    sourceStepRhs
      (sourceRecursionEmbedding i (sourceDistinguishedCoordinate i))
  simpa only [sourceStepRhs, map_div₀, map_pow, map_add, map_one] using
    sourceRecursion_equation i
theorem sourceBasicForward_adjoin_finrank (i : ℕ) :
    Module.finrank (SourceBasicForwardField i)
      (SourceBasicForwardField i)⟮sourceDistinguishedCoordinate (i + 1)⟯ = 16 := by
  let x := sourceRecursionEmbedding i (sourceDistinguishedCoordinate i)
  have hx : Transcendental F256 x := by
    intro halg
    exact sourceBasicSourceCoordinate_transcendental i
      ((isAlgebraic_algHom_iff (sourceRecursionEmbedding i)
        (sourceRecursionEmbedding i).injective).mp halg)
  let Pinf : GlobalPlace F256 (SourceBasicForwardField i) :=
    sourceBasicRationalInfinityPlace x hx
  exact sourceStepLiteral_adjoin_finrank Pinf (AdjoinSimple.gen F256 x)
    (sourceBasicRationalInfinityPlace_order_gen x hx)
    (sourceDistinguishedCoordinate (i + 1))
    (sourceBasicForward_root_equation i)
theorem sourceBasicStepRhs_inverse_eq_inverseArtinSchreier
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    (x : E) (hx : x ≠ 0) :
    (sourceStepRhs x)⁻¹ = x⁻¹ ^ 16 + x⁻¹ := by
  rw [sourceStepRhs, inv_div]
  field_simp [hx]
  ring
theorem sourceBasicStepRhs_inv_eq_artinSchreier_inverse
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    (x : E) (hx : x ≠ 0) :
    sourceStepRhs x⁻¹ = (x ^ 16 + x)⁻¹ := by
  rw [sourceStepRhs]
  field_simp [hx]
  ring
theorem sourceBasicRecursion_reverse_equation (i : ℕ) :
    sourceRecursionEmbedding i ((sourceDistinguishedCoordinate i)⁻¹) ^ 16 +
        sourceRecursionEmbedding i ((sourceDistinguishedCoordinate i)⁻¹) =
      (sourceDistinguishedCoordinate (i + 1) ^ 16 +
        sourceDistinguishedCoordinate (i + 1))⁻¹ := by
  have hx : sourceDistinguishedCoordinate i ≠ 0 := by
    intro hzero
    have horder := sourceDistinguishedCoordinate_order i
    rw [hzero] at horder
    simp [GlobalPlace.order] at horder
  rw [sourceRecursion_equation, ← map_inv₀]
  rw [sourceBasicStepRhs_inverse_eq_inverseArtinSchreier _ hx]
  simp only [map_add, map_pow, map_inv₀]
abbrev SourceBasicReverseField (i : ℕ) : Type :=
  F256⟮(sourceDistinguishedCoordinate (i + 1))⁻¹⟯
theorem sourceBasicReverse_root_equation (i : ℕ) :
    sourceRecursionEmbedding i ((sourceDistinguishedCoordinate i)⁻¹) ^ 16 +
        sourceRecursionEmbedding i ((sourceDistinguishedCoordinate i)⁻¹) =
      algebraMap (SourceBasicReverseField i) (SourceField (i + 1))
        (sourceStepRhs
          (AdjoinSimple.gen F256
            ((sourceDistinguishedCoordinate (i + 1))⁻¹))) := by
  have hy : sourceDistinguishedCoordinate (i + 1) ≠ 0 := by
    intro hzero
    have horder := sourceDistinguishedCoordinate_order (i + 1)
    rw [hzero] at horder
    simp [GlobalPlace.order] at horder
  change sourceRecursionEmbedding i ((sourceDistinguishedCoordinate i)⁻¹) ^ 16 +
      sourceRecursionEmbedding i ((sourceDistinguishedCoordinate i)⁻¹) =
    sourceStepRhs ((sourceDistinguishedCoordinate (i + 1))⁻¹)
  rw [sourceBasicStepRhs_inv_eq_artinSchreier_inverse _ hy]
  exact sourceBasicRecursion_reverse_equation i
theorem sourceBasicReverse_adjoin_finrank (i : ℕ) :
    Module.finrank (SourceBasicReverseField i)
      (SourceBasicReverseField i)⟮
        sourceRecursionEmbedding i ((sourceDistinguishedCoordinate i)⁻¹)⟯ = 16 := by
  let yInv := (sourceDistinguishedCoordinate (i + 1))⁻¹
  have hyInvTrans : Transcendental F256 yInv := by
    intro halg
    exact sourceBasicSourceCoordinate_transcendental (i + 1)
      (IsAlgebraic.inv_iff.mp halg)
  let Pinf : GlobalPlace F256 (SourceBasicReverseField i) :=
    sourceBasicRationalInfinityPlace yInv hyInvTrans
  exact sourceStepLiteral_adjoin_finrank Pinf (AdjoinSimple.gen F256 yInv)
    (sourceBasicRationalInfinityPlace_order_gen yInv hyInvTrans)
    (sourceRecursionEmbedding i ((sourceDistinguishedCoordinate i)⁻¹))
    (sourceBasicReverse_root_equation i)
abbrev SourceBasicForwardExtensionField (i : ℕ) : Type :=
  (SourceBasicForwardField i)⟮sourceDistinguishedCoordinate (i + 1)⟯
abbrev SourceBasicReverseExtensionField (i : ℕ) : Type :=
  (SourceBasicReverseField i)⟮
    sourceRecursionEmbedding i ((sourceDistinguishedCoordinate i)⁻¹)⟯
noncomputable instance sourceBasicForwardExtension_finite (i : ℕ) :
    FiniteDimensional (SourceBasicForwardField i) (SourceBasicForwardExtensionField i) :=
  Module.finite_of_finrank_pos (by rw [sourceBasicForward_adjoin_finrank]; norm_num)
noncomputable instance sourceBasicReverseExtension_finite (i : ℕ) :
    FiniteDimensional (SourceBasicReverseField i) (SourceBasicReverseExtensionField i) :=
  Module.finite_of_finrank_pos (by rw [sourceBasicReverse_adjoin_finrank]; norm_num)
noncomputable instance sourceBasicForwardExtension_separable (i : ℕ) :
    Algebra.IsSeparable (SourceBasicForwardField i) (SourceBasicForwardExtensionField i) := by
  let x := sourceRecursionEmbedding i (sourceDistinguishedCoordinate i)
  have hx : Transcendental F256 x := by
    intro halg
    exact sourceBasicSourceCoordinate_transcendental i
      ((isAlgebraic_algHom_iff (sourceRecursionEmbedding i)
        (sourceRecursionEmbedding i).injective).mp halg)
  let e := sourceStepLiteralAdjoinEquiv (sourceBasicRationalInfinityPlace x hx)
    (AdjoinSimple.gen F256 x) (sourceBasicRationalInfinityPlace_order_gen x hx)
    (sourceDistinguishedCoordinate (i + 1)) (sourceBasicForward_root_equation i)
  exact Algebra.IsSeparable.of_algHom (SourceBasicForwardField i)
    (SourceStepField (sourceBasicRationalInfinityPlace x hx)
      (AdjoinSimple.gen F256 x) (sourceBasicRationalInfinityPlace_order_gen x hx))
    e.symm.toAlgHom
noncomputable instance sourceBasicReverseExtension_separable (i : ℕ) :
    Algebra.IsSeparable (SourceBasicReverseField i) (SourceBasicReverseExtensionField i) := by
  let x := (sourceDistinguishedCoordinate (i + 1))⁻¹
  have hx : Transcendental F256 x := by
    intro halg
    exact sourceBasicSourceCoordinate_transcendental (i + 1)
      (IsAlgebraic.inv_iff.mp halg)
  let e := sourceStepLiteralAdjoinEquiv (sourceBasicRationalInfinityPlace x hx)
    (AdjoinSimple.gen F256 x) (sourceBasicRationalInfinityPlace_order_gen x hx)
    (sourceRecursionEmbedding i ((sourceDistinguishedCoordinate i)⁻¹))
    (sourceBasicReverse_root_equation i)
  exact Algebra.IsSeparable.of_algHom (SourceBasicReverseField i)
    (SourceStepField (sourceBasicRationalInfinityPlace x hx)
      (AdjoinSimple.gen F256 x) (sourceBasicRationalInfinityPlace_order_gen x hx))
    e.symm.toAlgHom
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


