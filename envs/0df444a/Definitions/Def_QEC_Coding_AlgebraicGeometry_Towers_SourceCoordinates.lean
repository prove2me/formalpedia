-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceCoordinates
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:38.263921+00:00
-- url     : https://prove2.me/theorems/67a5b85b-316a-467e-bcfc-b618f3b58f04
-- title:
--   Source Coordinates
-- statement:
--   Definitions and structural lemmas for Source Coordinates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceCoordinates.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalCoordinateCells
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_trans
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_regularQuadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_rationalRecursion_next_finite_separable
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceBasicSourceCoordinate_transcendental
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceRecursion_equation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepDistinguishedCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepFieldEmbedding
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepReciprocalRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_comapAlgEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_regularQuadraticArtinSchreierIntegralRoot
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
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
open IntermediateField
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
def sourceCoordinates : (m : ℕ) → ℕ → SourceField m
  | 0, _ => sourceDistinguishedCoordinate 0
  | m + 1, i => if i ≤ m then sourceRecursionEmbedding m (sourceCoordinates m i)
      else sourceDistinguishedCoordinate (m + 1)
theorem sourceCoordinates_succ_of_le (m i : ℕ) (hi : i ≤ m) :
    sourceCoordinates (m + 1) i = sourceRecursionEmbedding m (sourceCoordinates m i) := by
  simp only [sourceCoordinates, if_pos hi]
theorem sourceCoordinates_of_le (m i : ℕ) (hi : m ≤ i) :
    sourceCoordinates m i = sourceDistinguishedCoordinate m := by
  cases m with
  | zero => rfl
  | succ m => simp only [sourceCoordinates, if_neg (by omega : ¬i ≤ m)]
theorem sourceCoordinates_last (m : ℕ) :
    sourceCoordinates m m = sourceDistinguishedCoordinate m := sourceCoordinates_of_le m m le_rfl
theorem sourceCoordinates_transcendental (m i : ℕ) :
    Transcendental F256 (sourceCoordinates m i) := by
  induction m with
  | zero => exact sourceBasicSourceCoordinate_transcendental 0
  | succ m ih =>
      by_cases hi : i ≤ m
      · rw [sourceCoordinates_succ_of_le m i hi]
        intro ha
        exact ih ((isAlgebraic_algHom_iff (sourceRecursionEmbedding m)
          (sourceRecursionEmbedding m).injective).mp ha)
      · rw [sourceCoordinates_of_le (m + 1) i (by omega)]
        exact sourceBasicSourceCoordinate_transcendental (m + 1)
theorem sourceCoordinates_recursion (m i : ℕ) (hi : i < m) :
    sourceCoordinates m (i + 1) ^ 16 + sourceCoordinates m (i + 1) =
      sourceStepRhs (sourceCoordinates m i) := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases him : i < m
      · rw [sourceCoordinates_succ_of_le m (i + 1) (by omega),
          sourceCoordinates_succ_of_le m i (by omega)]
        simpa only [map_add, map_pow, sourceStepRhs, map_div₀, map_one] using
          congrArg (sourceRecursionEmbedding m) (ih him)
      · have hieq : i = m := by omega
        subst i
        rw [sourceCoordinates_last, sourceCoordinates_succ_of_le m m le_rfl,
          sourceCoordinates_last]
        simpa only [sourceStepRhs, map_div₀, map_pow, map_add, map_one] using
          sourceRecursion_equation m
theorem sourceCoordinates_zero (m : ℕ) :
    sourceCoordinates m 0 = algebraMap (RatFunc F256) (SourceField m) RatFunc.X := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [sourceCoordinates_succ_of_le m 0 (Nat.zero_le m), ih]
      rfl
theorem sourceCoordinates_seed_finite_separable (m : ℕ) :
    FiniteDimensional F256⟮sourceCoordinates m 0⟯ (SourceField m) ∧
      Algebra.IsSeparable F256⟮sourceCoordinates m 0⟯ (SourceField m) := by
  let j := IsScalarTower.toAlgHom F256 (RatFunc F256) (SourceField m)
  let K := j.fieldRange
  let jK : RatFunc F256 →ₐ[F256] K := j.codRestrict K.toSubalgebra (fun r => ⟨r, rfl⟩)
  letI : Algebra (RatFunc F256) K := jK.toRingHom.toAlgebra
  letI : IsScalarTower (RatFunc F256) K (SourceField m) := IsScalarTower.of_algebraMap_eq' rfl
  have hresult : FiniteDimensional K (SourceField m) ∧ Algebra.IsSeparable K (SourceField m) :=
    ⟨Module.Finite.of_restrictScalars_finite (RatFunc F256) K (SourceField m),
      Algebra.isSeparable_tower_top_of_isSeparable (RatFunc F256) K (SourceField m)⟩
  have hK : K = F256⟮sourceCoordinates m 0⟯ := by
    rw [sourceCoordinates_zero]
    change j.fieldRange = F256⟮j RatFunc.X⟯
    rw [AlgHom.fieldRange_eq_map, ← RatFunc.adjoin_X,
      IntermediateField.adjoin_map, Set.image_singleton]
  rw [hK] at hresult
  exact hresult
theorem sourceCoordinates_finite_separable (m i : ℕ) :
    FiniteDimensional F256⟮sourceCoordinates m i⟯ (SourceField m) ∧
      Algebra.IsSeparable F256⟮sourceCoordinates m i⟯ (SourceField m) := by
  induction i with
  | zero => exact sourceCoordinates_seed_finite_separable m
  | succ i ih =>
      by_cases hi : i < m
      · letI := ih.1
        letI := ih.2
        exact rationalRecursion_next_finite_separable (sourceCoordinates m i)
          (sourceCoordinates m (i + 1)) (sourceCoordinates_transcendental m i)
          (sourceCoordinates_transcendental m (i + 1)) (sourceCoordinates_recursion m i hi)
      · have heq : sourceCoordinates m (i + 1) = sourceCoordinates m i :=
          (sourceCoordinates_of_le m (i + 1) (by omega)).trans
            (sourceCoordinates_of_le m i (by omega)).symm
        rw [heq]
        exact ih
scoped instance sourceCoordinates_finite (m i : ℕ) :
    FiniteDimensional F256⟮sourceCoordinates m i⟯ (SourceField m) :=
  (sourceCoordinates_finite_separable m i).1
scoped instance sourceCoordinates_separable (m i : ℕ) :
    Algebra.IsSeparable F256⟮sourceCoordinates m i⟯ (SourceField m) :=
  (sourceCoordinates_finite_separable m i).2
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


