-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_CoordinateWindows
-- name    : QEC_Coding_AlgebraicGeometry_Towers_CoordinateWindows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:19:38.413325+00:00
-- url     : https://prove2.me/theorems/49a6a986-0647-415c-8d4a-8535af0a9977
-- title:
--   Coordinate Windows
-- statement:
--   Definitions and structural lemmas for Coordinate Windows, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/CoordinateWindows.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
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
variable {E : Type*} [_root_.Field E] [Algebra F256 E]
def coordinateWindow (x : ℕ → E) (a : ℕ) : ℕ → IntermediateField F256 E
  | 0 => F256⟮x a⟯
  | n + 1 => coordinateWindow x a n ⊔ F256⟮x (a + n + 1)⟯
theorem coordinateWindow_first_sup_tail (x : ℕ → E) (a n : ℕ) :
    coordinateWindow x a (n + 1) = F256⟮x a⟯ ⊔ coordinateWindow x (a + 1) n := by
  induction n with
  | zero => simp only [coordinateWindow, Nat.add_zero]
  | succ n ih =>
      rw [coordinateWindow, ih, sup_assoc, coordinateWindow]
      rw [show a + (n + 1) + 1 = (a + 1) + n + 1 by omega]
theorem coordinateWindow_first_le (x : ℕ → E) (a n : ℕ) :
    F256⟮x a⟯ ≤ coordinateWindow x a n := by
  cases n with
  | zero => exact le_rfl
  | succ n =>
      rw [coordinateWindow_first_sup_tail]
      exact le_sup_left
scoped instance coordinateWindow_finite (x : ℕ → E) (a n : ℕ)
    [FiniteDimensional F256⟮x a⟯ E] :
    FiniteDimensional (coordinateWindow x a n) E := by
  letI : Algebra F256⟮x a⟯ (coordinateWindow x a n) :=
    (IntermediateField.inclusion (coordinateWindow_first_le x a n)).toRingHom.toAlgebra
  letI : IsScalarTower F256⟮x a⟯ (coordinateWindow x a n) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact Module.Finite.of_restrictScalars_finite F256⟮x a⟯ (coordinateWindow x a n) E
scoped instance coordinateWindow_separable (x : ℕ → E) (a n : ℕ)
    [Algebra.IsSeparable F256⟮x a⟯ E] :
    Algebra.IsSeparable (coordinateWindow x a n) E := by
  letI : Algebra F256⟮x a⟯ (coordinateWindow x a n) :=
    (IntermediateField.inclusion (coordinateWindow_first_le x a n)).toRingHom.toAlgebra
  letI : IsScalarTower F256⟮x a⟯ (coordinateWindow x a n) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact Algebra.isSeparable_tower_top_of_isSeparable F256⟮x a⟯ (coordinateWindow x a n) E
variable (Q : GlobalPlace F256 E) [Finite Q.residueField] (x : ℕ → E)
    [∀ a, FiniteDimensional F256⟮x a⟯ E]
    [∀ a, Algebra.IsSeparable F256⟮x a⟯ E]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


