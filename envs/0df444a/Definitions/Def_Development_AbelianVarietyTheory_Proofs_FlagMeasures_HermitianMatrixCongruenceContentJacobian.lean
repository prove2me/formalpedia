-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMatrixCongruenceContentJacobian
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMatrixCongruenceContentJacobian
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:01:39.589238+00:00
-- url     : https://prove2.me/theorems/3cf88efa-674b-4135-9df9-31b295715718
-- title:
--   Hermitian Matrix Congruence Content Jacobian
-- statement:
--   Definitions and structural lemmas for Hermitian Matrix Congruence Content Jacobian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianMatrixCongruenceContentJacobian.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelVolMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical Kronecker
namespace GlobalTheory.HL.HermJacobian
section Alg
variable {E : Type} [CommRing E] {m : ℕ}
def coord (m : ℕ) (ω ω' e : E) (h : (ω - ω') * e = 1) :
    (Fin m × Fin m → E) ≃ₗ[E] Matrix (Fin m) (Fin m) E where
  toFun v := Matrix.of fun i j =>
    if i < j then v (i, j) + ω * v (j, i) else if j < i then v (j, i) + ω' * v (i, j) else v (i, j)
  invFun X := fun k =>
    if k.1 < k.2 then X k.1 k.2 - ω * (e * (X k.1 k.2 - X k.2 k.1))
    else if k.2 < k.1 then e * (X k.2 k.1 - X k.1 k.2) else X k.1 k.2
  map_add' v w := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c v := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring
  left_inv v := by
    funext ⟨i, j⟩
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp only [Matrix.of_apply, hij, hij.not_gt, if_true, if_false]
      linear_combination (-ω * v (j, i)) * h
    · simp
    · simp only [Matrix.of_apply, hij, hij.not_gt, if_true, if_false]
      linear_combination (v (i, j)) * h
  right_inv X := by
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp only [Matrix.of_apply, hij, hij.not_gt, if_true, if_false]
      ring
    · simp
    · simp only [Matrix.of_apply, hij, hij.not_gt, if_true, if_false]
      linear_combination (X i j - X j i) * h
def sandwich (B A : Matrix (Fin m) (Fin m) E) :
    Matrix (Fin m) (Fin m) E →ₗ[E] Matrix (Fin m) (Fin m) E where
  toFun X := B * X * A
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
end Alg
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
end GlobalTheory.HL.HermJacobian


