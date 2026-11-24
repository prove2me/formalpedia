-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:25:11.650284+00:00
-- url     : https://prove2.me/theorems/ac22f69d-d6fc-4073-982c-1667816936b9
-- title:
--   Continuous Mat Exp
-- statement:
--   Definitions and structural lemmas for Continuous Mat Exp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousMatExp.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
noncomputable section
namespace GlobalTheory.UpqExpChart
section General
variable {n : Type} [Fintype n] [DecidableEq n]
theorem exp_mul_exp_neg (X : Matrix n n ℂ) : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
  rw [← Matrix.exp_add_of_commute X (-X) (Commute.refl X).neg_right, add_neg_cancel,
    NormedSpace.exp_zero]
theorem exp_neg_mul_exp (X : Matrix n n ℂ) : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
  simpa using exp_mul_exp_neg (-X)
theorem exp_conj_invol {J : Matrix n n ℂ} (hJ : J * J = 1) (X : Matrix n n ℂ) :
    NormedSpace.exp (J * X * J) = J * NormedSpace.exp X * J :=
  Matrix.exp_units_conj (⟨J, J, hJ, hJ⟩ : (Matrix n n ℂ)ˣ) X
theorem exp_unitary {J : Matrix n n ℂ} (hJ : J * J = 1) {X : Matrix n n ℂ}
    (hX : Xᴴ * J + J * X = 0) : (NormedSpace.exp X)ᴴ * J * NormedSpace.exp X = J := by
  have h1 : Xᴴ = J * (-X) * J := by
    have : Xᴴ * J = J * (-X) := by rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hX
    rw [← this, Matrix.mul_assoc, hJ, Matrix.mul_one]
  rw [← Matrix.exp_conjTranspose, h1, exp_conj_invol hJ, Matrix.mul_assoc _ J J, hJ,
    Matrix.mul_one, Matrix.mul_assoc, exp_neg_mul_exp, Matrix.mul_one]
end General
theorem jpq_sq (P Q : ℕ) : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
def expU (P Q : ℕ) (X : lieU P Q) : UpqT P Q :=
  (⟨⟨NormedSpace.exp X.1, NormedSpace.exp (-X.1), exp_mul_exp_neg _, exp_neg_mul_exp _⟩,
    exp_unitary (jpq_sq P Q) X.2⟩ : Formalism.UG.Upq P Q)
end GlobalTheory.UpqExpChart


