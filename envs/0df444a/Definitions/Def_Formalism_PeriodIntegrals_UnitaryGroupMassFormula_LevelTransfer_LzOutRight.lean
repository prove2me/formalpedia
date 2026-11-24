-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzOutRight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzOutRight
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T13:50:47.544448+00:00
-- url     : https://prove2.me/theorems/6d83896e-2fe5-4640-923d-7861bdc321c8
-- title:
--   Lz Out Right
-- statement:
--   Definitions and structural lemmas for Lz Out Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzOutRight.lean

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PIQnLT
open Formalism.REAL Formalism.QuantumDeterminants
variable {k i r' : ℕ}
def Lz (k i r' : ℕ) (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ := fun p q =>
  if hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i then
    (if hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i then X ⟨p.val - i, by omega⟩ ⟨q.val - i, by omega⟩ else 0)
  else 0
def LzL (k i r' : ℕ) :
    Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ →ₗ[ℂ]
      Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ where
  toFun := Lz k i r'
  map_add' X Y := by
    ext p q; simp only [Lz, Matrix.add_apply]; split_ifs <;> simp
  map_smul' c X := by
    ext p q; simp only [Lz, Matrix.smul_apply, RingHom.id_apply]; split_ifs <;> simp
section Hom
variable (hL : LevHom)
include hL
end Hom
end PIQnLT


