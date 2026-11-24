-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousHPart
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousHPart
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:15:38.684957+00:00
-- url     : https://prove2.me/theorems/16463454-ae2c-4de6-b261-a1f8f6714daf
-- title:
--   Continuous HPart
-- statement:
--   Definitions and structural lemmas for Continuous HPart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousHPart.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open Matrix
namespace PI.ScMuExists.UnitaryGroupMassFormula
section Real
variable {n r : ℕ} (ε : Fin n → Bool)
def RFrame (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Prop :=
  (∀ a b, hJ ε (e a) (e b) = 0) ∧ (∀ a b, hJ ε (f a) (f b) = 0) ∧
  (∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) ∧
  (∀ a, hJ ε (e a) z = 0 ∧ hJ ε (f a) z = 0) ∧ hJ ε z z ≠ 0
def hJL (u : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun := hJ ε u
  map_add' x y := by simp [hJ, Matrix.mulVec_add, dotProduct_add]
  map_smul' c x := by simp [hJ, Matrix.mulVec_smul, dotProduct_smul]
def piW (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.id - ∑ a, (hJL ε (f a)).smulRight (e a) - ∑ a, (hJL ε (e a)).smulRight (f a) -
    ((hJ ε z z)⁻¹ • hJL ε z).smulRight z
variable {ε}
variable {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ}
def PwM (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' (piW ε e f z)
def hPart (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  1 - PwM ε e f z + PwM ε e f z * g * PwM ε e f z
end Real
end PI.ScMuExists.UnitaryGroupMassFormula


