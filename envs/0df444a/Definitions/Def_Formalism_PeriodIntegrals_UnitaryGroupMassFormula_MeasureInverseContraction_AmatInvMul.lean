-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:52:39.030719+00:00
-- url     : https://prove2.me/theorems/2c3db7b9-144d-4d7f-aaca-ee229367aafc
-- title:
--   Amat Inv Mul
-- statement:
--   Definitions and structural lemmas for Amat Inv Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
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
namespace PI.NMeasInv.UnitaryGroupMassFormula
section Loc
variable {n r : ℕ} (ε : Fin n → Bool)
theorem hJ_add (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  unfold hJ; rw [Matrix.mulVec_add, dotProduct_add]
theorem hJ_smul (x y : Fin n → ℂ) (c : ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  unfold hJ; rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
def lf (x : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun := hJ ε x
  map_add' := hJ_add ε x
  map_smul' y c := by simp [hJ_smul]
structure Gram (e f : Fin r → Fin n → ℂ) : Prop where
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ff : ∀ a b, hJ ε (f a) (f b) = 0
  ef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0
variable {ε} {e f : Fin r → Fin n → ℂ}
def Pw (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (v : Fin n → ℂ) : Fin n → ℂ :=
  v - ∑ b, hJ ε (f b) v • e b - ∑ b, hJ ε (e b) v • f b
def Afun (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (s : Fin r → ℝ) (v : Fin n → ℂ) : Fin n → ℂ :=
  ∑ b, ((s b : ℂ) * hJ ε (f b) v) • e b + ∑ b, ((s b : ℂ)⁻¹ * hJ ε (e b) v) • f b + Pw ε e f v
def Alin (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (s : Fin r → ℝ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  ∑ b, ((s b : ℂ) • lf ε (f b)).smulRight (e b) + ∑ b, ((s b : ℂ)⁻¹ • lf ε (e b)).smulRight (f b) +
    (LinearMap.id - ∑ b, (lf ε (f b)).smulRight (e b) - ∑ b, (lf ε (e b)).smulRight (f b))
def Amat (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (s : Fin r → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' (Alin ε e f s)
variable (hG : Gram ε e f)
include hG
end Loc
end PI.NMeasInv.UnitaryGroupMassFormula


