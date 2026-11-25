-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T08:11:44.608825+00:00
-- url     : https://prove2.me/theorems/da3e0ac2-b24e-4d84-a1d2-84b7f80c6fd7
-- title:
--   Det Mul RCReal
-- statement:
--   Definitions and structural lemmas for Det Mul RCReal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/DetMulRCReal.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_TupPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.AprimeInfW
open MeasureTheory Matrix
section MulR
variable {r m : ℕ}
def mulRC (A : Matrix (Fin m) (Fin m) ℂ) : (Fin r → Fin m → ℂ) →ₗ[ℂ] (Fin r → Fin m → ℂ) :=
  LinearMap.pi fun i => A.vecMulLinear.comp (LinearMap.proj i)
def reimE : (Fin r → Fin m → ℂ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin r × Fin m × Bool) where
  toFun Y := reim (Matrix.of Y)
  invFun y := fun i j => ⟨y (i, j, true), y (i, j, false)⟩
  map_add' Y Z := by
    ext p
    rcases p with ⟨i, j, s⟩
    cases s <;> simp [reim]
  map_smul' c Y := by
    ext p
    rcases p with ⟨i, j, s⟩
    cases s <;> simp [reim]
  left_inv Y := by
    funext i j
    apply Complex.ext <;> simp [reim]
  right_inv y := by
    ext p
    rcases p with ⟨i, j, s⟩
    cases s <;> simp [reim]
def trC {c : ℕ} : (Fin c → Fin m → ℂ) ≃ₗ[ℂ] (Fin m → Fin c → ℂ) where
  toFun Y := fun j i => Y i j
  invFun Z := fun i j => Z j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
def mulLC {c : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin c → ℂ) →ₗ[ℂ] (Fin m → Fin c → ℂ) :=
  (trC (m := m) (c := c)).toLinearMap ∘ₗ mulRC (r := c) Aᵀ ∘ₗ (trC (m := m) (c := c)).symm.toLinearMap
end MulR
end PI.AprimeInfW


