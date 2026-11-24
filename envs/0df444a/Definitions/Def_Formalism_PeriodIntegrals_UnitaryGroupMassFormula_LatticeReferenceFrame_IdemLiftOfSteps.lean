-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemLiftOfSteps
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemLiftOfSteps
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:02:00.767868+00:00
-- url     : https://prove2.me/theorems/6c27fdd3-cfc8-4e2b-ae2a-aae7fba7e74e
-- title:
--   Idem Lift Of Steps
-- statement:
--   Definitions and structural lemmas for Idem Lift Of Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/IdemLiftOfSteps.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
namespace PI.ScRefExists.Id
def LocIdem : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g : ℕ)
    (α β : v.adicCompletion F), 1 ≤ g → Valued.v ((g : ℕ) : v.adicCompletion F) < 1 →
    Valued.v α ≤ 1 → Valued.v β ≤ 1 →
    ∃ c₁ c₂ : v.adicCompletion F, Valued.v c₁ ≤ 1 ∧ Valued.v c₂ ≤ 1 ∧
      (1 + (g : v.adicCompletion F) * α) * (1 + g * c₁) ^ 2 - 2 * (1 + g * c₁) * (g * c₂) = 1 + g * c₁ ∧
      (g * c₂) ^ 2 - g * β * (1 + g * c₁) ^ 2 = -(g * c₂) ∧
      (g * c₂) ^ 2 - (1 + g * α) * (g * c₂) * (1 + g * c₁) + g * β * (1 + g * c₁) ^ 2 = 0
def AdIdem : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (α β : Af F), 1 ≤ g →
    α ∈ Formalism.UG.intAd F → β ∈ Formalism.UG.intAd F →
    ∃ C₁ C₂ : Af F, C₁ ∈ Formalism.UG.intAd F ∧ C₂ ∈ Formalism.UG.intAd F ∧
      (1 + (g : Af F) * α) * (1 + g * C₁) ^ 2 - 2 * (1 + g * C₁) * (g * C₂) = 1 + g * C₁ ∧
      (g * C₂) ^ 2 - g * β * (1 + g * C₁) ^ 2 = -(g * C₂) ∧
      (g * C₂) ^ 2 - (1 + g * α) * (g * C₂) * (1 + g * C₁) + g * β * (1 + g * C₁) ^ 2 = 0
def AdOfLoc : Prop := LocIdem → AdIdem
def FixInt : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (s : 𝓞 I.E), star (s : I.E) = s →
    ∃ a : 𝓞 I.F, algebraMap I.F I.E (a : I.F) = s
def TenStep : Prop := AdIdem → FixInt → PI.ScRefExists.Sk.IdemLift
end PI.ScRefExists.Id


