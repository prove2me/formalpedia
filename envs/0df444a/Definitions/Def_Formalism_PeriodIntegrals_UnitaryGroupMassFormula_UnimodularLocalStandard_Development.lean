-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_Development
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:21:39.695082+00:00
-- url     : https://prove2.me/theorems/a409a2f4-bf8d-4a9c-aa37-89d0667ed901
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/Development.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnimodLocStd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
def StepB : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)),
      IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λa →
      (∀ x ∈ Λa, cmTheta b d • x ∈ Λa) →
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λa ≠ 0 →
      relIdx Λa (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∀ l : ℕ, l.Prime → ∃ g : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
        IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m)
          (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧
        relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 ∧
        ¬ l ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ∧
        relIdx (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0
def StepC : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)) (g : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)),
      (∀ x ∈ Λa, cmTheta b d • x ∈ Λa) →
      ∀ l : ℕ, l.Prime →
      IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m)
          (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) →
        relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 →
        ¬ l ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) →
        relIdx (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∃ δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
        IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m)
          (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧ (∀ x, δ x = x → x = 0) ∧
        relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 ∧
        ¬ l ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ∧
        relIdx (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0
end PI.UnitaryGroupMassFormula.UnimodLocStd


