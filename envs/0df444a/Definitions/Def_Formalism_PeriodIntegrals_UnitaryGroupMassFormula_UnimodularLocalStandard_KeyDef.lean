-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_KeyDef
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_KeyDef
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:21:29.730803+00:00
-- url     : https://prove2.me/theorems/d7bb2e4a-42dd-4552-a52e-0c433b849343
-- title:
--   Key Def
-- statement:
--   Definitions and structural lemmas for Key Def, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/KeyDef.lean

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
def SatMem {m : Type*} (l : ℕ) (Λ : AddSubgroup (m → ℂ)) (x : m → ℂ) : Prop := ∃ n : ℕ, ¬ l ∣ n ∧ n • x ∈ Λ
def KeyRep : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)),
      IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ →
      (∀ x ∈ Λ, cmTheta b d • x ∈ Λ) →
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λ ≠ 0 →
      relIdx Λ (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∀ l : ℕ, l.Prime → ∀ x y : ℤ, ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2 →
      ∀ (T : Finset m) (i₀ : m), i₀ ∉ T →
        (∀ j ∈ T, SatMem l Λ (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)))) →
        ∃ v : m → ℂ, SatMem l Λ v ∧ (∀ j ∈ T, v j = 0) ∧
          stdH (cmL a b d ha hd lam hlam) m v v =
            stdH (cmL a b d ha hd lam hlam) m (Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d)))
              (Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d)))
end PI.UnitaryGroupMassFormula.UnimodLocStd


