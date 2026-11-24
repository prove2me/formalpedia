-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RamDef
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RamDef
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:39.844002+00:00
-- url     : https://prove2.me/theorems/e664e5d1-6837-4263-bbd4-1e056d978c2f
-- title:
--   Ram Def
-- statement:
--   Definitions and structural lemmas for Ram Def, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RamDef.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_HNsmulNsmul
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
def UnitVecRam : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m]
    [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (x0 y0 : ℤ) (T : Finset m) (i₀ : m),
    KeyHyps a b c d ha hd lam hlam m Λ d x0 y0 T i₀ →
    ∀ x : m → ℂ, SatMem d Λ x → (∀ j ∈ T, x j = 0) →
      (x = 0 ∨ ∃ p q : ℤ, ¬ (d : ℤ) ∣ p ∧ ¬ (d : ℤ) ∣ q ∧
        stdH (cmL a b d ha hd lam hlam) m x x = repKappa a b d ha hd lam hlam * p / q) →
    ∀ z₀ : m → ℂ, SatMem d Λ z₀ → (∀ j ∈ T, z₀ j = 0) → stdH (cmL a b d ha hd lam hlam) m z₀ x = 0 → z₀ ≠ 0 →
    ∃ y : m → ℂ, SatMem d Λ y ∧ (∀ j ∈ T, y j = 0) ∧ stdH (cmL a b d ha hd lam hlam) m y x = 0 ∧
      ∃ p q : ℤ, ¬ (d : ℤ) ∣ p ∧ ¬ (d : ℤ) ∣ q ∧
        stdH (cmL a b d ha hd lam hlam) m y y = repKappa a b d ha hd lam hlam * p / q
end PI.UnitaryGroupMassFormula.UnimodLocStd


