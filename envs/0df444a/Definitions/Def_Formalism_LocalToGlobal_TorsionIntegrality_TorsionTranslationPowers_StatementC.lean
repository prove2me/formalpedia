-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementC
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:46.854275+00:00
-- url     : https://prove2.me/theorems/8bd1a2c7-44ad-4e07-9714-edf33efb1590
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/StatementC.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_CMGoodModels_CM4
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Th1.E
def CMIntegrality : Prop :=
  ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]), lam ≠ 0 →
    ‖lam ^ 4 * ι L.g₂‖ ≤ 1 → ‖lam ^ 6 * ι L.g₃‖ ≤ 1 →
    ‖(lam ^ 4 * ι L.g₂) ^ 3 - 27 * (lam ^ 6 * ι L.g₃) ^ 2‖ = 1 →
    ∀ (z : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * z ∈ L.lattice → z ∉ L.lattice →
      ‖lam ^ 2 * ι (L.weierstrassP z)‖ ≤ 1 ∧ ‖lam ^ 3 * ι (L.derivWeierstrassP z)‖ ≤ 1
def CMUnramifiedMembership : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy d L →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ d → ∀ (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]), lam ≠ 0 →
      (lam ^ 4 * ι L.g₂) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l → (lam ^ 6 * ι L.g₃) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l →
      ‖lam ^ 4 * ι L.g₂‖ ≤ 1 → ‖lam ^ 6 * ι L.g₃‖ ≤ 1 →
      ‖(lam ^ 4 * ι L.g₂) ^ 3 - 27 * (lam ^ 6 * ι L.g₃) ^ 2‖ = 1 →
    ∀ (z : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * z ∈ L.lattice → z ∉ L.lattice →
      lam ^ 2 * ι (L.weierstrassP z) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l ∧
        lam ^ 3 * ι (L.derivWeierstrassP z) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l
open Classical in

def ScaledTorsionPointNonsingular : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]), lam ≠ 0 →
    ∀ (z : ℂ) (N : ℕ), (N : ℂ) * z ∈ L.lattice → z ∉ L.lattice →
      ∃ h : (Formalism.L2.Th1.A.shortW (lam ^ 4 * ι L.g₂) (lam ^ 6 * ι L.g₃)).toAffine.Nonsingular
          (lam ^ 2 * ι (L.weierstrassP z)) (lam ^ 3 * ι (L.derivWeierstrassP z) / 2),
        N • WeierstrassCurve.Affine.Point.some _ _ h = 0
def CMTorsionValuesOfIntegralAndUnramified : Prop := CMIntegrality → CMUnramifiedMembership → Formalism.L2.Th1.CM.CM4
end Formalism.L2.Th1.E


