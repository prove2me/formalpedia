-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementV
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementV
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T20:25:13.598256+00:00
-- url     : https://prove2.me/theorems/0d6be9a4-4689-40c0-be2e-bc8ddf8e2460
-- title:
--   Statement V
-- statement:
--   Definitions and structural lemmas for Statement V, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/StatementV.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
namespace Formalism.L2.Th1.E
def VIntegral : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]), l ≠ 2 → IntCurve (curveL l L ι) →
    ∀ ε : ℂ_[l], ‖ε‖ = 1 → (∀ n, ‖coeff n (Formalism.L2.Th1.D.thetaS l (ι L.g₂) (ι L.g₃) ε)‖ ≤ 1) →
    ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ∀ (s : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * s ∈ L.lattice →
      IntS (Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.D.phFF l (ι L.g₂) (ι L.g₃) (ι (Formalism.L2.Th1.F.s2 L)) ε) *
        (PowerSeries.map (ι : ℂ →+* ℂ_[l])
          (Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))).subst
          (C ε * Formalism.InvariantFactorPaths.G7.lgF ℂ_[l] l))
end Formalism.L2.Th1.E


