-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementX
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementX
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T21:41:21.814803+00:00
-- url     : https://prove2.me/theorems/3a6908fc-532e-4bda-9c2b-47fdf7a3a9b3
-- title:
--   Statement X
-- statement:
--   Definitions and structural lemmas for Statement X, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/StatementX.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementV
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementW
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementW
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
def VJoint : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]), l ≠ 2 → IntCurve (curveL l L ι) →
    ∀ (g2 g3 s2 ε : Formalism.L2.Th1.CM.MaximalUnramifiedExtension l), (g2 : ℂ_[l]) = ι L.g₂ → (g3 : ℂ_[l]) = ι L.g₃ →
    (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 L) → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (Formalism.L2.Th1.D.thetaS l g2 g3 ε)‖ ≤ 1) →
    ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ∀ (s : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * s ∈ L.lattice →
      ∃ V : PowerSeries ℂ_[l], IntS V ∧
        (Formalism.DworkPowerSeriesWeights.mvExp (-(PowerSeries.map (Formalism.L2.Th1.CM.MaximalUnramifiedExtension l).subtype
                  (Formalism.L2.Th1.D.phFF l g2 g3 s2 ε))) : PowerSeries ℂ_[l]) * V =
          (PowerSeries.map (ι : ℂ →+* ℂ_[l])
            (Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))).subst
            (C (ε : ℂ_[l]) * Formalism.InvariantFactorPaths.G7.lgF ℂ_[l] l)
def PhWEq : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    phW l L ι W = Formalism.L2.Th1.B.phW W (ι (Formalism.L2.Th1.F.s2 L))
def InWTh0 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
      inW l ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2)) =
        Formalism.L2.Th1.B.fExp (-(Formalism.L2.Th1.B.evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW l L ι W (ω₀ / 2)))))
def ThetaZeroFromPhiDerivative : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    IntCurve W → ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ‖px W (ptW l L ι W (ω₀ / 2))‖ ≤ 1 →
    Formalism.InvariantFactorPaths.G7.Simeq (ι := Unit)
      (Formalism.L2.Th1.B.evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW l L ι W (ω₀ / 2)))) 0 →
    ∀ (s : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * s ∈ L.lattice →
      GaussOne (inW l ι W (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))
end Formalism.L2.Th1.E


