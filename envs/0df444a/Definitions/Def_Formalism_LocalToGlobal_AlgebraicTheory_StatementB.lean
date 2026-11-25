-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_AlgebraicTheory_StatementB
-- name    : Formalism_LocalToGlobal_AlgebraicTheory_StatementB
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T09:06:44.943907+00:00
-- url     : https://prove2.me/theorems/a80cdb3d-521d-4a06-934c-a79cb875fb7a
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/AlgebraicTheory/StatementB.lean

import Definitions.Def_Formalism_LocalToGlobal_AlgebraicTheory_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.AlgTh
open Formalism.L2.Th1.E (IntCurve curveL ptOf px py gT OneUnit)
open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.Top (thetaZ)
open Formalism.L2.Th1.G (linSub)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
def IsQInt (dK : ℕ) (α : ℂ) : Prop := ∃ m n : ℤ, α = (m : ℂ) + (n : ℂ) * omegaK dK
def UnitKerInt : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), p ≠ 2 → ¬ p ∣ dK → IntCurve (curveL p L ι) →
  ∀ (α t : ℂ), IsQInt dK α → ‖ι α‖ = 1 → α * t ∈ L.lattice → t ∉ L.lattice →
    ‖px (curveL p L ι) (ptOf p L ι t)‖ ≤ 1 ∧ ‖py (curveL p L ι) (ptOf p L ι t)‖ ≤ 1
def EtPower : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), p ≠ 2 → ¬ p ∣ dK → IntCurve (curveL p L ι) →
  ∀ (α t : ℂ) (M : ℕ), IsQInt dK α → ‖ι α‖ = 1 → α * t ∈ L.lattice → t ∉ L.lattice → 0 < M → (M : ℂ) * t ∈ L.lattice →
    ‖ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0)‖ = 1 ∧
    ∃ V : PowerSeries ℂ_[p], OneUnit V ∧
      gT p L ι t ^ M = PowerSeries.C (ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0) ^ M) * V
def EtJetsSigma : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), p ≠ 2 → ¬ p ∣ dK → IntCurve (curveL p L ι) →
  ∀ (α t : ℂ) (M : ℕ), IsQInt dK α → ‖ι α‖ = 1 → α * t ∈ L.lattice → 0 < M → (M : ℂ) * t ∈ L.lattice →
  ∀ i : ℕ, ‖ι (iteratedDeriv i (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L)) 0)‖ * ‖(M : ℂ_[p])‖ ^ i ≤ 1
def EtJetsTh0 : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), p ≠ 2 → ¬ p ∣ dK → IntCurve (curveL p L ι) →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
  ∀ (α t : ℂ) (M : ℕ), IsQInt dK α → ‖ι α‖ = 1 → α * t ∈ L.lattice → 0 < M → (M : ℂ) * t ∈ L.lattice →
  ∀ i : ℕ, ‖ι (iteratedDeriv i (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) 0)‖ * ‖(M : ℂ_[p])‖ ^ i ≤ 1
def EtThetaZ : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), p ≠ 2 → ¬ p ∣ dK → IntCurve (curveL p L ι) →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
  ∀ (κ n : Type) [Fintype κ] [Fintype n] [DecidableEq n] (r : κ → ℂ_[p]) (s : κ → n → ℂ) (α : ℂ) (M : ℕ),
    IsQInt dK α → ‖ι α‖ = 1 → 0 < M → (∀ k, ‖r k‖ ≤ 1) →
    (∀ k i, α * s k i ∈ L.lattice) → (∀ k i, (M : ℂ) * s k i ∈ L.lattice) →
    JetsIntegral (linSub (scl n (M : ℂ_[p])) (thetaZ p L ι ω₀ r s))
end Formalism.L2.AlgTh


