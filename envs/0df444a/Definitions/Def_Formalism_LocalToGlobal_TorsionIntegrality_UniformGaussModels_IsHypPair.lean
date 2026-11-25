-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_IsHypPair
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_IsHypPair
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:54:48.810826+00:00
-- url     : https://prove2.me/theorems/ed2a07b8-23dd-4a43-9bec-20e6e3ad80bf
-- title:
--   Is Hyp Pair
-- statement:
--   Definitions and structural lemmas for Is Hyp Pair, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/UniformGaussModels/IsHypPair.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_OneLetterGaussFinal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementV
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
namespace Formalism.L2.Th1.Top
open Formalism.InvariantFactorPaths.G7 (lgF)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
def thetaOne (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (ε : ℂ_[l]) (ω₀ s : ℂ) :
    PowerSeries ℂ_[l] :=
  (PowerSeries.map (ι : ℂ →+* ℂ_[l])
    (Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))).subst
    (PowerSeries.C ε * lgF ℂ_[l] l)
def thetaOrth (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (ε : ℂ_[l]) (ω₀ : ℂ)
    {κ n : Type} [Fintype κ] [Fintype n] (r : κ → ℂ_[l]) (s : κ → n → ℂ) : MvPowerSeries n ℂ_[l] :=
  Formalism.L2.Th1.E.thetaProd r (fun k i => thetaOne l L ι ε ω₀ (s k i))
def IsHypPair {K : Type} [NormedField K] (σ : K →+* K) {E n : Type} [DecidableEq E] [Fintype n]
    (f f' : E → n → K) : Prop :=
  (∀ e i, ‖f e i‖ ≤ 1 ∧ σ (σ (f e i)) = f e i) ∧ (∀ e i, ‖f' e i‖ ≤ 1 ∧ σ (σ (f' e i)) = f' e i) ∧
  (∀ e e', ∑ i, σ (f e i) * f e' i = 0) ∧ (∀ e e', ∑ i, σ (f' e i) * f' e' i = 0) ∧
  (∀ e e', ∑ i, σ (f e i) * f' e' i = if e = e' then 1 else 0)
def thetaHyp (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (ε : ℂ_[l]) (ω₀ : ℂ)
    {E κ n : Type} [Fintype E] [Fintype κ] [Fintype n] (f f' : E → n → MaximalUnramifiedExtension l) (r : κ → ℂ_[l])
    (s : κ → n → ℂ) : MvPowerSeries (Bool × E) ℂ_[l] :=
  MvPowerSeries.subst
    (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[l] l) (Formalism.L2.Th1.D.expF ℂ_[l] l) (MaximalUnramifiedExtension l).subtype f f')
    (thetaOrth l L ι ε ω₀ r s)
end Formalism.L2.Th1.Top


