-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementN
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementN
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:32:17.058796+00:00
-- url     : https://prove2.me/theorems/aaab6bf3-469d-4a08-917c-f5b5c9e0ee01
-- title:
--   Statement N
-- statement:
--   Definitions and structural lemmas for Statement N, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/StatementN.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_ThetaInZIsThetaLog
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementK
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
namespace Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog Simeq)
def ChainNonVacuous : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 2 < l → ∀ (ν r0 r1 : ℕ) [NeZero ν],
    ∃ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F be : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (om oms : Fin ν → MaximalUnramifiedExtension l)
      (U0 Φ : MvPowerSeries (Bool × Fin ν × Fin r0 × Fin r1) ℂ_[l]) (ph : PowerSeries (MaximalUnramifiedExtension l)),
      UnrOK (MaximalUnramifiedExtension l) l σ ∧ CompleteSpace (MaximalUnramifiedExtension l) ∧ (∀ a, ‖(MaximalUnramifiedExtension l).subtype a‖ = ‖a‖) ∧
      (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ 2 - 1)) ∧
      (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ (2 * ν) - 1)) ∧ 2 ≤ 2 * ν ∧ Even (2 * ν) ∧
      (∃ ϖ : ℂ_[l], ϖ ^ (l ^ 2 - 1) = (l : ℂ_[l])) ∧
      OwOK (2 * ν) σ om oms ∧ TrDual (2 * ν) σ om oms ∧ IsLawOfLog l F ∧ F1 F be ∧ F2 l σ be ∧
      ¬ Simeq be 0 ∧ Integral U0 ∧ MvPowerSeries.constantCoeff Φ = 0 ∧
      Simeq Φ (sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be)) ∧
      Simeq (MvPowerSeries.C (2 : MaximalUnramifiedExtension l) * ph)
        (MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries (MaximalUnramifiedExtension l))) be)
end Formalism.L2.Th1.D


