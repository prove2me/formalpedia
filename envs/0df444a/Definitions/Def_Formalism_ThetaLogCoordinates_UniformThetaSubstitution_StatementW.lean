-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementW
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:57.817919+00:00
-- url     : https://prove2.me/theorems/904ad478-fc3c-4a92-b0d5-9132fcb89f38
-- title:
--   Statement W
-- statement:
--   Definitions and structural lemmas for Statement W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/StatementW.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
def ModelExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 2 < p →
    ∃ (K : Type) (_ : NormedField K), IsUltrametricDist K ∧ CharZero K ∧ CompleteSpace K ∧
      ∃ σ : K →+* K, UnrOK K p σ ∧ ∃ ζ : K, IsPrimitiveRoot ζ (p ^ 2 - 1)
def BetaNonVacuous : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 2 < p →
    ∃ (K : Type) (_ : NormedField K) (_ : IsUltrametricDist K) (_ : CharZero K)
      (_ : CompleteSpace K) (σ : K →+* K) (F be : MvPowerSeries (Fin 2) K),
      UnrOK K p σ ∧ (∃ ζ : K, IsPrimitiveRoot ζ (p ^ 2 - 1)) ∧ IsLawOfLog p F ∧ BetaHyp p F be ∧
        ¬ Simeq be 0
end Formalism.InvariantFactorPaths.G7


