-- Prove2me | Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
-- name    : Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:37.95982+00:00
-- url     : https://prove2.me/theorems/cf187715-c1bc-4eb8-8c7c-4fcd6df33bf5
-- title:
--   Sigma Norm Le One
-- statement:
--   Definitions and structural lemmas for Sigma Norm Le One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
namespace Formalism.LT.CoeffP
open Formalism.G
section Ball
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
end Ball
section Bd
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}
def Bd (c : ℝ) (F : MvPowerSeries ι K) : Prop := ∀ d : ι →₀ ℕ, ‖MvPowerSeries.coeff d F‖ ≤ c
end Bd
end Formalism.LT.CoeffP


