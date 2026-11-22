-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ScalingSwapLemmas
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ScalingSwapLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:59:18.840868+00:00
-- url     : https://prove2.me/theorems/d680cdd8-f959-4107-9844-e1459f6453f6
-- title:
--   Scaling Swap Lemmas
-- statement:
--   Definitions and structural lemmas for Scaling Swap Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
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
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
namespace TwoVariableSwapLemmas
open MvPowerSeries
section Swap
variable {K : Type} [Field K]
def sw (n : Fin 2 →₀ ℕ) : Fin 2 →₀ ℕ := Finsupp.equivMapDomain (Equiv.swap 0 1) n
end Swap
section Scale
variable {K : Type} [Field K]
def sc2 (u v : K) : Fin 2 → MvPowerSeries (Fin 2) K := ![C u * X 0, C v * X 1]
def sc3 (u v : K) : Fin 3 → MvPowerSeries (Fin 3) K := ![C u * X 0, C u * X 1, C v * X 2]
end Scale
section Sim
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
end Sim
end TwoVariableSwapLemmas
open TwoVariableSwapLemmas
end Formalism.InvariantFactorPaths.G7


