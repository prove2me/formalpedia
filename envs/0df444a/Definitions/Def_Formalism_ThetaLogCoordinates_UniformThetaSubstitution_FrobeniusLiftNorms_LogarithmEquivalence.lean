-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:20:02.928084+00:00
-- url     : https://prove2.me/theorems/d2fe0344-8f9c-4f74-8520-d39d87143940
-- title:
--   Logarithm Equivalence
-- statement:
--   Definitions and structural lemmas for Logarithm Equivalence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
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
namespace LogarithmEquivalence
noncomputable def ballRing (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K :=
  _root_.UpperTheory.Reformulated.B.ClosedUnitBallSubring.ballRing K
def altR (R : Type) [CommRing R] (p : ℕ) : PowerSeries R :=
  PowerSeries.mk fun n => ∑ l ∈ range (n + 1), if n = (p ^ 2) ^ l then (-1 : R) ^ l else 0
end LogarithmEquivalence
end Formalism.InvariantFactorPaths.G7


