-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffLawFirstTwoOfThree
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffLawFirstTwoOfThree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:46.977818+00:00
-- url     : https://prove2.me/theorems/b869ab7c-87de-4c5f-a265-60842db66d7a
-- title:
--   Constant Coeff Law First Two Of Three
-- statement:
--   Definitions and structural lemmas for Constant Coeff Law First Two Of Three, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffLawFirstTwoOfThree.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
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
namespace GramFrameCompositionLinFacts
section Alg
open MvPowerSeries
variable {K : Type} [Field K]
end Alg
section Norm
open MvPowerSeries
variable {K : Type} [NormedField K] [IsUltrametricDist K]
end Norm
end GramFrameCompositionLinFacts
namespace GramFrameCompositionLinFacts
end GramFrameCompositionLinFacts
end Formalism.InvariantFactorPaths.G7


