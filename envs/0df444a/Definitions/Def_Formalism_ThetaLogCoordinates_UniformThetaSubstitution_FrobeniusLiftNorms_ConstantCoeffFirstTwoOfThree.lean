-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:21.322913+00:00
-- url     : https://prove2.me/theorems/c0cf95fb-3f8e-467d-a3f1-ba8d4307a725
-- title:
--   Constant Coeff First Two Of Three
-- statement:
--   Definitions and structural lemmas for Constant Coeff First Two Of Three, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffFirstTwoOfThree.lean

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
namespace CoboundarySeries
open MvPowerSeries
section Cob
variable {K : Type} [Field K]
end Cob
section Supp
variable {K : Type} [Field K]
end Supp
section Norm
variable {K : Type} [NormedField K] [IsUltrametricDist K]
end Norm
section MapG
variable {K : Type} [Field K]
end MapG
end CoboundarySeries
open CoboundarySeries
end Formalism.InvariantFactorPaths.G7


