-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MPlaces
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MPlaces
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:21.836252+00:00
-- url     : https://prove2.me/theorems/9469dac9-8342-4269-a742-978a26381d75
-- title:
--   MPlaces
-- statement:
--   Definitions and structural lemmas for MPlaces, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/MPlaces.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementM
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp jetPair mfact)
open Formalism.FG.IntegralSubstitution (integral_mul integralSubstV)
open TwoS
namespace MPl
section Alg
variable {K Pl : Type} [Field K] {ι : Pl → Type}
variable [Fintype Pl]
abbrev eqv : ((Σ v, ι v) →₀ ℕ) ≃+ (∀ v, ι v →₀ ℕ) := Finsupp.sigmaFinsuppAddEquivPiFinsupp
variable [DecidableEq Pl]
end Alg
end MPl
open MPl
end Formalism.InvariantFactorPaths.G7


