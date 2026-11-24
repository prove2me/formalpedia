-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGauss
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGauss
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T10:38:23.11782+00:00
-- url     : https://prove2.me/theorems/24f97cfe-8ef6-420e-934d-36b3e2ca2069
-- title:
--   EGauss
-- statement:
--   Definitions and structural lemmas for EGauss, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGauss.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KOneConsequence
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
open Formalism.DworkPowerSeriesWeights (Integral frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
namespace EGauss
section Transfer
variable {F K : Type} [NormedField F] [NormedField K] (φ : F →+* K) {ν r0 r1 : ℕ}
end Transfer
section Comb
variable {K : Type} [Field K] {ν r0 r1 : ℕ}
end Comb
section Struct
variable {K : Type} [Field K] {ν r0 r1 : ℕ} [NeZero ν]
end Struct
section Reduce
end Reduce
end EGauss
open EGauss
end Formalism.InvariantFactorPaths.G7


