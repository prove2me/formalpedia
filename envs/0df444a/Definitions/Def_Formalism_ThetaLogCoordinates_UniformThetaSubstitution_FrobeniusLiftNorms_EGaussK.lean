-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGaussK
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGaussK
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:53:50.513302+00:00
-- url     : https://prove2.me/theorems/0268cf1d-5869-44d3-9bc0-0c14358f0335
-- title:
--   EGauss K
-- statement:
--   Definitions and structural lemmas for EGauss K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGaussK.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementGK
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KernelFromKOne
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
namespace EGaussK
open EGauss
end EGaussK
open EGaussK DeterminantJetScaling ScaledSeriesSubstitution
end Formalism.InvariantFactorPaths.G7


