-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_GaussElementarySymmetric
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_GaussElementarySymmetric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:26.77258+00:00
-- url     : https://prove2.me/theorems/572406a9-e57a-406e-828a-d6a2076bcc59
-- title:
--   Gauss Elementary Symmetric
-- statement:
--   Definitions and structural lemmas for Gauss Elementary Symmetric, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
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
namespace CSym
section gen
variable {K σ : Type} [CommRing K] [Fintype σ]
def genE (x : σ → K) : PowerSeries K := ∏ i, (1 + PowerSeries.C (x i) * PowerSeries.X)
end gen
section gauss
variable {K : Type} [Field K]
end gauss
end CSym
open CSym
namespace CSym
end CSym
end Formalism.InvariantFactorPaths.G7


