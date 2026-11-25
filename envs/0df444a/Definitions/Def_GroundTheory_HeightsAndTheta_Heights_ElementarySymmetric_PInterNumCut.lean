-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumCut
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumCut
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T07:21:48.503262+00:00
-- url     : https://prove2.me/theorems/2fa03270-79a5-5633-9ea7-3ba2125e9de9
-- title:
--   PInter Num Cut
-- statement:
--   Definitions and structural lemmas for PInter Num Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumCut.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StCutRestrLenExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StMixedTwistShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitFilt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutZeroNotLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TensorSubInsertion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
universe u w
section Combinatorics
end Combinatorics
section Snoc
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
end Snoc
section Dim
end Dim
end
end GroundTheory.Heights₂.Heights.Kleiman


