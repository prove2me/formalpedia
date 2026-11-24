-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MapInvMEq
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_MapInvMEq
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:36:03.375593+00:00
-- url     : https://prove2.me/theorems/8c2a0ee2-1674-4ae3-bad2-d478ad3a2042
-- title:
--   Map Inv MEq
-- statement:
--   Definitions and structural lemmas for Map Inv MEq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MapInvMEq.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiRegOf
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
namespace Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
def invP (p : B.SS k r) : B.SS k r :=
  ((B2.invM p.1.1, B2.invM p.1.2), (B2.invM p.2.1, B2.invM p.2.2))
end Formalism.FourierDecayAlt.P.S3dx4


