-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralInnerGermMoving
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralInnerGermMoving
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T05:02:09.220387+00:00
-- url     : https://prove2.me/theorems/bf022233-af3c-5bbf-b7a3-22d6c32266e2
-- title:
--   Tendsto Integral Inner Germ Moving
-- statement:
--   Definitions and structural lemmas for Tendsto Integral Inner Germ Moving, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TendstoIntegralInnerGermMoving.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermFibreKernels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
section L2m
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end L2m
end
end Formalism.FourierDecayAlt.P.PBK


