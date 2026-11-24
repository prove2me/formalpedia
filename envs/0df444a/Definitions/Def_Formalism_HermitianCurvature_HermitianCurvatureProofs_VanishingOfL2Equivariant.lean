-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VanishingOfL2Equivariant
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_VanishingOfL2Equivariant
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:54:16.836637+00:00
-- url     : https://prove2.me/theorems/67e9699f-fc73-4440-be04-ddb5015fc05a
-- title:
--   Vanishing Of L2 Equivariant
-- statement:
--   Definitions and structural lemmas for Vanishing Of L2 Equivariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VanishingOfL2Equivariant.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroOfAe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
set_option maxHeartbeats 3200000
namespace Formalism.FourierDecayAlt.P
namespace UnipotentHaarMeasurability
open Formalism.FourierDecayAlt.ThreeDimData
end UnipotentHaarMeasurability
end Formalism.FourierDecayAlt.P


