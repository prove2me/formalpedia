-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleAtomicFormOneReduction
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleAtomicFormOneReduction
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T17:13:22.565479+00:00
-- url     : https://prove2.me/theorems/0fb92c29-9367-42bc-8ba1-c89971d6b6dd
-- title:
--   Admissible Atomic Form One Reduction
-- statement:
--   Definitions and structural lemmas for Admissible Atomic Form One Reduction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtomicFormOneReduction.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VanishingOfL2Equivariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiscreteSeriesFormOneReduction
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


