-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PProjDegreePositive
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PProjDegreePositive
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T04:24:28.86241+00:00
-- url     : https://prove2.me/theorems/0139f967-7482-4cc6-87b3-766b60e4c2ce
-- title:
--   PProj Degree Positive
-- statement:
--   Definitions and structural lemmas for PProj Degree Positive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PProjDegreePositive.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegreePos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertDimZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIntersectionRecursion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
universe u
namespace ProjDegreePositive
variable {F : Type u} [Field F] {ι₀ : Type} [Fintype ι₀]
end ProjDegreePositive
end
end GroundTheory.Heights₂.Heights.Kleiman


