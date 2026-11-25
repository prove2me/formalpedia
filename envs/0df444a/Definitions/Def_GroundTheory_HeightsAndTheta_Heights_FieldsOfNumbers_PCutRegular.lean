-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:54:04.802365+00:00
-- url     : https://prove2.me/theorems/872827b0-acd3-4557-8c7e-193683989c2b
-- title:
--   PCut Regular
-- statement:
--   Definitions and structural lemmas for PCut Regular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
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
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace CutRegular
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
end CutRegular
end
end GroundTheory.Heights₂.Heights.FieldNumbers


