-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalIntegral
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalIntegral
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:16:39.398189+00:00
-- url     : https://prove2.me/theorems/065d5e02-8742-5396-83eb-e41115f26759
-- title:
--   PSemilocal Integral
-- statement:
--   Definitions and structural lemmas for PSemilocal Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalIntegral.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsValuativeCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PContractRelDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
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
namespace SemilocalIntegral
section Dim
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]
end Dim
section Centre
variable {F : Type u} [Field F] {K K' : Type} [Fintype K] [DecidableEq K] [Fintype K']
  [DecidableEq K'] {j : K ↪ K'} {ι' : K' → Type} [∀ k, Fintype (ι' k)]
end Centre
end SemilocalIntegral
end
end GroundTheory.Heights₂.Heights.FieldNumbers


