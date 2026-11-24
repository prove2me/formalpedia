-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PContractRelDimLe
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PContractRelDimLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:44.102576+00:00
-- url     : https://prove2.me/theorems/8e0309e2-c3aa-4cf7-87ef-635d1e1b63b4
-- title:
--   PContract Rel Dim Le
-- statement:
--   Definitions and structural lemmas for PContract Rel Dim Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PContractRelDimLe.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsContractRelDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted
noncomputable section
universe u
namespace ContractRelDimLe
section Chain
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
end Chain
section Contract
variable {K K' : Type*} [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K'] {F : Type*}
  [Field F] (j : K ↪ K') (ι' : K' → Type*)
end Contract
end ContractRelDimLe
end
end GroundTheory.Heights₂.Heights.FieldNumbers


