-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:44.061794+00:00
-- url     : https://prove2.me/theorems/fc8463d1-99c6-4b89-bcfc-dc74a8c70ded
-- title:
--   PPFContracted Dim
-- statement:
--   Definitions and structural lemmas for PPFContracted Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContractedDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
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
namespace PFContracted
section Drop
variable {K : Type*} {ι : K → Type*} {F : Type*} [Field F]
end Drop
section Kill
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
def killBlocks (T : Finset K) : MRing ι F →ₐ[F] MRing ι F :=
  aeval fun v => if v.1 ∈ T then 0 else X v
def killIdeal (Q : Ideal (MRing ι F)) (T : Finset K) : Ideal (MRing ι F) :=
  Q.comap (killBlocks T)
end Kill
end PFContracted
end
end GroundTheory.Heights₂.Heights.FieldNumbers


