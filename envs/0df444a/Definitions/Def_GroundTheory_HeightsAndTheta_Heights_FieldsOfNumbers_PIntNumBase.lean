-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBase
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBase
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:01.999476+00:00
-- url     : https://prove2.me/theorems/23215b25-abf3-4fbb-a534-17b5faa37d4e
-- title:
--   PInt Num Base
-- statement:
--   Definitions and structural lemmas for PInt Num Base, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBase.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
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
section Point
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
def blockMonomial (i : ∀ k, ι k) (m : K → ℕ) : MRing ι F :=
  ∏ k, X ⟨k, i k⟩ ^ m k
end Point
end
end GroundTheory.Heights₂.Heights.FieldNumbers


