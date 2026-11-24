-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:46.751162+00:00
-- url     : https://prove2.me/theorems/caa9e7a8-98ff-4d96-a62e-cb3f6dd118a7
-- title:
--   Statements Examples
-- statement:
--   Definitions and structural lemmas for Statements Examples, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean

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
universe u
abbrev ProjIdx (N : ℕ) : Unit → Type := fun _ => Fin (N + 1)
def binomFn (N : ℕ) (t : ℤ) : ℤ := if 0 ≤ t then ((t.toNat + N).choose N : ℤ) else 0
end
end GroundTheory.Heights₂.Heights.FieldNumbers


