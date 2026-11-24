-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:49.587603+00:00
-- url     : https://prove2.me/theorems/598b49ec-966a-46d3-8e08-251f477f7bb6
-- title:
--   PAntisym Divisible
-- statement:
--   Definitions and structural lemmas for PAntisym Divisible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
namespace AntisymDivisible
section General
variable {σ : Type*} [DecidableEq σ]
def collapse (u v : σ) : σ → σ := fun w => if w = u then v else w
end General
section Blocks
variable {T : Type} [Fintype T] [DecidableEq T] {N : ℕ}
end Blocks
end AntisymDivisible
end GroundTheory.Heights₂.Heights


