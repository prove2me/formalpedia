-- Prove2me | Definitions.Def_GroundTheory_LocalFields_BrauerInductionMonomial
-- name    : GroundTheory_LocalFields_BrauerInductionMonomial
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:45:55.216171+00:00
-- url     : https://prove2.me/theorems/52650633-12dc-43d9-9438-313a59d51f08
-- title:
--   Brauer Induction Monomial
-- statement:
--   Definitions and structural lemmas for Brauer Induction Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionMonomial.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open Module Representation
section Nilpotent
open scoped commutatorElement
variable {G : Type*} [Group G]
end Nilpotent
section Scalar
variable {G : Type*} [Group G] {A : Subgroup G} [A.Normal] [Fintype A]
end Scalar
section Monomial
universe u
end Monomial
end GroundTheory.LocalField


