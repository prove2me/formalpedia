-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConstantsDescend
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConstantsDescend
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:48.750452+00:00
-- url     : https://prove2.me/theorems/7e695396-6552-4d91-b2bb-a5b6e392bece
-- title:
--   PConstants Descend
-- statement:
--   Definitions and structural lemmas for PConstants Descend, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConstantsDescend.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConstantsDescend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial
namespace ConstantsDescend
section Fibre
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra ℚ A] [Algebra.FiniteType ℚ A]
end Fibre
end ConstantsDescend
end GroundTheory.Heights₂.Heights.HilbertSamuel


