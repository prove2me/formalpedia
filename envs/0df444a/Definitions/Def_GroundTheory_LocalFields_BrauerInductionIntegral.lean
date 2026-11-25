-- Prove2me | Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
-- name    : GroundTheory_LocalFields_BrauerInductionIntegral
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:38:00.603741+00:00
-- url     : https://prove2.me/theorems/ba00f5a5-5df6-4b3f-b78f-7bccafb12868
-- title:
--   Brauer Induction Integral
-- statement:
--   Definitions and structural lemmas for Brauer Induction Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionIntegral.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
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
section OneDim
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
end OneDim
section Comm
variable {G : Type*} [Group G] [IsMulCommutative G]
end Comm
section Values
variable {G : Type*} [Group G] [Fintype G]
end Values
section Retraction
end Retraction
section Frobenius
variable {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime)
include hp
end Frobenius
end GroundTheory.LocalField


