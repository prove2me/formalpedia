-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HformSumRight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HformSumRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:23:01.183247+00:00
-- url     : https://prove2.me/theorems/827217a9-d776-4eb4-b09a-e937a3a44de0
-- title:
--   Hform Sum Right
-- statement:
--   Definitions and structural lemmas for Hform Sum Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/HformSumRight.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PI.SelfDualLoc.W
open PI.SelfDualLoc
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
  (σ : A →+* A) (J : Matrix n n A)
end PI.SelfDualLoc.W


