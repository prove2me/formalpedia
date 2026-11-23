-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_Nondeg
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_Nondeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:23:18.135802+00:00
-- url     : https://prove2.me/theorems/52b092ff-ab64-4442-ab11-90859f82d224
-- title:
--   Nondeg
-- statement:
--   Definitions and structural lemmas for Nondeg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/Nondeg.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
noncomputable section
namespace PI.SelfDualLoc.W.ND
open PI.SelfDualLoc
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
end PI.SelfDualLoc.W.ND
namespace PI.SelfDualLoc.W
open PI.SelfDualLoc ND
end PI.SelfDualLoc.W


