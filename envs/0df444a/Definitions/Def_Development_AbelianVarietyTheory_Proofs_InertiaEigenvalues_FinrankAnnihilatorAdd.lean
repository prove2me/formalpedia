-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankAnnihilatorAdd
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankAnnihilatorAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:06.910612+00:00
-- url     : https://prove2.me/theorems/2803088c-41ef-4ece-bcac-1821d6fe347b
-- title:
--   Finrank Annihilator Add
-- statement:
--   Definitions and structural lemmas for Finrank Annihilator Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankAnnihilatorAdd.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
namespace GlobalTheory.HyodoDef.PairLin
variable {k M M' : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
  [FiniteDimensional k M] [FiniteDimensional k M']
end GlobalTheory.HyodoDef.PairLin


