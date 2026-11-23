-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ContractPowSuccMem
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ContractPowSuccMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:19.337349+00:00
-- url     : https://prove2.me/theorems/85451407-40a8-455f-93c5-cfc43604e822
-- title:
--   Contract Pow Succ Mem
-- statement:
--   Definitions and structural lemmas for Contract Pow Succ Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/ContractPowSuccMem.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Ii
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
namespace PI.KoszulExact
section General
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
end General
section Koszul
variable {R : Type u} [CommRing R] {D : ℕ}
end Koszul
end PI.KoszulExact


