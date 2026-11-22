-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_IdealEquiv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_IdealEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:41.352049+00:00
-- url     : https://prove2.me/theorems/564e4984-3ee8-48b4-9acb-774f09dcd994
-- title:
--   Ideal Equiv
-- statement:
--   Definitions and structural lemmas for Ideal Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/IdealEquiv.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors ENNReal Classical
noncomputable section
namespace PI.Residue
def idealEquiv (K : Type) [Field K] [NumberField K] :
    (Ideal (𝓞 K))⁰ ≃ {I : Ideal (𝓞 K) // I ≠ ⊥} :=
  Equiv.subtypeEquivRight fun I => by rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot]
end PI.Residue


