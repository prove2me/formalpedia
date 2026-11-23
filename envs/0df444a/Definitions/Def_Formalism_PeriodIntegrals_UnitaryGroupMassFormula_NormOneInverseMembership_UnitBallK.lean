-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOneInverseMembership_UnitBallK
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOneInverseMembership_UnitBallK
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:39.844062+00:00
-- url     : https://prove2.me/theorems/c850ada1-d698-44f7-8764-9fe2de536ad0
-- title:
--   Unit Ball K
-- statement:
--   Definitions and structural lemmas for Unit Ball K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormOneInverseMembership/UnitBallK.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace UnitBallK
variable (K : Type*) [NormedField K] [IsUltrametricDist K]
def subring : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  neg_mem' := by
    intro x hx
    simpa using hx
  add_mem' := by
    intro x y hx hy
    have key : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := IsUltrametricDist.norm_add_le_max x y
    rcases le_max_iff.1 key with h | h
    · exact le_trans h hx
    · exact le_trans h hy
  mul_mem' := by
    intro x y hx hy
    have hx' : ‖x‖ ≤ 1 := hx
    have hy' : ‖y‖ ≤ 1 := hy
    have h0x := norm_nonneg x
    have h0y := norm_nonneg y
    change ‖x * y‖ ≤ 1
    rw [norm_mul]
    nlinarith
variable {K}
end UnitBallK


