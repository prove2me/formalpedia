-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:44.762623+00:00
-- url     : https://prove2.me/theorems/b2a529b2-7e47-489a-b2b4-bceba2ebb09d
-- title:
--   Hpk Mul Mul Hpk Apply
-- statement:
--   Definitions and structural lemmas for Hpk Mul Mul Hpk Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/HpkMulMulHpkApply.lean

import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
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
namespace PI.HwUniqW
open PI.UpqRep
variable {k r : ℕ}
def piI (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩
def epsI (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1
end PI.HwUniqW


