-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:39.863868+00:00
-- url     : https://prove2.me/theorems/9b2f3e2a-a001-4a8f-9116-49d6a44a869d
-- title:
--   Shape Prod Var Mat Ne Zero
-- statement:
--   Definitions and structural lemmas for Shape Prod Var Mat Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
namespace PI.FJMD
open PI.FJM
def inS {p q r s : ℕ} (la lb lc ld : ℕ) : Ln p q r s → Prop
  | (Sum.inl i, Sum.inl k) => i.val < la ∧ k.val < la
  | (Sum.inl i, Sum.inr l) => p ≤ i.val + lb ∧ s ≤ l.val + lb
  | (Sum.inr j, Sum.inr l) => j.val < lc ∧ l.val < lc
  | (Sum.inr j, Sum.inl k) => q ≤ j.val + ld ∧ r ≤ k.val + ld
end PI.FJMD


