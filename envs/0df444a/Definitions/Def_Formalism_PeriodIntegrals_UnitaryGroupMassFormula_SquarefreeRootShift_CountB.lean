-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountB
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:55.932081+00:00
-- url     : https://prove2.me/theorems/2d532dd5-3fd1-40b0-8f22-749379109704
-- title:
--   Count B
-- statement:
--   Definitions and structural lemmas for Count B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountB.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
namespace PI.SqfRootShift.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]
def Good (c : (ZMod g)ˣ) (P : (ZMod g)[X]) : Prop :=
  P.Monic ∧ Irreducible P ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ ∃ j : ℕ,
    P ∣ X ^ (ℓ ^ j) - C ((c : ZMod g) ^ (ℓ ^ j))
end PI.SqfRootShift.W


