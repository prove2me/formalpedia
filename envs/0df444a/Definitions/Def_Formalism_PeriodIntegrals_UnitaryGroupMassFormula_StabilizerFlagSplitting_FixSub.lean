-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_FixSub
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_FixSub
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:46:14.337994+00:00
-- url     : https://prove2.me/theorems/d43657ba-2a4f-4b14-b3a9-210897f4209f
-- title:
--   Fix Sub
-- statement:
--   Definitions and structural lemmas for Fix Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/FixSub.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
namespace PI.StabSplit.FixW
def uOf (k r : ℕ) (g : B.Mat k r) : B.Mat k r :=
  Matrix.of fun i j =>
    if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then g i j
    else if i = j then 1 else 0
def yv (k r : ℕ) (g : B.Mat k r) (j : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  fun i => if i.val < r then g i j else if i = j then 1 else 0
end PI.StabSplit.FixW
namespace PI.StabSplit
end PI.StabSplit


