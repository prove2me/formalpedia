-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T14:23:34.113811+00:00
-- url     : https://prove2.me/theorems/e40cb202-18a0-441e-a4f0-14ebd9a5641c
-- title:
--   Mul Apply S
-- statement:
--   Definitions and structural lemmas for Mul Apply S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/MulApplyS.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}
def SP (k r : ℕ) (l : Fin r) (p q : Fin (2 * r + k + 1)) : Prop :=
  (p.val = l.val ∧ l.val < q.val ∧ q.val ≤ 2 * r + k - l.val) ∨
  (q.val = 2 * r + k - l.val ∧ l.val < p.val ∧ p.val < 2 * r + k - l.val)
def InS (k r : ℕ) (l : Fin r) (M : Mx k r) : Prop := ∀ p q, ¬ SP k r l p q → M p q = 0
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule


