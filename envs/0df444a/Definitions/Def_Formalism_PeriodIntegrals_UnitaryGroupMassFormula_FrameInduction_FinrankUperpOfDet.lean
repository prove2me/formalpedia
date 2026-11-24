-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_FinrankUperpOfDet
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_FinrankUperpOfDet
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:57:02.394926+00:00
-- url     : https://prove2.me/theorems/5ca14541-140a-4144-a7bc-c1a13867ae12
-- title:
--   Finrank Uperp Of Det
-- statement:
--   Definitions and structural lemmas for Finrank Uperp Of Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/FinrankUperpOfDet.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
namespace PI.FrameInd
def Vc (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.of fun l i => gramVec k r z z' g i l
end PI.FrameInd


