-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftQuantumMinor_QuantumMinorLeftHermitian
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftQuantumMinor_QuantumMinorLeftHermitian
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T14:24:14.504733+00:00
-- url     : https://prove2.me/theorems/b4c34e87-de49-4491-a377-0876c86cfe7f
-- title:
--   Quantum Minor Left Hermitian
-- statement:
--   Definitions and structural lemmas for Quantum Minor Left Hermitian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftQuantumMinor/QuantumMinorLeftHermitian.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
namespace Formalism.FourierDecayAlt.Q.QnMinorLeftPf
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.Q.QnMinorLeftPf


