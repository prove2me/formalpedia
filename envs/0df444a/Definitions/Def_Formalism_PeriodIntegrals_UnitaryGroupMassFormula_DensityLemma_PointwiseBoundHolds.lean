-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PointwiseBoundHolds
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PointwiseBoundHolds
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T20:06:53.843989+00:00
-- url     : https://prove2.me/theorems/2c0b4395-591d-4945-988e-4a359ea35c0a
-- title:
--   Pointwise Bound Holds
-- statement:
--   Definitions and structural lemmas for Pointwise Bound Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PointwiseBoundHolds.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFibreBoundDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
noncomputable section
namespace PI.UnitaryGroupMassFormula.DLm
section Frob
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace
end Frob
end PI.UnitaryGroupMassFormula.DLm


