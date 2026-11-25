-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_PRhoRw
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_PRhoRw
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:25:45.144329+00:00
-- url     : https://prove2.me/theorems/cbe7ed4e-e659-4bfd-b4aa-dd31c2d7b581
-- title:
--   PRho Rw
-- statement:
--   Definitions and structural lemmas for PRho Rw, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianCommutation/PRhoRw.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_CutDefs
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace PI.UnitaryGroupMassFormula.JCC
section twist
variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
def twistL (A : Wp →L[ℂ] Wp) (B : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  (((ContinuousLinearMap.compL ℂ Wq Wp Wp) A).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip B)).restrictScalars ℝ
end twist
variable {k r : ℕ}
section rho
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
end rho
end PI.UnitaryGroupMassFormula.JCC


