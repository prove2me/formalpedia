-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_IntegrableOfContOn
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_IntegrableOfContOn
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:03:25.680969+00:00
-- url     : https://prove2.me/theorems/2e744128-7256-4f66-b9b9-578e4269da27
-- title:
--   Integrable Of Cont On
-- statement:
--   Definitions and structural lemmas for Integrable Of Cont On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SkewAnalyticGroup/IntegrableOfContOn.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_HasDerivAtShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace QnRdSkewW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {μ : Measure (Fin n → Fin n → ℂ)}
end QnRdSkewW


