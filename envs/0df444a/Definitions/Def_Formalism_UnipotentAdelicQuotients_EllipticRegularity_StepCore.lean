-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_StepCore
-- name    : Formalism_UnipotentAdelicQuotients_EllipticRegularity_StepCore
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:16.395636+00:00
-- url     : https://prove2.me/theorems/1237f867-1d12-4b63-8e67-52472e59d8da
-- title:
--   Step Core
-- statement:
--   Definitions and structural lemmas for Step Core, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/StepCore.lean

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {d : ℕ}
def wn (s M ε : ℝ) (F : E d → ℂ) : ℝ≥0∞ := eLpNorm (fun ξ => om s M ε ξ * ‖F ξ‖) 2 volume
end
end ZetaZeros.D.EllReg


