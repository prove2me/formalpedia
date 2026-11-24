-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:37.901901+00:00
-- url     : https://prove2.me/theorems/517c1177-5eb3-4608-9556-7bc6c8e4c575
-- title:
--   PExp Extension
-- statement:
--   Definitions and structural lemmas for PExp Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
noncomputable section
namespace ExpQuad
def qf {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℤ) : ℂ :=
  (fun k => (v k : ℂ)) ⬝ᵥ A *ᵥ (fun k => (v k : ℂ))
variable {n a g : ℕ} (P : PeriodPolydisc n a g) (v : Fin g → ℤ)
def phi (w : Fin n → ℂ) : ℂ := 2 * Real.pi * Complex.I * qf (P.tau0 w) v
def psi (z : Fin n → ℂ) : ℂ := phi P v (logLift a z)
end ExpQuad
end
end GroundTheory.Heights₂.Heights.Regular


