-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PKernelPositive
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_PKernelPositive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:11.91441+00:00
-- url     : https://prove2.me/theorems/987dba3f-2d38-45ad-8fde-26aa5e1753af
-- title:
--   PKernel Positive
-- statement:
--   Definitions and structural lemmas for PKernel Positive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PKernelPositive.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
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
namespace KernelPositive
def cquad {g : ℕ} (v : Fin g → ℝ) (M : Matrix (Fin g) (Fin g) ℂ) : ℂ :=
  (fun k => (v k : ℂ)) ⬝ᵥ M *ᵥ fun k => (v k : ℂ)
def line {n : ℕ} (z : Fin n → ℂ) (t : ℂ) : Fin n → ℂ := z + t • fun _ => (1 : ℂ)
end KernelPositive
end
end GroundTheory.Heights₂.Heights.Regular


