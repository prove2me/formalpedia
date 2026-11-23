-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtInvApply
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtInvApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:48.089195+00:00
-- url     : https://prove2.me/theorems/6b2c646a-86d2-4c2a-a310-d120d26603cd
-- title:
--   Differentiable At Inv Apply
-- statement:
--   Definitions and structural lemmas for Differentiable At Inv Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtInvApply.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
namespace GlobalTheory.Mem.GaussPhase
variable {σ : Type} [Fintype σ] [DecidableEq σ]
end GlobalTheory.Mem.GaussPhase


