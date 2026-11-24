-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PiTensorMaximalStableContainsFactorKernel
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_PiTensorMaximalStableContainsFactorKernel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:37.60014+00:00
-- url     : https://prove2.me/theorems/ff02381c-6f8b-426c-820d-d9e47712a2e9
-- title:
--   Pi Tensor Maximal Stable Contains Factor Kernel
-- statement:
--   Definitions and structural lemmas for Pi Tensor Maximal Stable Contains Factor Kernel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PiTensorMaximalStableContainsFactorKernel.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeKerOfLocalFiniteLengthToSimpleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqTopOfPureTensorsOfFactorGenerators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
namespace GlobalTheory.TensHead
section Quot
variable {V : Type} [AddCommGroup V] [Module ℂ V]
noncomputable def quotOp (N : Submodule ℂ V) (f : Module.End ℂ V) : Module.End ℂ (V ⧸ N) := by
  classical
  exact if h : N ≤ N.comap f then N.mapQ N f h else 0
end Quot
section Slot
variable {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
end Slot
end GlobalTheory.TensHead
namespace GlobalTheory.TensHead
end GlobalTheory.TensHead


