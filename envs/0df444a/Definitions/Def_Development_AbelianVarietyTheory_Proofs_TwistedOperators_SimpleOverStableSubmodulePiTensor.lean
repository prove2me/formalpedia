-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmodulePiTensor
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmodulePiTensor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:56.579873+00:00
-- url     : https://prove2.me/theorems/1c807a42-a8ee-458c-97c6-b98758e7876a
-- title:
--   Simple Over Stable Submodule Pi Tensor
-- statement:
--   Definitions and structural lemmas for Simple Over Stable Submodule Pi Tensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SimpleOverStableSubmodulePiTensor.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmoduleTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OperatorStablePiTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
namespace GlobalTheory.PiSimple
open GlobalTheory.TensHead
def PP (σ : Type) : Prop :=
  ∀ [DecidableEq σ] (M : σ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i)),
    (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) → (∀ i, Stab (Op i) (K i)) →
    (∀ i, SimpleOver (Op i) (K i)) → SimpleOver (piOps Op) (piKer K)
end GlobalTheory.PiSimple


