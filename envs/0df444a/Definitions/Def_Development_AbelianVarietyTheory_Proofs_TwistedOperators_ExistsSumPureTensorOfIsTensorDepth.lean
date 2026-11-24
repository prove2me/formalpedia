-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSumPureTensorOfIsTensorDepth
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSumPureTensorOfIsTensorDepth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:08.646866+00:00
-- url     : https://prove2.me/theorems/5a1f3ef8-5bb7-42d8-9a05-63e5c4a215cd
-- title:
--   Exists Sum Pure Tensor Of Is Tensor Depth
-- statement:
--   Definitions and structural lemmas for Exists Sum Pure Tensor Of Is Tensor Depth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSumPureTensorOfIsTensorDepth.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.FunObj
noncomputable section
namespace GlobalTheory.TensorExpansion
open GlobalTheory.SplitFlip ValuativeRel Matrix
open scoped Pointwise
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def resClass (ϖ : kˣ) {e : ℕ} {m n : ℕ} (c : Fin m → Fin n → Res k e) : Set (Matrix (Fin m) (Fin n) k) :=
  {X | ∀ i j, X i j ∈ 𝒪[k] ∧ (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j - liftRes c i j) ∈ 𝒪[k]}
end GlobalTheory.TensorExpansion


