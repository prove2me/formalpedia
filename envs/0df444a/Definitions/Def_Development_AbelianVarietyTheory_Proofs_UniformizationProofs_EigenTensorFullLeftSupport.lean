-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EigenTensorFullLeftSupport
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EigenTensorFullLeftSupport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:42:42.589024+00:00
-- url     : https://prove2.me/theorems/68edb294-6cea-43b7-a751-f5689fdf1b71
-- title:
--   Eigen Tensor Full Left Support
-- statement:
--   Definitions and structural lemmas for Eigen Tensor Full Left Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EigenTensorFullLeftSupport.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open TensorProduct
noncomputable def rightContract {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) : TensorProduct F E E' →ₗ[F] E :=
  (TensorProduct.rid F E).toLinearMap ∘ₗ TensorProduct.map LinearMap.id l
end GlobalTheory


