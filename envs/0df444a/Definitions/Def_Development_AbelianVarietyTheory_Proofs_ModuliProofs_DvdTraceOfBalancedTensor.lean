-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdTraceOfBalancedTensor
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdTraceOfBalancedTensor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:02.08335+00:00
-- url     : https://prove2.me/theorems/2bc690d1-36a4-4ed3-958e-97619ae0881c
-- title:
--   Dvd Trace Of Balanced Tensor
-- statement:
--   Definitions and structural lemmas for Dvd Trace Of Balanced Tensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdTraceOfBalancedTensor.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
namespace GlobalTheory
section
variable {O H : Type*} [CommRing O] [CommRing H] [Algebra O H]
noncomputable def contractRight (Θ : H ⊗[O] H) : Module.Dual O H →ₗ[O] H where
  toFun α := TensorProduct.rid O H (LinearMap.lTensor H α Θ)
  map_add' a b := by simp [LinearMap.lTensor_add]
  map_smul' c a := by simp [LinearMap.lTensor_smul]
end
end GlobalTheory


