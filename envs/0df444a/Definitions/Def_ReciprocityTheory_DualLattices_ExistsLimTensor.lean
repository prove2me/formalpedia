-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ExistsLimTensor
-- name    : ReciprocityTheory_DualLattices_ExistsLimTensor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:45.469185+00:00
-- url     : https://prove2.me/theorems/03d494b7-b02c-4740-9abb-4c77c4af66ad
-- title:
--   Exists Lim Tensor
-- statement:
--   Definitions and structural lemmas for Exists Lim Tensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsLimTensor.lean

import Definitions.Def_ReciprocityTheory_DualLattices_NsmulKerZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
namespace ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
namespace BX
variable (B : BX R₀) {p : ℕ}
def coordK (M : Type u) [AddCommGroup M] [Module R₀ M] (k : Module.Free.ChooseBasisIndex R₀ B.gg) :
    B.gg ⊗[R₀] M →ₗ[R₀] M :=
  (TensorProduct.lid R₀ M).toLinearMap ∘ₗ LinearMap.rTensor M ((Module.Free.chooseBasis R₀ B.gg).coord k)
end BX
end ReciprocityTheory.PGsh


