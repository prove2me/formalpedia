-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:59.872549+00:00
-- url     : https://prove2.me/theorems/9b2d2261-799f-4967-ba69-8b26a7af4d56
-- title:
--   Finrank Dual And Range Dual Map Base Change
-- statement:
--   Definitions and structural lemmas for Finrank Dual And Range Dual Map Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankDualAndRangeDualMapBaseChange.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
namespace GlobalTheory.DualFibreRank
section
variable {O : Type} [CommRing O] (A : Type) [CommRing A] [Algebra O A]
noncomputable def cmp (M : Type) [AddCommGroup M] [Module O M] :
    A ⊗[O] Module.Dual O M →ₗ[A] Module.Dual A (A ⊗[O] M) :=
  LinearMap.liftBaseChange A (Module.Dual.baseChange A)
variable {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
end
end GlobalTheory.DualFibreRank


