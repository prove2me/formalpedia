-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:57.757022+00:00
-- url     : https://prove2.me/theorems/009be87b-1b58-4628-885d-019ad0229e24
-- title:
--   Exists One Tmul Of Forall Fixed
-- statement:
--   Definitions and structural lemmas for Exists One Tmul Of Forall Fixed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
namespace GlobalTheory.GaloisDescent
section Basis
variable {K L M G ι : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module L M]
end Basis
section IsBaseChange
variable {K L V M G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
  [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M] {f : V →ₗ[K] M}
noncomputable def contract (hf : IsBaseChange L f) (l : L →ₗ[K] K) : M →ₗ[K] V :=
  (TensorProduct.lid K V).toLinearMap ∘ₗ l.rTensor V ∘ₗ
    (hf.equiv.symm.toLinearMap.restrictScalars K)
section Maps
variable {V' M' : Type*} [AddCommGroup V'] [Module K V']
  [AddCommGroup M'] [Module K M'] [Module L M'] [IsScalarTower K L M'] {f' : V' →ₗ[K] M'}
end Maps
end IsBaseChange
section Tensor
variable {K L V G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
variable (K) in

def rationalPart (W : Submodule L (L ⊗[K] V)) : Submodule K V :=
  (W.restrictScalars K).comap (TensorProduct.mk K L V 1)
end Tensor
end GlobalTheory.GaloisDescent


