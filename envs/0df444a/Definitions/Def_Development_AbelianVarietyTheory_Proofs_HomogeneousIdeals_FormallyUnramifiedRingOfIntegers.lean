-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedRingOfIntegers
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedRingOfIntegers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:53.849424+00:00
-- url     : https://prove2.me/theorems/e1f7217d-ba0c-4cf9-8bb9-a7d98b6b7bc2
-- title:
--   Formally Unramified Ring Of Integers
-- statement:
--   Definitions and structural lemmas for Formally Unramified Ring Of Integers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
namespace GlobalTheory.Serre
section Eigen
variable {R O O' : Type*} [CommRing R] [CommRing O] [CommRing O'] [Algebra O O'] [Algebra O R]
  [Algebra O' R] [IsScalarTower O O' R]
variable (R O O') in

def mulChar : R ⊗[O] O' →ₐ[R] R :=
  Algebra.TensorProduct.lift (AlgHom.id R R) (IsScalarTower.toAlgHom O O' R) fun _ _ ↦ .all _ _
variable {M : Type*} [AddCommGroup M] [Module O M] [Module O' M] [IsScalarTower O O' M]
end Eigen
section Integers
open NumberField
variable (k K E : Type*) [Field k] [CharZero k] [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E]
end Integers
end GlobalTheory.Serre


