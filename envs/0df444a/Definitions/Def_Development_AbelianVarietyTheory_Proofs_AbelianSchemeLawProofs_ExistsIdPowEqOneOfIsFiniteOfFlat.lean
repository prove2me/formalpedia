-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIdPowEqOneOfIsFiniteOfFlat
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIdPowEqOneOfIsFiniteOfFlat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:47.270838+00:00
-- url     : https://prove2.me/theorems/04ec1c98-6453-44fa-958e-90f756c83091
-- title:
--   Exists Id Pow Eq One Of Is Finite Of Flat
-- statement:
--   Definitions and structural lemmas for Exists Id Pow Eq One Of Is Finite Of Flat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
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
namespace GlobalTheory
namespace FiniteFlatKilled
section Algebra
open TensorProduct WithConv Coalgebra
variable {R B C F : Type*} [CommRing R] [CommRing C] [CommRing F] [Algebra R C] [Algebra R F]
section Coalg
variable [AddCommGroup B] [Module R B] [Coalgebra R B] [IsCocomm R B]
variable (B) in

def postcomp (h : C →ₐ[R] F) : WithConv (B →ₗ[R] C) →+* WithConv (B →ₗ[R] F) where
  toFun f := toConv (h.toLinearMap ∘ₗ f.ofConv)
  map_one' := by ext c; simp
  map_mul' f g := by
    rw [LinearMap.algHom_comp_convMul_distrib]
  map_zero' := by ext c; simp
  map_add' f g := by ext c; simp
variable [Algebra C F] [IsScalarTower R C F]
end Coalg
variable [CommRing B] [HopfAlgebra R B]
variable [IsCocomm R B]
end Algebra
section Scheme
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TensorProduct WithConv
attribute [local instance] Over.cartesianMonoidalCategory
end Scheme
end FiniteFlatKilled
end GlobalTheory


