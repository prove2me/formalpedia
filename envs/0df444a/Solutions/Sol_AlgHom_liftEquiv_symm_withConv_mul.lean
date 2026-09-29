-- Prove2me | solution 1 for AlgHom.liftEquiv_symm_withConv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/efec05a6-9271-5918-b06b-b8c31ca9daf8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgHom_liftEquiv_symm_withConv_mul
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1600000
open TensorProduct

theorem solution
    (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (A : Type*) [CommRing A] [Bialgebra R A]
    (B : Type*) [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (f g : WithConv (S ⊗[R] A →ₐ[S] B)) :
    WithConv.toConv ((AlgHom.liftEquiv R S A B).symm (f * g).ofConv)
    = WithConv.toConv ((AlgHom.liftEquiv R S A B).symm f.ofConv)
      * WithConv.toConv ((AlgHom.liftEquiv R S A B).symm g.ofConv) := by
  set F := (AlgHom.liftEquiv R S A B).symm f.ofConv with hF
  set G := (AlgHom.liftEquiv R S A B).symm g.ofConv with hG
  rw [show (WithConv.toConv F * WithConv.toConv G)
      = WithConv.toConv ((WithConv.toConv F * WithConv.toConv G).ofConv) from
        (WithConv.toConv_ofConv _).symm]
  congr 1
  refine AlgHom.ext fun a => ?_
  show LinearMap.mul' S B
        (TensorProduct.map (f.ofConv).toLinearMap (g.ofConv).toLinearMap
          (Coalgebra.comul (R := S) ((1 : S) ⊗ₜ[R] a)))
     = LinearMap.mul' R B
        (TensorProduct.map F.toLinearMap G.toLinearMap (Coalgebra.comul (R := R) a))
  rw [TensorProduct.comul_tmul, Bialgebra.comul_one]

  have key : ∀ (a₁ a₂ : A),
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R S R S S S A A)
        ((1 : S ⊗[S] S) ⊗ₜ[R] (a₁ ⊗ₜ[R] a₂))
      = ((1 : S) ⊗ₜ[R] a₁) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] a₂) := fun a₁ a₂ => by
    rw [show (1 : S ⊗[S] S) = (1 : S) ⊗ₜ[S] (1 : S) from rfl]
    rfl
  induction Coalgebra.comul (R := R) a using TensorProduct.induction_on with
  | zero => simp
  | tmul a₁ a₂ =>
    rw [key a₁ a₂, TensorProduct.map_tmul, LinearMap.mul'_apply,
        TensorProduct.map_tmul, LinearMap.mul'_apply,
        AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
        AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply]
    rfl
  | add x y hx hy =>
    rw [TensorProduct.tmul_add, map_add, map_add, map_add, map_add, map_add, hx, hy]

end S_AlgHom_liftEquiv_symm_withConv_mul
end P2MW
export P2MW.S_AlgHom_liftEquiv_symm_withConv_mul (solution)
