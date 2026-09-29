-- Prove2me | solution 1 for Algebra.TensorProduct.nonempty_algEquiv_tensor_quotient_of_isScalarTower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/f06006da-2f48-5e13-85f9-998b961b6f72

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_TensorProduct_nonempty_algEquiv_tensor_quotient_of_isScalarTower

open scoped TensorProduct

namespace Algebra p2m_export "Algebra" "commutes TensorProduct.quotIdealMapEquivTensorQuot algebraMap TensorProduct.congr TensorProduct.comm restrictScalars TensorProduct.cancelBaseChange" namespace TensorProduct p2m_export "Algebra.TensorProduct" "quotIdealMapEquivTensorQuot congr algebraMap_apply map cancelBaseChange" end Algebra.TensorProduct
p2m_open_scoped "Algebra Algebra.TensorProduct" in
open scoped TensorProduct in

theorem Algebra.TensorProduct.nonempty_algEquiv_tensor_quotient_of_isScalarTower
    (Λ : Type*) [CommRing Λ] (I : Ideal Λ) (k : Type*) [CommRing k] [Algebra Λ k]
    [Algebra (Λ ⧸ I) k] [IsScalarTower Λ (Λ ⧸ I) k]
    (A : Type*) [CommRing A] [Algebra Λ A] :
    Nonempty (k ⊗[Λ] A ≃ₐ[k] k ⊗[Λ ⧸ I] (A ⧸ I.map (algebraMap Λ A))) := by
  let e2 : (Λ ⧸ I) ⊗[Λ] A ≃ₐ[Λ] A ⧸ I.map (algebraMap Λ A) :=
    (Algebra.TensorProduct.comm Λ (Λ ⧸ I) A).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).symm.restrictScalars Λ)
  let e2' : (Λ ⧸ I) ⊗[Λ] A ≃ₐ[Λ ⧸ I] A ⧸ I.map (algebraMap Λ A) :=
    AlgEquiv.ofRingEquiv (f := e2.toRingEquiv) (fun x => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
      exact e2.commutes a)
  exact ⟨(Algebra.TensorProduct.cancelBaseChange Λ (Λ ⧸ I) k k A).symm.trans
    (Algebra.TensorProduct.congr AlgEquiv.refl e2')⟩

theorem solution
    (Λ : Type*) [CommRing Λ] (I : Ideal Λ) (k : Type*) [CommRing k] [Algebra Λ k]
    [Algebra (Λ ⧸ I) k] [IsScalarTower Λ (Λ ⧸ I) k]
    (A : Type*) [CommRing A] [Algebra Λ A] :
    Nonempty (k ⊗[Λ] A ≃ₐ[k] k ⊗[Λ ⧸ I] (A ⧸ I.map (algebraMap Λ A))) :=
  Algebra.TensorProduct.nonempty_algEquiv_tensor_quotient_of_isScalarTower Λ I k A

end S_Algebra_TensorProduct_nonempty_algEquiv_tensor_quotient_of_isScalarTower
end P2MW
export P2MW.S_Algebra_TensorProduct_nonempty_algEquiv_tensor_quotient_of_isScalarTower (solution)
