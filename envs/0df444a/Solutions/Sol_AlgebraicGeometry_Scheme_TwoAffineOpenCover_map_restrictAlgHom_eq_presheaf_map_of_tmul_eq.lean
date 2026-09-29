-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.map_restrictAlgHom_eq_presheaf_map_of_tmul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8956e398-8499-5864-81cc-c9ff67c4548c

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_map_restrictAlgHom_eq_presheaf_map_of_tmul_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover TensorProduct"

universe u

theorem solution
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {X Y : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R)) (p : Y ⟶ X) (πA : Y ⟶ Spec (CommRingCat.of A))
    {U U' : X.Opens} (h : U' ≤ U) {W W' : Y.Opens} (hW : W ≤ p ⁻¹ᵁ U) (hW' : W' ≤ p ⁻¹ᵁ U') (hWW : W' ≤ W)
    (σ : letI := algebraOfHom π U
      A ⊗[R] Γ(X, U) →+* Γ(Y, W))
    (σ' : letI := algebraOfHom π U'
      A ⊗[R] Γ(X, U') →+* Γ(Y, W'))
    (hσ₁ : letI := algebraOfHom π U
      ∀ x : Γ(X, U), σ ((1 : A) ⊗ₜ[R] x) = (Y.presheaf.map (homOfLE hW).op).hom ((p.app U).hom x))
    (hσ₂ : letI := algebraOfHom π U
      letI := algebraOfHom πA W
      ∀ a : A, σ (a ⊗ₜ[R] (1 : Γ(X, U))) = algebraMap A Γ(Y, W) a)
    (hσ'₁ : letI := algebraOfHom π U'
      ∀ x : Γ(X, U'), σ' ((1 : A) ⊗ₜ[R] x) = (Y.presheaf.map (homOfLE hW').op).hom ((p.app U').hom x))
    (hσ'₂ : letI := algebraOfHom π U'
      letI := algebraOfHom πA W'
      ∀ a : A, σ' (a ⊗ₜ[R] (1 : Γ(X, U'))) = algebraMap A Γ(Y, W') a) :
    letI := algebraOfHom π U
    letI := algebraOfHom π U'
    ∀ y : A ⊗[R] Γ(X, U),
      σ' (Algebra.TensorProduct.map (AlgHom.id A A) (restrictAlgHom π h) y) = (Y.presheaf.map (homOfLE hWW).op).hom (σ y) := by
  letI := algebraOfHom π U
  letI := algebraOfHom π U'
  letI := algebraOfHom πA W
  letI := algebraOfHom πA W'
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    have e1 : a ⊗ₜ[R] x = (a ⊗ₜ[R] (1 : Γ(X, U))) * ((1 : A) ⊗ₜ[R] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e1, map_mul, map_mul, map_mul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AlgHom.id_apply, map_one, hσ'₂, hσ₂, hσ₁]
    have hr : (restrictAlgHom π h) x = (X.presheaf.map (homOfLE h).op).hom x := rfl
    rw [hr, hσ'₁, map_mul]
    congr 1
    · exact ((restrictAlgHom πA hWW).commutes a).symm
    · have hn := p.naturality (homOfLE h).op
      have hn' := congrArg (fun φ => φ.hom x) hn
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hn'
      have hpre : p ⁻¹ᵁ U' ≤ p ⁻¹ᵁ U := ((TopologicalSpace.Opens.map p.base).map (homOfLE h)).le
      have e2 : ((TopologicalSpace.Opens.map p.base).map (homOfLE h).op.unop).op = (homOfLE hpre).op :=
        Subsingleton.elim _ _
      rw [hn', e2, res_res, res_res]
  | add y z hy hz => simp only [map_add, hy, hz]

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_map_restrictAlgHom_eq_presheaf_map_of_tmul_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_map_restrictAlgHom_eq_presheaf_map_of_tmul_eq (solution)
