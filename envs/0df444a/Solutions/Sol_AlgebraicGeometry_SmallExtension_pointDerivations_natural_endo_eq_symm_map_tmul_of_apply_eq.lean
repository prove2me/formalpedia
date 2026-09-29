-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.pointDerivations_natural_endo_eq_symm_map_tmul_of_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/cc649a5f-3394-5926-a50f-9bdb515cbdb0

import Mathlib
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_pointDerivations_natural_endo_eq_symm_map_tmul_of_apply_eq

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem solution
    {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A] (ev : A →+* k)

    (W : Type u) [AddCommGroup W] [Module k W]
    (Φ : ∀ (M : Type u) [AddCommGroup M] [Module k M], ↥(Algebra.PointDerivations k A ev M) ≃ₗ[k] (W ⊗[k] M))
    (hΦnat : ∀ (M M' : Type u) [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M')
        (δ : ↥(Algebra.PointDerivations k A ev M)),
      Φ M' (Algebra.PointDerivations.map ev g δ) = TensorProduct.map (LinearMap.id : W →ₗ[k] W) g (Φ M δ))

    (θ : W →ₗ[k] W)
    (η : ∀ (M : Type u) [AddCommGroup M] [Module k M], ↥(Algebra.PointDerivations k A ev M) →ₗ[k] ↥(Algebra.PointDerivations k A ev M))
    (hηnat : ∀ (M M' : Type u) [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M')
        (δ : ↥(Algebra.PointDerivations k A ev M)),
      η M' (Algebra.PointDerivations.map ev g δ) = Algebra.PointDerivations.map ev g (η M δ))
    (hηpin : ∀ δ : ↥(Algebra.PointDerivations k A ev k),
      Φ k (η k δ) = TensorProduct.map θ (LinearMap.id : k →ₗ[k] k) (Φ k δ))
    (M : Type u) [AddCommGroup M] [Module k M] (δ : ↥(Algebra.PointDerivations k A ev M)) :
    η M δ = (Φ M).symm (TensorProduct.map θ (LinearMap.id : M →ₗ[k] M) (Φ M δ)) := by

  suffices h : ∀ z : W ⊗[k] M,
      Φ M (η M ((Φ M).symm z)) = TensorProduct.map θ (LinearMap.id : M →ₗ[k] M) z by
    apply (Φ M).injective
    rw [LinearEquiv.apply_symm_apply, ← h (Φ M δ), LinearEquiv.symm_apply_apply]
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul w m =>

    let g : k →ₗ[k] M := LinearMap.toSpanSingleton k M m

    let δ₀ : ↥(Algebra.PointDerivations k A ev k) := (Φ k).symm (w ⊗ₜ (1 : k))
    have hδ₀ : Φ k δ₀ = w ⊗ₜ (1 : k) := LinearEquiv.apply_symm_apply _ _

    have e1 : w ⊗ₜ[k] m = TensorProduct.map (LinearMap.id : W →ₗ[k] W) g (w ⊗ₜ (1 : k)) := by
      simp [g, LinearMap.toSpanSingleton_apply]
    have e2 : (Φ M).symm (w ⊗ₜ[k] m) = Algebra.PointDerivations.map ev g δ₀ := by
      apply (Φ M).injective
      rw [LinearEquiv.apply_symm_apply, hΦnat k M g δ₀, hδ₀, e1]
    rw [e2, hηnat k M g δ₀, hΦnat k M g (η k δ₀), hηpin δ₀, hδ₀]
    simp [g, LinearMap.toSpanSingleton_apply]

end S_AlgebraicGeometry_SmallExtension_pointDerivations_natural_endo_eq_symm_map_tmul_of_apply_eq
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_pointDerivations_natural_endo_eq_symm_map_tmul_of_apply_eq (solution)
