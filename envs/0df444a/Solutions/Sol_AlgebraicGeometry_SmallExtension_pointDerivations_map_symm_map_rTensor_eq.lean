-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.pointDerivations_map_symm_map_rTensor_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/257efb97-96ad-5b57-9df2-8530699c918f

import Mathlib
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_pointDerivations_map_symm_map_rTensor_eq

set_option autoImplicit false

open TensorProduct

universe u

theorem solution
    {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A] (ev : A →+* k)
    (W : Type u) [AddCommGroup W] [Module k W]
    (Φ : ∀ (M : Type u) [AddCommGroup M] [Module k M], ↥(Algebra.PointDerivations k A ev M) ≃ₗ[k] (W ⊗[k] M))
    (hΦnat : ∀ (M M' : Type u) [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M')
        (δ : ↥(Algebra.PointDerivations k A ev M)),
      Φ M' (Algebra.PointDerivations.map ev g δ) = TensorProduct.map (LinearMap.id : W →ₗ[k] W) g (Φ M δ))
    (θ : W →ₗ[k] W)
    (M M' : Type u) [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M')
    (δ : ↥(Algebra.PointDerivations k A ev M)) :
    Algebra.PointDerivations.map ev g ((Φ M).symm (TensorProduct.map θ (LinearMap.id : M →ₗ[k] M) (Φ M δ))) =
      (Φ M').symm (TensorProduct.map θ (LinearMap.id : M' →ₗ[k] M') (Φ M' (Algebra.PointDerivations.map ev g δ))) := by
  apply (Φ M').injective
  rw [hΦnat, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hΦnat, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id, LinearMap.id_comp,
    LinearMap.comp_id]

end S_AlgebraicGeometry_SmallExtension_pointDerivations_map_symm_map_rTensor_eq
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_pointDerivations_map_symm_map_rTensor_eq (solution)
