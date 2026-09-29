-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_linearMap_apply_eq_unitPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/6f12ea7d-b0ed-5aec-9bf6-f172b0294454

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_linearMap_apply_eq_unitPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (hh : h ≫ πY = πX)
    (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) :
    ∃ L : (OModulePresheaf.unit πY).cochain 𝒦 n →ₗ[R] (OModulePresheaf.unit πX).cochain 𝒲 n,
      ∀ z, L z = OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z := by
  classical
  subst hh
  refine ⟨{ toFun := fun z => OModulePresheaf.unitPullback (πX := h ≫ πY) h 𝒲 𝒦 lam hlam n z
            map_add' := ?_
            map_smul' := ?_ }, fun z => rfl⟩
  · intro z₁ z₂
    funext s
    by_cases hinj : Function.Injective (lam ∘ s.1)
    · rw [Pi.add_apply, OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj,
        OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj,
        OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj]
      erw [map_add, map_add, smul_add]
      try rfl
    · rw [Pi.add_apply, OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj,
        OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj,
        OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj, add_zero]
  · intro r z
    funext s
    by_cases hinj : Function.Injective (lam ∘ s.1)
    · rw [Pi.smul_apply, RingHom.id_apply, OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj,
        OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj]
      letI i1 := Scheme.TwoAffineOpenCover.algebraOfHom πY (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))
      letI i2 := Scheme.TwoAffineOpenCover.algebraOfHom (h ≫ πY) (𝒲.inter s)
      change (((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ)) • (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj)).op).hom ((h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))).hom (algebraMap R Γ(Y, 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) r * (show Γ(Y, 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) from z (𝒲.sortIdx 𝒦 lam s hinj)))) =
        algebraMap R Γ(X, 𝒲.inter s) r * ((((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ)) • (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj)).op).hom ((h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))).hom (show Γ(Y, 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) from z (𝒲.sortIdx 𝒦 lam s hinj))))
      rw [map_mul, map_mul, zsmul_eq_mul, zsmul_eq_mul, mul_left_comm]
      congr 1
      change ((πY.appLE ⊤ (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) le_top ≫ h.appLE (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) (𝒲.inter s) (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj))).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
        ((h ≫ πY).appLE ⊤ (𝒲.inter s) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
      rw [Scheme.Hom.appLE_comp_appLE]
    · rw [Pi.smul_apply, OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj,
        OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj, smul_zero]

end S_AlgebraicGeometry_OModulePresheaf_exists_linearMap_apply_eq_unitPullback
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_linearMap_apply_eq_unitPullback (solution)
