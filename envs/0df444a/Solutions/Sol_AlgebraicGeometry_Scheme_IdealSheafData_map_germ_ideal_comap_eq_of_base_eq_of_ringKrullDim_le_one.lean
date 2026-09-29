-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.map_germ_ideal_comap_eq_of_base_eq_of_ringKrullDim_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/d2f66f9f-a637-5826-8bbb-547b9d224e1a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_comap_eq_of_base_eq_of_ringKrullDim_le_one

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_comap_eq_of_base_eq_of_ringKrullDim_le_one.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Hom Scheme Scheme.Hom.appIso_hom Scheme.Hom.preimage_image_eq Scheme.Hom.germ_stalkMap Scheme.IdealSheafData Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion"
namespace StalkComapFixed
p2m_open "AlgebraicGeometry"

theorem ideal_map_ringEquiv_eq {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    [IsIntegrallyClosed R] (hdim : ringKrullDim R ≤ 1) (e : R ≃+* R) (J : Ideal R) :
    J.map (e : R →+* R) = J := by
  classical
  by_cases hJ : J = ⊥
  · subst hJ; exact Ideal.map_bot

  have hm : (IsLocalRing.maximalIdeal R).map (e : R →+* R) = IsLocalRing.maximalIdeal R := by
    haveI : (IsLocalRing.maximalIdeal R).IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
    exact IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e)
  by_cases hf : IsField R
  ·
    haveI := (Ring.isField_iff_isSimpleOrder_ideal.mp hf)
    rcases eq_bot_or_eq_top J with h | h
    · exact absurd h hJ
    · subst h; exact Ideal.map_top _
  ·
    haveI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim
    have hmne : IsLocalRing.maximalIdeal R ≠ ⊥ := fun h =>
      hf (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
    have hex : ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime :=
      ⟨IsLocalRing.maximalIdeal R, ⟨hmne, inferInstance⟩,
        fun Q hQ => IsLocalRing.eq_maximalIdeal (hQ.2.isMaximal_of_ne_bot hQ.1)⟩
    have t36 := (IsDiscreteValuationRing.TFAE R hf).out 3 6
    have key : ∀ (I : Ideal R), I ≠ ⊥ → ∃ n : ℕ, I = IsLocalRing.maximalIdeal R ^ n :=
      t36.mp ⟨‹IsIntegrallyClosed R›, hex⟩
    obtain ⟨n, rfl⟩ := key J hJ
    rw [Ideal.map_pow, hm]

variable {X : Scheme.{u}}

noncomputable def stalkIdeal (I : X.IdealSheafData) (U : X.affineOpens) (x : X) (hxU : x ∈ (U : X.Opens)) :
    Ideal (X.presheaf.stalk x) :=
  Ideal.map (X.presheaf.germ U x hxU).hom (I.ideal U)

theorem stalkIdeal_eq_of_le (I : X.IdealSheafData) {U V : X.affineOpens} (h : U ≤ V) (x : X)
    (hxU : x ∈ (U : X.Opens)) :
    stalkIdeal I U x hxU = stalkIdeal I V x (h hxU) := by
  unfold stalkIdeal
  have e := X.presheaf.germ_res (homOfLE (show (U : X.Opens) ≤ V from h)) x hxU
  rw [← I.map_ideal' (homOfLE (show (U : X.Opens) ≤ V from h)).op, Ideal.map_map, ← CommRingCat.hom_comp, e]

theorem stalkIdeal_eq (I : X.IdealSheafData) (U V : X.affineOpens) (x : X)
    (hxU : x ∈ (U : X.Opens)) (hxV : x ∈ (V : X.Opens)) :
    stalkIdeal I U x hxU = stalkIdeal I V x hxV := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (U : X.Opens) ⊓ V from ⟨hxU, hxV⟩)
      ((U : X.Opens) ⊓ V).isOpen
  have hWU : (⟨W, hW⟩ : X.affineOpens) ≤ U := fun y hy => (hWle hy).1
  have hWV : (⟨W, hW⟩ : X.affineOpens) ≤ V := fun y hy => (hWle hy).2
  rw [← stalkIdeal_eq_of_le I hWU x hxW, ← stalkIdeal_eq_of_le I hWV x hxW]

theorem map_eqToHom_stalkIdeal (I : X.IdealSheafData) (U : X.affineOpens) {y x : X} (e : y = x)
    (hyU : y ∈ (U : X.Opens)) :
    Ideal.map (eqToHom (congrArg X.presheaf.stalk e) : X.presheaf.stalk y ⟶ X.presheaf.stalk x).hom
      (stalkIdeal I U y hyU) = stalkIdeal I U x (e ▸ hyU) := by
  subst e
  simp [Ideal.map_id]

theorem comap_inv_eq_map {A B : CommRingCat.{u}} (f : A ≅ B) (J : Ideal A) :
    J.comap f.inv.hom = J.map f.hom.hom := by
  ext b
  constructor
  · intro hb
    have : b = f.hom.hom (f.inv.hom b) := by
      rw [← CommRingCat.comp_apply, f.inv_hom_id]; rfl
    rw [this]
    exact Ideal.mem_map_of_mem _ hb
  · intro hb
    rw [Ideal.mem_comap]
    have hsurj : Function.Surjective f.hom.hom := fun c => ⟨f.inv.hom c, by
      rw [← CommRingCat.comp_apply, f.inv_hom_id]; rfl⟩
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp hb
    rw [← CommRingCat.comp_apply, f.hom_inv_id]
    exact ha

theorem stalkIdeal_comap (I : X.IdealSheafData) (σ : X ≅ X) (U : X.affineOpens) (x : X)
    (hxU : x ∈ (U : X.Opens)) :
    stalkIdeal (I.comap σ.hom) U x hxU =
      Ideal.map (σ.hom.stalkMap x).hom
        (stalkIdeal I ⟨σ.hom ''ᵁ U, U.2.image_of_isOpenImmersion σ.hom⟩ (σ.hom.base x) ⟨x, hxU, rfl⟩) := by
  unfold stalkIdeal
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, comap_inv_eq_map, Ideal.map_map, Ideal.map_map,
    ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  congr 2

  rw [Scheme.Hom.appIso_hom, Category.assoc,
    X.presheaf.germ_res (eqToHom (Scheme.Hom.preimage_image_eq σ.hom U).symm) x hxU,
    Scheme.Hom.germ_stalkMap]

end AlgebraicGeometry.StalkComapFixed

open AlgebraicGeometry.StalkComapFixed in
theorem solution
    {X : Scheme.{u}} (I : X.IdealSheafData) (σ : X ≅ X) (x : X) (hx : σ.hom.base x = x)
    [IsNoetherianRing (X.presheaf.stalk x)] [IsDomain (X.presheaf.stalk x)]
    [IsIntegrallyClosed (X.presheaf.stalk x)] (hdim : ringKrullDim (X.presheaf.stalk x) ≤ 1)
    (U : X.affineOpens) (hxU : x ∈ (U : X.Opens)) :
    Ideal.map (X.presheaf.germ U x hxU).hom ((I.comap σ.hom).ideal U) =
      Ideal.map (X.presheaf.germ U x hxU).hom (I.ideal U) := by
  change stalkIdeal (I.comap σ.hom) U x hxU = stalkIdeal I U x hxU
  rw [stalkIdeal_comap]

  set V : X.affineOpens := ⟨σ.hom ''ᵁ U, U.2.image_of_isOpenImmersion σ.hom⟩ with hV
  have hxV : x ∈ (V : X.Opens) := hx ▸ (⟨x, hxU, rfl⟩ : σ.hom.base x ∈ (V : X.Opens))
  have ht := map_eqToHom_stalkIdeal I V hx.symm hxV

  have hproof : (hx.symm ▸ hxV : σ.hom.base x ∈ (V : X.Opens)) = ⟨x, hxU, rfl⟩ := rfl
  rw [← ht, Ideal.map_map, ← CommRingCat.hom_comp, stalkIdeal_eq I V U x hxV hxU]

  set φ : X.presheaf.stalk x ⟶ X.presheaf.stalk x :=
    eqToHom (congrArg X.presheaf.stalk hx.symm) ≫ σ.hom.stalkMap x with hφ
  haveI : IsIso (σ.hom.stalkMap x) := inferInstance
  haveI : IsIso φ := by rw [hφ]; infer_instance
  have := ideal_map_ringEquiv_eq hdim (asIso φ).commRingCatIsoToRingEquiv (stalkIdeal I U x hxU)
  exact this

end S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_comap_eq_of_base_eq_of_ringKrullDim_le_one
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_comap_eq_of_base_eq_of_ringKrullDim_le_one (solution)
