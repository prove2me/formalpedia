-- Prove2me | solution 1 for AlgebraicGeometry.isAffineOpen_of_isAffineOpen_preimage_of_app_surjective_of_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/0c284335-0075-577d-b16c-fda9945fe12a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isAffineOpen_of_isAffineOpen_preimage_of_app_surjective_of_mul_eq_zero

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AffineFromLift15

theorem mul_self_eq_zero_of_app_eq_zero {X X' : Scheme.{u}} (i : X ⟶ X')
    (hsq : ∀ (V : X'.Opens), IsAffineOpen V → ∀ a b : Γ(X', V),
      (i.app V).hom a = 0 → (i.app V).hom b = 0 → a * b = 0)
    {U : X'.Opens} (ε : Γ(X', U)) (hε : (i.app U).hom ε = 0) : ε * ε = 0 := by
  apply X'.IsSheaf.section_ext
  intro y hy
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open hy U.2
  refine ⟨V, hVU, hyV, ?_⟩
  have hres : (i.app V).hom ((X'.presheaf.map (homOfLE hVU).op) ε) = 0 := by
    change (X'.presheaf.map (homOfLE hVU).op ≫ i.app V) ε = 0
    rw [i.naturality, CommRingCat.comp_apply]
    change (X.presheaf.map _) ((i.app U).hom ε) = 0
    rw [hε, map_zero]
  rw [map_mul, map_zero]
  exact hsq V hV _ _ hres hres

end AffineFromLift15

open AffineFromLift15 in
theorem solution
    {X X' : Scheme.{u}} (i : X ⟶ X') [Surjective i]
    (hsq : ∀ (V : X'.Opens), IsAffineOpen V → ∀ a b : Γ(X', V), (i.app V).hom a = 0 → (i.app V).hom b = 0 → a * b = 0)
    (U : X'.Opens) (hU : IsAffineOpen (i ⁻¹ᵁ U)) (hsurj : Function.Surjective (i.app U).hom) : IsAffineOpen U := by

  let t : Set Γ(X', U) := {g | IsAffineOpen (X'.basicOpen g)}
  refine isAffineOpen_of_isAffineOpen_basicOpen U t ?_ (fun g hg => hg)

  have hcover : Ideal.span ((i.app U).hom '' t) = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    have hix : i x ∈ U := hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open hix U.2
    obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le (V := i ⁻¹ᵁ V) ⟨x, hxV⟩ hx
    obtain ⟨g, rfl⟩ := hsurj f

    have hgV : X'.basicOpen g ≤ V := by
      intro y hy
      obtain ⟨x', rfl⟩ := i.surjective y
      have hx' : x' ∈ i ⁻¹ᵁ X'.basicOpen g := hy
      rw [Scheme.preimage_basicOpen] at hx'
      exact hfV hx'

    have hgt : g ∈ t := by
      show IsAffineOpen (X'.basicOpen g)
      rw [← inf_eq_right.mpr hgV, ← X'.basicOpen_res g (homOfLE hVU).op]
      exact hV.basicOpen _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(i.app U).hom g, g, hgt, rfl⟩, hxf⟩

  have h1 : (1 : Γ(X, i ⁻¹ᵁ U)) ∈ Ideal.map (i.app U).hom (Ideal.span t) := by
    rw [Ideal.map_span, hcover]
    trivial
  obtain ⟨j, hj, hj1⟩ := (Ideal.mem_map_iff_of_surjective (i.app U).hom hsurj).mp h1
  have hε : (i.app U).hom (j - 1) = 0 := by rw [map_sub, hj1, map_one, sub_self]
  have hnil : IsNilpotent (j - 1) :=
    ⟨2, by rw [pow_two]; exact mul_self_eq_zero_of_app_eq_zero i hsq (j - 1) hε⟩
  have hunit : IsUnit j := by
    have h := hnil.isUnit_one_add
    have e : (1 : Γ(X', U)) + (j - 1) = j := by ring
    rwa [e] at h
  exact Ideal.eq_top_of_isUnit_mem _ hj hunit

end S_AlgebraicGeometry_isAffineOpen_of_isAffineOpen_preimage_of_app_surjective_of_mul_eq_zero
end P2MW
export P2MW.S_AlgebraicGeometry_isAffineOpen_of_isAffineOpen_preimage_of_app_surjective_of_mul_eq_zero (solution)
