-- Prove2me | solution 1 for AlgebraicGeometry.exists_smooth_maximal_and_image_eq_of_iso_over
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/5ff8a5ba-947f-571f-b7e5-1e7a0a07cbfd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_smooth_maximal_and_image_eq_of_iso_over

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    (hdim : ∀ V : X.Opens, Smooth (V.ι ≫ f) → SmoothOfRelativeDimension n (V.ι ≫ f)) :
    ∃ U : X.Opens, SmoothOfRelativeDimension n (U.ι ≫ f) ∧
      (∀ V : X.Opens, Smooth (V.ι ≫ f) → V ≤ U) ∧
      (∀ w : X ≅ X, w.hom ≫ f = f → w.hom ''ᵁ U = U) ∧
      (∀ w : X ≅ X, w.hom ≫ f = f → ∀ (T : Scheme.{u}) (ε : T ⟶ X),
        Set.range ε.base ⊆ (U : Set X) → Set.range (ε ≫ w.hom).base ⊆ (U : Set X)) := by
  classical

  let ι : Type u := {V : X.Opens // Smooth (V.ι ≫ f)}
  let U : X.Opens := ⨆ V : ι, V.1
  have hU_max : ∀ V : X.Opens, Smooth (V.ι ≫ f) → V ≤ U :=
    fun V hV => le_iSup (fun V : ι => V.1) ⟨V, hV⟩

  have hres : ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] (V : X.Opens),
      Smooth (V.ι ≫ f) → Smooth ((g ⁻¹ᵁ V).ι ≫ g ≫ f) := by
    intro Y g _ V hV
    have e : (g ⁻¹ᵁ V).ι ≫ g ≫ f = (g ∣_ V) ≫ V.ι ≫ f := by
      rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    rw [e]
    exact IsZariskiLocalAtSource.comp hV _

  have hU_smooth : Smooth (U.ι ≫ f) := by
    apply IsZariskiLocalAtSource.of_iSup_eq_top (fun V : ι => U.ι ⁻¹ᵁ V.1)
    · rw [← Scheme.Hom.preimage_iSup]
      exact U.ι_preimage_self
    · intro V
      exact hres U.ι V.1 V.2

  have hpre_le : ∀ w : X ≅ X, w.hom ≫ f = f → w.hom ⁻¹ᵁ U ≤ U := by
    intro w hw
    show w.hom ⁻¹ᵁ (⨆ V : ι, V.1) ≤ U
    rw [Scheme.Hom.preimage_iSup]
    refine iSup_le fun V => hU_max _ ?_
    have h := hres w.hom V.1 V.2
    rwa [hw] at h

  have hpre : ∀ w : X ≅ X, w.hom ≫ f = f → w.hom ⁻¹ᵁ U = U := by
    intro w hw
    have hw' : w.inv ≫ f = f := by rw [Iso.inv_comp_eq, hw]
    have h1 : w.inv ⁻¹ᵁ U ≤ U := hpre_le w.symm hw'
    refine le_antisymm (hpre_le w hw) ?_
    intro x hx
    show w.hom.base x ∈ (U : Set X)
    apply h1
    show (w.hom ≫ w.inv).base x ∈ (U : Set X)
    rw [Iso.hom_inv_id]
    exact hx
  refine ⟨U, hdim U hU_smooth, hU_max, ?_, ?_⟩
  ·
    intro w hw
    have hw' : w.inv ≫ f = f := by rw [Iso.inv_comp_eq, hw]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h : (y : X) ∈ w.hom ⁻¹ᵁ U := by rw [hpre w hw]; exact hy
      exact h
    · intro hx
      refine ⟨w.inv.base x, ?_, ?_⟩
      · have h : x ∈ w.symm.hom ⁻¹ᵁ U := by rw [hpre w.symm hw']; exact hx
        exact h
      · show (w.inv ≫ w.hom).base x = x
        rw [Iso.inv_hom_id]
        rfl
  ·
    intro w hw T ε hε
    rintro _ ⟨t, rfl⟩
    have ht : ε.base t ∈ U := hε ⟨t, rfl⟩
    have h2 : ε.base t ∈ w.hom ⁻¹ᵁ U := by rw [hpre w hw]; exact ht
    exact h2

end S_AlgebraicGeometry_exists_smooth_maximal_and_image_eq_of_iso_over
end P2MW
export P2MW.S_AlgebraicGeometry_exists_smooth_maximal_and_image_eq_of_iso_over (solution)
