-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_isAffineOpen_mem_forall_preimage_eq_of_forall_finset_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/b4b4ea9b-2f0e-53b9-ad8c-de0f873ab194

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem_forall_preimage_eq_of_forall_finset_of_isSeparated

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) [IsSeparated π]
    {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X)
    (hAF : ∀ F : Finset X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (x : X) : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U := by
  classical
  haveI : Fintype G := Fintype.ofFinite G

  have mem_finset_inf : ∀ {ι : Type v} (V : ι → X.Opens) (s : Finset ι) (y : X),
      y ∈ s.inf V ↔ ∀ i ∈ s, y ∈ V i := by
    intro ι V s y
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.inf_cons, Opens.mem_inf, ih, Finset.forall_mem_cons]

  have aff_finset_inf : ∀ {ι : Type v} (V : ι → X.Opens) (_ : ∀ i, IsAffineOpen (V i)) (s : Finset ι),
      s.Nonempty → IsAffineOpen (s.inf V) := by
    intro ι V hV s
    induction s using Finset.cons_induction with
    | empty => intro h; exact absurd h Finset.not_nonempty_empty
    | cons a s ha ih =>
      intro _
      rw [Finset.inf_cons]
      by_cases hs : s.Nonempty
      · exact Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated π (hV a) (ih hs)
      · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.inf_empty, inf_top_eq]; exact hV a

  obtain ⟨U₀, hU₀, hxU₀⟩ := hAF (Finset.univ.image fun g : G => (ρ g).hom.base x)
  let V : G → X.Opens := fun g => (ρ g).hom ⁻¹ᵁ U₀
  have hV : ∀ g, IsAffineOpen (V g) := fun g => hU₀.preimage_of_isIso (ρ g).hom
  refine ⟨Finset.univ.inf V, aff_finset_inf V hV _ ⟨1, Finset.mem_univ _⟩, ?_, ?_⟩
  · rw [mem_finset_inf]
    intro g _
    show (ρ g).hom.base x ∈ U₀
    exact hxU₀ _ (Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩)
  · intro h
    ext y
    constructor
    · intro hy

      have hy' : (ρ h).hom.base y ∈ Finset.univ.inf V := hy
      rw [SetLike.mem_coe, mem_finset_inf]
      intro g _
      have := (mem_finset_inf V _ _).mp hy' (g * h⁻¹) (Finset.mem_univ _)

      show (ρ g).hom.base y ∈ U₀
      have e : (ρ h).hom ≫ (ρ (g * h⁻¹)).hom = (ρ g).hom := by
        rw [← Iso.trans_hom, ← Aut.Aut_mul_def, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
      rw [← e, Scheme.Hom.comp_base, TopCat.comp_app]
      exact this
    · intro hy
      have hy' : y ∈ Finset.univ.inf V := hy
      show (ρ h).hom.base y ∈ Finset.univ.inf V
      rw [mem_finset_inf]
      intro g _
      have := (mem_finset_inf V _ _).mp hy' (g * h) (Finset.mem_univ _)
      show (ρ g).hom.base ((ρ h).hom.base y) ∈ U₀
      have e : (ρ h).hom ≫ (ρ g).hom = (ρ (g * h)).hom := by
        rw [← Iso.trans_hom, ← Aut.Aut_mul_def, ← map_mul]
      rw [← TopCat.comp_app, ← Scheme.Hom.comp_base, e]
      exact this

end S_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem_forall_preimage_eq_of_forall_finset_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem_forall_preimage_eq_of_forall_finset_of_isSeparated (solution)
