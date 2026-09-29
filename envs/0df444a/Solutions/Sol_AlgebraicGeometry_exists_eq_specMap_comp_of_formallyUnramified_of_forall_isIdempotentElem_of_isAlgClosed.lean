-- Prove2me | solution 1 for AlgebraicGeometry.exists_eq_specMap_comp_of_formallyUnramified_of_forall_isIdempotentElem_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/6e6e695f-8c1b-5845-a617-4a3001974551

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_formallyUnramified_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_connectedSpace_of_forall_isIdempotentElem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_eq_specMap_comp_of_formallyUnramified_of_forall_isIdempotentElem_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {H : Scheme.{u}} (q : H ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType q] [FormallyUnramified q]
    (B : Type u) [CommRing B] [Nontrivial B] (ψ : k →+* B) (hB : ∀ b : B, IsIdempotentElem b → b = 0 ∨ b = 1)
    (x : Spec (CommRingCat.of B) ⟶ H) (hx : x ≫ q = Spec.map (CommRingCat.ofHom ψ)) :
    ∃ h : Spec (CommRingCat.of k) ⟶ H, h ≫ q = 𝟙 _ ∧ x = Spec.map (CommRingCat.ofHom ψ) ≫ h := by
  classical

  let t : ↥(Spec (CommRingCat.of B)) := Classical.arbitrary (PrimeSpectrum B)
  haveI : Nonempty ↥(Spec (CommRingCat.of B)) := ⟨t⟩
  haveI : ConnectedSpace ↥(Spec (CommRingCat.of B)) := by
    refine Scheme.connectedSpace_of_forall_isIdempotentElem _ (fun e he => ?_)
    have he' : IsIdempotentElem ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom e) := he.map _
    have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom := fun a b hab => by
      have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom hab
      rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply,
        CommRingCat.id_apply] at h2
    rcases hB _ he' with h0 | h1
    · left; apply hinj; rw [h0, map_zero]
    · right; apply hinj; rw [h1, map_one]

  have hpt := fun z : H =>
    AlgebraicGeometry.exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_formallyUnramified_of_isAlgClosed q z
  obtain ⟨U, hU, hUiso⟩ := hpt (x.base t)

  have hopen : ∀ z : H, IsOpen ({z} : Set H) := fun z => by
    obtain ⟨W, hW, -⟩ := hpt z
    rw [← hW]; exact W.isOpen
  have hclopen : IsClopen (x.base ⁻¹' (U : Set H)) := by
    refine ⟨⟨?_⟩, U.isOpen.preimage x.base.hom.continuous⟩
    rw [← Set.preimage_compl, hU]
    refine IsOpen.preimage x.base.hom.continuous ?_
    rw [← Set.biUnion_of_singleton ({x.base t}ᶜ : Set H)]
    exact isOpen_biUnion fun z _ => hopen z
  have huniv : x.base ⁻¹' (U : Set H) = Set.univ :=
    (hclopen.eq_univ ⟨t, by show x.base t ∈ (U : Set H); rw [hU]; rfl⟩)
  have hrange : Set.range x.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨s, rfl⟩
    have : s ∈ x.base ⁻¹' (U : Set H) := by rw [huniv]; trivial
    exact this

  let x' := IsOpenImmersion.lift U.ι x hrange
  have hx' : x' ≫ U.ι = x := IsOpenImmersion.lift_fac _ _ _
  haveI := hUiso
  let e : (U : Scheme.{u}) ≅ Spec (CommRingCat.of k) := asIso (U.ι ≫ q)
  refine ⟨e.inv ≫ U.ι, ?_, ?_⟩
  · rw [Category.assoc]; exact e.inv_hom_id
  · calc x = x' ≫ U.ι := hx'.symm
      _ = (x' ≫ (U.ι ≫ q)) ≫ e.inv ≫ U.ι := by
          rw [Category.assoc, ← Category.assoc (U.ι ≫ q), show (U.ι ≫ q) ≫ e.inv = 𝟙 _ from e.hom_inv_id,
            Category.id_comp]
      _ = Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι := by rw [← Category.assoc x', hx', hx]

end S_AlgebraicGeometry_exists_eq_specMap_comp_of_formallyUnramified_of_forall_isIdempotentElem_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_exists_eq_specMap_comp_of_formallyUnramified_of_forall_isIdempotentElem_of_isAlgClosed (solution)
