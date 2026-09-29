-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.app_injective_and_range_eq_invariants_of_isBasis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/430d7cd4-800b-5b6a-8cfc-d40f1c8f2233

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_app_injective_and_range_eq_invariants_of_isBasis

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace QBAGC4

open TopologicalSpace Opposite TopCat TopCat.Presheaf

theorem mem_range_of_locally {X : TopCat.{u}} {F G : TopCat.Sheaf CommRingCat.{u} X} (f : F ⟶ G)
    (U : Opens X) (hinj : ∀ x ∈ U, Function.Injective ((TopCat.Presheaf.stalkFunctor _ x).map f.1))
    (t : ToType (G.1.obj (op U)))
    (hsurj : ∀ x ∈ U, ∃ (V : Opens X) (_ : x ∈ V) (iVU : V ⟶ U) (s : ToType (F.1.obj (op V))),
      f.1.app (op V) s = G.1.map iVU.op t) :
    t ∈ Set.range (f.1.app (op U)) := by
  choose V mV iVU sf heq using fun x : U => hsurj x.1 x.2
  have V_cover : U ≤ iSup V := fun x hxU => by
    simp only [Opens.mem_iSup]; exact ⟨⟨x, hxU⟩, mV ⟨x, hxU⟩⟩
  suffices h : TopCat.Presheaf.IsCompatible F.1 V sf by
    obtain ⟨s, s_spec, -⟩ := F.existsUnique_gluing' V U iVU V_cover sf h
    refine ⟨s, ?_⟩
    apply G.eq_of_locally_eq' V U iVU V_cover
    intro x
    rw [← ConcreteCategory.comp_apply, ← f.1.naturality, ConcreteCategory.comp_apply, s_spec, heq]
  intro x y
  apply TopCat.Presheaf.section_ext
  intro z hz
  apply hinj z ((iVU x).le ((inf_le_left : V x ⊓ V y ≤ V x) hz))
  dsimp only
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply]
  simp_rw [← ConcreteCategory.comp_apply, f.1.naturality, ConcreteCategory.comp_apply, heq,
    ← ConcreteCategory.comp_apply, ← G.1.map_comp]
  rfl

theorem appLE_app_eq {M X : Scheme.{u}} (π : M ⟶ X) (V : X.Opens) (f : M ⟶ M) (hf : f ≫ π = π)
    (e : π ⁻¹ᵁ V ≤ f ⁻¹ᵁ (π ⁻¹ᵁ V)) (t : Γ(X, V)) :
    f.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) e (π.app V t) = π.app V t := by
  have h1 := Scheme.Hom.appLE_comp_appLE f π V (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) le_rfl e
  have h2 : ∀ (k : M ⟶ X) (hk : k = π) (p : π ⁻¹ᵁ V ≤ k ⁻¹ᵁ V),
      k.appLE V (π ⁻¹ᵁ V) p = π.appLE V (π ⁻¹ᵁ V) le_rfl := by
    intro k hk p; subst hk; rfl
  have h3 : π.appLE V (π ⁻¹ᵁ V) le_rfl ≫ f.appLE _ _ e = π.appLE V (π ⁻¹ᵁ V) le_rfl := by
    rw [h1]; exact h2 _ hf _
  rw [Scheme.Hom.app_eq_appLE]
  change (π.appLE V (π ⁻¹ᵁ V) le_rfl ≫ f.appLE _ _ e) t = _
  rw [h3]

theorem appLE_map_eq {M X : Scheme.{u}} (π : M ⟶ X) {V W : X.Opens} (f : M ⟶ M)
    (eV : π ⁻¹ᵁ V ≤ f ⁻¹ᵁ (π ⁻¹ᵁ V)) (eW : π ⁻¹ᵁ W ≤ f ⁻¹ᵁ (π ⁻¹ᵁ W))
    (i : π ⁻¹ᵁ W ⟶ π ⁻¹ᵁ V) (s : Γ(M, π ⁻¹ᵁ V))
    (hs : f.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) eV s = s) :
    f.appLE (π ⁻¹ᵁ W) (π ⁻¹ᵁ W) eW (M.presheaf.map i.op s) = M.presheaf.map i.op s := by
  have key : M.presheaf.map i.op ≫ f.appLE (π ⁻¹ᵁ W) (π ⁻¹ᵁ W) eW =
      f.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) eV ≫ M.presheaf.map i.op := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  change (M.presheaf.map i.op ≫ f.appLE (π ⁻¹ᵁ W) (π ⁻¹ᵁ W) eW) s = _
  rw [key, CommRingCat.comp_apply, hs]

end QBAGC4

theorem solution
    {M X : Scheme.{0}} (π : M ⟶ X)
    {H : Type} [Group H] (ρ : H →* Aut M) (hπ : ∀ h : H, (ρ h).hom ≫ π = π)
    (B : Set X.Opens) (hB : TopologicalSpace.Opens.IsBasis B)
    (hsecB : ∀ W ∈ B, Function.Injective (π.app W))
    (hinvB : ∀ W ∈ B, Set.range (π.app W) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ W) (π ⁻¹ᵁ W) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s}) :
    (∀ V : X.Opens, Function.Injective (π.app V)) ∧
    (∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s}) := by
  let F : TopCat.Sheaf CommRingCat X.carrier := X.sheaf
  let G : TopCat.Sheaf CommRingCat X.carrier := (TopCat.Sheaf.pushforward _ π.base).obj M.sheaf
  let f : F ⟶ G := ⟨π.c⟩
  have hstalk : ∀ x : X, Function.Injective ((TopCat.Presheaf.stalkFunctor _ x).map f.1) :=
    TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hB (fun W hW => hsecB W hW)
  have hinjV : ∀ V : X.Opens, Function.Injective (π.app V) := fun V =>
    TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective f.1 V (fun x _ => hstalk x)
  refine ⟨hinjV, fun V => ?_⟩
  ext s
  constructor
  · rintro ⟨t, rfl⟩ h
    exact QBAGC4.appLE_app_eq π V (ρ h).hom (hπ h) _ t
  · intro hs
    change s ∈ Set.range (f.1.app (Opposite.op V))
    apply QBAGC4.mem_range_of_locally f V (fun x _ => hstalk x) s
    intro x hx
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := hB.exists_subset_of_mem_open hx V.2
    let i : π ⁻¹ᵁ W ⟶ π ⁻¹ᵁ V := (TopologicalSpace.Opens.map π.base).map (homOfLE hWV)
    have hs' : ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ W) (π ⁻¹ᵁ W)
        (by rw [← Scheme.Hom.comp_preimage, hπ h]) (M.presheaf.map i.op s) = M.presheaf.map i.op s :=
      fun h => QBAGC4.appLE_map_eq π (ρ h).hom _ _ i s (hs h)
    have hmem : M.presheaf.map i.op s ∈ Set.range (π.app W) := by rw [hinvB W hW]; exact hs'
    obtain ⟨tW, htW⟩ := hmem
    exact ⟨W, hxW, homOfLE hWV, tW, htW⟩

end S_AlgebraicGeometry_Scheme_app_injective_and_range_eq_invariants_of_isBasis
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_app_injective_and_range_eq_invariants_of_isBasis (solution)
