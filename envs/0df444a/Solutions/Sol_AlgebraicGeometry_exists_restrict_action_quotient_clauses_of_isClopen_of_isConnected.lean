-- Prove2me | solution 1 for AlgebraicGeometry.exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/27968ba1-fd89-56cd-8ac5-c63ec6a71e6a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace CQAux

noncomputable def restrictAut {C : Scheme.{0}} (U : C.Opens) (f : Aut C) (hf : f.hom ⁻¹ᵁ U = U) (hf' : f.inv ⁻¹ᵁ U = U) :
    Aut (U : Scheme.{0}) where
  hom := f.hom.resLE U U (le_of_eq hf.symm)
  inv := f.inv.resLE U U (le_of_eq hf'.symm)
  hom_inv_id := by
    rw [← cancel_mono U.ι]
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Category.id_comp]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  inv_hom_id := by
    rw [← cancel_mono U.ι]
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Category.id_comp]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem restrictAut_hom_ι {C : Scheme.{0}} (U : C.Opens) (f : Aut C) (hf : f.hom ⁻¹ᵁ U = U) (hf' : f.inv ⁻¹ᵁ U = U) :
    (restrictAut U f hf hf').hom ≫ U.ι = U.ι ≫ f.hom := Scheme.Hom.resLE_comp_ι _ _

theorem inv_preimage_eq {C : Scheme.{0}} (U : C.Opens) (f : Aut C) (hf : f.hom ⁻¹ᵁ U = U) : f.inv ⁻¹ᵁ U = U := by
  conv_lhs => rw [← hf]
  rw [← Scheme.Hom.comp_preimage, Iso.inv_hom_id, Scheme.Hom.id_preimage]

noncomputable def rho0 {C : Scheme.{0}} {G : Type} [Group G] (ρ : G →* Aut C) (U : C.Opens) (G₀ : Subgroup G)
    (hG₀ : ∀ g : G, g ∈ G₀ ↔ (ρ g).hom ⁻¹ᵁ U = U) : G₀ →* Aut (U : Scheme.{0}) where
  toFun g := restrictAut U (ρ (g : G)) ((hG₀ g).mp g.2) (inv_preimage_eq U (ρ (g : G)) ((hG₀ g).mp g.2))
  map_one' := by
    apply Iso.ext
    rw [← cancel_mono U.ι, restrictAut_hom_ι]
    rw [show ((1 : G₀) : G) = 1 from rfl, map_one]
    show U.ι ≫ (Iso.refl C).hom = (Iso.refl _).hom ≫ U.ι
    simp
  map_mul' g h := by
    apply Iso.ext
    rw [← cancel_mono U.ι, restrictAut_hom_ι]
    show U.ι ≫ (ρ ((g : G) * (h : G))).hom = (_ ≪≫ _).hom ≫ U.ι
    rw [map_mul, Aut.Aut_mul_def, Iso.trans_hom, Iso.trans_hom, Category.assoc, restrictAut_hom_ι]
    conv_rhs => rw [← Category.assoc, restrictAut_hom_ι]
    simp only [Category.assoc]

theorem rho0_hom_ι {C : Scheme.{0}} {G : Type} [Group G] (ρ : G →* Aut C) (U : C.Opens) (G₀ : Subgroup G)
    (hG₀ : ∀ g : G, g ∈ G₀ ↔ (ρ g).hom ⁻¹ᵁ U = U) (g : G₀) :
    (rho0 ρ U G₀ hG₀ g).hom ≫ U.ι = U.ι ≫ (ρ (g : G)).hom :=
  restrictAut_hom_ι U (ρ (g : G)) ((hG₀ g).mp g.2) (inv_preimage_eq U (ρ (g : G)) ((hG₀ g).mp g.2))

theorem isClosedImmersion_ι_of_isClosed {C : Scheme.{0}} (U : C.Opens) (hU : IsClosed (U : Set C)) : IsClosedImmersion U.ι :=
  IsClosedImmersion.of_isPreimmersion U.ι (by rw [Scheme.Opens.range_ι]; exact hU)

theorem preimage_preimage_act {C : Scheme.{0}} {G : Type} [Group G] (ρ : G →* Aut C) (g h : G) (U : C.Opens) :
    (ρ h).hom ⁻¹ᵁ ((ρ g).hom ⁻¹ᵁ U) = (ρ (g * h)).hom ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, map_mul, Aut.Aut_mul_def, Iso.trans_hom]

theorem range_ι_comp_eq_univ {C X : Scheme.{0}} [ConnectedSpace X] {G : Type} [Group G] [Finite G] (ρ : G →* Aut C)
    (π : C ⟶ X) [IsFinite π] (hπ : ∀ g : G, (ρ g).hom ≫ π = π) (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : C, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x')
    (U : C.Opens) (hUcl : IsClosed (U : Set C)) (hUne : (U : Set C).Nonempty) :
    Set.range (U.ι ≫ π).base = Set.univ := by
  classical
  haveI : Fintype G := Fintype.ofFinite G

  let W : Set C := ⋃ g : G, (ρ g).hom.base ⁻¹' (U : Set C)
  have hWopen : IsOpen W := isOpen_iUnion fun g => (U.isOpen.preimage (ρ g).hom.base.hom.continuous)
  have hWclosed : IsClosed W := isClosed_iUnion_of_finite fun g => hUcl.preimage (ρ g).hom.base.hom.continuous
  have hWstab : ∀ (h : G) (x : C), x ∈ W → (ρ h).hom.base x ∈ W := by
    intro h x hx
    obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨g * h⁻¹, ?_⟩
    show (ρ (g * h⁻¹)).hom.base ((ρ h).hom.base x) ∈ (U : Set C)
    have e1 : (ρ (g * h⁻¹)).hom.base ((ρ h).hom.base x) = ((ρ h).hom ≫ (ρ (g * h⁻¹)).hom).base x := rfl
    rw [e1, ← Iso.trans_hom, ← Aut.Aut_mul_def, ← map_mul, inv_mul_cancel_right]
    exact hg
  have hπW : π.base '' W = π.base '' (U : Set C) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hx
      refine ⟨(ρ g).hom.base x, hg, ?_⟩
      have e1 : π.base ((ρ g).hom.base x) = ((ρ g).hom ≫ π).base x := rfl
      rw [e1, hπ]
    · apply Set.image_mono
      intro x hx
      exact Set.mem_iUnion.mpr ⟨1, by rw [map_one]; exact hx⟩
  have hclosedmap : IsClosedMap π.base := π.isClosedMap
  have h1 : IsClosed (π.base '' W) := hclosedmap _ hWclosed
  have h2 : IsClosed (π.base '' Wᶜ) := hclosedmap _ hWopen.isClosed_compl
  have hdisj : Disjoint (π.base '' W) (π.base '' Wᶜ) := by
    rw [Set.disjoint_iff]
    rintro y ⟨⟨w, hw, rfl⟩, ⟨z, hz, hzy⟩⟩
    obtain ⟨g, hg⟩ := (horbit w z).mp hzy.symm
    exact hz (hg ▸ hWstab g w hw)
  have hcover : π.base '' W ∪ π.base '' Wᶜ = Set.univ := by
    rw [← Set.image_union, Set.union_compl_self, Set.image_univ, Set.range_eq_univ.mpr hsurj]
  have hclopen : IsClopen (π.base '' W) := by
    refine ⟨h1, ?_⟩
    have : (π.base '' W) = (π.base '' Wᶜ)ᶜ := by
      apply le_antisymm
      · exact Set.subset_compl_iff_disjoint_right.mpr hdisj
      · intro y hy
        have := hcover ▸ Set.mem_univ y
        rcases this with h | h
        · exact h
        · exact (hy h).elim
    rw [this]; exact h2.isOpen_compl
  have hne : (π.base '' W).Nonempty := by
    obtain ⟨u, hu⟩ := hUne
    exact ⟨π.base u, u, Set.mem_iUnion.mpr ⟨1, by rw [map_one]; exact hu⟩, rfl⟩
  have := hclopen.eq_univ hne
  rw [hπW] at this
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
  exact this

theorem preimage_eq_of_mem {C : Scheme.{0}} {G : Type} [Group G] (ρ : G →* Aut C)
    (U : C.Opens) (hUcl : IsClosed (U : Set C)) (hUconn : _root_.IsConnected (U : Set C))
    (g : G) (u : C) (hu : u ∈ (U : Set C)) (hgu : (ρ g).hom.base u ∈ (U : Set C)) :
    (ρ g).hom ⁻¹ᵁ U = U := by

  have hVclopen : IsClopen ((ρ g).hom.base ⁻¹' (U : Set C)) :=
    ⟨hUcl.preimage (ρ g).hom.base.hom.continuous, U.isOpen.preimage (ρ g).hom.base.hom.continuous⟩
  have hUclopen : IsClopen (U : Set C) := ⟨hUcl, U.isOpen⟩
  have hinvhom : ∀ y : C, (ρ g).hom.base ((ρ g).inv.base y) = y := fun y => by
    show ((ρ g).inv ≫ (ρ g).hom).base y = y
    rw [Iso.inv_hom_id]; rfl
  have hhominv : ∀ x : C, (ρ g).inv.base ((ρ g).hom.base x) = x := fun x => by
    show ((ρ g).hom ≫ (ρ g).inv).base x = x
    rw [Iso.hom_inv_id]; rfl
  have hVeq : (ρ g).hom.base ⁻¹' (U : Set C) = (ρ g).inv.base '' (U : Set C) := by
    ext x
    constructor
    · intro hx
      exact ⟨(ρ g).hom.base x, hx, hhominv x⟩
    · rintro ⟨y, hy, rfl⟩
      show (ρ g).hom.base ((ρ g).inv.base y) ∈ (U : Set C)
      rw [hinvhom]; exact hy
  have hVconn : _root_.IsConnected ((ρ g).hom.base ⁻¹' (U : Set C)) := by
    rw [hVeq]
    exact hUconn.image _ (ρ g).inv.base.hom.continuous.continuousOn
  apply TopologicalSpace.Opens.ext
  show (ρ g).hom.base ⁻¹' (U : Set C) = (U : Set C)
  apply le_antisymm
  · exact hVconn.isPreconnected.subset_isClopen hUclopen ⟨u, hgu, hu⟩
  · exact hUconn.isPreconnected.subset_isClopen hVclopen ⟨u, hu, hgu⟩

theorem appLE_app_eq_of_comp_eq {C X : Scheme.{0}} (f : C ⟶ C) (p : C ⟶ X) (hf : f ≫ p = p) (V : X.Opens)
    (e : p ⁻¹ᵁ V ≤ f ⁻¹ᵁ (p ⁻¹ᵁ V)) (t : Γ(X, V)) :
    f.appLE (p ⁻¹ᵁ V) (p ⁻¹ᵁ V) e (p.app V t) = p.app V t := by
  have key : ∀ (q : C ⟶ X) (hq : q = p) (e' : p ⁻¹ᵁ V ≤ q ⁻¹ᵁ V), q.appLE V (p ⁻¹ᵁ V) e' = p.app V := by
    rintro q rfl e'; exact Scheme.Hom.appLE_eq_app _
  have h : p.app V ≫ f.appLE (p ⁻¹ᵁ V) (p ⁻¹ᵁ V) e = p.app V := by
    rw [← Scheme.Hom.comp_appLE f p V (p ⁻¹ᵁ V) e, key (f ≫ p) hf]
  exact congrFun (congrArg (fun k => ⇑(CommRingCat.Hom.hom k)) h) t

theorem exists_mem_translate {C X : Scheme.{0}} [ConnectedSpace X] {G : Type} [Group G] [Finite G] (ρ : G →* Aut C)
    (π : C ⟶ X) [IsFinite π] (hπ : ∀ g : G, (ρ g).hom ≫ π = π) (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : C, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x')
    (U : C.Opens) (hUcl : IsClosed (U : Set C)) (hUne : (U : Set C).Nonempty) (x : C) :
    ∃ g : G, (ρ g).hom.base x ∈ (U : Set C) := by
  have hx : π.base x ∈ Set.range (U.ι ≫ π).base := by
    rw [range_ι_comp_eq_univ ρ π hπ hsurj horbit U hUcl hUne]; trivial
  obtain ⟨u, hu⟩ := hx
  have hu' : π.base (U.ι.base u) = π.base x := hu
  obtain ⟨g, hg⟩ := (horbit _ _).mp hu'.symm
  exact ⟨g, by rw [hg]; simp [Scheme.Opens.ι_apply]⟩

theorem iSup_preimage_inf_eq {C X : Scheme.{0}} [ConnectedSpace X] {G : Type} [Group G] [Finite G] (ρ : G →* Aut C)
    (π : C ⟶ X) [IsFinite π] (hπ : ∀ g : G, (ρ g).hom ≫ π = π) (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : C, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x')
    (U : C.Opens) (hUcl : IsClosed (U : Set C)) (hUne : (U : Set C).Nonempty) (V : X.Opens) :
    π ⁻¹ᵁ V ≤ ⨆ g : G, (ρ g).hom ⁻¹ᵁ (U ⊓ π ⁻¹ᵁ V) := by
  intro x hx
  obtain ⟨g, hg⟩ := exists_mem_translate ρ π hπ hsurj horbit U hUcl hUne x
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨g, ?_⟩
  show (ρ g).hom.base x ∈ ((U ⊓ π ⁻¹ᵁ V : C.Opens) : Set C)
  refine ⟨hg, ?_⟩
  show π.base ((ρ g).hom.base x) ∈ (V : Set X)
  have : π.base ((ρ g).hom.base x) = ((ρ g).hom ≫ π).base x := rfl
  rw [this, hπ]; exact hx

theorem le_iSup_preimage_imagePreimage {C X : Scheme.{0}} [ConnectedSpace X] {G : Type} [Group G] [Finite G] (ρ : G →* Aut C)
    (π : C ⟶ X) [IsFinite π] (hπ : ∀ g : G, (ρ g).hom ≫ π = π) (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : C, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x')
    (U : C.Opens) (hUcl : IsClosed (U : Set C)) (hUne : (U : Set C).Nonempty) (V : X.Opens) :
    π ⁻¹ᵁ V ≤ ⨆ g : G, (ρ g).hom ⁻¹ᵁ (U.ι ''ᵁ U.ι ⁻¹ᵁ (π ⁻¹ᵁ V)) := by
  have : U.ι ''ᵁ U.ι ⁻¹ᵁ (π ⁻¹ᵁ V) = U ⊓ π ⁻¹ᵁ V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  rw [this]
  exact iSup_preimage_inf_eq ρ π hπ hsurj horbit U hUcl hUne V

theorem appLE_appLE_apply {C : Scheme.{0}} (f₁ f₂ : C ⟶ C) (W A B : C.Opens) (e₁ : A ≤ f₁ ⁻¹ᵁ W) (e₂ : B ≤ f₂ ⁻¹ᵁ A)
    (e₃ : B ≤ (f₂ ≫ f₁) ⁻¹ᵁ W) (s : Γ(C, W)) :
    f₂.appLE A B e₂ (f₁.appLE W A e₁ s) = (f₂ ≫ f₁).appLE W B e₃ s := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem appLE_congr_hom {C : Scheme.{0}} {f f' : C ⟶ C} (h : f = f') (W A : C.Opens) (e : A ≤ f ⁻¹ᵁ W) (e' : A ≤ f' ⁻¹ᵁ W)
    (s : Γ(C, W)) : f.appLE W A e s = f'.appLE W A e' s := by
  subst h; rfl

theorem map_appLE_apply {C : Scheme.{0}} (f : C ⟶ C) (W A B : C.Opens) (e : A ≤ f ⁻¹ᵁ W) (hBA : B ≤ A) (s : Γ(C, W)) :
    C.presheaf.map (homOfLE hBA).op (f.appLE W A e s) = f.appLE W B (hBA.trans e) s := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_map_apply {C : Scheme.{0}} (f : C ⟶ C) (W W' A : C.Opens) (hW : W' ≤ W) (e : A ≤ f ⁻¹ᵁ W') (s : Γ(C, W)) :
    f.appLE W' A e (C.presheaf.map (homOfLE hW).op s) = f.appLE W A (e.trans (f.preimage_mono hW)) s := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem appLE_one_apply {C : Scheme.{0}} {G : Type} [Group G] (ρ : G →* Aut C) (W : C.Opens) (e : W ≤ (ρ 1).hom ⁻¹ᵁ W)
    (s : Γ(C, W)) : (ρ 1).hom.appLE W W e s = s := by
  have : (ρ 1).hom = 𝟙 C := by rw [map_one]; rfl
  rw [appLE_congr_hom this W W e le_rfl s]
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
  have h2 : ∀ (i : (Opposite.op W) ⟶ (Opposite.op W)), (𝟙 Γ(C, W) ≫ C.presheaf.map i) s = s := by
    intro i; rw [Subsingleton.elim i (𝟙 _), CategoryTheory.Functor.map_id]; rfl
  exact h2 _

theorem preimage_O_eq {C X : Scheme.{0}} {G : Type} [Group G] (ρ : G →* Aut C) (π : C ⟶ X)
    (hπ : ∀ g : G, (ρ g).hom ≫ π = π) (U : C.Opens) (V : X.Opens) (k : G) (hk : (ρ k).hom ⁻¹ᵁ U = U) :
    (ρ k).hom ⁻¹ᵁ (U.ι ''ᵁ U.ι ⁻¹ᵁ (π ⁻¹ᵁ V)) = U.ι ''ᵁ U.ι ⁻¹ᵁ (π ⁻¹ᵁ V) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, Scheme.Hom.preimage_inf, hk,
    ← Scheme.Hom.comp_preimage, hπ k]

end CQAux

open CQAux in
theorem solution
    {C X : Scheme.{0}} [ConnectedSpace X]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut C)
    (π : C ⟶ X) [IsFinite π] (hπ : ∀ g : G, (ρ g).hom ≫ π = π)
    (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : C, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x')
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (U : C.Opens) (hUcl : IsClosed (U : Set C)) (hUconn : _root_.IsConnected (U : Set C))
    (G₀ : Subgroup G) (hG₀ : ∀ g : G, g ∈ G₀ ↔ (ρ g).hom ⁻¹ᵁ U = U) :
    ∃ ρ₀ : G₀ →* Aut (U : Scheme.{0}),
      (∀ g : G₀, (ρ₀ g).hom ≫ U.ι = U.ι ≫ (ρ (g : G)).hom) ∧
      (∃ hπ₀ : ∀ g : G₀, (ρ₀ g).hom ≫ (U.ι ≫ π) = U.ι ≫ π,
        IsFinite (U.ι ≫ π) ∧
        Function.Surjective (U.ι ≫ π).base ∧
        (∀ u u' : (U : Scheme.{0}), (U.ι ≫ π).base u = (U.ι ≫ π).base u' ↔ ∃ g : G₀, (ρ₀ g).hom.base u = u') ∧
        (∀ V : X.Opens, Function.Injective ((U.ι ≫ π).app V)) ∧
        (∀ V : X.Opens, Set.range ((U.ι ≫ π).app V) =
          {s | ∀ g : G₀, (ρ₀ g).hom.appLE ((U.ι ≫ π) ⁻¹ᵁ V) ((U.ι ≫ π) ⁻¹ᵁ V)
            (by rw [← Scheme.Hom.comp_preimage, hπ₀ g]) s = s})) := by
  classical
  have hUne : (U : Set C).Nonempty := hUconn.nonempty
  refine ⟨rho0 ρ U G₀ hG₀, rho0_hom_ι ρ U G₀ hG₀, ?_⟩
  have hπ₀ : ∀ g : G₀, (rho0 ρ U G₀ hG₀ g).hom ≫ (U.ι ≫ π) = U.ι ≫ π := by
    intro g; rw [← Category.assoc, rho0_hom_ι, Category.assoc, hπ]
  refine ⟨hπ₀, ?_, ?_, ?_, ?_, ?_⟩
  · haveI := isClosedImmersion_ι_of_isClosed U hUcl
    infer_instance
  · exact Set.range_eq_univ.mp (range_ι_comp_eq_univ ρ π hπ hsurj horbit U hUcl hUne)
  · intro u u'
    constructor
    · intro h
      have h' : π.base (U.ι.base u) = π.base (U.ι.base u') := h
      obtain ⟨g, hg⟩ := (horbit _ _).mp h'
      have hgU : (ρ g).hom ⁻¹ᵁ U = U :=
        preimage_eq_of_mem ρ U hUcl hUconn g (U.ι.base u) (by simp [Scheme.Opens.ι_apply]) (by rw [hg]; simp [Scheme.Opens.ι_apply])
      refine ⟨⟨g, (hG₀ g).mpr hgU⟩, ?_⟩
      apply U.ι.isOpenEmbedding.injective
      show (((rho0 ρ U G₀ hG₀ ⟨g, _⟩).hom ≫ U.ι).base u) = U.ι.base u'
      rw [rho0_hom_ι]
      exact hg
    · rintro ⟨g, hg⟩
      rw [← hg]
      show (U.ι ≫ π).base u = ((rho0 ρ U G₀ hG₀ g).hom ≫ U.ι ≫ π).base u
      rw [hπ₀]
  ·
    intro V t₁ t₂ h
    apply hsec V
    let O : C.Opens := U.ι ''ᵁ U.ι ⁻¹ᵁ (π ⁻¹ᵁ V)
    have hO : O ≤ π ⁻¹ᵁ V := U.ι.image_preimage_le _
    have hT : ∀ g : G, (ρ g).hom ⁻¹ᵁ O ≤ π ⁻¹ᵁ V := by
      intro g
      calc (ρ g).hom ⁻¹ᵁ O ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V) := ((ρ g).hom.preimage_mono hO)
        _ = π ⁻¹ᵁ V := by rw [← Scheme.Hom.comp_preimage, hπ g]
    apply C.sheaf.eq_of_locally_eq' (fun g : G => (ρ g).hom ⁻¹ᵁ O) (π ⁻¹ᵁ V) (fun g => homOfLE (hT g))
      (le_iSup_preimage_imagePreimage ρ π hπ hsurj horbit U hUcl hUne V)
    intro g
    have e : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V) := by rw [← Scheme.Hom.comp_preimage, hπ g]
    have key : ∀ t : Γ(X, V), C.sheaf.1.map (homOfLE (hT g)).op (π.app V t) =
        (ρ g).hom.appLE O ((ρ g).hom ⁻¹ᵁ O) le_rfl ((U.ι ≫ π).app V t) := by
      intro t
      have m1 : (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) e ≫ C.presheaf.map (homOfLE (hT g)).op =
          (ρ g).hom.appLE (π ⁻¹ᵁ V) ((ρ g).hom ⁻¹ᵁ O) ((ρ g).hom.preimage_mono hO) := Scheme.Hom.appLE_map _ _ _
      have m2 : C.presheaf.map (homOfLE hO).op ≫ (ρ g).hom.appLE O ((ρ g).hom ⁻¹ᵁ O) le_rfl =
          (ρ g).hom.appLE (π ⁻¹ᵁ V) ((ρ g).hom ⁻¹ᵁ O) ((ρ g).hom.preimage_mono hO) := Scheme.Hom.map_appLE _ _ _
      have m3 : (U.ι ≫ π).app V t = C.presheaf.map (homOfLE hO).op (π.app V t) := rfl
      calc C.sheaf.1.map (homOfLE (hT g)).op (π.app V t)
          = C.presheaf.map (homOfLE (hT g)).op ((ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) e (π.app V t)) := by
            rw [appLE_app_eq_of_comp_eq (ρ g).hom π (hπ g) V e t]; rfl
        _ = ((ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) e ≫ C.presheaf.map (homOfLE (hT g)).op) (π.app V t) := by
            rw [CommRingCat.comp_apply]
        _ = (C.presheaf.map (homOfLE hO).op ≫ (ρ g).hom.appLE O ((ρ g).hom ⁻¹ᵁ O) le_rfl) (π.app V t) := by
            rw [m1, m2]
        _ = (ρ g).hom.appLE O ((ρ g).hom ⁻¹ᵁ O) le_rfl ((U.ι ≫ π).app V t) := by
            rw [CommRingCat.comp_apply, m3]
    rw [key, key, h]
  ·
    intro V
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩ g
      exact appLE_app_eq_of_comp_eq _ _ (hπ₀ g) V _ t
    · intro s hs

      let O : C.Opens := U.ι ''ᵁ U.ι ⁻¹ᵁ (π ⁻¹ᵁ V)
      have hO : O ≤ π ⁻¹ᵁ V := U.ι.image_preimage_le _
      have hOU : O ≤ U := U.ι_image_le _
      have hT : ∀ g : G, (ρ g).hom ⁻¹ᵁ O ≤ π ⁻¹ᵁ V := by
        intro g
        calc (ρ g).hom ⁻¹ᵁ O ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V) := ((ρ g).hom.preimage_mono hO)
          _ = π ⁻¹ᵁ V := by rw [← Scheme.Hom.comp_preimage, hπ g]
      have hcover := le_iSup_preimage_imagePreimage ρ π hπ hsurj horbit U hUcl hUne V

      have hs' : ∀ (k : G) (hk : (ρ k).hom ⁻¹ᵁ U = U) (e : O ≤ (ρ k).hom ⁻¹ᵁ O),
          (ρ k).hom.appLE O O e s = s := by
        intro k hk e
        have h1 := hs ⟨k, (hG₀ k).mpr hk⟩
        exact (Scheme.Hom.resLE_appLE (ρ k).hom (le_of_eq ((hG₀ k).mp ((hG₀ k).mpr hk)).symm) _ _ _ ▸ h1 :)

      let T : G → C.Opens := fun g => (ρ g).hom ⁻¹ᵁ O
      let sf : ∀ g : G, Γ(C, T g) := fun g => (ρ g).hom.appLE O (T g) le_rfl s

      have hmeet : ∀ (g h : G) (x : C), x ∈ (T g : Set C) → x ∈ (T h : Set C) →
          (ρ (g * h⁻¹)).hom ⁻¹ᵁ U = U := by
        intro g h x hxg hxh
        have hgx : (ρ g).hom.base x ∈ (U : Set C) := hOU hxg
        have hhx : (ρ h).hom.base x ∈ (U : Set C) := hOU hxh
        refine preimage_eq_of_mem ρ U hUcl hUconn (g * h⁻¹) ((ρ h).hom.base x) hhx ?_
        have e1 : (ρ (g * h⁻¹)).hom.base ((ρ h).hom.base x) = ((ρ h).hom ≫ (ρ (g * h⁻¹)).hom).base x := rfl
        rw [e1, ← Iso.trans_hom, ← Aut.Aut_mul_def, ← map_mul, inv_mul_cancel_right]
        exact hgx
      have hTeq : ∀ (g h : G), (ρ (g * h⁻¹)).hom ⁻¹ᵁ U = U → T g = T h := by
        intro g h hk
        show (ρ g).hom ⁻¹ᵁ O = (ρ h).hom ⁻¹ᵁ O
        conv_lhs => rw [← inv_mul_cancel_right g h, ← preimage_preimage_act ρ (g * h⁻¹) h O,
          preimage_O_eq ρ π hπ U V (g * h⁻¹) hk]
      have hsf : ∀ (g h : G) (hk : (ρ (g * h⁻¹)).hom ⁻¹ᵁ U = U) (e : T g ≤ (ρ h).hom ⁻¹ᵁ O),
          sf g = (ρ h).hom.appLE O (T g) e s := by
        intro g h hk e
        have eO : O ≤ (ρ (g * h⁻¹)).hom ⁻¹ᵁ O := by rw [preimage_O_eq ρ π hπ U V (g * h⁻¹) hk]
        have hcomp : (ρ h).hom ≫ (ρ (g * h⁻¹)).hom = (ρ g).hom := by
          rw [← Iso.trans_hom, ← Aut.Aut_mul_def, ← map_mul, inv_mul_cancel_right]
        conv_rhs => rw [← hs' (g * h⁻¹) hk eO]
        rw [appLE_appLE_apply (ρ (g * h⁻¹)).hom (ρ h).hom O O (T g) eO e
          (by rw [hcomp]) s]
        exact (appLE_congr_hom hcomp O (T g) _ le_rfl s).symm
      have hcompat : TopCat.Presheaf.IsCompatible C.sheaf.1 T sf := by
        intro g h
        by_cases hne : ((T g ⊓ T h : C.Opens) : Set C).Nonempty
        · obtain ⟨x, hxg, hxh⟩ := hne
          have hk := hmeet g h x hxg hxh
          have hgh : T g = T h := hTeq g h hk
          have e : T g ≤ (ρ h).hom ⁻¹ᵁ O := hgh.le
          show C.presheaf.map (homOfLE inf_le_left).op (sf g) = C.presheaf.map (homOfLE inf_le_right).op (sf h)
          rw [hsf g h hk e, map_appLE_apply, map_appLE_apply]
        · have hbot : (T g ⊓ T h : C.Opens) = ⊥ := by
            ext x; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
            exact fun hx => hne ⟨x, hx⟩
          haveI := CommRingCat.subsingleton_of_isTerminal (C.sheaf.isTerminalOfEqEmpty hbot)
          exact Subsingleton.elim _ _

      obtain ⟨S, hS, -⟩ := C.sheaf.existsUnique_gluing' T (π ⁻¹ᵁ V) (fun g => homOfLE (hT g)) hcover sf hcompat

      have hSinv : ∀ k : G, (ρ k).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ k]) S = S := by
        intro k
        apply C.sheaf.eq_of_locally_eq' T (π ⁻¹ᵁ V) (fun g => homOfLE (hT g)) hcover
        intro g
        have eTk : T g ≤ (ρ k).hom ⁻¹ᵁ (T (g * k⁻¹)) := by
          show (ρ g).hom ⁻¹ᵁ O ≤ (ρ k).hom ⁻¹ᵁ ((ρ (g * k⁻¹)).hom ⁻¹ᵁ O)
          rw [preimage_preimage_act ρ (g * k⁻¹) k O, inv_mul_cancel_right]
        have hcomp : (ρ k).hom ≫ (ρ (g * k⁻¹)).hom = (ρ g).hom := by
          rw [← Iso.trans_hom, ← Aut.Aut_mul_def, ← map_mul, inv_mul_cancel_right]
        show C.presheaf.map (homOfLE (hT g)).op ((ρ k).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) _ S) =
          C.presheaf.map (homOfLE (hT g)).op S
        rw [map_appLE_apply]
        have step : (ρ k).hom.appLE (π ⁻¹ᵁ V) (T g) ((hT g).trans (by rw [← Scheme.Hom.comp_preimage, hπ k])) S =
            (ρ k).hom.appLE (T (g * k⁻¹)) (T g) eTk (C.presheaf.map (homOfLE (hT (g * k⁻¹))).op S) := by
          rw [appLE_map_apply]
        rw [step]
        have hSg : C.presheaf.map (homOfLE (hT (g * k⁻¹))).op S = sf (g * k⁻¹) := hS (g * k⁻¹)
        rw [hSg]
        show (ρ k).hom.appLE (T (g * k⁻¹)) (T g) eTk ((ρ (g * k⁻¹)).hom.appLE O (T (g * k⁻¹)) le_rfl s) = _
        rw [appLE_appLE_apply (ρ (g * k⁻¹)).hom (ρ k).hom O (T (g * k⁻¹)) (T g) le_rfl eTk (by rw [hcomp]) s,
          appLE_congr_hom hcomp O (T g) _ le_rfl s]
        exact (hS g).symm

      have hSrange : S ∈ Set.range (π.app V) := by
        rw [hinv V]; exact hSinv
      obtain ⟨t, ht⟩ := hSrange
      refine ⟨t, ?_⟩

      have hT1 : O ≤ T 1 := by
        show O ≤ (ρ 1).hom ⁻¹ᵁ O
        rw [preimage_O_eq ρ π hπ U V 1 (by rw [map_one]; rfl)]
      have m3 : (U.ι ≫ π).app V t = C.presheaf.map (homOfLE hO).op (π.app V t) := rfl
      rw [m3, ht]
      have : C.presheaf.map (homOfLE hO).op S = C.presheaf.map (homOfLE hT1).op (C.presheaf.map (homOfLE (hT 1)).op S) := by
        rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
      rw [this]
      have hS1 : C.presheaf.map (homOfLE (hT 1)).op S = sf 1 := hS 1
      rw [hS1]
      show C.presheaf.map (homOfLE hT1).op ((ρ 1).hom.appLE O (T 1) le_rfl s) = s
      rw [map_appLE_apply]
      exact appLE_one_apply ρ O _ s

#print axioms solution

end S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected
end P2MW
export P2MW.S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected (solution)
