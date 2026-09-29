-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_opens_isClosed_preimage_eq_existsUnique_of_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e48fa541-0741-54be-b14c-f04e6a202a23

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_opens_isClosed_preimage_eq_existsUnique_of_quotient

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace QuotRestrict

variable {X : Scheme.{u}}

theorem mem_preimage_iff {Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens) (x : X) : x ∈ f ⁻¹ᵁ W ↔ f.base x ∈ W := Iff.rfl

def pair (A B : X.Opens) : Bool → X.Opens := fun b => bif b then A else B

theorem isOpenCover_pair (A B : X.Opens) (h : A ⊔ B = ⊤) : IsOpenCover (pair A B) := by
  show ⨆ b, pair A B b = ⊤
  rw [iSup_bool_eq]
  exact h

noncomputable def cover2 (A B : X.Opens) (h : A ⊔ B = ⊤) : X.OpenCover :=
  X.openCoverOfIsOpenCover (pair A B) (isOpenCover_pair A B h)

theorem isEmpty_pullback_ι (A B : X.Opens) (hd : A ⊓ B = ⊥) : IsEmpty ↑(pullback A.ι B.ι) := by
  refine ⟨fun p => ?_⟩
  have h1 : (pullback.fst A.ι B.ι ≫ A.ι).base p = (pullback.snd A.ι B.ι ≫ B.ι).base p := by
    rw [pullback.condition]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, Scheme.Opens.ι_apply] at h1
  have hA : ((pullback.fst A.ι B.ι).base p).1 ∈ A := ((pullback.fst A.ι B.ι).base p).2
  have hB : ((pullback.snd A.ι B.ι).base p).1 ∈ B := ((pullback.snd A.ι B.ι).base p).2
  rw [← h1] at hB
  have hmem : ((pullback.fst A.ι B.ι).base p).1 ∈ A ⊓ B := ⟨hA, hB⟩
  rw [hd] at hmem
  exact hmem

noncomputable def glue2 (A B : X.Opens) (h : A ⊔ B = ⊤) (hd : A ⊓ B = ⊥) {T : Scheme.{u}}
    (fa : (A : Scheme.{u}) ⟶ T) (fb : (B : Scheme.{u}) ⟶ T) : X ⟶ T :=
  (cover2 A B h).glueMorphisms (fun b => match b with | true => fa | false => fb) (by
    haveI := isEmpty_pullback_ι A B hd
    haveI := isEmpty_pullback_ι B A (by rw [inf_comm]; exact hd)
    rintro (_ | _) (_ | _)
    · show pullback.fst B.ι B.ι ≫ fb = pullback.snd B.ι B.ι ≫ fb
      rw [fst_eq_snd_of_mono_eq]
    · exact (isInitialOfIsEmpty (X := pullback B.ι A.ι)).hom_ext _ _
    · exact (isInitialOfIsEmpty (X := pullback A.ι B.ι)).hom_ext _ _
    · show pullback.fst A.ι A.ι ≫ fa = pullback.snd A.ι A.ι ≫ fa
      rw [fst_eq_snd_of_mono_eq])

theorem ι_glue2_left (A B : X.Opens) (h : A ⊔ B = ⊤) (hd : A ⊓ B = ⊥) {T : Scheme.{u}}
    (fa : (A : Scheme.{u}) ⟶ T) (fb : (B : Scheme.{u}) ⟶ T) : A.ι ≫ glue2 A B h hd fa fb = fa :=
  Scheme.Cover.ι_glueMorphisms (cover2 A B h) _ _ true

theorem ι_glue2_right (A B : X.Opens) (h : A ⊔ B = ⊤) (hd : A ⊓ B = ⊥) {T : Scheme.{u}}
    (fa : (A : Scheme.{u}) ⟶ T) (fb : (B : Scheme.{u}) ⟶ T) : B.ι ≫ glue2 A B h hd fa fb = fb :=
  Scheme.Cover.ι_glueMorphisms (cover2 A B h) _ _ false

theorem hom_ext2 (A B : X.Opens) (h : A ⊔ B = ⊤) {T : Scheme.{u}} (F G : X ⟶ T)
    (ha : A.ι ≫ F = A.ι ≫ G) (hb : B.ι ≫ F = B.ι ≫ G) : F = G :=
  Scheme.Cover.hom_ext (cover2 A B h) F G (by rintro (_ | _); exacts [hb, ha])

def complOpen (A : X.Opens) (hA : IsClosed (A : Set X)) : X.Opens := ⟨(A : Set X)ᶜ, hA.isOpen_compl⟩

theorem sup_complOpen (A : X.Opens) (hA : IsClosed (A : Set X)) : A ⊔ complOpen A hA = ⊤ :=
  Opens.ext (by simp [complOpen])

theorem inf_complOpen (A : X.Opens) (hA : IsClosed (A : Set X)) : A ⊓ complOpen A hA = ⊥ :=
  Opens.ext (by simp [complOpen])

theorem main
    {M X : Scheme.{u}} {H : Type} [Group H] [Finite H] (ρ : H →* Aut M) (π : M ⟶ X)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π) (hint : IsIntegralHom π) (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : M, π.base x = π.base x' ↔ ∃ h : H, (ρ h).hom.base x = x')
    (hcat : ∀ (T : Scheme.{u}) (f : M ⟶ T), (∀ h : H, (ρ h).hom ≫ f = f) → ∃! f' : X ⟶ T, π ≫ f' = f)
    (V : M.Opens) (hVcl : IsClosed (V : Set M)) (hV : ∀ h : H, (ρ h).hom ⁻¹ᵁ V = V) :
    ∃ (U : X.Opens) (hUV : π ⁻¹ᵁ U = V), IsClosed (U : Set X) ∧ Set.image π.base (V : Set M) = (U : Set X) ∧
      ∀ (T : Scheme.{u}) (f : (V : Scheme.{u}) ⟶ T),
        (∀ h : H, (ρ h).hom.resLE V V (by rw [hV h]) ≫ f = f) →
        ∃! f' : (U : Scheme.{u}) ⟶ T, π.resLE U V (by rw [hUV]) ≫ f' = f := by
  classical
  haveI := hint

  have hstab : ∀ (h : H) (m : M), (ρ h).hom.base m ∈ V ↔ m ∈ V := fun h m => by
    rw [← mem_preimage_iff, hV h]

  have hsat : ∀ m : M, π.base m ∈ π.base '' (V : Set M) → m ∈ V := by
    rintro m ⟨v, hv, hvm⟩
    obtain ⟨h, rfl⟩ := (horbit v m).mp hvm
    exact (hstab h v).mpr hv

  have hUcl : IsClosed (π.base '' (V : Set M)) := π.isClosedMap _ hVcl
  have hcompl : (π.base '' (V : Set M))ᶜ = π.base '' (V : Set M)ᶜ := by
    ext x
    constructor
    · intro hx
      obtain ⟨m, rfl⟩ := hsurj x
      exact ⟨m, fun hm => hx ⟨m, hm, rfl⟩, rfl⟩
    · rintro ⟨m, hm, rfl⟩ hx
      exact hm (hsat m hx)
  have hUop : IsOpen (π.base '' (V : Set M)) := by
    rw [← compl_compl (π.base '' (V : Set M)), hcompl]
    exact (π.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl
  let U : X.Opens := ⟨π.base '' (V : Set M), hUop⟩
  have hUV : π ⁻¹ᵁ U = V := by
    ext m
    exact ⟨fun hm => hsat m hm, fun hm => ⟨m, hm, rfl⟩⟩

  let Vc : M.Opens := complOpen V hVcl
  let Uc : X.Opens := complOpen U hUcl
  have hVc : ∀ h : H, (ρ h).hom ⁻¹ᵁ Vc = Vc := fun h => by
    ext m
    show (ρ h).hom.base m ∈ (V : Set M)ᶜ ↔ m ∈ (V : Set M)ᶜ
    rw [Set.mem_compl_iff, Set.mem_compl_iff, SetLike.mem_coe, SetLike.mem_coe, hstab]
  have hUcVc : π ⁻¹ᵁ Uc = Vc := by
    ext m
    show π.base m ∈ (π.base '' (V : Set M))ᶜ ↔ m ∈ (V : Set M)ᶜ
    rw [Set.mem_compl_iff, Set.mem_compl_iff, SetLike.mem_coe]
    exact ⟨fun hm hmV => hm ⟨m, hmV, rfl⟩, fun hm hx => hm (hsat m hx)⟩
  refine ⟨U, hUV, hUcl, rfl, ?_⟩
  intro T f hf

  let F : M ⟶ T ⨿ X := glue2 V Vc (sup_complOpen V hVcl) (inf_complOpen V hVcl)
    (f ≫ coprod.inl) (Vc.ι ≫ π ≫ coprod.inr)
  have hFV : V.ι ≫ F = f ≫ coprod.inl := ι_glue2_left _ _ _ _ _ _
  have hFVc : Vc.ι ≫ F = Vc.ι ≫ π ≫ coprod.inr := ι_glue2_right _ _ _ _ _ _
  have hFinv : ∀ h : H, (ρ h).hom ≫ F = F := by
    intro h
    apply hom_ext2 V Vc (sup_complOpen V hVcl)
    · rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι (ρ h).hom (show V ≤ (ρ h).hom ⁻¹ᵁ V by rw [hV h]),
        Category.assoc, hFV, ← Category.assoc, hf h]
    · rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι (ρ h).hom (show Vc ≤ (ρ h).hom ⁻¹ᵁ Vc by rw [hVc h]),
        Category.assoc, hFVc, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, ← Category.assoc (ρ h).hom, hπ h]
  obtain ⟨Fbar, hFbar, hFbar_uniq⟩ := hcat _ F hFinv

  have hrange : Set.range (U.ι ≫ Fbar).base ⊆ Set.range (coprod.inl : T ⟶ T ⨿ X).base := by
    rintro _ ⟨u, rfl⟩
    obtain ⟨v, hv, hvu⟩ := u.2
    refine ⟨f.base ⟨v, hv⟩, ?_⟩
    have e1 : (U.ι ≫ Fbar).base u = Fbar.base (π.base v) := by
      rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, ← hvu]
    have e2 : Fbar.base (π.base v) = F.base (V.ι.base ⟨v, hv⟩) := by
      rw [← Scheme.Hom.comp_apply, hFbar, Scheme.Opens.ι_apply]
    have e3 : F.base (V.ι.base ⟨v, hv⟩) = (coprod.inl : T ⟶ T ⨿ X).base (f.base ⟨v, hv⟩) := by
      rw [← Scheme.Hom.comp_apply, hFV, Scheme.Hom.comp_apply]
    rw [e1, e2, e3]
  let f' : (U : Scheme.{u}) ⟶ T := IsOpenImmersion.lift coprod.inl (U.ι ≫ Fbar) hrange
  have hf' : f' ≫ coprod.inl = U.ι ≫ Fbar := IsOpenImmersion.lift_fac _ _ _
  have hresV : π.resLE U V (by rw [hUV]) ≫ U.ι = V.ι ≫ π := Scheme.Hom.resLE_comp_ι _ _
  have hresVc : π.resLE Uc Vc (by rw [hUcVc]) ≫ Uc.ι = Vc.ι ≫ π := Scheme.Hom.resLE_comp_ι _ _
  refine ⟨f', ?_, ?_⟩
  ·
    show π.resLE U V (by rw [hUV]) ≫ f' = f
    rw [← cancel_mono (coprod.inl : T ⟶ T ⨿ X), Category.assoc, hf', ← Category.assoc, hresV, Category.assoc, hFbar, hFV]
  ·
    intro f'' hf''
    let Fbar'' : X ⟶ T ⨿ X := glue2 U Uc (sup_complOpen U hUcl) (inf_complOpen U hUcl)
      (f'' ≫ coprod.inl) (Uc.ι ≫ coprod.inr)
    have h1 : U.ι ≫ Fbar'' = f'' ≫ coprod.inl := ι_glue2_left _ _ _ _ _ _
    have h2 : Uc.ι ≫ Fbar'' = Uc.ι ≫ coprod.inr := ι_glue2_right _ _ _ _ _ _
    have hπF : π ≫ Fbar'' = F := by
      apply hom_ext2 V Vc (sup_complOpen V hVcl)
      · rw [← Category.assoc, ← hresV, Category.assoc, h1, ← Category.assoc, hf'', hFV]
      · rw [← Category.assoc, ← hresVc, Category.assoc, h2, ← Category.assoc, hresVc, Category.assoc, hFVc]
    have heq : Fbar'' = Fbar := hFbar_uniq Fbar'' hπF
    rw [← cancel_mono (coprod.inl : T ⟶ T ⨿ X), hf', ← heq, h1]

end QuotRestrict

theorem solution
    {M X : Scheme.{u}} {H : Type} [Group H] [Finite H] (ρ : H →* Aut M) (π : M ⟶ X)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π) (hint : IsIntegralHom π) (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : M, π.base x = π.base x' ↔ ∃ h : H, (ρ h).hom.base x = x')
    (hcat : ∀ (T : Scheme.{u}) (f : M ⟶ T), (∀ h : H, (ρ h).hom ≫ f = f) → ∃! f' : X ⟶ T, π ≫ f' = f)
    (V : M.Opens) (hVcl : IsClosed (V : Set M)) (hV : ∀ h : H, (ρ h).hom ⁻¹ᵁ V = V) :
    ∃ (U : X.Opens) (hUV : π ⁻¹ᵁ U = V), IsClosed (U : Set X) ∧ Set.image π.base (V : Set M) = (U : Set X) ∧
      ∀ (T : Scheme.{u}) (f : (V : Scheme.{u}) ⟶ T),
        (∀ h : H, (ρ h).hom.resLE V V (by rw [hV h]) ≫ f = f) →
        ∃! f' : (U : Scheme.{u}) ⟶ T, π.resLE U V (by rw [hUV]) ≫ f' = f :=
  QuotRestrict.main ρ π hπ hint hsurj horbit hcat V hVcl hV

end S_AlgebraicGeometry_Scheme_exists_opens_isClosed_preimage_eq_existsUnique_of_quotient
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_opens_isClosed_preimage_eq_existsUnique_of_quotient (solution)
