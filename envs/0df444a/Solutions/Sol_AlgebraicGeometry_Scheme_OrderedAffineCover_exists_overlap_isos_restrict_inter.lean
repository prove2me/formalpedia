-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.OrderedAffineCover.exists_overlap_isos_restrict_inter
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/2d8b07cd-3481-54f7-a8e0-1b02cd93461d

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_Algebra_PointDerivations
import Theorems.Thm_AlgebraicGeometry_IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_overlap_isos_restrict_inter

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

noncomputable section

namespace RestrictTriples

section Generic

variable {Y₁ Y₂ : Scheme.{u}} {V₁ Z₁ : Y₁.Opens} {V₂ Z₂ : Y₂.Opens} (h₁ : Z₁ ≤ V₁) (h₂ : Z₂ ≤ V₂)
  (φ : (↑V₁ : Scheme.{u}) ≅ ↑V₂) (hpre : φ.hom ⁻¹ᵁ (V₂.ι ⁻¹ᵁ Z₂) = V₁.ι ⁻¹ᵁ Z₁)

include hpre in
theorem range_homOfLE_comp_eq : Set.range (Y₁.homOfLE h₁ ≫ φ.hom) = Set.range (Y₂.homOfLE h₂) := by
  have e₂ : Set.range (Y₂.homOfLE h₂) = ((V₂.ι ⁻¹ᵁ Z₂ : (↑V₂ : Scheme.{u}).Opens) : Set (↑V₂ : Scheme.{u})) := by
    rw [← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE]
  have e₁ : Set.range (Y₁.homOfLE h₁) = ((V₁.ι ⁻¹ᵁ Z₁ : (↑V₁ : Scheme.{u}).Opens) : Set (↑V₁ : Scheme.{u})) := by
    rw [← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE]
  rw [e₂, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, e₁]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ φ.hom ⁻¹ᵁ (V₂.ι ⁻¹ᵁ Z₂) := by rw [hpre]; exact hx
    exact hx'
  · intro hy
    refine ⟨φ.inv.base y, ?_, ?_⟩
    · change φ.inv.base y ∈ V₁.ι ⁻¹ᵁ Z₁
      rw [← hpre]
      change φ.hom.base (φ.inv.base y) ∈ V₂.ι ⁻¹ᵁ Z₂
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      exact hy
    · rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl

def resIso : (↑Z₁ : Scheme.{u}) ≅ ↑Z₂ :=
  IsOpenImmersion.isoOfRangeEq (Y₁.homOfLE h₁ ≫ φ.hom) (Y₂.homOfLE h₂) (range_homOfLE_comp_eq h₁ h₂ φ hpre)

theorem resIso_hom_homOfLE : (resIso h₁ h₂ φ hpre).hom ≫ Y₂.homOfLE h₂ = Y₁.homOfLE h₁ ≫ φ.hom :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

omit hpre in

theorem res_over {S : Scheme.{u}} (q₁ : Y₁ ⟶ S) (q₂ : Y₂ ⟶ S) (hφq : φ.hom ≫ V₂.ι ≫ q₂ = V₁.ι ≫ q₁)
    (ρ : (↑Z₁ : Scheme.{u}) ≅ ↑Z₂) (hρ : ρ.hom ≫ Y₂.homOfLE h₂ = Y₁.homOfLE h₁ ≫ φ.hom) :
    ρ.hom ≫ Z₂.ι ≫ q₂ = Z₁.ι ≫ q₁ := by
  rw [← Scheme.homOfLE_ι Y₂ h₂, Category.assoc, reassoc_of% hρ, hφq, Scheme.homOfLE_ι_assoc]

theorem isoSpec_inv_ι_comp {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) {D : X.Opens}
    (hD : IsAffineOpen D) :
    letI := algebraOfHom c D
    hD.isoSpec.inv ≫ D.ι ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, D))) := by
  change hD.fromSpec ≫ c = Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ D le_top).hom)
  rw [CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact (IsAffineOpen.SpecMap_appLE_fromSpec c (isAffineOpen_top _) hD le_top).symm

end Generic

section Frame

variable {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
  (hker : IsNilpotent (RingHom.ker π))
  {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T))
  (𝒰 : A₀.OrderedAffineCover)
  (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T'))
  (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
  (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))
  (O : ∀ a, A₀.Opens → (Y a).Opens)
  (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
  (hOm : ∀ a, Monotone (O a))
  (φ : ∀ (a b : 𝒰.ι), a < b → ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
  (hφq : ∀ (a b : 𝒰.ι) (h : a < b),
    (φ a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a)
  (hφg : ∀ (a b : 𝒰.ι) (h : a < b),
    ∃ (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
      (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
      γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
      γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
      γ ≫ (φ a b h).hom = γ')
  (hφO : ∀ (a b : 𝒰.ι) (h : a < b) (W : A₀.Opens),
    (φ a b h).hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W)

def ρ (x y : 𝒰.ι) (hxy : x < y) (W : A₀.Opens) (hW : W ≤ 𝒰.U x ⊓ 𝒰.U y) : (↑(O x W) : Scheme.{u}) ≅ ↑(O y W) :=
  resIso (hOm x hW) (hOm y hW) (φ x y hxy) (hφO x y hxy W)

theorem ρ_homOfLE (x y : 𝒰.ι) (hxy : x < y) (W : A₀.Opens) (hW : W ≤ 𝒰.U x ⊓ 𝒰.U y) :
    (ρ 𝒰 Y O hOm φ hφO x y hxy W hW).hom ≫ (Y y).homOfLE (hOm y hW) = (Y x).homOfLE (hOm x hW) ≫ (φ x y hxy).hom :=
  resIso_hom_homOfLE _ _ _ _

include hφq in
theorem ρ_over (x y : 𝒰.ι) (hxy : x < y) (W : A₀.Opens) (hW : W ≤ 𝒰.U x ⊓ 𝒰.U y) :
    (ρ 𝒰 Y O hOm φ hφO x y hxy W hW).hom ≫ (O y W).ι ≫ q y = (O x W).ι ≫ q x :=
  res_over _ _ (φ x y hxy) (q x) (q y) (hφq x y hxy) _ (ρ_homOfLE 𝒰 Y O hOm φ hφO x y hxy W hW)

include hφg in

theorem transport (x y : 𝒰.ι) (hxy : x < y) (W : A₀.Opens) (hW : W ≤ 𝒰.U x ⊓ 𝒰.U y) {E : Scheme.{u}}
    (m : E ⟶ ↑(O x W)) (θ : E ⟶ ↑(𝒰.U x ⊓ 𝒰.U y)) (hm : m ≫ (O x W).ι = θ ≫ A₀.homOfLE inf_le_left ≫ g x) :
    m ≫ (ρ 𝒰 Y O hOm φ hφO x y hxy W hW).hom ≫ (O y W).ι = θ ≫ A₀.homOfLE inf_le_right ≫ g y := by
  obtain ⟨γ, γ', hγ, hγ', hγφ⟩ := hφg x y hxy
  have h1 : m ≫ (Y x).homOfLE (hOm x hW) = θ ≫ γ := by
    rw [← cancel_mono (O x (𝒰.U x ⊓ 𝒰.U y)).ι, Category.assoc, Scheme.homOfLE_ι, hm, Category.assoc, hγ]
  rw [← Scheme.homOfLE_ι (Y y) (hOm y hW), ← Category.assoc (ρ 𝒰 Y O hOm φ hφO x y hxy W hW).hom, ρ_homOfLE,
    Category.assoc, reassoc_of% h1, reassoc_of% hγφ, hγ']

include hO in

theorem exists_θ (a x y : 𝒰.ι) (W : A₀.Opens) (hW : W ≤ 𝒰.U x ⊓ 𝒰.U y) :
    ∃ θ : (↑(g a ⁻¹ᵁ O a W) : Scheme.{u}) ⟶ ↑(𝒰.U x ⊓ 𝒰.U y),
      θ ≫ (𝒰.U x ⊓ 𝒰.U y).ι = (g a ⁻¹ᵁ O a W).ι ≫ (𝒰.U a).ι := by
  have hrange : Set.range ((g a ⁻¹ᵁ O a W).ι ≫ (𝒰.U a).ι) ⊆ Set.range (𝒰.U x ⊓ 𝒰.U y).ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hp : (g a ⁻¹ᵁ O a W).ι p ∈ (g a ⁻¹ᵁ O a W) := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
      exact ⟨p, rfl⟩
    have hp' : (g a ⁻¹ᵁ O a W).ι p ∈ (𝒰.U a).ι ⁻¹ᵁ W := by rw [← hO a W]; exact hp
    rw [Scheme.Hom.comp_apply]
    exact hW hp'
  exact ⟨IsOpenImmersion.lift _ _ hrange, IsOpenImmersion.lift_fac _ _ hrange⟩

include hπ hker hg hO hφg in

theorem agree_mod (a b c : 𝒰.ι) (hab : a < b) (hbc : b < c) (hac : a < c) (W : A₀.Opens)
    (hWab : W ≤ 𝒰.U a ⊓ 𝒰.U b) (hWbc : W ≤ 𝒰.U b ⊓ 𝒰.U c) (hWac : W ≤ 𝒰.U a ⊓ 𝒰.U c) (hD : IsAffineOpen (O a W)) :
    letI := algebraOfHom (q a) (O a W)
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Y a, O a W))))) ≫
        hD.isoSpec.inv ≫ (ρ 𝒰 Y O hOm φ hφO a c hac W hWac).hom ≫ (O c W).ι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Y a, O a W))))) ≫
        hD.isoSpec.inv ≫ (ρ 𝒰 Y O hOm φ hφO a b hab W hWab).hom ≫ (ρ 𝒰 Y O hOm φ hφO b c hbc W hWbc).hom ≫ (O c W).ι := by
  obtain ⟨-, ε, hε⟩ := AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq π hπ hker (q a)
    ((𝒰.U a).ι ≫ f₀) (g a) (hg a) (O a W) hD
  have hεinv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map
      (algebraOfHom (q a) (O a W)).algebraMap))) ≫ hD.isoSpec.inv = ε.hom ≫ (g a ∣_ O a W) := by
    rw [← hε, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraOfHom (q a) (O a W)).algebraMap))) ≫ _ =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraOfHom (q a) (O a W)).algebraMap))) ≫ _
  rw [reassoc_of% hεinv, reassoc_of% hεinv]
  congr 1

  obtain ⟨θac, hθac⟩ := exists_θ 𝒰 Y g O hO a a c W hWac
  obtain ⟨θab, hθab⟩ := exists_θ 𝒰 Y g O hO a a b W hWab
  obtain ⟨θbc, hθbc⟩ := exists_θ 𝒰 Y g O hO a b c W hWbc

  have hA : ∀ (y : 𝒰.ι) (hW : W ≤ 𝒰.U a ⊓ 𝒰.U y) (θ : (↑(g a ⁻¹ᵁ O a W) : Scheme.{u}) ⟶ ↑(𝒰.U a ⊓ 𝒰.U y)),
      θ ≫ (𝒰.U a ⊓ 𝒰.U y).ι = (g a ⁻¹ᵁ O a W).ι ≫ (𝒰.U a).ι →
      (g a ∣_ O a W) ≫ (O a W).ι = θ ≫ A₀.homOfLE inf_le_left ≫ g a := by
    intro y hW θ hθ
    have h : θ ≫ A₀.homOfLE inf_le_left = (g a ⁻¹ᵁ O a W).ι := by
      rw [← cancel_mono (𝒰.U a).ι, Category.assoc, Scheme.homOfLE_ι, hθ]
    rw [morphismRestrict_ι, reassoc_of% h]

  have h1 := transport 𝒰 Y g O hOm φ hφg hφO a c hac W hWac (g a ∣_ O a W) θac (hA c hWac θac hθac)

  have h2 := transport 𝒰 Y g O hOm φ hφg hφO a b hab W hWab (g a ∣_ O a W) θab (hA b hWab θab hθab)
  have hre : θab ≫ A₀.homOfLE inf_le_right = θbc ≫ A₀.homOfLE inf_le_left := by
    rw [← cancel_mono (𝒰.U b).ι, Category.assoc, Scheme.homOfLE_ι, hθab, Category.assoc, Scheme.homOfLE_ι, hθbc]
  rw [reassoc_of% hre, ← Category.assoc] at h2
  have h3 := transport 𝒰 Y g O hOm φ hφg hφO b c hbc W hWbc ((g a ∣_ O a W) ≫ (ρ 𝒰 Y O hOm φ hφO a b hab W hWab).hom) θbc h2
  have hre' : θac ≫ A₀.homOfLE inf_le_right = θbc ≫ A₀.homOfLE inf_le_right := by
    rw [← cancel_mono (𝒰.U c).ι, Category.assoc, Scheme.homOfLE_ι, hθac, Category.assoc, Scheme.homOfLE_ι, hθbc]
  rw [Category.assoc] at h3
  rw [h1, h3, reassoc_of% hre']

end Frame

end RestrictTriples

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover RestrictTriples in

theorem solution
    (T' T : Type u) [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀]
    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))

    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOtop : ∀ a, O a (𝒰.U a) = ⊤)
    (hOinf : ∀ (a : 𝒰.ι) (W W' : A₀.Opens), O a W ⊓ O a W' ≤ O a (W ⊓ W'))
    (hOaff : ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W))
    (φ : ∀ (a b : 𝒰.ι), a < b → ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
    (hφq : ∀ (a b : 𝒰.ι) (h : a < b),
      (φ a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a)
    (hφg : ∀ (a b : 𝒰.ι) (h : a < b),
      ∃ (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
        (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
        γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
        γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
        γ ≫ (φ a b h).hom = γ')
    (hφO : ∀ (a b : 𝒰.ι) (h : a < b) (W : A₀.Opens),
      (φ a b h).hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W)
    :
    ∃ (ρab : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 1) (𝒰.inter r))))
      (ρbc : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 1) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
      (ρac : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
      (hρab : ∀ r : 𝒰.Idx 2,
        (ρab r).hom ≫ (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) =
          (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) ≫
            (φ (r.1 0) (r.1 1) (r.2 (by decide))).hom)
      (hρbc : ∀ r : 𝒰.Idx 2,
        (ρbc r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) =
          (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) ≫
            (φ (r.1 1) (r.1 2) (r.2 (by decide))).hom)
      (hρac : ∀ r : 𝒰.Idx 2,
        (ρac r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) =
          (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) ≫
            (φ (r.1 0) (r.1 2) (r.2 (by decide))).hom),
      (∀ r : 𝒰.Idx 2,
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
          (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι) ≫ q (r.1 2) =
        Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))) ∧
      ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
          (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι) ≫ q (r.1 2) =
        Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))))) ∧
      (∀ r : 𝒰.Idx 2,
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))))) ≫
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
            (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))))) ≫
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
            (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)) := by
  have h01 : ∀ r : 𝒰.Idx 2, r.1 0 < r.1 1 := fun r => r.2 (by decide)
  have h12 : ∀ r : 𝒰.Idx 2, r.1 1 < r.1 2 := fun r => r.2 (by decide)
  have h02 : ∀ r : 𝒰.Idx 2, r.1 0 < r.1 2 := fun r => r.2 (by decide)
  refine ⟨fun r => ρ 𝒰 Y O hOm φ hφO (r.1 0) (r.1 1) (h01 r) (𝒰.inter r) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1)),
    fun r => ρ 𝒰 Y O hOm φ hφO (r.1 1) (r.1 2) (h12 r) (𝒰.inter r) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2)),
    fun r => ρ 𝒰 Y O hOm φ hφO (r.1 0) (r.1 2) (h02 r) (𝒰.inter r) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2)),
    fun r => ρ_homOfLE 𝒰 Y O hOm φ hφO _ _ _ _ _, fun r => ρ_homOfLE 𝒰 Y O hOm φ hφO _ _ _ _ _,
    fun r => ρ_homOfLE 𝒰 Y O hOm φ hφO _ _ _ _ _, fun r => ⟨?_, ?_⟩, fun r => ?_⟩
  · rw [Category.assoc, Category.assoc, ρ_over 𝒰 Y q O hOm φ hφq hφO]
    exact isoSpec_inv_ι_comp (q (r.1 0)) _
  · rw [Category.assoc, Category.assoc, Category.assoc, ρ_over 𝒰 Y q O hOm φ hφq hφO, ρ_over 𝒰 Y q O hOm φ hφq hφO]
    exact isoSpec_inv_ι_comp (q (r.1 0)) _
  · exact agree_mod π hπ hker f₀ 𝒰 Y q g hg O hO hOm φ hφg hφO (r.1 0) (r.1 1) (r.1 2) (h01 r) (h12 r) (h02 r) (𝒰.inter r)
      _ _ _ _

end S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_overlap_isos_restrict_inter
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_overlap_isos_restrict_inter (solution)
