-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
-- name    : Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T19:13:31.022723+00:00
-- url     : https://prove2.me/theorems/8e3a7539-4133-4953-b1e7-f2e1e8983f95
-- title:
--   Is Domain And Is Integrally Closed Localization Of Is Inv
-- statement:
--   Definitions and structural lemmas for Is Domain And Is Integrally Closed Localization Of Is Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor


set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace GlobalTheory
section Ring
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {A : Type*} [CommRing A] [MulSemiringAction G A]
end Ring
section Ring
variable {G : Type*} [Group G] [Fintype G] {B B' A A' : Type*} [CommRing B] [CommRing B']
  [CommRing A] [CommRing A'] [Algebra B B'] [Algebra B A] [Algebra B A'] [Algebra B' A']
  [IsScalarTower B B' A'] [MulSemiringAction G A] [SMulCommClass G B A] [MulSemiringAction G A']
  [SMulCommClass G B' A'] [FaithfulSMul B A] [Algebra.IsInvariant B A G]
end Ring
section Ring
variable {G : Type*} [Group G] [Finite G] {A k : Type*} [CommRing A] [MulSemiringAction G A]
  [CommRing k] [IsDomain k]
end Ring
section Quotient
variable {G : Type v} [Group G] {X Y Z : Scheme.{u}}
structure IsAffineQuotient (ρ : G →* Aut X) (π : X ⟶ Y) : Prop where

  comp_eq : ∀ g, (ρ g).hom ≫ π = π

  isAffineHom : IsAffineHom π

  app_injective : ∀ W : Y.Opens, Function.Injective (π.app W)

  mem_range_app : ∀ (W : Y.Opens) (s : Γ(X, π ⁻¹ᵁ W)), IsInvariantSection ρ _ s →
    s ∈ Set.range (π.app W)
theorem isAffineQuotient_spec [Finite G] (B A : Type u) [CommRing B] [CommRing A]
    [MulSemiringAction G A] [Algebra B A] [SMulCommClass G B A] [FaithfulSMul B A]
    [Algebra.IsInvariant B A G] :
    IsAffineQuotient (specAction G A) (Spec.map (CommRingCat.ofHom (algebraMap B A))) :=
  have := isSchemeTheoreticallyDominant_spec_algebraMap B A
  ⟨specAction_comp G B A, inferInstance, Scheme.Hom.app_injective _,
    mem_range_spec_app_of_isInvariant G B A⟩
example (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    IsAffineQuotient (specAction Gal(L/K) L) (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  isAffineQuotient_spec K L
theorem epi_of_surjective_of_app_injective (π : X ⟶ Y) [Surjective π]
    (h : ∀ W, Function.Injective (π.app W)) : Epi π := ⟨fun {Z} a b hab ↦ by
  have hb : a.base = b.base := by
    ext y
    obtain ⟨x, rfl⟩ := π.surjective y
    exact congr($hab x)
  refine Scheme.Hom.ext hb fun U ↦ ?_
  have : Mono (π.app (b ⁻¹ᵁ U)) := ConcreteCategory.mono_of_injective _ (h _)
  rw [← cancel_mono (π.app _)]
  simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE, hab]⟩
theorem isSchemeTheoreticallyDominant_of_cover (π : X ⟶ Y) [QuasiCompact π]
    (h : ∀ y : Y, ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W ∧ Function.Injective (π.app W)) :
    IsSchemeTheoreticallyDominant π := by
  choose W hW hy hi using h
  refine ⟨Scheme.IdealSheafData.ext_of_iSup_eq_top (fun y ↦ ⟨W y, hW y⟩)
    (top_le_iff.mp fun y _ ↦ Opens.mem_iSup.mpr ⟨y, hy y⟩) fun y ↦ ?_⟩
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
    ← RingHom.injective_iff_ker_eq_bot]
  exact hi y
namespace IsAffineQuotient
variable {ρ : G →* Aut X} {π : X ⟶ Y}
variable (h : IsAffineQuotient ρ π)
include h
theorem preimage_le (W : Y.Opens) (g : G) : π ⁻¹ᵁ W ≤ (ρ g).hom ⁻¹ᵁ π ⁻¹ᵁ W :=
  preimage_le_of_invariant ρ π h.comp_eq W g
theorem isSchemeTheoreticallyDominant : IsSchemeTheoreticallyDominant π :=
  have := h.isAffineHom
  isSchemeTheoreticallyDominant_of_cover π fun y ↦ by
    obtain ⟨_, ⟨W, hW, rfl⟩, hy, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact ⟨W, hW, hy, h.app_injective W⟩
theorem isInvariant (W : Y.Opens) :
    letI := sectionsAction ρ _ (h.preimage_le W)
    letI := (π.app W).hom.toAlgebra
    SMulCommClass G Γ(Y, W) Γ(X, π ⁻¹ᵁ W) ∧ FaithfulSMul Γ(Y, W) Γ(X, π ⁻¹ᵁ W) ∧
      Algebra.IsInvariant Γ(Y, W) Γ(X, π ⁻¹ᵁ W) G := by
  let := sectionsAction ρ _ (h.preimage_le W)
  let := (π.app W).hom.toAlgebra
  have hfix (g : G) (a : Γ(Y, W)) : g • algebraMap Γ(Y, W) Γ(X, π ⁻¹ᵁ W) a = algebraMap _ _ a :=
    (isInvariantSection_app ρ π h.comp_eq W a g⁻¹).2
  refine ⟨⟨fun g a s ↦ by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩,
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (h.app_injective W), ⟨fun s hs ↦
      h.mem_range_app W s fun g ↦ ⟨h.preimage_le W g, ?_⟩⟩⟩
  simpa only [inv_inv] using
    (show (ρ g⁻¹⁻¹).hom.appLE _ _ (h.preimage_le W _) s = s from hs g⁻¹)
variable [Finite G]
theorem isIntegralHom : IsIntegralHom π where
  toIsAffineHom := h.isAffineHom
  isIntegral_app W _ := by
    let := sectionsAction ρ _ (h.preimage_le W)
    let := (π.app W).hom.toAlgebra
    obtain ⟨_, _, _⟩ := h.isInvariant W
    exact (Algebra.IsInvariant.isIntegral Γ(Y, W) Γ(X, π ⁻¹ᵁ W) G).isIntegral
theorem surjective : Surjective π :=
  have := h.isIntegralHom
  have := h.isSchemeTheoreticallyDominant
  inferInstance
theorem apply_eq_iff (x y : X) : π x = π y ↔ ∃ g, (ρ g).hom x = y :=
  have := h.isAffineHom
  apply_eq_iff_exists_aut_of_invariant ρ π h.comp_eq (fun W _ ↦ h.mem_range_app W) x y
theorem isQuotientMap : Topology.IsQuotientMap π :=
  have := h.isIntegralHom
  have := h.surjective
  π.isClosedMap.isQuotientMap π.continuous π.surjective
theorem epi : Epi π :=
  have := h.surjective
  epi_of_surjective_of_app_injective π h.app_injective
theorem exists_comp_eq (f : X ⟶ Z) (hf : ∀ g, (ρ g).hom ≫ f = f) : ∃ f' : Y ⟶ Z, π ≫ f' = f := by
  have := h.surjective
  let π₀ : C(X, Y) := π.base.hom
  have hq : Topology.IsQuotientMap π₀ := h.isQuotientMap
  have hfac : Function.FactorsThrough f.base.hom π₀ := fun x y e ↦ by
    obtain ⟨g, rfl⟩ := (h.apply_eq_iff _ _).mp e
    exact congr($(hf g) x).symm
  let φ : C(Y, Z) := hq.lift f.base.hom hfac
  have hφ (x : X) : φ (π x) = f x := congr($(hq.lift_comp f.base.hom hfac) x)
  let φ' : Y.toPresheafedSpace.carrier ⟶ Z.toPresheafedSpace.carrier := TopCat.ofHom φ
  let V (W : Z.Opens) : Y.Opens := (Opens.map φ').obj W
  have e (W : Z.Opens) : π ⁻¹ᵁ V W ≤ f ⁻¹ᵁ W := fun x hx ↦ by
    change f x ∈ W
    rw [← hφ]; exact hx
  have hex (W : Z.Opens) (s : Γ(Z, W)) : ∃ t, π.app (V W) t = f.appLE W _ (e W) s :=
    h.mem_range_app _ _ fun g ↦ ⟨h.preimage_le _ g, by
      simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, hf]⟩
  choose c hc using hex
  let c' (W : Z.Opens) : Γ(Z, W) ⟶ Γ(Y, V W) := CommRingCat.ofHom
    { toFun := c W
      map_one' := h.app_injective _ (by rw [hc, map_one, map_one])
      map_mul' a b := h.app_injective _ (by rw [map_mul, hc, hc, hc, map_mul])
      map_zero' := h.app_injective _ (by rw [hc, map_zero, map_zero])
      map_add' a b := h.app_injective _ (by rw [map_add, hc, hc, hc, map_add]) }
  have hc' (W : Z.Opens) : c' W ≫ π.app (V W) = f.appLE W _ (e W) := by
    ext s; exact hc W s
  let m : Y.toPresheafedSpace.Hom Z.toPresheafedSpace :=
    { base := φ'
      c :=
        { app W := c' W.unop
          naturality W W' i := by
            have : Mono (π.app (V W'.unop)) :=
              ConcreteCategory.mono_of_injective _ (h.app_injective _)
            change Z.presheaf.map i ≫ c' W'.unop =
              c' W.unop ≫ Y.presheaf.map ((Opens.map φ').map i.unop).op
            rw [← cancel_mono (π.app (V W'.unop)), Category.assoc, Category.assoc, hc',
              π.naturality, reassoc_of% hc', Scheme.Hom.map_appLE, Scheme.Hom.appLE_map] } }
  let f' : Y ⟶ Z := ⟨m, fun y ↦ ⟨fun a ha ↦ by
    obtain ⟨W, hW, s, rfl⟩ := Z.presheaf.germ_exist a
    erw [PresheafedSpace.stalkMap_germ_apply] at ha
    obtain ⟨x, rfl⟩ := π.surjective y
    have h₁ : π x ∈ Y.basicOpen (c W s) := (Y.mem_basicOpen (c W s) (π x) hW).mpr ha
    have h₂ : x ∈ X.basicOpen (π.app (V W) (c W s)) := by
      rw [← Scheme.preimage_basicOpen]; exact h₁
    rw [hc, Scheme.basicOpen_appLE] at h₂
    have h₃ : φ (π x) ∈ Z.basicOpen s := by rw [hφ]; exact h₂.2
    exact (Z.mem_basicOpen s _ hW).mp h₃⟩⟩
  refine ⟨f', Scheme.Hom.ext (by ext x; exact hφ x) fun W ↦ ?_⟩
  change (c' W ≫ π.app (V W)) ≫ _ = _
  rw [hc']
  exact (f.appLE_map _ _).trans f.appLE_eq_app
noncomputable def desc (f : X ⟶ Z) (hf : ∀ g, (ρ g).hom ≫ f = f) : Y ⟶ Z :=
  (h.exists_comp_eq f hf).choose
@[reassoc (attr := simp)]
theorem comp_desc (f : X ⟶ Z) (hf : ∀ g, (ρ g).hom ≫ f = f) : π ≫ h.desc f hf = f :=
  (h.exists_comp_eq f hf).choose_spec
theorem hom_ext {a b : Y ⟶ Z} (e : π ≫ a = π ≫ b) : a = b :=
  have := h.epi
  (cancel_epi π).mp e
noncomputable def uniqueIso {Y' : Scheme.{u}} {π' : X ⟶ Y'} (h' : IsAffineQuotient ρ π') :
    Y ≅ Y' where
  hom := h.desc π' h'.comp_eq
  inv := h'.desc π h.comp_eq
  hom_inv_id := h.hom_ext (by simp)
  inv_hom_id := h'.hom_ext (by simp)
@[reassoc (attr := simp)]
theorem comp_uniqueIso_hom {Y' : Scheme.{u}} {π' : X ⟶ Y'} (h' : IsAffineQuotient ρ π') :
    π ≫ (h.uniqueIso h').hom = π' :=
  h.comp_desc _ h'.comp_eq
@[reassoc (attr := simp)]
theorem comp_uniqueIso_inv {Y' : Scheme.{u}} {π' : X ⟶ Y'} (h' : IsAffineQuotient ρ π') :
    π' ≫ (h.uniqueIso h').inv = π :=
  h'.comp_desc _ h.comp_eq
section Base
variable {S : Scheme.{u}} (q : Y ⟶ S)
end Base
end IsAffineQuotient
end Quotient
section Free
variable {G : Type v} [Group G] {X Y : Scheme.{u}}
def IsFreeAction (ρ : G →* Aut X) : Prop :=
  ∀ (k : Type u) [Field k] (x : Spec (.of k) ⟶ X) (g : G), x ≫ (ρ g).hom = x → g = 1
namespace IsAffineQuotient
variable [Finite G] {ρ : G →* Aut X} {π : X ⟶ Y} (h : IsAffineQuotient ρ π) (hρ : IsFreeAction ρ)
include h hρ
end IsAffineQuotient
end Free
section BaseChange
variable {G : Type v} [Group G] {X Y X' Y' S S' : Scheme.{u}}
attribute [local simp] pullback.map pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
namespace IsAffineQuotient
variable {ρ : G →* Aut X} {π : X ⟶ Y} (h : IsAffineQuotient ρ π)
  {ρ' : G →* Aut X'} {π' : X' ⟶ Y'} {p : X' ⟶ X} {t : Y' ⟶ Y} (H : IsPullback p π' π t)
  (hp : ∀ g, (ρ' g).hom ≫ p = p ≫ (ρ g).hom) (hπ' : ∀ g, (ρ' g).hom ≫ π' = π')
include h H hp hπ'
variable [Finite G]
end IsAffineQuotient
noncomputable def pullbackAction (ρ : G →* Aut X) (f : X ⟶ S) (hf : ∀ g, (ρ g).hom ≫ f = f)
    (t : S' ⟶ S) : G →* Aut (pullback f t) :=
  MonoidHom.mk' (fun g ↦
    { hom := pullback.map f t f t (ρ g).hom (𝟙 _) (𝟙 _) (by simp [hf]) (by simp)
      inv := pullback.map f t f t (ρ g).inv (𝟙 _) (𝟙 _)
        ((Category.comp_id _).trans ((Iso.eq_inv_comp (ρ g)).mpr (hf g))) (by simp)
      hom_inv_id := by apply pullback.hom_ext <;> simp [(ρ g).hom_inv_id]
      inv_hom_id := by apply pullback.hom_ext <;> simp [(ρ g).inv_hom_id] }) fun g k ↦ by
    refine Iso.ext ?_
    change _ = pullback.map f t f t (ρ k).hom (𝟙 _) (𝟙 _) (by simp [hf]) (by simp) ≫
      pullback.map f t f t (ρ g).hom (𝟙 _) (𝟙 _) (by simp [hf]) (by simp)
    have e : (ρ (g * k)).hom = (ρ k).hom ≫ (ρ g).hom := by rw [map_mul]; rfl
    apply pullback.hom_ext <;> simp [-map_mul, e]
variable (ρ : G →* Aut X) (f : X ⟶ S) (hf : ∀ g, (ρ g).hom ≫ f = f) (t : S' ⟶ S)
variable {ρ f} [Finite G] {π : X ⟶ Y} (h : IsAffineQuotient ρ π) (q : Y ⟶ S) (hq : π ≫ q = f)
include h
end BaseChange
namespace IsAffineQuotient
variable {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} {ρ : G →* Aut X} {π : X ⟶ Y}
  (h : IsAffineQuotient ρ π) {k : Type u} [Field k]
include h
end IsAffineQuotient
end GlobalTheory


