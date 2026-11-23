-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasChartsOfForallIsAffineOpen
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasChartsOfForallIsAffineOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:30.21396+00:00
-- url     : https://prove2.me/theorems/def8d7f8-4704-4538-b8d2-d2505cca7ddf
-- title:
--   Has Charts Of Forall Is Affine Open
-- statement:
--   Definitions and structural lemmas for Has Charts Of Forall Is Affine Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasChartsOfForallIsAffineOpen.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp)
namespace GlobalTheory.NatFun
variable {k : Type} [CommRing k]
section Points
scoped instance sectionsAlgebra (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) :
    Algebra k Γ(X.left, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appLE ⊤ U le_top).hom.toAlgebra
theorem algebraMap_sections (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) :
    algebraMap k Γ(X.left, U) =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appLE ⊤ U le_top).hom := rfl
theorem algebraMap_sections_top (X : Over (Spec (CommRingCat.of k))) :
    algebraMap k Γ(X.left, ⊤) =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop).hom := by
  rw [algebraMap_sections, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl
def pull {X Y : Over (Spec (CommRingCat.of k))} (m : Y ⟶ X) : Γ(X.left, ⊤) →ₐ[k] Γ(Y.left, ⊤) where
  __ := m.left.appTop.hom
  commutes' c := by
    rw [algebraMap_sections_top, algebraMap_sections_top, ← Over.w m, Scheme.Hom.comp_appTop]
    rfl
variable {X : Over (Spec (CommRingCat.of k))}
variable {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [CommRing C] [Algebra k C]
def value (x : sp A ⟶ X) : Γ(X.left, ⊤) →ₐ[k] A where
  __ := (x.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom
  commutes' c := by
    have h : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop ≫ x.left.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom = CommRingCat.ofHom (algebraMap k A) := by
      rw [← Scheme.Hom.comp_appTop_assoc, Over.w x]
      change _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap k A))).appTop ≫ _ = _
      rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    rw [algebraMap_sections_top]
    exact congr(($h).hom c)
theorem value_comp {Y : Over (Spec (CommRingCat.of k))} (y : sp A ⟶ Y) (m : Y ⟶ X)
    (s : Γ(X.left, ⊤)) : value (y ≫ m) s = value y (pull m s) := rfl
theorem value_spMap (φ : A →ₐ[k] B) (x : sp A ⟶ X) (s : Γ(X.left, ⊤)) :
    value (spMap φ ≫ x) s = φ (value x s) :=
  congr(($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ.toRingHom))).hom (x.left.appTop s))
theorem spMap_injective : Function.Injective (spMap : (A →ₐ[k] B) → (sp B ⟶ sp A)) := by
  intro φ ψ h
  have h1 : (spMap φ).left = (spMap ψ).left := by rw [h]
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective h1))
theorem spMap_surjective : Function.Surjective (spMap : (A →ₐ[k] B) → (sp B ⟶ sp A)) := by
  intro m
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (R := CommRingCat.of A) (S := CommRingCat.of B) m.left
  have h : CommRingCat.ofHom (algebraMap k A) ≫ φ = CommRingCat.ofHom (algebraMap k B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ]
    exact Over.w m
  exact ⟨⟨φ.hom, fun c => congr(($h).hom c)⟩, Over.OverMorphism.ext hφ⟩
def spEquiv : (A →ₐ[k] B) ≃ (sp (R₀ := k) B ⟶ sp A) :=
  Equiv.ofBijective spMap ⟨spMap_injective, spMap_surjective⟩
def spSections (A : Type) [CommRing A] [Algebra k A] : Γ((sp (R₀ := k) A).left, ⊤) ≃ₐ[k] A :=
  AlgEquiv.ofBijective (value (𝟙 (sp A)))
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.bijective
theorem value_spMap_eq (φ : A →ₐ[k] B) (s : Γ((sp (R₀ := k) A).left, ⊤)) :
    value (spMap φ) s = φ (spSections A s) := by
  rw [← Category.comp_id (spMap φ), value_spMap]
  rfl
def affinePoint {U : X.left.Opens} (hU : IsAffineOpen U) : sp Γ(X.left, U) ⟶ X :=
  Over.homMk hU.fromSpec (by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom
      (isAffineOpen_top (Spec (CommRingCat.of k))) hU (le_top : U ≤ X.hom ⁻¹ᵁ ⊤)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    change hU.fromSpec ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X.left, U)))
    rw [← h, algebraMap_sections, CommRingCat.ofHom_hom, Spec.map_comp])
abbrev toAway (r : A) : A →ₐ[k] Localization.Away r :=
  IsScalarTower.toAlgHom k A (Localization.Away r)
theorem eq_of_forall_prime {a b : A}
    (h : ∀ p : PrimeSpectrum A, ∃ r ∉ p.asIdeal,
      algebraMap A (Localization.Away r) a = algebraMap A (Localization.Away r) b) : a = b := by
  by_contra hne
  have hI : LinearMap.ker (LinearMap.toSpanSingleton A A (a - b)) ≠ ⊤ := fun e => hne (by
    have h1 : (1 : A) ∈ LinearMap.ker (LinearMap.toSpanSingleton A A (a - b)) := e ▸ trivial
    simpa [sub_eq_zero] using h1)
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨r, hr, e⟩ := h ⟨P, hP.isPrime⟩
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers r) _).mp e
  refine hr (hP.isPrime.mem_of_pow_mem n (hle ?_))
  simpa [mul_sub, sub_eq_zero] using hn
theorem exists_away_factor (x : sp A ⟶ X) (v : sp B ⟶ X) [IsOpenImmersion v.left]
    (p : PrimeSpectrum A) (hp : x.left p ∈ Set.range v.left) :
    ∃ r ∉ p.asIdeal, ∃ ψ : B →ₐ[k] Localization.Away r,
      spMap (toAway r) ≫ x = spMap ψ ≫ v := by
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hr, hle⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open (a := p)
      (u := (x.left ⁻¹ᵁ v.left.opensRange).1) hp
      (x.left ⁻¹ᵁ v.left.opensRange).2
  have hsub : Set.range (spMap (toAway (k := k) r) ≫ x).left ⊆ Set.range v.left := by
    rintro _ ⟨q, rfl⟩
    refine hle (a := PrimeSpectrum.comap (algebraMap A (Localization.Away r)) q) ?_
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact ⟨q, rfl⟩
  have hl := IsOpenImmersion.lift_fac v.left _ hsub
  obtain ⟨ψ, hψ⟩ := spMap_surjective (k := k) (A := B) (B := Localization.Away r)
    (Over.homMk (IsOpenImmersion.lift v.left _ hsub) (by
      rw [← Over.w v, ← Category.assoc, hl, Over.w]))
  refine ⟨r, hr, ψ, Over.OverMorphism.ext ?_⟩
  rw [hψ]
  exact hl.symm
end Points
section Families
abbrev AlgClass (k : Type) [CommRing k] : Type 1 :=
  ∀ (A : Type) [CommRing A] [Algebra k A], Prop
abbrev AlgClass.noCondition (k : Type) [CommRing k] : AlgClass k := fun _ _ _ => True
def AlgClass.StableAway (𝒯 : AlgClass k) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra k A] (a : A), 𝒯 A → 𝒯 (Localization.Away a)
def HasCharts (𝒯 : AlgClass k) (X : Over (Spec (CommRingCat.of k))) : Prop :=
  ∀ p : X.left, ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (u : sp A ⟶ X),
    𝒯 A ∧ IsOpenImmersion u.left ∧ p ∈ Set.range u.left
variable {𝒯 𝒯' : AlgClass k} {X : Over (Spec (CommRingCat.of k))}
theorem HasCharts.exists_bundled (h : HasCharts 𝒯 X) (p : X.left) :
    ∃ (A : CommAlgCat.{0} k) (u : sp A ⟶ X),
      𝒯 A ∧ IsOpenImmersion u.left ∧ p ∈ Set.range u.left := by
  obtain ⟨A, _, _, u, hu⟩ := h p
  exact ⟨CommAlgCat.of k A, u, hu⟩
theorem ext_of_charts (hX : HasCharts 𝒯 X) {s t : Γ(X.left, ⊤)}
    (h : ∀ (A : Type) [CommRing A] [Algebra k A], 𝒯 A → ∀ u : sp A ⟶ X, IsOpenImmersion u.left →
      value u s = value u t) : s = t := by
  choose A u hA hu hp using hX.exists_bundled
  let 𝒰 : X.left.OpenCover := Scheme.Cover.mkOfCovers X.left
    (fun p => Spec (CommRingCat.of (A p))) (fun p => (u p).left) (fun p => ⟨p, hp p⟩) hu
  exact 𝒰.ext_elem s t fun p =>
    (Scheme.ΓSpecIso (CommRingCat.of (A p))).commRingCatIsoToRingEquiv.injective
      (h (A p) (hA p) (u p) (hu p))
theorem ext_of_values (hX : HasCharts 𝒯 X) {s t : Γ(X.left, ⊤)}
    (h : ∀ (A : Type) [CommRing A] [Algebra k A], 𝒯 A → ∀ x : sp A ⟶ X,
      value x s = value x t) : s = t :=
  ext_of_charts hX fun A _ _ hA u _ => h A hA u
variable (𝒯 X) in

def natSubalgebra : Subalgebra k
    (∀ A : {A : CommAlgCat.{0} k // 𝒯 A}, (sp A.1 ⟶ X) → A.1) where
  carrier := {f | ∀ (A B : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (hA : 𝒯 A) (hB : 𝒯 B) (φ : A →ₐ[k] B) (x : sp A ⟶ X),
      f ⟨CommAlgCat.of k B, hB⟩ (spMap φ ≫ x) = φ (f ⟨CommAlgCat.of k A, hA⟩ x)}
  mul_mem' {f g} hf hg A B _ _ _ _ hA hB φ x := by
    simp only [Pi.mul_apply, map_mul, hf A B hA hB φ x, hg A B hA hB φ x]
  add_mem' {f g} hf hg A B _ _ _ _ hA hB φ x := by
    simp only [Pi.add_apply, map_add, hf A B hA hB φ x, hg A B hA hB φ x]
  algebraMap_mem' c A B _ _ _ _ hA hB φ x := (φ.commutes c).symm
variable (𝒯 X) in

def NatFamily : Type 1 := natSubalgebra 𝒯 X
instance : CommRing (NatFamily 𝒯 X) := inferInstanceAs (CommRing (natSubalgebra 𝒯 X))
instance : Algebra k (NatFamily 𝒯 X) := inferInstanceAs (Algebra k (natSubalgebra 𝒯 X))
def NatFamily.app (f : NatFamily 𝒯 X) (A : Type) [CommRing A] [Algebra k A] (hA : 𝒯 A)
    (x : sp A ⟶ X) : A :=
  f.1 ⟨CommAlgCat.of k A, hA⟩ x
def NatFamily.mk (f : ∀ (A : Type) [CommRing A] [Algebra k A], 𝒯 A → (sp A ⟶ X) → A)
    (hf : ∀ (A B : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
      (hA : 𝒯 A) (hB : 𝒯 B) (φ : A →ₐ[k] B) (x : sp A ⟶ X),
      f B hB (spMap φ ≫ x) = φ (f A hA x)) : NatFamily 𝒯 X :=
  ⟨fun A x => f A.1 A.2 x, hf⟩
section
variable (A : Type) [CommRing A] [Algebra k A] (hA : 𝒯 A) (x : sp A ⟶ X)
@[simp] theorem NatFamily.mk_app (f : ∀ (A : Type) [CommRing A] [Algebra k A],
    𝒯 A → (sp A ⟶ X) → A) (hf) : (NatFamily.mk f hf).app A hA x = f A hA x := rfl
@[simp] theorem NatFamily.add_app (f g : NatFamily 𝒯 X) :
    (f + g).app A hA x = f.app A hA x + g.app A hA x := rfl
@[simp] theorem NatFamily.mul_app (f g : NatFamily 𝒯 X) :
    (f * g).app A hA x = f.app A hA x * g.app A hA x := rfl
@[simp] theorem NatFamily.zero_app : (0 : NatFamily 𝒯 X).app A hA x = 0 := rfl
@[simp] theorem NatFamily.one_app : (1 : NatFamily 𝒯 X).app A hA x = 1 := rfl
@[simp] theorem NatFamily.smul_app (c : k) (f : NatFamily 𝒯 X) :
    (c • f).app A hA x = c • f.app A hA x := rfl
end
theorem NatFamily.natural (f : NatFamily 𝒯 X) {A B : Type} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (hA : 𝒯 A) (hB : 𝒯 B) (φ : A →ₐ[k] B) (x : sp A ⟶ X) :
    f.app B hB (spMap φ ≫ x) = φ (f.app A hA x) :=
  f.2 A B hA hB φ x
theorem NatFamily.ext {f g : NatFamily 𝒯 X}
    (h : ∀ (A : Type) [CommRing A] [Algebra k A] (hA : 𝒯 A) (x : sp A ⟶ X),
      f.app A hA x = g.app A hA x) : f = g := by
  apply Subtype.ext
  funext A x
  exact h A.1 A.2 x
variable (𝒯 X) in

def toFamily : Γ(X.left, ⊤) →ₐ[k] NatFamily 𝒯 X where
  toFun s := NatFamily.mk (fun _ _ _ _ x => value x s) fun _ _ _ _ _ _ _ _ φ x => value_spMap φ x s
  map_one' := NatFamily.ext fun _ _ _ _ x => map_one (value x)
  map_mul' s t := NatFamily.ext fun _ _ _ _ x => map_mul (value x) s t
  map_zero' := NatFamily.ext fun _ _ _ _ x => map_zero (value x)
  map_add' s t := NatFamily.ext fun _ _ _ _ x => map_add (value x) s t
  commutes' c := NatFamily.ext fun _ _ _ _ x => (value x).commutes c
@[simp] theorem toFamily_apply (s : Γ(X.left, ⊤)) (A : Type) [CommRing A] [Algebra k A]
    (hA : 𝒯 A) (x : sp A ⟶ X) : (toFamily 𝒯 X s).app A hA x = value x s := rfl
theorem toFamily_injective (hX : HasCharts 𝒯 X) : Function.Injective (toFamily 𝒯 X) :=
  fun _ _ h => ext_of_values hX fun A _ _ hA x => congr(($h).app A hA x)
theorem NatFamily.compatible (h𝒯 : 𝒯.StableAway) (f : NatFamily 𝒯 X) {A B C : Type} [CommRing A]
    [Algebra k A] [CommRing B] [Algebra k B] [CommRing C] [Algebra k C] (hA : 𝒯 A) (hB : 𝒯 B)
    (u : sp A ⟶ X) (v : sp B ⟶ X) [IsOpenImmersion v.left] (α : A →ₐ[k] C) (β : B →ₐ[k] C)
    (h : spMap α ≫ u = spMap β ≫ v) : α (f.app A hA u) = β (f.app B hB v) := by
  refine eq_of_forall_prime fun q => ?_
  obtain ⟨g, hg, ψ, hψ⟩ := exists_away_factor u v (PrimeSpectrum.comap α.toRingHom q)
    ⟨(spMap β).left q, congr(($h).left q).symm⟩
  refine ⟨α g, hg, ?_⟩
  let α' : Localization.Away g →ₐ[k] Localization.Away (α g) :=
    IsLocalization.Away.mapₐ _ _ α g
  have hα' : α'.comp (toAway g) = (toAway (α g)).comp α := by
    ext a
    simp [α', IsLocalization.Away.mapₐ, IsLocalization.Away.map]
  have : Mono v := Over.mono_of_mono_left v
  have e : α'.comp ψ = (toAway (α g)).comp β := by
    apply spMap_injective
    rw [← cancel_mono v, ← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc, ← hψ, ← h,
      ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, hα']
  have h1 := f.natural hA (h𝒯 A g hA) (toAway g) u
  rw [hψ, f.natural hB (h𝒯 A g hA) ψ v] at h1
  have h2 := congr($hα' (f.app A hA u))
  have h3 := congr($e (f.app B hB v))
  simp only [AlgHom.comp_apply] at h2 h3
  exact h2.symm.trans ((congrArg α' h1.symm).trans h3)
set_option backward.isDefEq.respectTransparency false in

theorem NatFamily.compatible_left (h𝒯 : 𝒯.StableAway) (f : NatFamily 𝒯 X) {A B : Type}
    [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (hA : 𝒯 A) (hB : 𝒯 B)
    (u : sp A ⟶ X) (v : sp B ⟶ X) [IsOpenImmersion v.left] (C : CommRingCat.{0})
    (a : Spec C ⟶ (sp (R₀ := k) A).left) (b : Spec C ⟶ (sp (R₀ := k) B).left)
    (hab : a ≫ u.left = b ≫ v.left) :
    a ≫ (spMap (Polynomial.aeval (R := k) (f.app A hA u))).left =
      b ≫ (spMap (Polynomial.aeval (R := k) (f.app B hB v))).left := by
  obtain ⟨c, hc⟩ := Spec.map_surjective (R := CommRingCat.of k) (S := C) (a ≫ u.left ≫ X.hom)
  let _ : Algebra k C := c.hom.toAlgebra
  have hc' : (sp (R₀ := k) C).hom = a ≫ u.left ≫ X.hom := hc
  obtain ⟨α, hα⟩ := spMap_surjective (k := k) (A := A) (B := C)
    (Over.homMk a (by rw [← Over.w u, hc']))
  obtain ⟨β, hβ⟩ := spMap_surjective (k := k) (A := B) (B := C)
    (Over.homMk b (by rw [← Over.w v, hc', ← Category.assoc, ← hab, Category.assoc]))
  have hα' : (spMap α).left = a := by rw [hα]; rfl
  have hβ' : (spMap β).left = b := by rw [hβ]; rfl
  have h : spMap α ≫ u = spMap β ≫ v := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, hα', hβ', hab]
  have e : α.comp (Polynomial.aeval (f.app A hA u)) = β.comp (Polynomial.aeval (f.app B hB v)) := by
    apply Polynomial.algHom_ext
    simpa using f.compatible h𝒯 hA hB u v α β h
  rw [← hα', ← hβ', ← Over.comp_left, ← Over.comp_left, spMap_comp, spMap_comp, e]
set_option backward.isDefEq.respectTransparency false in
theorem toFamily_surjective (h𝒯 : 𝒯.StableAway) (hX : HasCharts 𝒯 X) :
    Function.Surjective (toFamily 𝒯 X) := by
  intro f
  choose A u hA hu hp using hX.exists_bundled
  let 𝒰 : X.left.OpenCover := Scheme.Cover.mkOfCovers X.left
    (fun p => Spec (CommRingCat.of (A p))) (fun p => (u p).left) (fun p => ⟨p, hp p⟩) hu
  let ev (p : X.left) : Polynomial k →ₐ[k] A p := Polynomial.aeval (f.app (A p) (hA p) (u p))
  have hglue : ∀ p q : X.left, pullback.fst (u p).left (u q).left ≫ (spMap (ev p)).left =
      pullback.snd (u p).left (u q).left ≫ (spMap (ev q)).left := by
    intro p q
    refine Scheme.Cover.hom_ext (pullback (u p).left (u q).left).affineOpenCover.openCover _ _
      fun i => ?_
    let C := (pullback (u p).left (u q).left).affineOpenCover.X i
    let w : Spec C ⟶ pullback (u p).left (u q).left :=
      (pullback (u p).left (u q).left).affineOpenCover.f i
    have := f.compatible_left h𝒯 (hA p) (hA q) (u p) (u q) C (w ≫ pullback.fst _ _)
      (w ≫ pullback.snd _ _) (by rw [Category.assoc, Category.assoc, pullback.condition])
    rw [Category.assoc, Category.assoc] at this
    exact this
  let F : X.left ⟶ Spec (CommRingCat.of (Polynomial k)) :=
    𝒰.glueMorphisms (fun p => (spMap (ev p)).left) hglue
  have hF : ∀ p, (u p).left ≫ F = (spMap (ev p)).left := fun p =>
    Scheme.Cover.ι_glueMorphisms 𝒰 _ hglue p
  let F' : X ⟶ sp (Polynomial k) := Over.homMk F (by
    refine Scheme.Cover.hom_ext 𝒰 _ _ fun p => ?_
    change (u p).left ≫ _ = (u p).left ≫ _
    rw [← Category.assoc, hF, Over.w, Over.w])
  have hF' : ∀ p, u p ≫ F' = spMap (ev p) := fun p => Over.OverMorphism.ext (hF p)
  let s : Γ(X.left, ⊤) := pull F' ((spSections (Polynomial k)).symm Polynomial.X)
  have hs : ∀ p, value (u p) s = f.app (A p) (hA p) (u p) := fun p => by
    rw [← value_comp, hF', value_spMap_eq, AlgEquiv.apply_symm_apply, Polynomial.aeval_X]
  refine ⟨s, NatFamily.ext fun R _ _ hR x => eq_of_forall_prime fun q => ?_⟩
  obtain ⟨r, hr, ψ, hψ⟩ := exists_away_factor x (u (x.left q)) q (hp _)
  refine ⟨r, hr, ?_⟩
  have h1 := value_spMap (toAway r) x s
  have h2 := f.natural hR (h𝒯 R r hR) (toAway r) x
  rw [hψ] at h1 h2
  rw [value_spMap, hs] at h1
  rw [f.natural (hA _) (h𝒯 R r hR)] at h2
  exact h1.symm.trans h2
def familyEquiv (h𝒯 : 𝒯.StableAway) (hX : HasCharts 𝒯 X) : Γ(X.left, ⊤) ≃ₐ[k] NatFamily 𝒯 X :=
  AlgEquiv.ofBijective (toFamily 𝒯 X) ⟨toFamily_injective hX, toFamily_surjective h𝒯 hX⟩
end Families
end GlobalTheory.NatFun


