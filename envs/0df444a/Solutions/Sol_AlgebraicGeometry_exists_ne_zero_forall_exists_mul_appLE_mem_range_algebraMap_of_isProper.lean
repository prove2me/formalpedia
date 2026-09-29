-- Prove2me | solution 1 for AlgebraicGeometry.exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8439a412-b14d-5c8e-b77a-0c056d4155bb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper

set_option autoImplicit false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper.AlgebraicGeometry Filter"

universe u v

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.basicOpen_res Surjective Spec.map_inj isAffineOpen_opensRange Spec.map_comp_assoc IsProper Scheme.Hom Scheme.Hom.appLE_comp_appLE IsAffineOpen.fromSpec_top IsProper.eq_valuativeCriterion basicOpen_eq_of_affine' ValuativeCommSq QuasiCompact Scheme.preimage_basicOpen IsAffineOpen.SpecMap_appLE_fromSpec IsAffineOpen.fromSpec_preimage_self Spec Spec.map Scheme QuasiCompact.compactSpace_of_compactSpace Scheme.isoSpec_Spec_inv Scheme.Hom.preimage_mono isAffineOpen_top Spec.map_id IsAffineOpen ValuativeCriterion.Existence ValuativeCriterion Scheme.ΓSpecIso_naturality Scheme.Hom.appLE Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app"
namespace ProperBounded
p2m_open "AlgebraicGeometry"

section Eval

variable {X : Scheme.{u}}

def evalHom {L : Type u} [CommRing L] (a : Spec (CommRingCat.of L) ⟶ X) (V : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ V) :
    Γ(X, V) →+* L :=
  (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.comp (a.appLE V ⊤ h).hom

theorem ofHom_evalHom {L : Type u} [CommRing L] (a : Spec (CommRingCat.of L) ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ a ⁻¹ᵁ V) :
    CommRingCat.ofHom (evalHom a V h) = a.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom :=
  rfl

theorem evalHom_apply {L : Type u} [CommRing L] (a : Spec (CommRingCat.of L) ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ a ⁻¹ᵁ V) (g : Γ(X, V)) :
    evalHom a V h g = (Scheme.ΓSpecIso (CommRingCat.of L)).hom (a.appLE V ⊤ h g) :=
  rfl

theorem evalHom_map {L : Type u} [CommRing L] (a : Spec (CommRingCat.of L) ⟶ X) {V V' : X.Opens}
    (h : ⊤ ≤ a ⁻¹ᵁ V) (h' : ⊤ ≤ a ⁻¹ᵁ V') (i : V' ≤ V) (g : Γ(X, V)) :
    evalHom a V' h' (X.presheaf.map (homOfLE i).op g) = evalHom a V h g := by
  change (Scheme.ΓSpecIso (CommRingCat.of L)).hom ((X.presheaf.map (homOfLE i).op ≫ a.appLE V' ⊤ h') g) = _
  rw [Scheme.Hom.map_appLE]
  rfl

theorem evalHom_specMap_comp {L L' : Type u} [CommRing L] [CommRing L'] (φ : L →+* L')
    (b : Spec (CommRingCat.of L) ⟶ X) (V : X.Opens) (hb : ⊤ ≤ b ⁻¹ᵁ V)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ b) ⁻¹ᵁ V) :
    evalHom (Spec.map (CommRingCat.ofHom φ) ≫ b) V h = φ.comp (evalHom b V hb) := by
  have h1 : b.appLE V ⊤ hb ≫ (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top =
      (Spec.map (CommRingCat.ofHom φ) ≫ b).appLE V ⊤ h :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have h2 : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top = (Spec.map (CommRingCat.ofHom φ)).appTop :=
    Scheme.Hom.appLE_eq_app _
  have h3 : CommRingCat.ofHom (evalHom (Spec.map (CommRingCat.ofHom φ) ≫ b) V h) =
      CommRingCat.ofHom (φ.comp (evalHom b V hb)) := by
    rw [ofHom_evalHom, ← h1, h2, Category.assoc, Scheme.ΓSpecIso_naturality, CommRingCat.ofHom_comp,
      ofHom_evalHom, Category.assoc]
  exact congrArg CommRingCat.Hom.hom h3

theorem top_le_preimage_iff {L : Type u} [Field L] (a : Spec (CommRingCat.of L) ⟶ X) (V : X.Opens) :
    ⊤ ≤ a ⁻¹ᵁ V ↔ a.base default ∈ V := by
  constructor
  · intro h; exact h (Set.mem_univ (default : ↥(Spec (CommRingCat.of L))))
  · rintro h x -
    rw [Subsingleton.elim x default]
    exact h

theorem primeSpectrum_basicOpen_eq_top_iff {L : Type u} [Field L] (r : L) :
    PrimeSpectrum.basicOpen r = ⊤ ↔ r ≠ 0 := by
  constructor
  · intro h
    have hm : (default : PrimeSpectrum L) ∈ PrimeSpectrum.basicOpen r := by rw [h]; trivial
    rw [PrimeSpectrum.mem_basicOpen] at hm
    intro hr
    exact hm (hr ▸ Ideal.zero_mem _)
  · intro hr
    refine le_antisymm le_top ?_
    rw [← PrimeSpectrum.basicOpen_one, ← mul_inv_cancel₀ hr, PrimeSpectrum.basicOpen_mul]
    exact inf_le_left

theorem top_le_preimage_basicOpen_iff {L : Type u} [Field L] (a : Spec (CommRingCat.of L) ⟶ X) {V : X.Opens}
    (h : ⊤ ≤ a ⁻¹ᵁ V) (e : Γ(X, V)) :
    ⊤ ≤ a ⁻¹ᵁ X.basicOpen e ↔ evalHom a V h e ≠ 0 := by
  have h1 : (Spec (CommRingCat.of L)).basicOpen (a.appLE V ⊤ h e) = a ⁻¹ᵁ X.basicOpen e := by
    rw [Scheme.preimage_basicOpen, Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res]
    exact top_inf_eq _
  rw [← h1, basicOpen_eq_of_affine', top_le_iff]
  exact primeSpectrum_basicOpen_eq_top_iff _

theorem exists_eval_mul_pow_eq {V V' : X.Opens} (hV : IsAffineOpen V) (e : Γ(X, V)) (he : X.basicOpen e ≤ V')
    (g : Γ(X, V')) :
    ∃ (p : Γ(X, V)) (n : ℕ), ∀ {L : Type u} [Field L] (a : Spec (CommRingCat.of L) ⟶ X)
      (h : ⊤ ≤ a ⁻¹ᵁ V), evalHom a V h e ≠ 0 →
      ∃ h' : ⊤ ≤ a ⁻¹ᵁ V', evalHom a V' h' g * (evalHom a V h e) ^ n = evalHom a V h p := by
  have := hV.isLocalization_basicOpen e
  obtain ⟨⟨p, ⟨_, n, rfl⟩⟩, hp⟩ :=
    IsLocalization.surj (Submonoid.powers e) (X.presheaf.map (homOfLE he).op g)
  refine ⟨p, n, fun {L} _ a h hne => ?_⟩
  have hD : ⊤ ≤ a ⁻¹ᵁ X.basicOpen e := (top_le_preimage_basicOpen_iff a h e).mpr hne
  refine ⟨hD.trans (Scheme.Hom.preimage_mono a he), ?_⟩
  have hp' := congrArg (evalHom a (X.basicOpen e) hD) hp
  rw [map_mul, evalHom_map a _ hD he] at hp'
  change _ * evalHom a (X.basicOpen e) hD (X.presheaf.map (homOfLE (X.basicOpen_le e)).op (e ^ n)) =
    evalHom a (X.basicOpen e) hD (X.presheaf.map (homOfLE (X.basicOpen_le e)).op p) at hp'
  rwa [evalHom_map a h hD, evalHom_map a h hD, map_pow] at hp'

theorem evalHom_congr {L : Type u} [CommRing L] {a b : Spec (CommRingCat.of L) ⟶ X} (hab : a = b) (V : X.Opens)
    (ha : ⊤ ≤ a ⁻¹ᵁ V) (hb : ⊤ ≤ b ⁻¹ᵁ V) : evalHom a V ha = evalHom b V hb := by
  subst hab; rfl

theorem eq_specMap_evalHom_comp_fromSpec {L : Type u} [CommRing L] (a : Spec (CommRingCat.of L) ⟶ X)
    {V : X.Opens} (hV : IsAffineOpen V) (h : ⊤ ≤ a ⁻¹ᵁ V) :
    a = Spec.map (CommRingCat.ofHom (evalHom a V h)) ≫ hV.fromSpec := by
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec a hV (isAffineOpen_top (Spec (CommRingCat.of L))) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h1
  rw [ofHom_evalHom, Spec.map_comp, Category.assoc, h1, ← Spec.map_comp_assoc, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

theorem evalHom_specMap_comp_fromSpec {L : Type u} [CommRing L] {V : X.Opens} (hV : IsAffineOpen V)
    (Φ : Γ(X, V) →+* L) (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom Φ) ≫ hV.fromSpec) ⁻¹ᵁ V) :
    evalHom (Spec.map (CommRingCat.ofHom Φ) ≫ hV.fromSpec) V h = Φ := by
  have h1 := eq_specMap_evalHom_comp_fromSpec (Spec.map (CommRingCat.ofHom Φ) ≫ hV.fromSpec) hV h
  rw [cancel_mono, Spec.map_inj] at h1
  exact (congrArg CommRingCat.Hom.hom h1).symm

theorem top_le_preimage_of_mem {L : Type u} [CommRing L] [IsLocalRing L] (a : Spec (CommRingCat.of L) ⟶ X)
    {V : X.Opens} (h : a.base (IsLocalRing.closedPoint L) ∈ V) : ⊤ ≤ a ⁻¹ᵁ V := by
  rintro x -
  change a.base x ∈ V
  exact ((IsLocalRing.specializes_closedPoint x).map a.base.hom.continuous).mem_open V.2 h

variable {K : Type u} [Field K] (f : X ⟶ Spec (CommRingCat.of K))

private def _root_.AlgebraicGeometry.ProperBounded.algK (V : X.Opens) : K →+* Γ(X, V) :=
  (f.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

p2m_export "AlgebraicGeometry.ProperBounded" "algK"
theorem ofHom_algK (V : X.Opens) :
    CommRingCat.ofHom (algK f V) = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ V le_top :=
  rfl

theorem fromSpec_comp_eq {V : X.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algK f V)) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (CommRingCat.of K))) hV
    (le_top : V ≤ f ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  rw [← h, ofHom_algK]

theorem evalHom_comp_algK {L : Type u} [CommRing L] (φ : K →+* L) (a : Spec (CommRingCat.of L) ⟶ X)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom φ)) (V : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ V) :
    (evalHom a V h).comp (algK f V) = φ := by
  have h1 : f.appLE ⊤ V le_top ≫ a.appLE V ⊤ h = (Spec.map (CommRingCat.ofHom φ)).appTop := by
    rw [Scheme.Hom.appLE_comp_appLE, ← ha]
    exact Scheme.Hom.appLE_eq_app _
  have h2 : CommRingCat.ofHom ((evalHom a V h).comp (algK f V)) = CommRingCat.ofHom φ := by
    rw [CommRingCat.ofHom_comp, ofHom_evalHom, ofHom_algK, Category.assoc,
      reassoc_of% h1, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congrArg CommRingCat.Hom.hom h2

end Eval

section Ultra

variable {J : Type u} (L : J → Type u) [∀ j, Field (L j)] (𝔘 : Ultrafilter J)

def nullIdeal : Ideal (Π j, L j) where
  carrier := {x | ∀ᶠ j in 𝔘, x j = 0}
  add_mem' {x y} hx hy := by
    filter_upwards [hx, hy] with j hxj hyj
    simp [hxj, hyj]
  zero_mem' := by simp
  smul_mem' r {x} hx := by
    filter_upwards [hx] with j hxj
    simp [hxj]

def UProd : Type u := (Π j, L j) ⧸ nullIdeal L 𝔘

scoped instance : CommRing (UProd L 𝔘) := inferInstanceAs (CommRing ((Π j, L j) ⧸ nullIdeal L 𝔘))

def cls : (Π j, L j) →+* UProd L 𝔘 := Ideal.Quotient.mk (nullIdeal L 𝔘)

variable {L 𝔘}

theorem cls_surjective : Function.Surjective (cls L 𝔘) := Ideal.Quotient.mk_surjective

theorem cls_eq_cls_iff {x y : Π j, L j} : cls L 𝔘 x = cls L 𝔘 y ↔ ∀ᶠ j in 𝔘, x j = y j := by
  change Ideal.Quotient.mk _ x = Ideal.Quotient.mk _ y ↔ _
  rw [Ideal.Quotient.eq]
  change (∀ᶠ j in 𝔘, (x - y) j = 0) ↔ _
  simp only [Pi.sub_apply, sub_eq_zero]

theorem cls_eq_zero_iff {x : Π j, L j} : cls L 𝔘 x = 0 ↔ ∀ᶠ j in 𝔘, x j = 0 := by
  rw [← map_zero (cls L 𝔘), cls_eq_cls_iff]; rfl

theorem cls_ne_zero_iff {x : Π j, L j} : cls L 𝔘 x ≠ 0 ↔ ∀ᶠ j in 𝔘, x j ≠ 0 := by
  rw [Ne, cls_eq_zero_iff, Ultrafilter.eventually_not]

variable (L 𝔘) in
theorem isField_uProd : IsField (UProd L 𝔘) where
  exists_pair_ne := ⟨0, 1, fun h => by
    have h' : cls L 𝔘 0 = cls L 𝔘 1 := by simpa using h
    rw [cls_eq_cls_iff] at h'
    obtain ⟨j, hj⟩ := h'.exists
    exact zero_ne_one hj⟩
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := by
    obtain ⟨x, rfl⟩ := cls_surjective x
    refine ⟨cls L 𝔘 (fun j => (x j)⁻¹), ?_⟩
    rw [← map_mul, ← map_one (cls L 𝔘), cls_eq_cls_iff]
    filter_upwards [cls_ne_zero_iff.mp hx] with j hj
    simp [hj]

scoped instance : Field (UProd L 𝔘) := (isField_uProd L 𝔘).toField

theorem cls_inv (x : Π j, L j) : cls L 𝔘 (fun j => (x j)⁻¹) = (cls L 𝔘 x)⁻¹ := by
  by_cases hx : cls L 𝔘 x = 0
  · rw [hx, inv_zero, cls_eq_zero_iff]
    filter_upwards [cls_eq_zero_iff.mp hx] with j hj
    simp [hj]
  · symm
    apply inv_eq_of_mul_eq_one_right
    rw [← map_mul, ← map_one (cls L 𝔘), cls_eq_cls_iff]
    filter_upwards [cls_ne_zero_iff.mp hx] with j hj
    simp [hj]

def uSubring (S : ∀ j, Subring (L j)) : Subring (UProd L 𝔘) :=
  Subring.map (cls L 𝔘)
    { carrier := {x | ∀ᶠ j in 𝔘, x j ∈ S j}
      mul_mem' := fun {x y} hx hy => by filter_upwards [hx, hy] with j hxj hyj; exact mul_mem hxj hyj
      one_mem' := by simp
      add_mem' := fun {x y} hx hy => by filter_upwards [hx, hy] with j hxj hyj; exact add_mem hxj hyj
      zero_mem' := by simp
      neg_mem' := fun {x} hx => by filter_upwards [hx] with j hxj; exact neg_mem hxj }

theorem cls_mem_uSubring_iff {S : ∀ j, Subring (L j)} {x : Π j, L j} :
    cls L 𝔘 x ∈ uSubring S ↔ ∀ᶠ j in 𝔘, x j ∈ S j := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    filter_upwards [hy, cls_eq_cls_iff.mp hxy] with j hyj hxyj
    rwa [← hxyj]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem mem_uSubring_or_inv_mem (S : ∀ j, ValuationSubring (L j)) (x : UProd L 𝔘) :
    x ∈ uSubring (fun j => (S j).toSubring) ∨ x⁻¹ ∈ uSubring (fun j => (S j).toSubring) := by
  obtain ⟨x, rfl⟩ := cls_surjective x
  rcases 𝔘.em (fun j => x j ∈ (S j).toSubring) with h | h
  · exact Or.inl (cls_mem_uSubring_iff.mpr h)
  · right
    rw [← cls_inv, cls_mem_uSubring_iff]
    filter_upwards [h] with j hj
    exact ((S j).mem_or_inv_mem (x j)).resolve_left hj

def saturation {R M : Type*} [CommRing R] [IsDomain R] [Field M] (φ : R →+* M) (V : Subring M)
    (hV : ∀ x : M, x ∈ V ∨ x⁻¹ ∈ V) (hR : ∀ r, φ r ∈ V) : ValuationSubring M where
  carrier := {x | ∃ r : R, r ≠ 0 ∧ φ r * x ∈ V}
  mul_mem' := by
    rintro x y ⟨r, hr, hx⟩ ⟨t, ht, hy⟩
    refine ⟨r * t, mul_ne_zero hr ht, ?_⟩
    have : φ (r * t) * (x * y) = (φ r * x) * (φ t * y) := by rw [map_mul]; ring
    rw [this]; exact mul_mem hx hy
  one_mem' := ⟨1, one_ne_zero, by simpa only [map_one, one_mul] using hR 1⟩
  add_mem' := by
    rintro x y ⟨r, hr, hx⟩ ⟨t, ht, hy⟩
    refine ⟨r * t, mul_ne_zero hr ht, ?_⟩
    have : φ (r * t) * (x + y) = φ t * (φ r * x) + φ r * (φ t * y) := by rw [map_mul]; ring
    rw [this]; exact add_mem (mul_mem (hR t) hx) (mul_mem (hR r) hy)
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  neg_mem' := by
    rintro x ⟨r, hr, hx⟩
    exact ⟨r, hr, by rw [mul_neg]; exact neg_mem hx⟩
  mem_or_inv_mem' x := by
    rcases hV x with h | h
    · exact Or.inl ⟨1, one_ne_zero, by simpa using h⟩
    · exact Or.inr ⟨1, one_ne_zero, by simpa using h⟩

end Ultra

section Main

variable {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
variable {ι : Type v} (U : ι → X.Opens) (s : ∀ i, Finset Γ(X, U i))

structure BadDatum (c : R) where

  L : Type u
  [fld : Field L]
  [algR : Algebra R L]
  [algK : Algebra K L]
  [tow : IsScalarTower R K L]

  V : ValuationSubring L
  hRV : ∀ r : R, algebraMap R L r ∈ V

  a : Spec (CommRingCat.of L) ⟶ X
  ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))
  bad : ∀ (i : ι) (h : ⊤ ≤ a ⁻¹ᵁ U i), ∃ g ∈ s i, algebraMap R L c * evalHom a (U i) h g ∉ V

attribute [scoped instance] BadDatum.fld BadDatum.algR BadDatum.algK BadDatum.tow

variable {K f U s}

theorem false_of_badDatum [IsProper f] (hcov : ⨆ i, U i = ⊤)
    (d : ∀ c : {c : R // c ≠ 0}, BadDatum K f U s c.1) : False := by
  classical

  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒲 := X.affineCover.finiteSubcover
  let W : 𝒲.I₀ → X.Opens := fun j => (𝒲.f j).opensRange
  have hWaff : ∀ j, IsAffineOpen (W j) := fun j => isAffineOpen_opensRange (𝒲.f j)
  have hWcov : ⨆ j, W j = ⊤ := 𝒲.iSup_opensRange

  haveI : Nonempty {c : R // c ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  let F : Filter {c : R // c ≠ 0} := ⨅ c₀ : {c : R // c ≠ 0}, 𝓟 {c | c₀.1 ∣ c.1}
  haveI hF : F.NeBot := by
    refine Filter.iInf_neBot_of_directed' ?_ (fun c₀ => Filter.principal_neBot_iff.mpr ⟨c₀, dvd_rfl⟩)
    intro c₁ c₂
    refine ⟨⟨c₁.1 * c₂.1, mul_ne_zero c₁.2 c₂.2⟩, ?_, ?_⟩
    · exact Filter.principal_mono.mpr fun c (hc : c₁.1 * c₂.1 ∣ c.1) => (dvd_mul_right c₁.1 c₂.1).trans hc
    · exact Filter.principal_mono.mpr fun c (hc : c₁.1 * c₂.1 ∣ c.1) => (dvd_mul_left c₂.1 c₁.1).trans hc
  let 𝔘 : Ultrafilter {c : R // c ≠ 0} := Ultrafilter.of F
  have hdvd : ∀ c₀ : {c : R // c ≠ 0}, ∀ᶠ c in (𝔘 : Filter {c : R // c ≠ 0}), c₀.1 ∣ c.1 := fun c₀ =>
    Ultrafilter.of_le F (Filter.mem_iInf_of_mem c₀ (Filter.mem_principal_self _))

  let Lc : {c : R // c ≠ 0} → Type u := fun c => (d c).L
  let Lu : Type u := UProd Lc 𝔘
  let Vu : Subring Lu := uSubring (fun c => ((d c).V).toSubring)
  let φR : R →+* Lu := (cls Lc 𝔘).comp (RingHom.pi fun c => algebraMap R (d c).L)
  let φK : K →+* Lu := (cls Lc 𝔘).comp (RingHom.pi fun c => algebraMap K (d c).L)
  have hφ : φK.comp (algebraMap R K) = φR := by
    ext r
    change cls Lc 𝔘 _ = cls Lc 𝔘 _
    congr 1
    funext c
    exact (IsScalarTower.algebraMap_apply R K (d c).L r).symm
  have hRV : ∀ r, φR r ∈ Vu := fun r =>
    cls_mem_uSubring_iff.mpr (Filter.Eventually.of_forall fun c => (d c).hRV r)
  let W' : ValuationSubring Lu :=
    saturation φR Vu (mem_uSubring_or_inv_mem (fun c => (d c).V)) hRV
  have hKW : ∀ k, φK k ∈ W' := by
    intro k
    obtain ⟨n, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := R) k
    show ∃ r : R, r ≠ 0 ∧ φR r * φK _ ∈ Vu
    refine ⟨m, nonZeroDivisors.ne_zero hm, ?_⟩
    have hm' : algebraMap R K m ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
    have : φR m * φK (algebraMap R K n / algebraMap R K m) = φR n := by
      rw [← hφ]
      change φK (algebraMap R K m) * φK _ = φK (algebraMap R K n)
      rw [← map_mul, mul_div_cancel₀ _ hm']
    rw [this]
    exact hRV n
  let φKW : K →+* W' := φK.codRestrict W'.toSubring hKW

  have hall : ∀ c : {c : R // c ≠ 0}, ∃ j, ⊤ ≤ (d c).a ⁻¹ᵁ W j := fun c => by
    have hx : (d c).a.base default ∈ (⊤ : X.Opens) := trivial
    rw [← hWcov, TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨j, hj⟩ := hx
    exact ⟨j, (top_le_preimage_iff _ _).mpr hj⟩
  obtain ⟨j₀, hj₀⟩ : ∃ j, ∀ᶠ c in (𝔘 : Filter {c : R // c ≠ 0}), ⊤ ≤ (d c).a ⁻¹ᵁ W j :=
    Ultrafilter.eventually_exists_iff.mp (Filter.Eventually.of_forall hall)

  let ev : Γ(X, W j₀) → Π c : {c : R // c ≠ 0}, Lc c := fun g c =>
    if h : ⊤ ≤ (d c).a ⁻¹ᵁ W j₀ then evalHom (d c).a (W j₀) h g else 0
  have hev : ∀ (g) (c : {c : R // c ≠ 0}) (h : ⊤ ≤ (d c).a ⁻¹ᵁ W j₀), ev g c = evalHom (d c).a (W j₀) h g :=
    fun g c h => dif_pos h
  let Φ : Γ(X, W j₀) →+* Lu :=
    { toFun := fun g => cls Lc 𝔘 (ev g)
      map_one' := by
        rw [← map_one (cls Lc 𝔘), cls_eq_cls_iff]
        filter_upwards [hj₀] with c hc
        rw [hev _ c hc, map_one]; rfl
      map_mul' := fun x y => by
        rw [← map_mul, cls_eq_cls_iff]
        filter_upwards [hj₀] with c hc
        rw [Pi.mul_apply, hev _ c hc, hev _ c hc, hev _ c hc, map_mul]
      map_zero' := by
        rw [← map_zero (cls Lc 𝔘), cls_eq_cls_iff]
        filter_upwards [hj₀] with c hc
        rw [hev _ c hc, map_zero]; rfl
      map_add' := fun x y => by
        rw [← map_add, cls_eq_cls_iff]
        filter_upwards [hj₀] with c hc
        rw [Pi.add_apply, hev _ c hc, hev _ c hc, hev _ c hc, map_add] }
  have hΦ_apply : ∀ g, Φ g = cls Lc 𝔘 (ev g) := fun g => rfl
  have hΦK : Φ.comp (algK f (W j₀)) = φK := by
    ext k
    change cls Lc 𝔘 _ = cls Lc 𝔘 _
    rw [cls_eq_cls_iff]
    filter_upwards [hj₀] with c hc
    rw [hev _ c hc, ← RingHom.comp_apply, evalHom_comp_algK f (algebraMap K (d c).L) (d c).a (d c).ha]
    rfl
  obtain ⟨a, ha_def⟩ :
      ∃ a : Spec (CommRingCat.of Lu) ⟶ X, a = Spec.map (CommRingCat.ofHom Φ) ≫ (hWaff j₀).fromSpec :=
    ⟨_, rfl⟩
  have ha : a ≫ f = Spec.map (CommRingCat.ofHom φK) := by
    rw [ha_def, Category.assoc, fromSpec_comp_eq f (hWaff j₀), ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      hΦK]
  have ha₀ : ⊤ ≤ a ⁻¹ᵁ W j₀ := by
    rw [ha_def, top_le_iff]
    change Spec.map (CommRingCat.ofHom Φ) ⁻¹ᵁ ((hWaff j₀).fromSpec ⁻¹ᵁ W j₀) = ⊤
    rw [IsAffineOpen.fromSpec_preimage_self]
    rfl
  have hΦ : evalHom a (W j₀) ha₀ = Φ := by
    subst ha_def
    exact evalHom_specMap_comp_fromSpec (hWaff j₀) Φ ha₀

  have hVC : ValuativeCriterion.Existence f := by
    have hp : IsProper f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1.existence
  have sq : CommSq a (Spec.map (CommRingCat.ofHom (algebraMap W' Lu))) f (Spec.map (CommRingCat.ofHom φKW)) := by
    constructor
    rw [ha, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let S : ValuativeCommSq f :=
    { R := W', K := Lu, i₁ := a, i₂ := Spec.map (CommRingCat.ofHom φKW), commSq := sq }
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (hVC S).exists_lift
  change Spec.map (CommRingCat.ofHom (algebraMap W' Lu)) ≫ l = a at hl₁

  obtain ⟨i₁, hi₁⟩ : ∃ i, l.base (IsLocalRing.closedPoint W') ∈ U i := by
    have hx : l.base (IsLocalRing.closedPoint W') ∈ (⊤ : X.Opens) := trivial
    rwa [← hcov, TopologicalSpace.Opens.mem_iSup] at hx
  have hl₁' : ⊤ ≤ l ⁻¹ᵁ U i₁ := top_le_preimage_of_mem l hi₁
  have ha₁ : ⊤ ≤ a ⁻¹ᵁ U i₁ := by
    rw [← hl₁]; exact fun x _ => hl₁' (Set.mem_univ _)
  have hW : ∀ g : Γ(X, U i₁), ∃ r : R, r ≠ 0 ∧ φR r * evalHom a (U i₁) ha₁ g ∈ Vu := by
    intro g
    have hmem : evalHom a (U i₁) ha₁ g ∈ W' := by
      rw [evalHom_congr hl₁.symm (U i₁) ha₁ (by rw [hl₁]; exact ha₁),
        evalHom_specMap_comp (algebraMap W' Lu) l (U i₁) hl₁']
      exact (evalHom l (U i₁) hl₁' g).2
    exact hmem

  obtain ⟨e, he, hxe⟩ := (hWaff j₀).exists_basicOpen_le
    ⟨a.base default, (top_le_preimage_iff a _).mp ha₁⟩ ((top_le_preimage_iff a _).mp ha₀)
  have hea : evalHom a (W j₀) ha₀ e ≠ 0 :=
    (top_le_preimage_basicOpen_iff a ha₀ e).mp ((top_le_preimage_iff a _).mpr hxe)
  have he𝔘 : ∀ᶠ c in (𝔘 : Filter {c : R // c ≠ 0}),
      ∃ h : ⊤ ≤ (d c).a ⁻¹ᵁ W j₀, evalHom (d c).a (W j₀) h e ≠ 0 := by
    have hne : Φ e ≠ 0 := by rwa [← hΦ]
    rw [hΦ_apply, cls_ne_zero_iff] at hne
    filter_upwards [hne, hj₀] with c hc hc₀
    exact ⟨hc₀, by rwa [← hev e c hc₀]⟩

  have key : ∀ g : Γ(X, U i₁), ∃ r : R, r ≠ 0 ∧ ∀ᶠ c in (𝔘 : Filter {c : R // c ≠ 0}),
      ∃ h : ⊤ ≤ (d c).a ⁻¹ᵁ U i₁, algebraMap R (d c).L r * evalHom (d c).a (U i₁) h g ∈ (d c).V := by
    intro g
    obtain ⟨r, hr, hrg⟩ := hW g
    obtain ⟨p, n, hp⟩ := exists_eval_mul_pow_eq (hWaff j₀) e he g
    obtain ⟨h₁', hpa⟩ := hp a ha₀ hea
    obtain ⟨q, hq⟩ := cls_surjective (evalHom a (U i₁) ha₁ g)
    refine ⟨r, hr, ?_⟩
    have h1 : ∀ᶠ c in (𝔘 : Filter {c : R // c ≠ 0}), algebraMap R (d c).L r * q c ∈ (d c).V := by
      have : φR r * evalHom a (U i₁) ha₁ g = cls Lc 𝔘 (fun c => algebraMap R (d c).L r * q c) := by
        rw [← hq]; rfl
      rw [this] at hrg
      exact cls_mem_uSubring_iff.mp hrg
    have h2 : ∀ᶠ c in (𝔘 : Filter {c : R // c ≠ 0}), q c * (ev e c) ^ n = ev p c := by
      have : cls Lc 𝔘 (fun c => q c * (ev e c) ^ n) = cls Lc 𝔘 (ev p) := by
        rw [← hΦ_apply p, ← hΦ, ← hpa, show evalHom a (U i₁) h₁' g = evalHom a (U i₁) ha₁ g from rfl, ← hq,
          hΦ, hΦ_apply, ← map_pow, ← map_mul]
        rfl
      exact cls_eq_cls_iff.mp this
    filter_upwards [h1, h2, he𝔘] with c hc1 hc2 hce
    obtain ⟨hc₀, hce⟩ := hce
    obtain ⟨hc₁, hcomp⟩ := hp (d c).a hc₀ hce
    refine ⟨hc₁, ?_⟩
    rw [hev e c hc₀, hev p c hc₀, ← hcomp] at hc2
    rwa [mul_right_cancel₀ (pow_ne_zero n hce) hc2] at hc1

  choose r hr hkey using key
  have hfin : ∀ᶠ c in (𝔘 : Filter {c : R // c ≠ 0}), ∀ g ∈ s i₁, r g ∣ c.1 ∧
      ∃ h : ⊤ ≤ (d c).a ⁻¹ᵁ U i₁, algebraMap R (d c).L (r g) * evalHom (d c).a (U i₁) h g ∈ (d c).V :=
    (Filter.eventually_all_finset (s i₁)).mpr fun g _ => (hdvd ⟨r g, hr g⟩).and (hkey g)
  obtain ⟨c, hcfin, hc₀, hce⟩ := (hfin.and he𝔘).exists
  have hc₁ : ⊤ ≤ (d c).a ⁻¹ᵁ U i₁ :=
    ((top_le_preimage_basicOpen_iff (d c).a hc₀ e).mpr hce).trans (Scheme.Hom.preimage_mono (d c).a he)
  obtain ⟨g, hgs, hbad⟩ := (d c).bad i₁ hc₁
  obtain ⟨⟨t, ht⟩, ⟨h', hmem⟩⟩ := hcfin g hgs
  apply hbad
  have : algebraMap R (d c).L c.1 * evalHom (d c).a (U i₁) hc₁ g =
      algebraMap R (d c).L t * (algebraMap R (d c).L (r g) * evalHom (d c).a (U i₁) h' g) := by
    have h1 : algebraMap R (d c).L c.1 = algebraMap R (d c).L (r g) * algebraMap R (d c).L t := by
      rw [← map_mul]; exact congrArg _ ht
    rw [h1]; ring
  rw [this]
  exact mul_mem ((d c).hRV t) hmem

def valuationSubringOf (V L : Type u) [CommRing V] [IsDomain V] [ValuationRing V] [Field L] [Algebra V L]
    [IsFractionRing V L] : ValuationSubring L :=
  { (algebraMap V L).range with
    mem_or_inv_mem' := fun x => by
      rcases ValuationRing.isInteger_or_isInteger V x with h | h
      · exact Or.inl h
      · exact Or.inr h }

theorem mem_valuationSubringOf_iff {V L : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Field L]
    [Algebra V L] [IsFractionRing V L] (x : L) :
    x ∈ valuationSubringOf V L ↔ x ∈ Set.range (algebraMap V L) :=
  Iff.rfl

end Main

end AlgebraicGeometry.ProperBounded
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper.AlgebraicGeometry.ProperBounded"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper.AlgebraicGeometry"

open AlgebraicGeometry.ProperBounded in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    {ι : Type v} (U : ι → X.Opens) (hcov : ⨆ i, U i = ⊤) (s : ∀ i, Finset Γ(X, U i)) :
    ∃ c : R, c ≠ 0 ∧
      ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra R V]
        (L : Type u) [Field L] [Algebra V L] [IsFractionRing V L] [Algebra R L] [IsScalarTower R V L]
        [Algebra K L] [IsScalarTower R K L]
        (a : Spec (CommRingCat.of L) ⟶ X), a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) →
        ∃ (i : ι) (h : ⊤ ≤ a ⁻¹ᵁ U i), ∀ g ∈ s i,
          algebraMap R L c * (Scheme.ΓSpecIso (CommRingCat.of L)).hom (a.appLE (U i) ⊤ h g) ∈
            Set.range (algebraMap V L) := by
  by_contra H
  have hbad : ∀ c : {c : R // c ≠ 0}, Nonempty (BadDatum K f U s c.1) := by
    intro c
    by_contra hne
    apply H
    refine ⟨c.1, c.2, ?_⟩
    intro V _ _ _ _ L _ _ _ _ _ _ _ a ha
    by_contra hP
    push Not at hP
    apply hne
    exact ⟨{ L := L
             V := valuationSubringOf V L
             hRV := fun r => ⟨algebraMap R V r, (IsScalarTower.algebraMap_apply R V L r).symm⟩
             a := a
             ha := ha
             bad := fun i h => hP i h }⟩
  exact false_of_badDatum hcov fun c => (hbad c).some

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper.AlgebraicGeometry.ProperBounded"

end S_AlgebraicGeometry_exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper (solution)
