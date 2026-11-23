-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_finitePresentation_diagram_over_integer
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-23T01:52:38.388574+00:00
-- url     : https://prove2.me/submissions/cc76656e-5455-4bce-8184-7416c7eb4cbf

import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Cover.Directed
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Away.Basic
import Theorems.Thm_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry AlgebraicGeometry.SubalgebraStages
open CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponAbsoluteApproximationAffine

universe u

/-- The affine case of absolute Noetherian approximation, with finitely
generated subalgebras of the global coordinate ring as the stages. -/
theorem exists_diagram (X : Scheme.{u}) [IsAffine X]
    (f : X ⟶ Spec (.of (ULift.{u} ℤ))) :
    ∃ (I : Type u) (_ : Category.{u} I) (_ : IsCofiltered I)
      (D : I ⥤ Scheme.{u}) (c : Cone D)
      (g : D ⟶ (Functor.const I).obj (Spec (.of (ULift.{u} ℤ)))) (e : X ≅ c.pt),
      Nonempty (IsLimit c) ∧
      (∀ i, e.hom ≫ c.π.app i ≫ g.app i = f) ∧
      (∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)) ∧
      (∀ i, LocallyOfFinitePresentation (g.app i) ∧ QuasiCompact (g.app i) ∧ QuasiSeparated (g.app i)) := by
  let A := ULift.{u} ℤ
  let R : Type u := Γ(X, ⊤)
  let f₀ : Spec (.of R) ⟶ Spec (.of A) := X.isoSpec.inv ≫ f
  let ρ := Spec.preimage f₀
  let : Algebra A R := ρ.hom.toAlgebra
  let : IsNoetherianRing A := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  let J : Type u := {T : Subalgebra A R // T.FG}
  let : Nonempty J := ⟨⟨Algebra.adjoin A (∅ : Finset R), Subalgebra.fg_adjoin_finset ∅⟩⟩
  let : IsDirected J (· ≤ ·) := ⟨fun T U =>
    ⟨⟨T.1 ⊔ U.1, T.2.sup U.2⟩, le_sup_left (a := T.1) (b := U.1),
      le_sup_right (a := T.1) (b := U.1)⟩⟩
  let S : J →o Subalgebra A R := ⟨Subtype.val, fun _ _ h => h⟩
  have hS (r : R) : ∃ j, r ∈ S j :=
    ⟨⟨Algebra.adjoin A ({r} : Finset R), Subalgebra.fg_adjoin_finset _⟩,
      Algebra.subset_adjoin (by simp)⟩
  let T := Spec (CommRingCat.of A)
  let D := diagram S (𝟙 T)
  let c := cone S (𝟙 T)
  let g : D ⟶ (Functor.const Jᵒᵖ).obj T :=
    { app i := pullback.fst (𝟙 T) (specHom S i.unop)
      naturality i j v := (diagram_map_fst S (𝟙 T) v).trans (Category.comp_id _).symm }
  let k : Spec (.of R) ⟶ T := specHomTop
  have hk : k = f₀ := Spec.map_preimage f₀
  let p := pullback.snd (𝟙 T) k
  let e : X ≅ c.pt := X.isoSpec ≪≫ (asIso p).symm
  refine ⟨Jᵒᵖ, inferInstance, inferInstance, D, c, g, e,
    SubalgebraStages.nonempty_isLimit_cone S hS (𝟙 T), ?_, ?_, ?_⟩
  · intro i
    have hi : c.π.app i ≫ g.app i = pullback.fst (𝟙 T) k :=
      cone_π_app_fst S (𝟙 T) i
    have hpk : pullback.fst (𝟙 T) k = p ≫ k := by
      simpa only [Category.comp_id] using (pullback.condition (f := 𝟙 T) (g := k))
    rw [hi, hpk]
    change (X.isoSpec.hom ≫ (asIso p).inv) ≫ p ≫ k = f
    simp only [Category.assoc, asIso_inv, IsIso.inv_hom_id_assoc, hk, f₀, Iso.hom_inv_id_assoc]
  · intro i j v
    exact SubalgebraStages.isAffineHom_diagram_map S (𝟙 T) v
  · intro i
    let : Algebra.FiniteType A ↥(S i.unop) := (Subalgebra.fg_iff_finiteType _).mp i.unop.2
    let : LocallyOfFiniteType (specHom S i.unop) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
        (RingHom.finiteType_algebraMap.mpr inferInstance)
    have hG : g.app i = pullback.snd (𝟙 T) (specHom S i.unop) ≫ specHom S i.unop := by
      simpa only [Category.comp_id] using
        (pullback.condition (f := 𝟙 T) (g := specHom S i.unop))
    have hAff : IsAffineHom (g.app i) :=
      inferInstanceAs (IsAffineHom (pullback.fst (𝟙 T) (specHom S i.unop)))
    let _ := hAff
    refine ⟨?_, inferInstance, inferInstance⟩
    rw [hG]
    exact (LocallyOfFinitePresentation.iff_locallyOfFiniteType (Y := T)).mpr inferInstance

end PhilipponAbsoluteApproximationAffine

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponAbsoluteModels

universe u

abbrev integerBase : Scheme.{u} := Spec (.of (ULift.{u} ℤ))

def toBase (X : Scheme.{u}) : X ⟶ integerBase :=
  specULiftZIsTerminal.from X

@[reassoc (attr := simp)]
theorem comp_toBase {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f ≫ toBase Y = toBase X :=
  specULiftZIsTerminal.hom_ext _ _

instance integerBase_isLocallyNoetherian : IsLocallyNoetherian (integerBase : Scheme.{u}) := by
  let : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  change IsLocallyNoetherian (Spec (.of (ULift.{u} ℤ)))
  infer_instance

attribute [local instance] ULift.algebra'

theorem toBase_Spec (R : Type u) [CommRing R] :
    toBase (Spec (.of R)) = Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) R)) :=
  specULiftZIsTerminal.hom_ext _ _

theorem finiteType_toBase_Spec (R : Type u) [CommRing R] [Algebra.FiniteType (ULift.{u} ℤ) R] :
    LocallyOfFiniteType (toBase (Spec (.of R))) := by
  rw [toBase_Spec]
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- An absolute approximation by quasi-compact schemes of finite type over
the integers with affine transition morphisms. -/
structure Models (X : Scheme.{u}) where
  index : Type u
  category : Category.{u} index
  cofiltered : IsCofiltered index
  diagram : index ⥤ Scheme.{u}
  cone : Cone diagram
  limit : IsLimit cone
  iso : X ≅ cone.pt
  affine : ∀ {i j} (v : i ⟶ j), IsAffineHom (diagram.map v)
  compact : ∀ i, CompactSpace (diagram.obj i)
  finiteType : ∀ i, LocallyOfFiniteType (toBase (diagram.obj i))

attribute [instance] Models.category Models.cofiltered

def Models.onScheme {X : Scheme.{u}} (m : Models X) : Cone m.diagram where
  pt := X
  π :=
    { app i := m.iso.hom ≫ m.cone.π.app i
      naturality _ _ _ := by simp }

def Models.onSchemeLimit {X : Scheme.{u}} (m : Models X) : IsLimit m.onScheme :=
  m.limit.ofIsoLimit (Cone.ext m.iso.symm (fun i => by
    change _ = m.iso.inv ≫ m.iso.hom ≫ m.cone.π.app i
    rw [Iso.inv_hom_id_assoc]))

def Models.ofIso {X Y : Scheme.{u}} (m : Models Y) (e : X ≅ Y) : Models X :=
  { m with iso := e ≪≫ m.iso }

theorem nonempty_for_affine (X : Scheme.{u}) [IsAffine X] : Nonempty (Models X) := by
  obtain ⟨I, hCat, hCof, D, c, g, e, ⟨hc⟩, _, hAff, hFin⟩ :=
    PhilipponAbsoluteApproximationAffine.exists_diagram X (toBase X)
  let _ := hCat
  let _ := hCof
  refine ⟨⟨I, hCat, hCof, D, c, hc, e, @hAff, ?_, ?_⟩⟩
  · intro i
    let _ := (hFin i).2.1
    exact @QuasiCompact.compactSpace_of_compactSpace _ (integerBase : Scheme.{u})
      (g.app i) inferInstance inferInstance
  · intro i
    let _ := (hFin i).1
    have hEq : g.app i = toBase (D.obj i) := specULiftZIsTerminal.hom_ext _ _
    exact hEq ▸ (inferInstance : LocallyOfFiniteType (g.app i))

end PhilipponAbsoluteModels

end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace PhilipponLocalizationPullback

universe u

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* C) (g : B →+* C)

abbrev ring : Type u :=
  (CommRingCat.pullbackCone (CommRingCat.ofHom f) (CommRingCat.ofHom g)).pt

abbrev first : ring f g →+* A :=
  (CommRingCat.pullbackCone (CommRingCat.ofHom f) (CommRingCat.ofHom g)).fst.hom

abbrev second : ring f g →+* B :=
  (CommRingCat.pullbackCone (CommRingCat.ofHom f) (CommRingCat.ofHom g)).snd.hom

def pair (a : A) (b : B) (h : f a = g b) : ring f g :=
  ⟨(a, b), h⟩

@[simp] theorem first_pair (a : A) (b : B) (h : f a = g b) :
    first f g (pair f g a b h) = a := rfl

@[simp] theorem second_pair (a : A) (b : B) (h : f a = g b) :
    second f g (pair f g a b h) = b := rfl

theorem condition (z : ring f g) : f (first f g z) = g (second f g z) :=
  z.2

@[ext] theorem ext {x y : ring f g} (h₁ : first f g x = first f g y)
    (h₂ : second f g x = second f g y) : x = y :=
  Subtype.ext (Prod.ext h₁ h₂)

/-- In a pullback of rings, if the top arrow becomes an isomorphism after
inverting a matching element, the bottom arrow does as well. -/
theorem bijective_awayMap_second (a : A) (b : B) (h : f a = g b)
    (hf : Function.Bijective (Localization.awayMap f a)) :
    Function.Bijective (Localization.awayMap (second f g) (pair f g a b h)) := by
  constructor
  · rw [Localization.awayMap_injective_iff]
    intro z hz
    have hz₀ : f (first f g z) = 0 := by rw [condition, hz, map_zero]
    obtain ⟨n, hn⟩ := Localization.awayMap_injective_iff.mp hf.1 _ hz₀
    refine ⟨n, ext f g ?_ ?_⟩
    · simpa only [map_mul, map_pow, map_zero, first_pair] using hn
    · simp [hz]
  · rw [Localization.awayMap_surjective_iff]
    intro y
    obtain ⟨x, n, hx⟩ := Localization.awayMap_surjective_iff.mp hf.2 (g y)
    have hxy : f x = g (b ^ n * y) := by rw [hx, h, map_mul, map_pow]
    exact ⟨pair f g x (b ^ n * y) hxy, n, rfl⟩

end PhilipponLocalizationPullback

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace PhilipponBasicOpenLocalizationMap

universe u v

theorem isIso_restrict_basicOpen {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) (h : Function.Bijective (Localization.awayMap f r)) :
    IsIso (Spec.map (CommRingCat.ofHom f) ∣_ PrimeSpectrum.basicOpen r) := by
  let p := CommRingCat.ofHom f
  let a := CommRingCat.ofHom (Localization.awayMap f r)
  let : IsIso a := (ConcreteCategory.isIso_iff_bijective a).mpr h
  exact (MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms Scheme)
    (SpecMapRestrictBasicOpenIso p r)).mpr (inferInstance : IsIso (Spec.map a))

/-- A map that becomes an isomorphism on each of a family of basic opens
is an isomorphism on their union. -/
theorem isIso_restrict_iSup {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {J : Type v} (r : J → R)
    (h : ∀ j, Function.Bijective (Localization.awayMap f (r j))) :
    IsIso (Spec.map (CommRingCat.ofHom f) ∣_ ⨆ j, PrimeSpectrum.basicOpen (r j)) := by
  let d := Spec.map (CommRingCat.ofHom f)
  let V (j : J) : (Spec (.of R)).Opens := PrimeSpectrum.basicOpen (r j)
  let U := iSup V
  let W (j : J) : U.toScheme.Opens := U.ι ⁻¹ᵁ V j
  have hW : iSup W = ⊤ := by
    change (⨆ j, U.ι ⁻¹ᵁ V j) = ⊤
    rw [← Scheme.Hom.preimage_iSup]
    exact U.ι_preimage_self
  have hIm (j : J) : U.ι ''ᵁ W j = V j := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right]
    exact le_iSup V j
  change MorphismProperty.isomorphisms Scheme (d ∣_ U)
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms Scheme) W hW]
  intro j
  rw [MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms Scheme) (morphismRestrictRestrict d U (W j)),
    MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms Scheme) (morphismRestrictEq d (hIm j))]
  exact isIso_restrict_basicOpen f (r j) (h j)

private theorem preimage_iSup_basicOpen {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {J : Type v} (r : J → R) :
    Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ (⨆ j, PrimeSpectrum.basicOpen (r j)) =
      ⨆ j, PrimeSpectrum.basicOpen (f (r j)) := by
  simp only [Scheme.Hom.preimage_iSup]
  rfl

theorem isOpenImmersion_on_basicOpens {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {J : Type v} (r : J → R)
    (h : ∀ j, Function.Bijective (Localization.awayMap f (r j))) :
    IsOpenImmersion ((⨆ j, PrimeSpectrum.basicOpen (f (r j)) :
        (Spec (.of S)).Opens).ι ≫ Spec.map (CommRingCat.ofHom f)) := by
  let d := Spec.map (CommRingCat.ofHom f)
  let U : (Spec (.of R)).Opens := ⨆ j, PrimeSpectrum.basicOpen (r j)
  let : IsIso (d ∣_ U) := isIso_restrict_iSup f r h
  have hp : IsOpenImmersion ((d ∣_ U) ≫ U.ι) := inferInstance
  rwa [morphismRestrict_ι, preimage_iSup_basicOpen f r] at hp

theorem range_on_basicOpens {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {J : Type v} (r : J → R)
    (h : ∀ j, Function.Bijective (Localization.awayMap f (r j))) :
    Set.range ((⨆ j, PrimeSpectrum.basicOpen (f (r j)) :
        (Spec (.of S)).Opens).ι ≫ Spec.map (CommRingCat.ofHom f)) =
      (⨆ j, PrimeSpectrum.basicOpen (r j) : (Spec (.of R)).Opens).1 := by
  let d := Spec.map (CommRingCat.ofHom f)
  let U : (Spec (.of R)).Opens := ⨆ j, PrimeSpectrum.basicOpen (r j)
  let : IsIso (d ∣_ U) := isIso_restrict_iSup f r h
  rw [← preimage_iSup_basicOpen f r, ← morphismRestrict_ι]
  change ((d ∣_ U) ≫ U.ι).opensRange.1 = U.1
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

/-- A family of matching localizations of a ring pullback supplies the open
embedding of the overlap used to attach an affine chart. -/
theorem isOpenImmersion_pullback_overlap {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* C) (g : B →+* C) {J : Type v} (a : J → A) (b : J → B)
    (h : ∀ j, f (a j) = g (b j))
    (hf : ∀ j, Function.Bijective (Localization.awayMap f (a j))) :
    IsOpenImmersion ((⨆ j, PrimeSpectrum.basicOpen (b j) :
        (Spec (.of B)).Opens).ι ≫ Spec.map (CommRingCat.ofHom (PhilipponLocalizationPullback.second f g))) :=
  isOpenImmersion_on_basicOpens (PhilipponLocalizationPullback.second f g)
    (fun j => PhilipponLocalizationPullback.pair f g (a j) (b j) (h j))
    (fun j => PhilipponLocalizationPullback.bijective_awayMap_second f g (a j) (b j) (h j) (hf j))

end PhilipponBasicOpenLocalizationMap

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PhilipponSubalgebraLocalizations

universe u

variable (A : Type u) [CommRing A] {R : Type u} [CommRing R] [Algebra A R]

/-- A finite-type localization can be recovered from any subalgebra containing
its denominator and a finite set of numerators for its generators. -/
theorem exists_finset_bijective_awayMap (r : R) [Algebra.FiniteType A (Localization.Away r)] :
    ∃ (s : Finset R) (hr : r ∈ s), ∀ (T : Subalgebra A R) (hs : (s : Set R) ⊆ T),
      Function.Bijective (Localization.awayMap T.val.toRingHom ⟨r, hs hr⟩) := by
  classical
  obtain ⟨generators, hGen⟩ := (Algebra.FiniteType.out (R := A) (A := Localization.Away r))
  have hNumerator (x : ↥generators) :
      ∃ (n : ℕ) (y : R),
        (x : Localization.Away r) * algebraMap R (Localization.Away r) r ^ n =
          algebraMap R (Localization.Away r) y := IsLocalization.Away.surj r x.1
  choose n y hNumerator using hNumerator
  let s := insert r (generators.attach.image y)
  have hr : r ∈ s := Finset.mem_insert_self ..
  refine ⟨s, hr, ?_⟩
  intro T hs
  let a : T := ⟨r, hs hr⟩
  let p := Localization.awayMap T.val.toRingHom a
  change Function.Bijective p
  constructor
  · rw [show p = Localization.awayMap T.val.toRingHom a by rfl, Localization.awayMap_injective_iff]
    intro x hx
    exact ⟨0, by simpa using (Subtype.ext hx : x = 0)⟩
  · let : IsLocalization.Away (T.val a) (Localization.Away r) :=
      inferInstanceAs (IsLocalization.Away r (Localization.Away r))
    let q : Localization.Away a →ₐ[A] Localization.Away r :=
      IsLocalization.Away.mapₐ (Localization.Away a) (Localization.Away r) T.val a
    change Function.Surjective q
    apply (AlgHom.range_eq_top q).mp
    refine top_unique ?_
    rw [← hGen]
    apply Algebra.adjoin_le
    intro x hx
    let i : ↥generators := ⟨x, hx⟩
    have hy : y i ∈ T := hs (Finset.mem_insert_of_mem (Finset.mem_image_of_mem y (by simp)))
    let z : T := ⟨y i, hy⟩
    let m : Submonoid.powers a := ⟨a ^ n i, n i, rfl⟩
    refine ⟨IsLocalization.mk' (Localization.Away a) z m, ?_⟩
    change IsLocalization.Away.map (Localization.Away a) (Localization.Away r) T.val.toRingHom a
      (IsLocalization.mk' (Localization.Away a) z m) = x
    rw [IsLocalization.Away.map, IsLocalization.map_mk']
    apply IsLocalization.mk'_eq_iff_eq_mul.mpr
    change algebraMap R (Localization.Away r) (y i) =
      x * algebraMap R (Localization.Away r) (r ^ n i)
    rw [map_pow]
    exact (hNumerator i).symm

end PhilipponSubalgebraLocalizations

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace PhilipponFiniteTypeOpenSubalgebra

universe u

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]

theorem exists_basicOpen_cover (U : (Spec (.of R)).Opens)
    [CompactSpace U.toScheme] :
    ∃ s : Finset R, U = ⨆ k : ↥s, PrimeSpectrum.basicOpen k.1 := by
  classical
  have hCompact : IsCompact (U : Set (Spec (.of R))) := by
    rw [← Scheme.Opens.range_ι]
    exact isCompact_range U.ι.continuous
  obtain ⟨s, hs, he⟩ := (isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis
    (fun r : R => (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)))
    PrimeSpectrum.isTopologicalBasis_basic_opens PrimeSpectrum.isCompact_basicOpen _).mp
      ⟨hCompact, U.isOpen⟩
  refine ⟨hs.toFinset, Opens.ext ?_⟩
  simpa only [Opens.coe_iSup, Set.iUnion_subtype, Set.Finite.mem_toFinset] using he

private abbrev structureMap (A R : Type u) [CommRing A] [CommRing R] [Algebra A R] :
    Spec (.of R) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A R))

private theorem finiteType_of_basicOpen_le (U : (Spec (.of R)).Opens)
    [LocallyOfFiniteType (U.ι ≫ structureMap A R)] (r : R)
    (h : PrimeSpectrum.basicOpen r ≤ U) :
    Algebra.FiniteType A (Localization.Away r) := by
  let W : (Spec (.of R)).Opens := PrimeSpectrum.basicOpen r
  let e := basicOpenIsoSpecAway (R := CommRingCat.of R) r
  have hComp : e.hom ≫ structureMap A (Localization.Away r) =
      (Spec (.of R)).homOfLE h ≫ U.ι ≫ structureMap A R := by
    rw [← Category.assoc ((Spec (.of R)).homOfLE h), Scheme.homOfLE_ι]
    have hMap : structureMap A (Localization.Away r) =
        structureMap R (Localization.Away r) ≫ structureMap A R := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun g : A →+* Localization.Away r => Spec.map (CommRingCat.ofHom g))
        (IsScalarTower.algebraMap_eq A R (Localization.Away r))
    rw [hMap, ← Category.assoc]
    exact congrArg (fun f : W.toScheme ⟶ Spec (.of R) => f ≫ structureMap A R)
      (basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of R) r)
  have hFin : LocallyOfFiniteType (e.hom ≫ structureMap A (Localization.Away r)) := hComp.symm ▸
    (inferInstance : LocallyOfFiniteType ((Spec (.of R)).homOfLE h ≫ U.ι ≫ structureMap A R))
  have hSpec := (MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType)
    e.hom (structureMap A (Localization.Away r))).mp hFin
  exact RingHom.finiteType_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hSpec)

/-- A prescribed finite basic-open cover of a finite-type open can be
retained over all subalgebras containing a common finite set. -/
theorem exists_finset_for_basicOpens (U : (Spec (.of R)).Opens)
    [LocallyOfFiniteType (U.ι ≫ structureMap A R)]
    {J : Type u} [Finite J] (r : J → R) (hU : U = ⨆ j, PrimeSpectrum.basicOpen (r j)) :
    ∃ (s : Finset R) (hr : ∀ j, r j ∈ s), ∀ (T : Subalgebra A R) (hT : (s : Set R) ⊆ T),
      ∀ j, Function.Bijective (Localization.awayMap T.val.toRingHom ⟨r j, hT (hr j)⟩) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  have hAff (j : J) : Algebra.FiniteType A (Localization.Away (r j)) :=
    finiteType_of_basicOpen_le (A := A) U (r j)
      (hU.symm ▸ le_iSup (fun j => PrimeSpectrum.basicOpen (r j)) j)
  have hSeed (j : J) := by
    let _ := hAff j
    exact PhilipponSubalgebraLocalizations.exists_finset_bijective_awayMap A (r j)
  choose t ht hBij using hSeed
  let s := Finset.univ.biUnion t
  have hr (j : J) : r j ∈ s := Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, ht j⟩
  refine ⟨s, hr, ?_⟩
  intro T hT j
  exact hBij j T (fun _ hx => hT (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hx⟩))

/-- A quasi-compact finite-type open of an affine scheme remains an open
subscheme over any subalgebra containing a prescribed finite set of
coefficients. -/
theorem exists_finset_isOpenImmersion (U : (Spec (.of R)).Opens)
    [CompactSpace U.toScheme] [LocallyOfFiniteType (U.ι ≫ structureMap A R)] :
    ∃ s : Finset R, ∀ (T : Subalgebra A R), (s : Set R) ⊆ T →
      IsOpenImmersion (U.ι ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom)) := by
  obtain ⟨s, hs⟩ := exists_basicOpen_cover U
  obtain ⟨t, ht, hBij⟩ := exists_finset_for_basicOpens (A := A) U (fun r : ↥s => r.1) hs
  refine ⟨t, ?_⟩
  intro T hT
  have hOpen := PhilipponBasicOpenLocalizationMap.isOpenImmersion_on_basicOpens
    T.val.toRingHom (fun r : ↥s => ⟨r.1, hT (ht r)⟩) (hBij T hT)
  exact hs.symm ▸ hOpen

end PhilipponFiniteTypeOpenSubalgebra

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace PhilipponOverlapAffineChart

universe u

variable {W : Scheme.{u}} {B : CommRingCat.{u}} (f : W ⟶ Spec B)

def ringMap : B ⟶ Γ(W, ⊤) := (Scheme.ΓSpecIso B).inv ≫ f.appTop

@[reassoc (attr := simp)]
theorem toSpec_ringMap : W.toSpecΓ ≫ Spec.map (ringMap f) = f := by
  rw [ringMap, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
    Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

variable [IsOpenImmersion f] [W.IsQuasiAffine]

private theorem opensRange_affine_basicOpen (r : Γ(W, ⊤)) (h : IsAffineOpen (W.basicOpen r)) :
    Set.range ((W.basicOpen r).ι ≫ W.toSpecΓ) =
      (PrimeSpectrum.basicOpen r : (Spec Γ(W, ⊤)).Opens).1 := by
  let U := W.basicOpen r
  let R := W.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
  let : Algebra Γ(W, ⊤) Γ(W, U) := R.hom.toAlgebra
  let : IsLocalization.Away r Γ(W, U) := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ r
  let : IsOpenImmersion (Spec.map R) := IsOpenImmersion.of_isLocalization r
  let : IsAffine U.toScheme := h
  let : IsIso U.toSpecΓ := by
    unfold Scheme.Opens.toSpecΓ
    infer_instance
  change Set.range (U.ι ≫ W.toSpecΓ) = _
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]
  change (U.toSpecΓ ≫ Spec.map R).opensRange.1 = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact PrimeSpectrum.localization_away_comap_range Γ(W, U) r

private theorem basicOpen_data (r : B)
    (hr : (PrimeSpectrum.basicOpen r : (Spec B).Opens) ≤ f.opensRange) :
    W.toSpecΓ ''ᵁ f ⁻¹ᵁ PrimeSpectrum.basicOpen r = PrimeSpectrum.basicOpen (ringMap f r) ∧
      Function.Bijective (Localization.awayMap (ringMap f).hom r) := by
  let V : (Spec B).Opens := PrimeSpectrum.basicOpen r
  let U := f ⁻¹ᵁ V
  let s := ringMap f r
  let BOpen : (Spec Γ(W, ⊤)).Opens := PrimeSpectrum.basicOpen s
  have hPre : Spec.map (ringMap f) ⁻¹ᵁ V = BOpen := rfl
  have hU : U = W.basicOpen s := by
    change f ⁻¹ᵁ V = _
    rw [← toSpec_ringMap f, Scheme.Hom.comp_preimage, hPre]
    exact W.toSpecΓ_preimage_basicOpen s
  have hAff : IsAffineOpen U := by
    rw [← f.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
      inf_eq_right.mpr hr]
    exact IsAffineOpen.Spec_basicOpen r
  have hSpecRange : Set.range (U.ι ≫ W.toSpecΓ) = BOpen.1 := by
    rw [hU]
    exact opensRange_affine_basicOpen s (hU ▸ hAff)
  have hRange : Set.range (U.ι ≫ f) = V.1 := by
    change ((U.ι ≫ f).opensRange).1 = _
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, Scheme.Hom.image_preimage_eq_opensRange_inf,
      inf_eq_right.mpr hr]
  have hImage : W.toSpecΓ ''ᵁ U = BOpen := by
    have hOp : (U.ι ≫ W.toSpecΓ).opensRange = W.toSpecΓ ''ᵁ U := by
      rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι U]
    exact hOp ▸ Opens.ext hSpecRange
  let m := Spec.map (ringMap f) ∣_ V
  let e : U.toScheme ≅ (Spec.map (ringMap f) ⁻¹ᵁ V).toScheme :=
    IsOpenImmersion.isoOfRangeEq (U.ι ≫ W.toSpecΓ) (Spec.map (ringMap f) ⁻¹ᵁ V).ι
      (by rw [Scheme.Opens.range_ι, hPre]; exact hSpecRange)
  let e' : U.toScheme ≅ V.toScheme :=
    IsOpenImmersion.isoOfRangeEq (U.ι ≫ f) V.ι (by rw [Scheme.Opens.range_ι]; exact hRange)
  have hm : e.hom ≫ m = e'.hom := by
    have hE : e.hom ≫ (Spec.map (ringMap f) ⁻¹ᵁ V).ι = U.ι ≫ W.toSpecΓ :=
      IsOpenImmersion.isoOfRangeEq_hom_fac ..
    have hE' : e'.hom ≫ V.ι = U.ι ≫ f := IsOpenImmersion.isoOfRangeEq_hom_fac ..
    apply (cancel_mono V.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hE, hE', Category.assoc,
      toSpec_ringMap]
  let : IsIso (e.hom ≫ m) := hm.symm ▸ inferInstance
  let : IsIso m := IsIso.of_isIso_comp_left e.hom _
  let φ := CommRingCat.ofHom (Localization.awayMap (ringMap f).hom r)
  let : IsIso (Spec.map φ) :=
    (MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms Scheme)
      (SpecMapRestrictBasicOpenIso (ringMap f) r)).mp (inferInstance : IsIso m)
  let : IsIso (Scheme.Spec.map φ.op) := inferInstanceAs (IsIso (Spec.map φ))
  let : IsIso φ.op := isIso_of_reflects_iso φ.op Scheme.Spec
  let : IsIso φ := isIso_of_op φ
  exact ⟨hImage, (ConcreteCategory.isIso_iff_bijective φ).mp inferInstance⟩

/-- The overlap with an affine chart admits matching principal opens in the
chart and its affinization, with isomorphic localizations. -/
theorem exists_denominators :
    ∃ t : Finset B,
      f.opensRange = (⨆ j : ↥t, PrimeSpectrum.basicOpen j.1) ∧
      W.toSpecΓ.opensRange = (⨆ j : ↥t, PrimeSpectrum.basicOpen (ringMap f j.1)) ∧
      ∀ j : ↥t, Function.Bijective (Localization.awayMap (ringMap f).hom j.1) := by
  let U := f.opensRange
  let : CompactSpace U.toScheme := (f.isoOpensRange.hom.homeomorph).compactSpace
  obtain ⟨t, ht⟩ := PhilipponFiniteTypeOpenSubalgebra.exists_basicOpen_cover (R := B) U
  have hB (j : ↥t) := basicOpen_data f j.1 (show PrimeSpectrum.basicOpen j.1 ≤ U from by
    rw [ht]
    exact le_iSup (fun j : ↥t => PrimeSpectrum.basicOpen j.1) j)
  refine ⟨t, ht, ?_, fun j => (hB j).2⟩
  have he : f ⁻¹ᵁ (⨆ j : ↥t, PrimeSpectrum.basicOpen j.1) = ⊤ := ht ▸ f.preimage_opensRange
  calc
    _ = W.toSpecΓ ''ᵁ f ⁻¹ᵁ (⨆ j : ↥t, PrimeSpectrum.basicOpen j.1) :=
      ((congrArg (fun V : W.Opens => W.toSpecΓ ''ᵁ V) he).trans W.toSpecΓ.image_top_eq_opensRange).symm
    _ = _ := by
      rw [Scheme.Hom.preimage_iSup, Scheme.Hom.image_iSup]
      exact congrArg iSup (funext fun j => (hB j).1)

end PhilipponOverlapAffineChart

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace PhilipponOverlapStageBasicOpens

universe u v

/-- A finite basic-open description of a quasi-affine limit in its affinization
comes from the same finite family of principal opens at a stage. -/
theorem exists_stage {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)]
    [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ i, (D.obj i).IsQuasiAffine] [c.pt.IsQuasiAffine]
    {J : Type v} [Finite J] (r : J → Γ(c.pt, ⊤))
    (hr : c.pt.toSpecΓ.opensRange = ⨆ j, PrimeSpectrum.basicOpen (r j)) :
    ∃ (i : I) (s : J → Γ(D.obj i, ⊤)), (∀ j, (c.π.app i).appTop (s j) = r j) ∧
      (D.obj i).toSpecΓ.opensRange = ⨆ j, PrimeSpectrum.basicOpen (s j) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  choose i t ht using fun j => exists_appTop_π_eq_of_isLimit D c hc (r j)
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  let a (j : J) : k ⟶ i j := (hk (Finset.mem_image_of_mem i (Finset.mem_univ j))).some
  let s (j : J) := (D.map (a j)).appTop (t j)
  have hs (j : J) : (c.π.app k).appTop (s j) = r j := by
    dsimp only [s]
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, c.w]
    exact (ht j).symm
  let G : Scheme.{u} ⥤ Scheme.{u} := Scheme.Γ.rightOp ⋙ Scheme.Spec
  let F := D ⋙ G
  let cF := G.mapCone c
  let hF : IsLimit cF := isLimitOfPreserves G hc
  let : ∀ {i j : I} (v : i ⟶ j), IsAffineHom (F.map v) := fun v => by
    change IsAffineHom (Spec.map (D.map v).appTop)
    infer_instance
  let : ∀ i, IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc
  let U : (F.obj k).Opens := (D.obj k).toSpecΓ.opensRange
  let V : (F.obj k).Opens := ⨆ j, PrimeSpectrum.basicOpen (s j)
  have hU : IsCompact (U : Set (F.obj k)) := isCompact_range (D.obj k).toSpecΓ.continuous
  have hV : IsCompact (V : Set (F.obj k)) := by
    change IsCompact ((⨆ j, PrimeSpectrum.basicOpen (s j) : (Spec Γ(D.obj k, ⊤)).Opens) :
      Set (Spec Γ(D.obj k, ⊤)))
    rw [Opens.coe_iSup]
    exact isCompact_iUnion fun j => PrimeSpectrum.isCompact_basicOpen (s j)
  have hUV : cF.π.app k ⁻¹ᵁ U = cF.π.app k ⁻¹ᵁ V := by
    have hUa : cF.π.app k ⁻¹ᵁ U = c.pt.toSpecΓ.opensRange :=
      Scheme.preimage_opensRange_toSpecΓ (X := c.pt) (Y := D.obj k) (c.π.app k)
    rw [hUa, hr]
    change (⨆ j, PrimeSpectrum.basicOpen (r j)) =
      Spec.map (c.π.app k).appTop ⁻¹ᵁ (⨆ j, PrimeSpectrum.basicOpen (s j))
    rw [Scheme.Hom.preimage_iSup]
    congr 1
    funext j
    change PrimeSpectrum.basicOpen (r j) = PrimeSpectrum.basicOpen ((c.π.app k).appTop (s j))
    rw [hs]
  obtain ⟨l, v, hv⟩ := exists_map_preimage_eq_map_preimage F cF hF hU hV hUV
  let z (j : J) : Γ(D.obj l, ⊤) := (D.map v).appTop (s j)
  refine ⟨l, z, fun j => ?_, ?_⟩
  · dsimp only [z]
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, c.w]
    exact hs j
  · have hUl : F.map v ⁻¹ᵁ U = (D.obj l).toSpecΓ.opensRange :=
      Scheme.preimage_opensRange_toSpecΓ (D.map v)
    rw [← hUl, hv]
    change Spec.map (D.map v).appTop ⁻¹ᵁ (⨆ j, PrimeSpectrum.basicOpen (s j)) =
      ⨆ j, PrimeSpectrum.basicOpen (z j)
    rw [Scheme.Hom.preimage_iSup]
    rfl

end PhilipponOverlapStageBasicOpens

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits


namespace PhilipponAffineChartRingLimits

universe u

variable {J : Type u} [Category.{u} J] {D : J ⥤ CommRingCat.{u}} (c : Cocone D)
    {B : CommRingCat.{u}} (f : B ⟶ c.pt)

private abbrev stage (j : J) := CommRingCat.pullbackCone f (c.ι.app j)

private theorem square (j : J) : IsPullback (stage c f j).fst (stage c f j).snd f (c.ι.app j) :=
  IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit f (c.ι.app j))

private def transition {i j : J} (v : i ⟶ j) : (stage c f i).pt ⟶ (stage c f j).pt :=
  (square c f j).lift (stage c f i).fst ((stage c f i).snd ≫ D.map v)
    (by rw [Category.assoc, c.w, (stage c f i).condition])

@[reassoc (attr := simp)]
private theorem transition_fst {i j : J} (v : i ⟶ j) :
    transition c f v ≫ (stage c f j).fst = (stage c f i).fst :=
  IsPullback.lift_fst ..

@[reassoc (attr := simp)]
private theorem transition_snd {i j : J} (v : i ⟶ j) :
    transition c f v ≫ (stage c f j).snd = (stage c f i).snd ≫ D.map v :=
  IsPullback.lift_snd ..

/-- The affine chart rings obtained by pulling the ring of an affine open
back along the rings of the overlap stages. -/
def diagram : J ⥤ CommRingCat.{u} where
  obj j := (stage c f j).pt
  map := transition c f
  map_id j := (square c f j).hom_ext (by simp) (by simp)
  map_comp v w := (square c f _).hom_ext (by simp) (by simp)

def toOverlap : diagram c f ⟶ D where
  app j := (stage c f j).snd
  naturality _ _ v := transition_snd c f v

def toChart : diagram c f ⟶ (Functor.const J).obj B where
  app j := (stage c f j).fst
  naturality _ _ v := (transition_fst c f v).trans (Category.comp_id _).symm

def cocone : Cocone (diagram c f) where
  pt := B
  ι := toChart c f

private theorem isPullback_natTrans :
    IsPullback (toChart c f) (toOverlap c f) ((Functor.const J).map f) c.ι :=
  IsPullback.of_forall_isPullback_app (square c f)

/-- If the overlap rings have the claimed filtered colimit, the pullback
chart rings have colimit equal to the original affine chart ring. -/
def isColimit [IsFiltered J] (hc : IsColimit c) : IsColimit (cocone c f) := by
  let : IsConnected J := IsFiltered.isConnected J
  have hColim := (isPullback_natTrans c f).map (colim : (J ⥤ CommRingCat.{u}) ⥤ CommRingCat.{u})
  let eR : colimit D ≅ c.pt := (colimit.isColimit D).coconePointUniqueUpToIso hc
  let eConst : colimit ((Functor.const J).obj c.pt) ≅ c.pt :=
    (colimit.isColimit ((Functor.const J).obj c.pt)).coconePointUniqueUpToIso
    (isColimitConstCocone J c.pt)
  have heR : colimMap c.ι = eR.hom ≫ eConst.inv := by
    apply (cancel_mono eConst.hom).mp
    apply colimit.hom_ext
    intro j
    have hr : colimit.ι D j ≫ eR.hom = c.ι.app j :=
      IsColimit.comp_coconePointUniqueUpToIso_hom _ hc j
    have hConst : colimit.ι ((Functor.const J).obj c.pt) j ≫ eConst.hom = 𝟙 c.pt :=
      IsColimit.comp_coconePointUniqueUpToIso_hom _ (isColimitConstCocone J c.pt) j
    simp only [Category.assoc, ι_colimMap_assoc, hConst]
    let z : D.obj j ⟶ c.pt := c.ι.app j
    change z ≫ 𝟙 c.pt = _
    calc
      _ = z := Category.comp_id z
      _ = colimit.ι D j ≫ eR.hom := hr.symm
      _ = _ := by rw [eConst.inv_hom_id, Category.comp_id]
  let hIso : IsIso (colimMap c.ι) := heR.symm ▸ inferInstance
  let : IsIso (colimMap (toChart c f)) := hColim.isIso_fst_of_isIso hIso
  let eB : colimit ((Functor.const J).obj B) ≅ B :=
    (colimit.isColimit ((Functor.const J).obj B)).coconePointUniqueUpToIso (isColimitConstCocone J B)
  let e := asIso (colimMap (toChart c f)) ≪≫ eB
  refine (colimit.isColimit (diagram c f)).ofIsoColimit (Cocone.ext e (fun j => ?_))
  change colimit.ι (diagram c f) j ≫ colimMap (toChart c f) ≫ eB.hom = _
  have hB : colimit.ι ((Functor.const J).obj B) j ≫ eB.hom = 𝟙 B :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ (isColimitConstCocone J B) j
  rw [ι_colimMap_assoc, hB]
  change (stage c f j).fst ≫ 𝟙 B = (stage c f j).fst
  exact Category.comp_id _

end PhilipponAffineChartRingLimits

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits


namespace PhilipponFiniteChartRingRefinement

universe u

attribute [local instance] ULift.algebra'

variable {I : Type u} [Category.{u} I] (D : I ⥤ CommRingCat.{u})
    (seed : ∀ i, Finset (D.obj i))

/-- A finitely generated subalgebra of a stage ring containing its required
finite set of coefficients. -/
structure Stage where
  index : I
  algebra : Subalgebra (ULift.{u} ℤ) (D.obj index)
  finiteGeneration : algebra.FG
  containsSeed : (seed index : Set (D.obj index)) ⊆ algebra

private def algebraMapAlong {i j : I} (v : i ⟶ j) : D.obj i →ₐ[ULift.{u} ℤ] D.obj j :=
  { toRingHom := (D.map v).hom
    commutes' := fun x => by
      change (D.map v).hom (x.down : D.obj i) = (x.down : D.obj j)
      exact map_intCast (D.map v).hom x.down }

instance : Category.{u} (Stage D seed) where
  Hom S T := {v : S.index ⟶ T.index // S.algebra ≤ T.algebra.comap (algebraMapAlong D v)}
  id S := ⟨𝟙 _, fun x hx => by simpa [algebraMapAlong] using hx⟩
  comp {_ _ R} v w := ⟨v.1 ≫ w.1, fun x hx => by
    change (D.map (v.1 ≫ w.1)).hom x ∈ R.algebra
    rw [Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]
    exact w.2 (v.2 hx)⟩
  id_comp _ := Subtype.ext (Category.id_comp _)
  comp_id _ := Subtype.ext (Category.comp_id _)
  assoc _ _ _ := Subtype.ext (Category.assoc _ _ _)

private def extend (i : I) (T : Subalgebra (ULift.{u} ℤ) (D.obj i)) (hT : T.FG) : Stage D seed :=
  ⟨i, T ⊔ Algebra.adjoin (ULift.{u} ℤ) (seed i : Set (D.obj i)),
    hT.sup (Subalgebra.fg_adjoin_finset _),
    Algebra.subset_adjoin.trans (SetLike.coe_subset_coe.mpr le_sup_right)⟩

private def extendImage (S : Stage D seed) {j : I} (v : S.index ⟶ j) : Stage D seed :=
  extend D seed j (S.algebra.map (algebraMapAlong D v))
    (S.finiteGeneration.map (algebraMapAlong D v))

private def toExtendImage (S : Stage D seed) {j : I} (v : S.index ⟶ j) :
    S ⟶ extendImage D seed S v := by
  refine ⟨v, fun x hx => ?_⟩
  have hle : S.algebra.map (algebraMapAlong D v) ≤ (extendImage D seed S v).algebra :=
    le_sup_left
  exact hle ⟨x, hx, rfl⟩

instance [IsFiltered I] : IsFiltered (Stage D seed) where
  nonempty := ⟨extend D seed (IsFiltered.nonempty (C := I)).some ⊥ Subalgebra.fg_bot⟩
  cocone_objs S T := by
    obtain ⟨i, a, b, _⟩ := IsFilteredOrEmpty.cocone_objs S.index T.index
    let Sa := S.algebra.map (algebraMapAlong D a)
    let Tb := T.algebra.map (algebraMapAlong D b)
    let hSa := S.finiteGeneration.map (algebraMapAlong D a)
    let hTb := T.finiteGeneration.map (algebraMapAlong D b)
    have hle : Sa ⊔ Tb ≤ (extend D seed i (Sa ⊔ Tb) (hSa.sup hTb)).algebra :=
      le_sup_left
    refine ⟨extend D seed i (Sa ⊔ Tb) (hSa.sup hTb), ⟨a, ?_⟩, ⟨b, ?_⟩, trivial⟩
    · intro x hx
      exact hle (le_sup_left (a := Sa) (b := Tb) ⟨x, hx, rfl⟩)
    · intro x hx
      exact hle (le_sup_right (a := Sa) (b := Tb) ⟨x, hx, rfl⟩)
  cocone_maps {_ _} v w := by
    obtain ⟨i, a, ha⟩ := IsFilteredOrEmpty.cocone_maps v.1 w.1
    exact ⟨extendImage D seed _ a, toExtendImage D seed _ a, Subtype.ext ha⟩

/-- The projection forgetting the choice of finitely generated subalgebra. -/
def projection : Stage D seed ⥤ I where
  obj S := S.index
  map v := v.1

instance [IsFiltered I] : (projection D seed).Final := by
  refine Functor.final_of_exists_of_isFiltered _ ?_ ?_
  · intro j
    exact ⟨extend D seed j ⊥ Subalgebra.fg_bot, ⟨𝟙 j⟩⟩
  · intro _ S a b
    obtain ⟨j, v, hv⟩ := IsFilteredOrEmpty.cocone_maps a b
    exact ⟨extendImage D seed S v, toExtendImage D seed S v, hv⟩

private abbrev restrict {S T : Stage D seed} (v : S ⟶ T) :=
  ((algebraMapAlong D v.1).comp S.algebra.val).codRestrict T.algebra (fun x => v.2 x.2)

/-- The diagram of finitely generated subalgebras with their restricted
transition maps. -/
def diagram : Stage D seed ⥤ CommRingCat.{u} where
  obj S := CommRingCat.of S.algebra
  map v := CommRingCat.ofHom (restrict D seed v).toRingHom
  map_id S := CommRingCat.hom_ext <| RingHom.ext fun x => Subtype.ext (by
    change (D.map (𝟙 S.index)).hom x.1 = x.1
    simp)
  map_comp v w := CommRingCat.hom_ext <| RingHom.ext fun x => Subtype.ext (by
    change (D.map (v.1 ≫ w.1)).hom x.1 = (D.map w.1).hom ((D.map v.1).hom x.1)
    simp)

def inclusion : diagram D seed ⟶ projection D seed ⋙ D where
  app S := CommRingCat.ofHom S.algebra.val.toRingHom
  naturality _ _ _ := rfl

def cocone (c : Cocone D) : Cocone (diagram D seed) :=
  (Cocone.precompose (inclusion D seed)).obj (c.whisker (projection D seed))

/-- Refining all stages by finitely generated subalgebras containing the
prescribed coefficients leaves the filtered colimit unchanged. -/
def isColimit [IsFiltered I] (c : Cocone D) (hc : IsColimit c) :
    IsColimit (cocone D seed c) := by
  let : ReflectsFilteredColimits (forget CommRingCat.{u}) :=
    ⟨fun _ => reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  let hTypes := isColimitOfPreserves (forget CommRingCat.{u}) hc
  apply isColimitOfReflects (forget CommRingCat.{u})
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    obtain ⟨i, y, hy⟩ := Types.jointly_surjective_of_isColimit hTypes x
    let T := Algebra.adjoin (ULift.{u} ℤ) (↑({y} : Finset (D.obj i)) : Set (D.obj i))
    let S := extend D seed i T (Subalgebra.fg_adjoin_finset _)
    have hle : T ≤ S.algebra := le_sup_left
    have hY : y ∈ S.algebra := hle (Algebra.subset_adjoin (by simp))
    exact ⟨S, ⟨y, hY⟩, hy.symm⟩
  · intro S x y hxy
    have he : (c.ι.app S.index) x.1 = (c.ι.app S.index) y.1 := hxy
    obtain ⟨j, v, hv⟩ := (Types.FilteredColimit.isColimit_eq_iff' hTypes x.1 y.1).mp he
    exact ⟨extendImage D seed S v, toExtendImage D seed S v, Subtype.ext hv⟩

end PhilipponFiniteChartRingRefinement

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace PhilipponFiniteOverlapChart

universe u

attribute [local instance] ULift.algebra'

private theorem comp_open_image {W X Y : Scheme.{u}} (a : W ⟶ X) [IsOpenImmersion a]
    (f : X ⟶ Y) (U : X.Opens) (hU : a.opensRange = U)
    (h : IsOpenImmersion (U.ι ≫ f)) :
    IsOpenImmersion (a ≫ f) ∧ Set.range (a ≫ f) = Set.range (U.ι ≫ f) := by
  let e := IsOpenImmersion.isoOfRangeEq a U.ι (by
    rw [Scheme.Opens.range_ι, ← hU]
    rfl)
  have he : e.hom ≫ U.ι = a := IsOpenImmersion.isoOfRangeEq_hom_fac ..
  let _ := h
  have hx : e.hom ≫ (U.ι ≫ f) = a ≫ f := by rw [← Category.assoc, he]
  rw [← hx]
  refine ⟨inferInstance, ?_⟩
  change (e.hom ≫ (U.ι ≫ f)).opensRange.1 = (U.ι ≫ f).opensRange.1
  rw [Scheme.Hom.opensRange_comp_of_isIso]

variable {W : Scheme.{u}} [W.IsQuasiAffine] {B R : CommRingCat.{u}}
    (f : B ⟶ R) (g : Γ(W, ⊤) ⟶ R)

abbrev ring := (CommRingCat.pullbackCone f g).pt

abbrev toOverlap := (CommRingCat.pullbackCone f g).snd

def overlapMap : W ⟶ Spec (ring f g) := W.toSpecΓ ≫ Spec.map (toOverlap f g)

variable {J : Type u} (t : J → B) (s : J → Γ(W, ⊤)) (h : ∀ j, f (t j) = g (s j))

def denominator (j : J) : ring f g :=
  PhilipponLocalizationPullback.pair f.hom g.hom (t j) (s j) (h j)

theorem overlapMap_open_and_range
    (hW : W.toSpecΓ.opensRange = ⨆ j, PrimeSpectrum.basicOpen (s j))
    (hf : ∀ j, Function.Bijective (Localization.awayMap f.hom (t j))) :
    IsOpenImmersion (overlapMap f g) ∧
      Set.range (overlapMap f g) = (⨆ j, PrimeSpectrum.basicOpen (denominator f g t s h j) :
        (Spec (ring f g)).Opens).1 := by
  let U : (Spec Γ(W, ⊤)).Opens := ⨆ j, PrimeSpectrum.basicOpen (s j)
  have hBij (j : J) : Function.Bijective
      (Localization.awayMap (toOverlap f g).hom (denominator f g t s h j)) :=
    PhilipponLocalizationPullback.bijective_awayMap_second f.hom g.hom (t j) (s j) (h j) (hf j)
  let q : Spec Γ(W, ⊤) ⟶ Spec (ring f g) := Spec.map (toOverlap f g)
  have hOpen : IsOpenImmersion (U.ι ≫ q) :=
    PhilipponBasicOpenLocalizationMap.isOpenImmersion_on_basicOpens
      (toOverlap f g).hom (denominator f g t s h) hBij
  have hRange : Set.range (U.ι ≫ q) =
        (⨆ j, PrimeSpectrum.basicOpen (denominator f g t s h j) : (Spec (ring f g)).Opens).1 :=
    PhilipponBasicOpenLocalizationMap.range_on_basicOpens
      (toOverlap f g).hom (denominator f g t s h) hBij
  have he := comp_open_image W.toSpecΓ q U hW hOpen
  exact ⟨he.1, he.2.trans hRange⟩

/-- Finite stage coefficients can be chosen so every subalgebra containing
them retains the prescribed principal-open overlap. -/
theorem exists_seed [Finite J] [LocallyOfFiniteType (PhilipponAbsoluteModels.toBase W)]
    (hW : W.toSpecΓ.opensRange = ⨆ j, PrimeSpectrum.basicOpen (s j))
    (hf : ∀ j, Function.Bijective (Localization.awayMap f.hom (t j))) :
    ∃ (seed : Finset (ring f g)) (hseed : ∀ j, denominator f g t s h j ∈ seed),
      ∀ (A : Subalgebra (ULift.{u} ℤ) (ring f g)) (hA : (seed : Set (ring f g)) ⊆ A),
        IsOpenImmersion (overlapMap f g ≫ Spec.map (CommRingCat.ofHom A.val.toRingHom)) ∧
        Set.range (overlapMap f g ≫ Spec.map (CommRingCat.ofHom A.val.toRingHom)) =
          (⨆ j, PrimeSpectrum.basicOpen
            (⟨denominator f g t s h j, hA (hseed j)⟩ : A) : (Spec (.of A)).Opens).1 := by
  obtain ⟨hOpen, hRange⟩ := overlapMap_open_and_range f g t s h hW hf
  let _ := hOpen
  let U := (overlapMap f g).opensRange
  have hU : U = ⨆ j, PrimeSpectrum.basicOpen (denominator f g t s h j) := Opens.ext hRange
  have hFin : LocallyOfFiniteType (PhilipponAbsoluteModels.toBase U.toScheme) := by
    rw [← PhilipponAbsoluteModels.comp_toBase ((overlapMap f g).isoOpensRange.inv)]
    infer_instance
  let : LocallyOfFiniteType (U.ι ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ) (ring f g)))) := by
    have he : PhilipponAbsoluteModels.toBase U.toScheme =
        U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (ring f g))) :=
      specULiftZIsTerminal.hom_ext _ _
    exact he ▸ hFin
  obtain ⟨seed, hseed, hBij⟩ := PhilipponFiniteTypeOpenSubalgebra.exists_finset_for_basicOpens
    (A := ULift.{u} ℤ) U (denominator f g t s h) hU
  refine ⟨seed, hseed, fun A hA => ?_⟩
  let q := Spec.map (CommRingCat.ofHom A.val.toRingHom)
  let z (j : J) : A := ⟨denominator f g t s h j, hA (hseed j)⟩
  have hOpen' : IsOpenImmersion (U.ι ≫ q) := hU.symm ▸
    PhilipponBasicOpenLocalizationMap.isOpenImmersion_on_basicOpens A.val.toRingHom z (hBij A hA)
  have hRange' : Set.range (U.ι ≫ q) =
      (⨆ j, PrimeSpectrum.basicOpen (z j) : (Spec (.of A)).Opens).1 := hU.symm ▸
    PhilipponBasicOpenLocalizationMap.range_on_basicOpens A.val.toRingHom z (hBij A hA)
  have he := comp_open_image (overlapMap f g) q U rfl hOpen'
  exact ⟨he.1, he.2.trans hRange'⟩

end PhilipponFiniteOverlapChart

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


namespace PhilipponRefinedAffineChart

universe u

attribute [local instance] ULift.algebra'

variable {I : Type u} [Category.{u} I] {W : I ⥤ Scheme.{u}} {w : Cone W}
    [∀ i, (W.obj i).IsQuasiAffine] {B : CommRingCat.{u}}

/-- Matching principal opens of the affine chart and of the overlap
affinizations, with the same denominators at every stage. -/
structure Denominators (q : w.pt ⟶ Spec B) [IsOpenImmersion q] where
  elements : Finset B
  coeff : ∀ i, ↥elements → Γ(W.obj i, ⊤)
  map_coeff : ∀ {i j} (v : i ⟶ j) (x : ↥elements), (W.map v).appTop (coeff j x) = coeff i x
  limit_coeff : ∀ i (x : ↥elements),
    PhilipponOverlapAffineChart.ringMap q x.1 = (w.π.app i).appTop (coeff i x)
  stage_cover : ∀ i,
    (W.obj i).toSpecΓ.opensRange = ⨆ x : ↥elements, PrimeSpectrum.basicOpen (coeff i x)
  limit_cover : q.opensRange = ⨆ x : ↥elements, PrimeSpectrum.basicOpen x.1
  localization : ∀ x : ↥elements,
    Function.Bijective (Localization.awayMap (PhilipponOverlapAffineChart.ringMap q).hom x.1)

variable {q : w.pt ⟶ Spec B} [IsOpenImmersion q] (d : Denominators q)
    [∀ i, LocallyOfFiniteType (PhilipponAbsoluteModels.toBase (W.obj i))]

private abbrev sectionsCone (w : Cone W) := Scheme.Γ.mapCocone w.op

private abbrev sectionsMap (q : w.pt ⟶ Spec B) := PhilipponOverlapAffineChart.ringMap q

private abbrev raw (q : w.pt ⟶ Spec B) :=
  PhilipponAffineChartRingLimits.diagram (sectionsCone w) (sectionsMap q)

private def mark (i : I) (x : ↥d.elements) : (raw q).obj (op i) :=
  PhilipponFiniteOverlapChart.denominator (sectionsMap q) ((sectionsCone w).ι.app (op i))
    (fun x : ↥d.elements => x.1) (d.coeff i) (d.limit_coeff i) x

private theorem seed_exists (i : I) :
    ∃ (s : Finset ((raw q).obj (op i))) (hs : ∀ x, mark d i x ∈ s),
      ∀ (T : Subalgebra (ULift.{u} ℤ) ((raw q).obj (op i))) (hT : (s : Set _) ⊆ T),
        IsOpenImmersion (PhilipponFiniteOverlapChart.overlapMap (sectionsMap q)
          ((sectionsCone w).ι.app (op i)) ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom)) ∧
        Set.range (PhilipponFiniteOverlapChart.overlapMap (sectionsMap q)
          ((sectionsCone w).ι.app (op i)) ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom)) =
          (⨆ x : ↥d.elements, PrimeSpectrum.basicOpen
            (⟨mark d i x, @hT (mark d i x) (hs x)⟩ : T) :
            (Spec (.of T)).Opens).1 :=
  PhilipponFiniteOverlapChart.exists_seed (W := W.obj i) (sectionsMap q)
    ((sectionsCone w).ι.app (op i)) (fun x : ↥d.elements => x.1) (d.coeff i)
    (d.limit_coeff i) (d.stage_cover i) d.localization

private def seed (j : Iᵒᵖ) : Finset ((raw q).obj j) := (seed_exists d j.unop).choose

private theorem marks_in_seed (i : I) (x : ↥d.elements) : mark d i x ∈ seed d (op i) :=
  (seed_exists d i).choose_spec.choose x

abbrev Index := (PhilipponFiniteChartRingRefinement.Stage (raw q) (seed d))ᵒᵖ

private abbrev rings := PhilipponFiniteChartRingRefinement.diagram (raw q) (seed d)

private abbrev proj := PhilipponFiniteChartRingRefinement.projection (raw q) (seed d)

/-- The projection to the original overlap stage before choosing a subalgebra. -/
def projection : Index d ⥤ I :=
  (proj d).op ⋙ (opOpEquivalence I).functor

instance [IsCofiltered I] : (projection d).Initial := by
  unfold projection
  infer_instance

private abbrev ringLegs :=
  PhilipponFiniteChartRingRefinement.cocone (raw q) (seed d)
    (PhilipponAffineChartRingLimits.cocone (sectionsCone w) (sectionsMap q))

/-- The new affine chart at every refined stage. -/
def diagram : Index d ⥤ Scheme.{u} :=
  (rings d).op ⋙ Scheme.Spec

private def ringMaps : rings d ⟶ proj d ⋙ (W.op ⋙ Scheme.Γ) :=
  PhilipponFiniteChartRingRefinement.inclusion (raw q) (seed d) ≫
    Functor.whiskerLeft (proj d)
      (PhilipponAffineChartRingLimits.toOverlap (sectionsCone w) (sectionsMap q))

private def overlapRingMap (i : Index d) :
    (rings d).obj i.unop ⟶ Γ(W.obj ((projection d).obj i), ⊤) :=
  (ringMaps d).app i.unop

private theorem overlapRingMap_naturality {i j : Index d} (v : i ⟶ j) :
    (rings d).map v.unop ≫ overlapRingMap d i =
      overlapRingMap d j ≫ (W.map ((projection d).map v)).appTop :=
  (ringMaps d).naturality v.unop

/-- The overlap into the refined affine chart. -/
def inChart : projection d ⋙ W ⟶ diagram d where
  app i := (W.obj ((projection d).obj i)).toSpecΓ ≫ Spec.map (overlapRingMap d i)
  naturality i j v := by
    change W.map ((projection d).map v) ≫ (W.obj ((projection d).obj j)).toSpecΓ ≫
      Spec.map (overlapRingMap d j) = _
    rw [Scheme.toSpecΓ_naturality_assoc]
    change (W.obj ((projection d).obj i)).toSpecΓ ≫ Spec.map (W.map ((projection d).map v)).appTop ≫
      Spec.map (overlapRingMap d j) =
      ((W.obj ((projection d).obj i)).toSpecΓ ≫ Spec.map (overlapRingMap d i)) ≫
        Spec.map ((rings d).map v.unop)
    rw [Category.assoc, ← Spec.map_comp, ← Spec.map_comp, overlapRingMap_naturality]

private def marked (i : Index d) (x : ↥d.elements) : (rings d).obj i.unop :=
  ⟨mark d ((projection d).obj i) x, i.unop.containsSeed (marks_in_seed d _ x)⟩

private theorem inChart_open_and_range (i : Index d) :
    IsOpenImmersion ((inChart d).app i) ∧
      Set.range ((inChart d).app i) = (⨆ x : ↥d.elements, PrimeSpectrum.basicOpen (marked d i x) :
        ((diagram d).obj i).Opens).1 := by
  have he := (seed_exists d ((projection d).obj i)).choose_spec.choose_spec
    i.unop.algebra i.unop.containsSeed
  have hh : (inChart d).app i = PhilipponFiniteOverlapChart.overlapMap (sectionsMap q)
      ((sectionsCone w).ι.app i.unop.index) ≫ Spec.map (CommRingCat.ofHom i.unop.algebra.val.toRingHom) := by
    change _ ≫ Spec.map (overlapRingMap d i) = _
    change _ ≫ Spec.map (_ ≫ _) = _
    rw [Spec.map_comp, PhilipponFiniteOverlapChart.overlapMap, Category.assoc]
    rfl
  rw [hh]
  exact he

instance (i : Index d) : IsOpenImmersion ((inChart d).app i) := (inChart_open_and_range d i).1

private theorem inChart_opensRange (i : Index d) :
    ((inChart d).app i).opensRange = ⨆ x : ↥d.elements, PrimeSpectrum.basicOpen (marked d i x) :=
  Opens.ext (inChart_open_and_range d i).2

omit [∀ i, LocallyOfFiniteType (PhilipponAbsoluteModels.toBase (W.obj i))] in
private theorem map_mark {i j : I} (v : i ⟶ j) (x : ↥d.elements) :
    (raw q).map v.op (mark d j x) = mark d i x := by
  apply PhilipponLocalizationPullback.ext
  · have he := (PhilipponAffineChartRingLimits.toChart (sectionsCone w) (sectionsMap q)).naturality v.op
    exact congrArg (fun h : (raw q).obj (op j) ⟶ B => h (mark d j x))
      (he.trans (Category.comp_id _))
  · have he := (PhilipponAffineChartRingLimits.toOverlap (sectionsCone w) (sectionsMap q)).naturality v.op
    have hh := congrArg (fun h : (raw q).obj (op j) ⟶ Γ(W.obj i, ⊤) => h (mark d j x)) he
    exact hh.trans (d.map_coeff v x)

private theorem map_marked {i j : Index d} (v : i ⟶ j) (x : ↥d.elements) :
    (rings d).map v.unop (marked d j x) = marked d i x :=
  Subtype.ext (map_mark d ((projection d).map v) x)

theorem isPullback_map {i j : Index d} (v : i ⟶ j) :
    IsPullback ((projection d ⋙ W).map v) ((inChart d).app i) ((inChart d).app j) ((diagram d).map v) := by
  refine IsOpenImmersion.isPullback _ _ _ _ ((inChart d).naturality v).symm ?_
  rw [inChart_opensRange, inChart_opensRange, Scheme.Hom.preimage_iSup]
  congr 1
  funext x
  change PrimeSpectrum.basicOpen ((rings d).map v.unop (marked d j x)) =
    PrimeSpectrum.basicOpen (marked d i x)
  rw [map_marked]

/-- The affine chart cone, before gluing it to the original open part. -/
def cone : Cone (diagram d) :=
  Scheme.Spec.mapCone (ringLegs d).op

theorem isPullback_leg (i : Index d) :
    IsPullback (w.π.app ((projection d).obj i)) q ((inChart d).app i) ((cone d).π.app i) := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · let leg : (rings d).obj i.unop ⟶ B := (ringLegs d).ι.app i.unop
    let π : w.pt ⟶ W.obj ((projection d).obj i) := w.π.app ((projection d).obj i)
    have hRing : leg ≫ sectionsMap q = overlapRingMap d i ≫ π.appTop := by
      let j := i.unop.index
      let a := (PhilipponFiniteChartRingRefinement.inclusion (raw q) (seed d)).app i.unop
      let pullbackCone := CommRingCat.pullbackCone (sectionsMap q) ((sectionsCone w).ι.app j)
      change (a ≫ pullbackCone.fst) ≫ sectionsMap q =
        (a ≫ pullbackCone.snd) ≫ (sectionsCone w).ι.app j
      simpa only [Category.assoc] using congrArg (fun m => a ≫ m) pullbackCone.condition
    change q ≫ Spec.map leg =
      w.π.app ((projection d).obj i) ≫
        (W.obj ((projection d).obj i)).toSpecΓ ≫ Spec.map (overlapRingMap d i)
    calc
      q ≫ Spec.map leg = (w.pt.toSpecΓ ≫ Spec.map (sectionsMap q)) ≫ Spec.map leg :=
        congrArg (fun m => m ≫ Spec.map leg) (PhilipponOverlapAffineChart.toSpec_ringMap q).symm
      _ = w.pt.toSpecΓ ≫ Spec.map (leg ≫ sectionsMap q) := by rw [Spec.map_comp, Category.assoc]
      _ = w.pt.toSpecΓ ≫ Spec.map (overlapRingMap d i ≫ π.appTop) :=
        congrArg (fun f => w.pt.toSpecΓ ≫ Spec.map f) hRing
      _ = _ := by
        change _ = π ≫ (W.obj ((projection d).obj i)).toSpecΓ ≫ Spec.map (overlapRingMap d i)
        rw [Scheme.toSpecΓ_naturality_assoc, Spec.map_comp]
  · rw [d.limit_cover, inChart_opensRange, Scheme.Hom.preimage_iSup]
    rfl

theorem finiteType (i : Index d) :
    LocallyOfFiniteType (PhilipponAbsoluteModels.toBase ((diagram d).obj i)) := by
  let : Algebra.FiniteType (ULift.{u} ℤ) i.unop.algebra :=
    (Subalgebra.fg_iff_finiteType _).mp i.unop.finiteGeneration
  exact PhilipponAbsoluteModels.finiteType_toBase_Spec i.unop.algebra

instance (i : Index d) : IsAffine ((diagram d).obj i) :=
  inferInstanceAs (IsAffine (Spec ((rings d).obj i.unop)))

def isLimit [IsCofiltered I]
    [∀ {i j : I} (v : i ⟶ j), IsAffineHom (W.map v)]
    [∀ i, QuasiSeparatedSpace (W.obj i)] (hw : IsLimit w) : IsLimit (cone d) := by
  let hΓ := (nonempty_isColimit_Γ_mapCocone W w hw).some
  let hRing := PhilipponAffineChartRingLimits.isColimit (sectionsCone w) (sectionsMap q) hΓ
  let hFin := PhilipponFiniteChartRingRefinement.isColimit (raw q) (seed d)
    (PhilipponAffineChartRingLimits.cocone (sectionsCone w) (sectionsMap q)) hRing
  exact isLimitOfPreserves Scheme.Spec hFin.op

end PhilipponRefinedAffineChart

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponOpenGluingPoints

universe u

variable {W X Y : Scheme.{u}} (f : W ⟶ X) (g : W ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g]

/-- The two chart inclusions cover the pushout along open immersions. -/
theorem union_range : Set.range (pushout.inl f g) ∪ Set.range (pushout.inr f g) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨j, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span f g) p
  cases j with
  | none =>
    refine Or.inl ⟨f x, ?_⟩
    have he : colimit.ι (span f g) WalkingSpan.zero = f ≫ pushout.inl f g :=
      (colimit.w (span f g) (WidePushoutShape.Hom.init WalkingPair.left)).symm
    rw [he, Scheme.Hom.comp_apply] at hx
    exact hx
  | some j =>
    cases j
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨x, hx⟩

/-- Two chart points have the same image precisely when they come from a
point of the open overlap. -/
theorem inl_eq_inr_iff (x : X) (y : Y) :
    pushout.inl f g x = pushout.inr f g y ↔ ∃ w : W, f w = x ∧ g w = y := by
  constructor
  · intro h
    obtain ⟨k, a, b, w, ha, hb⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (span f g) (i := WalkingSpan.left)
        (j := WalkingSpan.right)).mp h
    cases k with
    | none =>
      change WidePushoutShape.Hom (J := WalkingPair) none (some WalkingPair.left) at a
      change WidePushoutShape.Hom (J := WalkingPair) none (some WalkingPair.right) at b
      cases a
      cases b
      exact ⟨w, ha, hb⟩
    | some k =>
      cases k
      · change WidePushoutShape.Hom (some WalkingPair.left) (some WalkingPair.right) at b
        cases b
      · change WidePushoutShape.Hom (some WalkingPair.right) (some WalkingPair.left) at a
        cases a
  · rintro ⟨w, rfl, rfl⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pushout.condition]

section Transition

variable {W' X' Y' : Scheme.{u}} (f' : W' ⟶ X') (g' : W' ⟶ Y')
    [IsOpenImmersion f'] [IsOpenImmersion g']
    (a : W ⟶ W') (b : X ⟶ X') (d : Y ⟶ Y')
    (hl : IsPullback a f f' b) (hr : IsPullback a g g' d)

/-- The map of glued schemes induced by a map of the two charts and their
common open. -/
noncomputable def map : pushout f g ⟶ pushout f' g' :=
  pushout.map f g f' g' b d a hl.w.symm hr.w.symm

@[reassoc (attr := simp)]
theorem inl_map : pushout.inl f g ≫ map f g f' g' a b d hl hr = b ≫ pushout.inl f' g' :=
  pushout.inl_desc ..

@[reassoc (attr := simp)]
theorem inr_map : pushout.inr f g ≫ map f g f' g' a b d hl hr = d ≫ pushout.inr f' g' :=
  pushout.inr_desc ..

/-- If both overlap squares are pullbacks, the left chart of the glued scheme
also pulls back along the transition. -/
theorem isPullback_inl :
    IsPullback b (pushout.inl f g) (pushout.inl f' g') (map f g f' g' a b d hl hr) := by
  let p := map f g f' g' a b d hl hr
  let l := pushout.inl f g
  let r := pushout.inr f g
  let l' := pushout.inl f' g'
  let r' := pushout.inr f' g'
  let : IsOpenImmersion l := inferInstanceAs (IsOpenImmersion (colimit.ι (span f g) WalkingSpan.left))
  let : IsOpenImmersion l' := inferInstanceAs (IsOpenImmersion (colimit.ι (span f' g') WalkingSpan.left))
  have hL : l ≫ p = b ≫ l' := inl_map f g f' g' a b d hl hr
  have hR : r ≫ p = d ≫ r' := inr_map f g f' g' a b d hl hr
  refine IsOpenImmersion.isPullback b l l' p hL ?_
  apply TopologicalSpace.Opens.ext
  change p ⁻¹' Set.range l' = Set.range l
  ext x
  constructor
  · intro hx
    have hUnion : x ∈ Set.range l ∪ Set.range r :=
      (union_range f g).ge (Set.mem_univ x)
    rcases hUnion with h | ⟨y, rfl⟩
    · exact h
    obtain ⟨z, hz⟩ : ∃ z, l' z = p (r y) := hx
    have hEq : l' z = r' (d y) := by
      rw [hz, ← Scheme.Hom.comp_apply r p, hR, Scheme.Hom.comp_apply]
    obtain ⟨w, _, hw⟩ := (inl_eq_inr_iff f' g' z (d y)).mp hEq
    obtain ⟨w₀, _, hw₀⟩ := Scheme.exists_preimage_of_isPullback hr w y hw
    refine ⟨f w₀, ?_⟩
    rw [← Scheme.Hom.comp_apply f l, show f ≫ l = g ≫ r from pushout.condition,
      Scheme.Hom.comp_apply, hw₀]
  · rintro ⟨y, rfl⟩
    refine ⟨b y, ?_⟩
    rw [← Scheme.Hom.comp_apply b l', ← hL, Scheme.Hom.comp_apply]

theorem isPullback_inr :
    IsPullback d (pushout.inr f g) (pushout.inr f' g') (map f g f' g' a b d hl hr) := by
  have hMap : map g f g' f' a d b hr hl ≫ (pushoutSymmetry g' f').hom =
      (pushoutSymmetry g f).hom ≫ map f g f' g' a b d hl hr := by
    apply pushout.hom_ext <;> simp
  exact (isPullback_inl g f g' f' a d b hr hl).of_iso (Iso.refl _) (Iso.refl _)
    (pushoutSymmetry g f) (pushoutSymmetry g' f') (by simp) (by simp) (by simp) hMap

private theorem affine_restrict_opensRange {P Q L M : Scheme.{u}}
    (m : P ⟶ Q) (p : L ⟶ P) (q : M ⟶ Q) (s : L ⟶ M)
    [IsOpenImmersion q] [IsAffineHom s] (hs : IsPullback s p q m) :
    IsAffineHom (m ∣_ q.opensRange) := by
  have h : IsAffineHom (hs.flip.isoPullback.hom ≫ pullback.snd m q) :=
    hs.flip.isoPullback_hom_snd.symm ▸ (inferInstance : IsAffineHom s)
  rw [MorphismProperty.arrow_mk_iso_iff (P := @IsAffineHom) (morphismRestrictOpensRange m q)]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsAffineHom) hs.flip.isoPullback.hom _).mp h

/-- Affine chart transitions glue to an affine transition when the overlap
squares are pullbacks. -/
theorem isAffineHom_map [IsAffineHom b] [IsAffineHom d] :
    IsAffineHom (map f g f' g' a b d hl hr) := by
  let p := map f g f' g' a b d hl hr
  let l := pushout.inl f' g'
  let r := pushout.inr f' g'
  let : IsOpenImmersion l := inferInstanceAs (IsOpenImmersion (colimit.ι (span f' g') WalkingSpan.left))
  let : IsOpenImmersion r := inferInstanceAs (IsOpenImmersion (colimit.ι (span f' g') WalkingSpan.right))
  let U : Bool → (pushout f' g').Opens := fun j => if j then r.opensRange else l.opensRange
  have hU : iSup U = ⊤ := top_unique (fun x _ => by
    have hx : x ∈ Set.range l ∪ Set.range r := (union_range f' g').ge (Set.mem_univ x)
    rcases hx with h | h
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨false, h⟩
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨true, h⟩)
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsAffineHom) U hU]
  intro j
  cases j
  · exact affine_restrict_opensRange p (pushout.inl f g) l b (isPullback_inl f g f' g' a b d hl hr)
  · exact affine_restrict_opensRange p (pushout.inr f g) r d (isPullback_inr f g f' g' a b d hl hr)

end Transition

end PhilipponOpenGluingPoints

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponLimitChartComparison

universe u

private def chartIso {V W X Y : Scheme.{u}} {q : V ⟶ W} {a : V ⟶ X}
    {b : W ⟶ Y} {p : X ⟶ Y} [IsOpenImmersion a] [IsOpenImmersion b]
    (h : IsPullback q a b p) : V ≅ (p ⁻¹ᵁ b.opensRange).toScheme :=
  IsOpenImmersion.isoOfRangeEq a (p ⁻¹ᵁ b.opensRange).ι (by
    rw [Scheme.Opens.range_ι]
    change Set.range a = p ⁻¹' Set.range b
    simpa only [Set.preimage_univ, Set.image_univ] using
      Scheme.image_preimage_eq_of_isPullback h Set.univ)

@[reassoc]
private theorem chartIso_hom_ι {V W X Y : Scheme.{u}} {q : V ⟶ W} {a : V ⟶ X}
    {b : W ⟶ Y} {p : X ⟶ Y} [IsOpenImmersion a] [IsOpenImmersion b]
    (h : IsPullback q a b p) : (chartIso h).hom ≫ (p ⁻¹ᵁ b.opensRange).ι = a :=
  IsOpenImmersion.isoOfRangeEq_hom_fac ..

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D V : I ⥤ Scheme.{u}}
    (c : Cone D) (v : Cone V) (a : V ⟶ D) [∀ i, IsOpenImmersion (a.app i)]

/-- A cartesian diagram of open immersions identifies with the diagram of
inverse images of any one of its stage opens. -/
def chartLimit (hv : IsLimit v) (m : v.pt ⟶ c.pt) [IsOpenImmersion m]
    (hTrans : ∀ {i j : I} (f : i ⟶ j), IsPullback (V.map f) (a.app i) (a.app j) (D.map f))
    (hCone : ∀ i, IsPullback (v.π.app i) m (a.app i) (c.π.app i)) (i : I) :
    IsLimit (opensCone D c i (a.app i).opensRange) := by
  let U := (a.app i).opensRange
  let e : Over.forget i ⋙ V ≅ opensDiagram D i U :=
    NatIso.ofComponents (fun j => chartIso (hTrans j.hom)) (by
      intro j k f
      apply (cancel_mono (D.map k.hom ⁻¹ᵁ U).ι).mp
      change (V.map f.left ≫ (chartIso (hTrans k.hom)).hom) ≫ (D.map k.hom ⁻¹ᵁ U).ι =
        ((chartIso (hTrans j.hom)).hom ≫ (opensDiagram D i U).map f) ≫
          (D.map k.hom ⁻¹ᵁ U).ι
      have hRes : (opensDiagram D i U).map f ≫ (D.map k.hom ⁻¹ᵁ U).ι =
          (D.map j.hom ⁻¹ᵁ U).ι ≫ D.map f.left :=
        Scheme.Hom.resLE_comp_ι ..
      rw [Category.assoc, chartIso_hom_ι, Category.assoc, hRes, ← Category.assoc, chartIso_hom_ι]
      exact a.naturality f.left)
  let hWhisker := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) v).symm hv
  let hE := (IsLimit.postcomposeHomEquiv e (v.whisker (Over.forget i))).symm hWhisker
  refine hE.ofIsoLimit (Cone.ext (chartIso (hCone i)) fun j => ?_)
  apply (cancel_mono (D.map j.hom ⁻¹ᵁ U).ι).mp
  change (v.π.app j.left ≫ (chartIso (hTrans j.hom)).hom) ≫ (D.map j.hom ⁻¹ᵁ U).ι =
    ((chartIso (hCone i)).hom ≫ (opensCone D c i U).π.app j) ≫ (D.map j.hom ⁻¹ᵁ U).ι
  have hRes : (opensCone D c i U).π.app j ≫ (D.map j.hom ⁻¹ᵁ U).ι =
      (c.π.app i ⁻¹ᵁ U).ι ≫ c.π.app j.left :=
    Scheme.Hom.resLE_comp_ι ..
  rw [Category.assoc, chartIso_hom_ι, Category.assoc, hRes, ← Category.assoc, chartIso_hom_ι]
  exact (hCone j.left).w

end PhilipponLimitChartComparison

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace PhilipponLimitFromOpenCover

universe u v

variable {I : Type u} [Category.{u} I]
    {D : I ⥤ Scheme.{u}} (c : Cone D) (i : I)

private theorem leg_comp_ι (U : (D.obj i).Opens) (j : Over i) :
    (opensCone D c i U).π.app j ≫ (D.map j.hom ⁻¹ᵁ U).ι =
      (c.π.app i ⁻¹ᵁ U).ι ≫ c.π.app j.left :=
  Scheme.Hom.resLE_comp_ι ..

private theorem eq_of_image_subset (U : (D.obj i).Opens)
    (h : IsLimit (opensCone D c i U)) {T : Scheme.{u}} (a b : T ⟶ c.pt)
    (hb : Set.range b ⊆ (c.π.app i ⁻¹ᵁ U).1)
    (he : ∀ j : Over i, a ≫ c.π.app j.left = b ≫ c.π.app j.left) : a = b := by
  let W := c.π.app i ⁻¹ᵁ U
  have hi : a ≫ c.π.app i = b ≫ c.π.app i := he (Over.mk (𝟙 i))
  have ha : Set.range a ⊆ W.1 := by
    rintro _ ⟨x, rfl⟩
    have hx : c.π.app i (a x) = c.π.app i (b x) :=
      (Scheme.Hom.comp_apply a (c.π.app i) x).symm.trans
        ((congrArg (fun f : T ⟶ D.obj i => f x) hi).trans
          (Scheme.Hom.comp_apply b (c.π.app i) x))
    change c.π.app i (a x) ∈ U
    rw [hx]
    exact hb ⟨x, rfl⟩
  let a' := IsOpenImmersion.lift W.ι a (by rw [Scheme.Opens.range_ι]; exact ha)
  let b' := IsOpenImmersion.lift W.ι b (by rw [Scheme.Opens.range_ι]; exact hb)
  have hA : a' ≫ W.ι = a := IsOpenImmersion.lift_fac ..
  have hB : b' ≫ W.ι = b := IsOpenImmersion.lift_fac ..
  have hEqual : a' = b' := by
    apply h.hom_ext
    intro j
    rw [← cancel_mono (D.map j.hom ⁻¹ᵁ U).ι, Category.assoc, Category.assoc, leg_comp_ι,
      ← Category.assoc, ← Category.assoc b', hA, hB]
    exact he j
  rw [← hA, ← hB, hEqual]

variable {J : Type v} (U : J → (D.obj i).Opens)
    (hU : ∀ x, IsLimit (opensCone D c i (U x))) (t : Cone D)

private def fromChart (x : J) : (t.π.app i ⁻¹ᵁ U x).toScheme ⟶ c.pt :=
  (hU x).lift (opensCone D t i (U x)) ≫ (c.π.app i ⁻¹ᵁ U x).ι

private theorem fromChart_fac (x : J) (j : Over i) :
    fromChart c i U hU t x ≫ c.π.app j.left = (t.π.app i ⁻¹ᵁ U x).ι ≫ t.π.app j.left := by
  have hEq := (hU x).fac (opensCone D t i (U x)) j
  calc
    _ = ((hU x).lift (opensCone D t i (U x)) ≫ (opensCone D c i (U x)).π.app j) ≫
        (D.map j.hom ⁻¹ᵁ U x).ι := by
      rw [Category.assoc, leg_comp_ι]
      exact Category.assoc _ _ _
    _ = _ := by rw [hEq, leg_comp_ι]

private theorem fromChart_range (x : J) :
    Set.range (fromChart c i U hU t x) ⊆ (c.π.app i ⁻¹ᵁ U x).1 := by
  rintro _ ⟨s, rfl⟩
  exact ((hU x).lift (opensCone D t i (U x)) s).2

private theorem fromChart_compatible (x y : J) :
    pullback.fst (t.π.app i ⁻¹ᵁ U x).ι (t.π.app i ⁻¹ᵁ U y).ι ≫ fromChart c i U hU t x =
      pullback.snd (t.π.app i ⁻¹ᵁ U x).ι (t.π.app i ⁻¹ᵁ U y).ι ≫ fromChart c i U hU t y := by
  apply eq_of_image_subset c i (U y) (hU y)
  · rintro _ ⟨s, rfl⟩
    exact fromChart_range c i U hU t y
      ⟨pullback.snd (t.π.app i ⁻¹ᵁ U x).ι (t.π.app i ⁻¹ᵁ U y).ι s,
        (Scheme.Hom.comp_apply _ _ _).symm⟩
  · intro j
    rw [Category.assoc, Category.assoc, fromChart_fac c i U hU t x j,
      fromChart_fac c i U hU t y j, ← Category.assoc, ← Category.assoc, pullback.condition]

variable (hCover : IsOpenCover U)

private def sourceCover : t.pt.OpenCover :=
  t.pt.openCoverOfIsOpenCover (fun j => t.π.app i ⁻¹ᵁ U j)
    (hCover.comap (t.π.app i).base.hom)

private def liftFromCover : t.pt ⟶ c.pt :=
  (sourceCover i U t hCover).glueMorphisms (fromChart c i U hU t)
    (fromChart_compatible c i U hU t)

private theorem ι_liftFromCover (x : J) :
    (t.π.app i ⁻¹ᵁ U x).ι ≫ liftFromCover c i U hU t hCover =
      fromChart c i U hU t x :=
  Scheme.Cover.ι_glueMorphisms (sourceCover i U t hCover) _ _ x

private theorem liftFromCover_fac_over (j : Over i) :
    liftFromCover c i U hU t hCover ≫ c.π.app j.left = t.π.app j.left := by
  apply (sourceCover i U t hCover).hom_ext
  intro x
  change (t.π.app i ⁻¹ᵁ U x).ι ≫ liftFromCover c i U hU t hCover ≫ c.π.app j.left = _
  rw [← Category.assoc, ι_liftFromCover, fromChart_fac]
  rfl

variable [IsCofiltered I]

private theorem liftFromCover_fac (j : I) :
    liftFromCover c i U hU t hCover ≫ c.π.app j = t.π.app j := by
  obtain ⟨k, v, w, _⟩ := IsCofilteredOrEmpty.cone_objs i j
  have hk := liftFromCover_fac_over c i U hU t hCover (Over.mk v)
  rw [← c.w w, ← t.w w, ← Category.assoc]
  exact congrArg (fun a : t.pt ⟶ D.obj k => a ≫ D.map w) hk

/-- To establish a cofiltered limit of schemes, it suffices to establish the
limits on the inverse images of an open cover at a single stage. -/
def isLimit : IsLimit c where
  lift t := liftFromCover c i U hU t hCover
  fac t j := liftFromCover_fac c i U hU t hCover j
  uniq t m hm := by
    apply (sourceCover i U t hCover).hom_ext
    intro x
    change (t.π.app i ⁻¹ᵁ U x).ι ≫ m =
      (t.π.app i ⁻¹ᵁ U x).ι ≫ liftFromCover c i U hU t hCover
    rw [ι_liftFromCover]
    apply eq_of_image_subset c i (U x) (hU x) _ _ (fromChart_range c i U hU t x)
    intro j
    rw [Category.assoc, hm, fromChart_fac]

end PhilipponLimitFromOpenCover

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace PhilipponGluedSchemeLimit

universe u

/-- Two diagrams of schemes connected along compatible open subschemes. -/
structure Charts (I : Type u) [Category.{u} I] where
  overlap : I ⥤ Scheme.{u}
  left : I ⥤ Scheme.{u}
  right : I ⥤ Scheme.{u}
  inLeft : overlap ⟶ left
  inRight : overlap ⟶ right
  leftOpen : ∀ i, IsOpenImmersion (inLeft.app i)
  rightOpen : ∀ i, IsOpenImmersion (inRight.app i)
  leftCart : ∀ {i j} (v : i ⟶ j),
    IsPullback (overlap.map v) (inLeft.app i) (inLeft.app j) (left.map v)
  rightCart : ∀ {i j} (v : i ⟶ j),
    IsPullback (overlap.map v) (inRight.app i) (inRight.app j) (right.map v)

variable {I : Type u} [Category.{u} I] (s : Charts I)

instance (i : I) : IsOpenImmersion (s.inLeft.app i) := s.leftOpen i
instance (i : I) : IsOpenImmersion (s.inRight.app i) := s.rightOpen i

private abbrev glued (i : I) := pushout (s.inLeft.app i) (s.inRight.app i)

private def transition {i j : I} (v : i ⟶ j) : glued s i ⟶ glued s j :=
  PhilipponOpenGluingPoints.map _ _ _ _ _ _ _ (s.leftCart v) (s.rightCart v)

/-- The diagram taking the pushout of the two charts at each stage. -/
def diagram : I ⥤ Scheme.{u} where
  obj := glued s
  map := transition s
  map_id i := by
    apply pushout.hom_ext <;> simp [transition]
  map_comp v w := by
    apply pushout.hom_ext <;> simp [transition]

instance {i j : I} (v : i ⟶ j) [IsAffineHom (s.left.map v)] [IsAffineHom (s.right.map v)] :
    IsAffineHom ((diagram s).map v) :=
  PhilipponOpenGluingPoints.isAffineHom_map _ _ _ _ _ _ _ (s.leftCart v) (s.rightCart v)

def leftInclusion : s.left ⟶ diagram s where
  app i := pushout.inl (s.inLeft.app i) (s.inRight.app i)
  naturality _ _ v := (PhilipponOpenGluingPoints.inl_map _ _ _ _ _ _ _ (s.leftCart v) (s.rightCart v)).symm

def rightInclusion : s.right ⟶ diagram s where
  app i := pushout.inr (s.inLeft.app i) (s.inRight.app i)
  naturality _ _ v := (PhilipponOpenGluingPoints.inr_map _ _ _ _ _ _ _ (s.leftCart v) (s.rightCart v)).symm

instance (i : I) : IsOpenImmersion ((leftInclusion s).app i) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span (s.inLeft.app i) (s.inRight.app i)) WalkingSpan.left))

instance (i : I) : IsOpenImmersion ((rightInclusion s).app i) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span (s.inLeft.app i) (s.inRight.app i)) WalkingSpan.right))

theorem left_cartesian {i j : I} (v : i ⟶ j) :
    IsPullback (s.left.map v) ((leftInclusion s).app i) ((leftInclusion s).app j) ((diagram s).map v) :=
  PhilipponOpenGluingPoints.isPullback_inl _ _ _ _ _ _ _ (s.leftCart v) (s.rightCart v)

theorem right_cartesian {i j : I} (v : i ⟶ j) :
    IsPullback (s.right.map v) ((rightInclusion s).app i) ((rightInclusion s).app j) ((diagram s).map v) :=
  PhilipponOpenGluingPoints.isPullback_inr _ _ _ _ _ _ _ (s.leftCart v) (s.rightCart v)

variable {w : Cone s.overlap} {l : Cone s.left} {r : Cone s.right}
    (p : w.pt ⟶ l.pt) (q : w.pt ⟶ r.pt) [IsOpenImmersion p] [IsOpenImmersion q]
    (hp : ∀ i, IsPullback (w.π.app i) p (s.inLeft.app i) (l.π.app i))
    (hq : ∀ i, IsPullback (w.π.app i) q (s.inRight.app i) (r.π.app i))

/-- The cone on the glued diagram whose vertex glues the two chart vertices. -/
def cone : Cone (diagram s) where
  pt := pushout p q
  π :=
    { app i := PhilipponOpenGluingPoints.map _ _ _ _ _ _ _ (hp i) (hq i)
      naturality i j v := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        apply pushout.hom_ext
        · simp only [diagram, transition, PhilipponOpenGluingPoints.inl_map,
            PhilipponOpenGluingPoints.inl_map_assoc, l.w_assoc]
        · simp only [diagram, transition, PhilipponOpenGluingPoints.inr_map,
            PhilipponOpenGluingPoints.inr_map_assoc, r.w_assoc] }

theorem left_cone_cartesian (i : I) :
    IsPullback (l.π.app i) (pushout.inl p q) ((leftInclusion s).app i) ((cone s p q hp hq).π.app i) :=
  PhilipponOpenGluingPoints.isPullback_inl _ _ _ _ _ _ _ (hp i) (hq i)

theorem right_cone_cartesian (i : I) :
    IsPullback (r.π.app i) (pushout.inr p q) ((rightInclusion s).app i) ((cone s p q hp hq).π.app i) :=
  PhilipponOpenGluingPoints.isPullback_inr _ _ _ _ _ _ _ (hp i) (hq i)

/-- A cofiltered limit of such glued schemes is the gluing of the limits of
the two charts, provided the overlap squares remain cartesian at the limit. -/
def isLimit [IsCofiltered I] (hl : IsLimit l) (hr : IsLimit r) :
    IsLimit (cone s p q hp hq) := by
  let i : I := (IsCofiltered.nonempty (C := I)).some
  let c := cone s p q hp hq
  let U : Bool → ((diagram s).obj i).Opens := fun j =>
    if j then ((rightInclusion s).app i).opensRange else ((leftInclusion s).app i).opensRange
  have hU : IsOpenCover U := top_unique (fun x _ => by
    have hx : x ∈ Set.range ((leftInclusion s).app i) ∪ Set.range ((rightInclusion s).app i) :=
      (PhilipponOpenGluingPoints.union_range (s.inLeft.app i) (s.inRight.app i)).ge (Set.mem_univ x)
    rcases hx with h | h
    · exact Opens.mem_iSup.mpr ⟨false, h⟩
    · exact Opens.mem_iSup.mpr ⟨true, h⟩)
  let : IsOpenImmersion (pushout.inl p q) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (span p q) WalkingSpan.left))
  let : IsOpenImmersion (pushout.inr p q) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (span p q) WalkingSpan.right))
  refine PhilipponLimitFromOpenCover.isLimit c i U (fun j => ?_) hU
  cases j
  · exact PhilipponLimitChartComparison.chartLimit c l (leftInclusion s) hl (pushout.inl p q)
      (left_cartesian s) (left_cone_cartesian s p q hp hq) i
  · exact PhilipponLimitChartComparison.chartLimit c r (rightInclusion s) hr (pushout.inr p q)
      (right_cartesian s) (right_cone_cartesian s p q hp hq) i

end PhilipponGluedSchemeLimit

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponAbsoluteModels


namespace PhilipponAssembleAffineChart

universe u

private theorem compact_glued {W X Y : Scheme.{u}} (p : W ⟶ X) (q : W ⟶ Y)
    [IsOpenImmersion p] [IsOpenImmersion q] [CompactSpace X] [CompactSpace Y] :
    CompactSpace (pushout p q : Scheme.{u}) :=
  ⟨(PhilipponOpenGluingPoints.union_range p q) ▸
    (isCompact_range (pushout.inl p q).continuous).union (isCompact_range (pushout.inr p q).continuous)⟩

private theorem finiteType_glued {W X Y : Scheme.{u}} (p : W ⟶ X) (q : W ⟶ Y)
    [IsOpenImmersion p] [IsOpenImmersion q] [LocallyOfFiniteType (toBase W)]
    [LocallyOfFiniteType (toBase X)] [LocallyOfFiniteType (toBase Y)] :
    LocallyOfFiniteType (toBase (pushout p q)) := by
  let C := Scheme.IsLocallyDirected.openCover (span p q)
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType) C]
  intro i
  rw [comp_toBase]
  cases i with
  | none => exact inferInstanceAs (LocallyOfFiniteType (toBase W))
  | some i =>
    cases i
    · exact inferInstanceAs (LocallyOfFiniteType (toBase X))
    · exact inferInstanceAs (LocallyOfFiniteType (toBase Y))

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
    {W V : I ⥤ Scheme.{u}} {w : Cone W} {v : Cone V} {B : CommRingCat.{u}}
    [∀ i, (W.obj i).IsQuasiAffine] [∀ i, LocallyOfFiniteType (toBase (W.obj i))]
    [∀ i, QuasiSeparatedSpace (W.obj i)]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (W.map a)]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (V.map a)]
    [∀ i, LocallyOfFiniteType (toBase (V.obj i))] [∀ i, CompactSpace (V.obj i)]
    (p : w.pt ⟶ v.pt) (q : w.pt ⟶ Spec B) [IsOpenImmersion p] [IsOpenImmersion q]
    (a : W ⟶ V) [∀ i, IsOpenImmersion (a.app i)]

/-- The refined affine charts and the original stages give an absolute
approximation of the glued scheme. -/
theorem nonempty_models (hw : IsLimit w) (hv : IsLimit v)
    (hLeg : ∀ i, IsPullback (w.π.app i) p (a.app i) (v.π.app i))
    (hMap : ∀ {i j : I} (u : i ⟶ j), IsPullback (W.map u) (a.app i) (a.app j) (V.map u))
    (d : PhilipponRefinedAffineChart.Denominators q) :
    Nonempty (Models (pushout p q)) := by
  let α := PhilipponRefinedAffineChart.projection d
  let s : PhilipponGluedSchemeLimit.Charts (PhilipponRefinedAffineChart.Index d) :=
    { overlap := α ⋙ W
      left := α ⋙ V
      right := PhilipponRefinedAffineChart.diagram d
      inLeft := Functor.whiskerLeft α a
      inRight := PhilipponRefinedAffineChart.inChart d
      leftOpen i := inferInstanceAs (IsOpenImmersion (a.app (α.obj i)))
      rightOpen _ := inferInstance
      leftCart u := hMap (α.map u)
      rightCart u := PhilipponRefinedAffineChart.isPullback_map d u }
  let w' : Cone s.overlap := w.whisker α
  let v' : Cone s.left := v.whisker α
  let r' : Cone s.right := PhilipponRefinedAffineChart.cone d
  have hLeg' (i : PhilipponRefinedAffineChart.Index d) :
      IsPullback (w'.π.app i) p (s.inLeft.app i) (v'.π.app i) := hLeg (α.obj i)
  have hRight (i : PhilipponRefinedAffineChart.Index d) :
      IsPullback (w'.π.app i) q (s.inRight.app i) (r'.π.app i) :=
    PhilipponRefinedAffineChart.isPullback_leg d i
  let c := PhilipponGluedSchemeLimit.cone s (w := w') (l := v') (r := r') p q hLeg' hRight
  let hv' : IsLimit v' := (Functor.Initial.isLimitWhiskerEquiv α v).symm hv
  let hr' : IsLimit r' := PhilipponRefinedAffineChart.isLimit d hw
  let hc : IsLimit c :=
    PhilipponGluedSchemeLimit.isLimit s (w := w') (l := v') (r := r') p q hLeg' hRight hv' hr'
  refine ⟨⟨_, inferInstance, inferInstance, PhilipponGluedSchemeLimit.diagram s, c, hc, Iso.refl _, ?_, ?_, ?_⟩⟩
  · intro i j u
    let : IsAffineHom (s.left.map u) := inferInstanceAs (IsAffineHom (V.map (α.map u)))
    let : IsAffine ((s.right).obj i) := inferInstanceAs (IsAffine ((PhilipponRefinedAffineChart.diagram d).obj i))
    let : IsAffine ((s.right).obj j) := inferInstanceAs (IsAffine ((PhilipponRefinedAffineChart.diagram d).obj j))
    let : IsAffineHom (s.right.map u) := isAffineHom_of_isAffine _
    infer_instance
  · intro i
    let := s.leftOpen i
    let := s.rightOpen i
    let : CompactSpace (s.left.obj i) := inferInstanceAs (CompactSpace (V.obj (α.obj i)))
    let : IsAffine ((s.right).obj i) := inferInstanceAs (IsAffine ((PhilipponRefinedAffineChart.diagram d).obj i))
    exact compact_glued (s.inLeft.app i) (s.inRight.app i)
  · intro i
    let := s.leftOpen i
    let := s.rightOpen i
    let : LocallyOfFiniteType (toBase (s.overlap.obj i)) :=
      inferInstanceAs (LocallyOfFiniteType (toBase (W.obj (α.obj i))))
    let : LocallyOfFiniteType (toBase (s.left.obj i)) :=
      inferInstanceAs (LocallyOfFiniteType (toBase (V.obj (α.obj i))))
    let : LocallyOfFiniteType (toBase (s.right.obj i)) := PhilipponRefinedAffineChart.finiteType d i
    exact finiteType_glued (s.inLeft.app i) (s.inRight.app i)

end PhilipponAssembleAffineChart

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponAbsoluteModels


namespace PhilipponAppendAffineChart

universe u

private theorem cartesian_opensDiagram {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (i : I) (U : (D.obj i).Opens) {j k : Over i} (f : j ⟶ k) :
    IsPullback ((opensDiagram D i U).map f) ((opensDiagramι D i U).app j)
      ((opensDiagramι D i U).app k) ((Over.forget i ⋙ D).map f) := by
  refine IsOpenImmersion.isPullback _ _ _ _ ((opensDiagramι D i U).naturality f).symm ?_
  change D.map f.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ U).ι.opensRange = (D.map j.hom ⁻¹ᵁ U).ι.opensRange
  rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, ← Scheme.Hom.comp_preimage,
    ← Functor.map_comp, Over.w]

private theorem cartesian_opensCone {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I) (U : (D.obj i).Opens) (j : Over i) :
    IsPullback ((opensCone D c i U).π.app j) (c.π.app i ⁻¹ᵁ U).ι
      ((opensDiagramι D i U).app j) ((c.whisker (Over.forget i)).π.app j) := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · exact (Scheme.Hom.resLE_comp_ι ..).symm
  · change c.π.app j.left ⁻¹ᵁ (D.map j.hom ⁻¹ᵁ U).ι.opensRange = (c.π.app i ⁻¹ᵁ U).ι.opensRange
    rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, ← Scheme.Hom.comp_preimage, c.w]

/-- A quasi-compact overlap with an affine scheme allows that affine chart
to be attached to an absolute approximation. -/
theorem nonempty_models {V : Scheme.{u}} (M : Models V)
    (U : V.Opens) [CompactSpace U.toScheme] {B : CommRingCat.{u}} (q : U.toScheme ⟶ Spec B)
    [IsOpenImmersion q] : Nonempty (Models (pushout U.ι q)) := by
  let D := M.diagram
  let c := M.onScheme
  let hc := M.onSchemeLimit
  let : ∀ {i j : M.index} (a : i ⟶ j), IsAffineHom (D.map a) := @M.affine
  let : ∀ i, CompactSpace (D.obj i) := M.compact
  let : ∀ i, LocallyOfFiniteType (toBase (D.obj i)) := M.finiteType
  have hU : IsCompact (U : Set V) := by
    rw [← Scheme.Opens.range_ι]
    exact isCompact_range U.ι.continuous
  obtain ⟨i, Vᵢ, hVᵢ, he⟩ := exists_preimage_eq D c hc U hU
  let E := opensDiagram D i Vᵢ
  let w := opensCone D c i Vᵢ
  let hW := isLimitOpensCone D c hc i Vᵢ
  let p : w.pt ⟶ V := (c.π.app i ⁻¹ᵁ Vᵢ).ι
  let iso : w.pt ≅ U.toScheme := V.isoOfEq he
  let q' := iso.hom ≫ q
  let : IsOpenImmersion p := inferInstanceAs (IsOpenImmersion (c.π.app i ⁻¹ᵁ Vᵢ).ι)
  let : IsOpenImmersion q' := inferInstanceAs (IsOpenImmersion (iso.hom ≫ q))
  let : CompactSpace w.pt := iso.inv.homeomorph.compactSpace
  let : w.pt.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion q'
  let : ∀ {j k : Over i} (u : j ⟶ k), IsAffineHom (E.map u) := fun u =>
    inferInstanceAs (IsAffineHom ((opensDiagram D i Vᵢ).map u))
  let : ∀ j : Over i, CompactSpace (E.obj j) := fun j =>
    isCompact_iff_compactSpace.mp ((D.map j.hom).isCompact_preimage hVᵢ)
  let : ∀ j : Over i, LocallyOfFiniteType (toBase (E.obj j)) := fun j => by
    change LocallyOfFiniteType (toBase (D.map j.hom ⁻¹ᵁ Vᵢ).toScheme)
    rw [← comp_toBase (D.map j.hom ⁻¹ᵁ Vᵢ).ι]
    infer_instance
  let : ∀ j : Over i, QuasiSeparatedSpace (E.obj j) := fun j => by
    let : IsLocallyNoetherian (E.obj j) := LocallyOfFiniteType.isLocallyNoetherian (toBase (E.obj j))
    infer_instance
  obtain ⟨j, hj⟩ := Scheme.exists_isQuasiAffine_of_isLimit E w hW
  let F := Over.forget j ⋙ E
  let w₁ := w.whisker (Over.forget j)
  let hw₁ := (Functor.Initial.isLimitWhiskerEquiv (Over.forget j) w).symm hW
  let : w₁.pt.IsQuasiAffine := inferInstanceAs (w.pt.IsQuasiAffine)
  let : ∀ {a b : Over j} (u : a ⟶ b), IsAffineHom (F.map u) := fun u =>
    inferInstanceAs (IsAffineHom (E.map u.left))
  let : ∀ a : Over j, QuasiSeparatedSpace (F.obj a) := fun a =>
    inferInstanceAs (QuasiSeparatedSpace (E.obj a.left))
  let _ := hj
  let : ∀ a : Over j, (F.obj a).IsQuasiAffine := fun a => Scheme.IsQuasiAffine.of_isAffineHom (E.map a.hom)
  obtain ⟨t, ht, hTop, hLoc⟩ := PhilipponOverlapAffineChart.exists_denominators q'
  let r (x : ↥t) := PhilipponOverlapAffineChart.ringMap q' x.1
  obtain ⟨k, s, hs, hStage⟩ := PhilipponOverlapStageBasicOpens.exists_stage F w₁ hw₁ r hTop
  let ρ := Over.forget k ⋙ Over.forget j
  let τ := ρ ⋙ Over.forget i
  let G := ρ ⋙ E
  let H := τ ⋙ D
  let w₂ : Cone G := (w₁.whisker (Over.forget k))
  let v₂ : Cone H := (c.whisker (Over.forget i)).whisker ρ
  let hw₂ := (Functor.Initial.isLimitWhiskerEquiv (Over.forget k) w₁).symm hw₁
  let hv₂ := (Functor.Initial.isLimitWhiskerEquiv τ c).symm hc
  let a : G ⟶ H := Functor.whiskerLeft ρ (opensDiagramι D i Vᵢ)
  let : ∀ b : Over k, (G.obj b).IsQuasiAffine := fun b =>
    inferInstanceAs ((F.obj b.left).IsQuasiAffine)
  let : ∀ b : Over k, QuasiSeparatedSpace (G.obj b) := fun b =>
    inferInstanceAs (QuasiSeparatedSpace (E.obj (ρ.obj b)))
  let : ∀ b : Over k, LocallyOfFiniteType (toBase (G.obj b)) := fun b =>
    inferInstanceAs (LocallyOfFiniteType (toBase (E.obj (ρ.obj b))))
  let : ∀ b : Over k, LocallyOfFiniteType (toBase (H.obj b)) := fun b =>
    inferInstanceAs (LocallyOfFiniteType (toBase (D.obj (τ.obj b))))
  let : ∀ b : Over k, CompactSpace (H.obj b) := fun b =>
    inferInstanceAs (CompactSpace (D.obj (τ.obj b)))
  let : ∀ b : Over k, IsOpenImmersion (a.app b) := fun b =>
    inferInstanceAs (IsOpenImmersion ((opensDiagramι D i Vᵢ).app (ρ.obj b)))
  let : ∀ {b b' : Over k} (f : b ⟶ b'), IsAffineHom (G.map f) := fun f =>
    inferInstanceAs (IsAffineHom (E.map (ρ.map f)))
  let : ∀ {b b' : Over k} (f : b ⟶ b'), IsAffineHom (H.map f) := fun f =>
    inferInstanceAs (IsAffineHom (D.map (τ.map f)))
  let d : PhilipponRefinedAffineChart.Denominators (w := w₂) q' :=
    { elements := t
      coeff b x := (F.map b.hom).appTop (s x)
      map_coeff u x := by
        change (F.map u.left).appTop ((F.map _).appTop (s x)) = _
        rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, ← Functor.map_comp, Over.w]
      limit_coeff b x := by
        change r x = (w₁.π.app b.left).appTop ((F.map b.hom).appTop (s x))
        rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, w₁.w]
        exact (hs x).symm
      stage_cover b := by
        change (F.obj b.left).toSpecΓ.opensRange = _
        rw [← Scheme.preimage_opensRange_toSpecΓ (F.map b.hom), hStage, Scheme.Hom.preimage_iSup]
        rfl
      limit_cover := ht
      localization := hLoc }
  obtain ⟨N⟩ := PhilipponAssembleAffineChart.nonempty_models (w := w₂) (v := v₂) p q' a
    hw₂ hv₂ (fun b => cartesian_opensCone D c i Vᵢ (ρ.obj b))
    (fun f => cartesian_opensDiagram D i Vᵢ (ρ.map f)) d
  have hP : p ≫ 𝟙 V = iso.hom ≫ U.ι := by
    rw [Category.comp_id]
    exact (V.isoOfEq_hom_ι he).symm
  have hQ : q' ≫ 𝟙 (Spec B) = iso.hom ≫ q := Category.comp_id _
  let m := pushout.map p q' U.ι q (𝟙 _) (𝟙 _) iso.hom hP hQ
  let : IsIso m := inferInstanceAs (IsIso (pushout.map p q' U.ι q (𝟙 _) (𝟙 _) iso.hom hP hQ))
  exact ⟨N.ofIso (asIso m).symm⟩

end PhilipponAppendAffineChart

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponOpenUnionPushout

universe u

variable {X : Scheme.{u}} (U V : X.Opens)

private abbrev jU : (U ⊓ V).toScheme ⟶ U.toScheme := X.homOfLE inf_le_left
private abbrev jV : (U ⊓ V).toScheme ⟶ V.toScheme := X.homOfLE inf_le_right
private abbrev iU : U.toScheme ⟶ (U ⊔ V).toScheme := X.homOfLE le_sup_left
private abbrev iV : V.toScheme ⟶ (U ⊔ V).toScheme := X.homOfLE le_sup_right

private def chart : Bool → Scheme.{u}
  | false => U.toScheme
  | true => V.toScheme

private def inclusion : ∀ b, chart U V b ⟶ (U ⊔ V).toScheme
  | false => iU U V
  | true => iV U V

private def cover : (U ⊔ V).toScheme.OpenCover where
  I₀ := Bool
  X := chart U V
  f := inclusion U V
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      rcases x.2 with hx | hx
      · exact ⟨false, ⟨⟨x.1, hx⟩, Subtype.ext (Scheme.homOfLE_apply le_sup_left _)⟩⟩
      · exact ⟨true, ⟨⟨x.1, hx⟩, Subtype.ext (Scheme.homOfLE_apply le_sup_right _)⟩⟩
    · intro b
      cases b
      · exact inferInstanceAs (IsOpenImmersion (iU U V))
      · exact inferInstanceAs (IsOpenImmersion (iV U V))

private theorem agree_on_pullback {S A B T Y : Scheme.{u}}
    {j₁ : S ⟶ A} {j₂ : S ⟶ B} {i₁ : A ⟶ T} {i₂ : B ⟶ T}
    (h : IsPullback j₁ j₂ i₁ i₂) (f : A ⟶ Y) (g : B ⟶ Y) (he : j₁ ≫ f = j₂ ≫ g) :
    pullback.fst i₁ i₂ ≫ f = pullback.snd i₁ i₂ ≫ g := by
  rw [← cancel_epi h.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc,
    IsPullback.isoPullback_hom_snd_assoc]
  exact he

private theorem agree_on_self {A T Y : Scheme.{u}} (i : A ⟶ T) [Mono i] (f : A ⟶ Y) :
    pullback.fst i i ≫ f = pullback.snd i i ≫ f := by
  have he : pullback.fst i i = pullback.snd i i := (cancel_mono i).mp pullback.condition
  rw [he]

/-- The union of two open subschemes is the pushout over their intersection. -/
def isoUnion : pushout (jU U V) (jV U V) ≅ (U ⊔ V).toScheme := by
  let h : IsPullback (jU U V) (jV U V) (iU U V) (iV U V) :=
    isPullback_opens_inf_le le_sup_left le_sup_right
  let P := pushout (jU U V) (jV U V)
  let f : P ⟶ (U ⊔ V).toScheme := pushout.desc (iU U V) (iV U V) h.w
  let g : ∀ b : (cover U V).I₀, (cover U V).X b ⟶ P
    | false => pushout.inl _ _
    | true => pushout.inr _ _
  have hg : ∀ b c, pullback.fst ((cover U V).f b) ((cover U V).f c) ≫ g b =
      pullback.snd ((cover U V).f b) ((cover U V).f c) ≫ g c := by
    intro b c
    cases b <;> cases c
    · exact agree_on_self (iU U V) (pushout.inl _ _)
    · exact agree_on_pullback h (pushout.inl _ _) (pushout.inr _ _) pushout.condition
    · exact agree_on_pullback h.flip (pushout.inr _ _) (pushout.inl _ _) pushout.condition.symm
    · exact agree_on_self (iV U V) (pushout.inr _ _)
  let l := (cover U V).glueMorphisms g hg
  refine ⟨f, l, ?_, ?_⟩
  · apply pushout.hom_ext
    · change pushout.inl _ _ ≫ f ≫ l = pushout.inl _ _ ≫ 𝟙 _
      rw [pushout.inl_desc_assoc, Category.comp_id]
      exact (cover U V).ι_glueMorphisms g hg false
    · change pushout.inr _ _ ≫ f ≫ l = pushout.inr _ _ ≫ 𝟙 _
      rw [pushout.inr_desc_assoc, Category.comp_id]
      exact (cover U V).ι_glueMorphisms g hg true
  · apply (cover U V).hom_ext
    intro b
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, Category.comp_id]
    cases b
    · exact pushout.inl_desc _ _ _
    · exact pushout.inr_desc _ _ _

end PhilipponOpenUnionPushout

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponAbsoluteModels


namespace PhilipponAbsoluteApproximation

universe u

private theorem nonempty_models_sup {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (M : Models U.toScheme) : Nonempty (Models (U ⊔ V).toScheme) := by
  let P := U.ι ⁻¹ᵁ V
  let e : P.toScheme ≅ (U ⊓ V).toScheme :=
    U.ι.isoImage P ≪≫ X.isoOfEq ((U.functor_map_eq_inf V).trans (inf_comm V U))
  let j₁ : (U ⊓ V).toScheme ⟶ U.toScheme := X.homOfLE inf_le_left
  let j₂ : (U ⊓ V).toScheme ⟶ V.toScheme := X.homOfLE inf_le_right
  let a : P.toScheme ⟶ V.toScheme := U.ι ∣_ V
  let I := hV.isoSpec
  let q := a ≫ I.hom
  have hC : IsCompact ((U ⊓ V : X.Opens) : Set X) :=
    QuasiSeparatedSpace.inter_isCompact _ _ U.isOpen hU V.isOpen hV.isCompact
  let : CompactSpace (U ⊓ V).toScheme := isCompact_iff_compactSpace.mp hC
  let : CompactSpace P.toScheme := e.inv.homeomorph.compactSpace
  let : IsOpenImmersion q := inferInstanceAs (IsOpenImmersion ((U.ι ∣_ V) ≫ I.hom))
  obtain ⟨N⟩ := PhilipponAppendAffineChart.nonempty_models M P q
  have he : e.hom ≫ (U ⊓ V).ι = P.ι ≫ U.ι := by
    simp [e]
  have h₁ : P.ι ≫ 𝟙 _ = e.hom ≫ j₁ := by
    apply (cancel_mono U.ι).mp
    simpa [j₁] using he.symm
  have h₂ : q ≫ I.inv = e.hom ≫ j₂ := by
    apply (cancel_mono V.ι).mp
    simpa [q, a, j₂] using he.symm
  let g := pushout.map P.ι q j₁ j₂ (𝟙 _) I.inv e.hom h₁ h₂
  let : IsIso g := inferInstanceAs (IsIso (pushout.map P.ι q j₁ j₂ (𝟙 _) I.inv e.hom h₁ h₂))
  exact ⟨N.ofIso ((PhilipponOpenUnionPushout.isoUnion U V).symm ≪≫ (asIso g).symm)⟩

private theorem nonempty_models_finset (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (s : Finset X.affineOpens) :
    let U : X.Opens := s.sup fun V => V.1
    IsCompact (U : Set X) ∧ Nonempty (Models U.toScheme) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    let : IsAffine (⊥ : X.Opens).toScheme := isAffineOpen_bot X
    simpa using And.intro (isCompact_empty (X := X))
      (nonempty_for_affine (⊥ : X.Opens).toScheme)
  | @insert V s hV ih =>
    let U : X.Opens := s.sup fun T => T.1
    change IsCompact (U : Set X) ∧ Nonempty (Models U.toScheme) at ih
    dsimp only
    rw [Finset.sup_insert, sup_comm]
    exact ⟨ih.1.union V.2.isCompact,
      ih.2.elim (nonempty_models_sup U V.1 ih.1 V.2)⟩

theorem nonempty_models (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    Nonempty (Models X) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => (U.1 : Set X)) (fun U => U.1.isOpen)
    (by rw [← Opens.coe_iSup, iSup_affineOpens_eq_top]; exact Set.Subset.rfl)
  have ht : (s.sup fun U : X.affineOpens => U.1) = ⊤ := by
    refine top_unique fun x hx => ?_
    obtain ⟨U, hUs, hxU⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact (Finset.le_sup (f := fun U : X.affineOpens => U.1) hUs) hxU
  have h := (nonempty_models_finset X s).2
  rw [ht] at h
  exact h.elim fun M => ⟨M.ofIso (X.topIso).symm⟩

theorem exists_diagram (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of (ULift.{u} ℤ))) :
    ∃ (I : Type u) (_ : Category.{u} I) (_ : IsCofiltered I)
      (D : I ⥤ Scheme.{u}) (c : Cone D)
      (g : D ⟶ (Functor.const I).obj (Spec (.of (ULift.{u} ℤ)))) (e : X ≅ c.pt),
      Nonempty (IsLimit c) ∧
      (∀ i, e.hom ≫ c.π.app i ≫ g.app i = f) ∧
      (∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)) ∧
      (∀ i, LocallyOfFinitePresentation (g.app i) ∧ QuasiCompact (g.app i) ∧ QuasiSeparated (g.app i)) := by
  obtain ⟨M⟩ := nonempty_models X
  let g : M.diagram ⟶ (Functor.const M.index).obj (integerBase : Scheme.{u}) :=
    { app i := toBase (M.diagram.obj i)
      naturality _ _ _ := specULiftZIsTerminal.hom_ext _ _ }
  refine ⟨M.index, M.category, M.cofiltered, M.diagram, M.cone, g, M.iso, ⟨M.limit⟩,
    fun _ => specULiftZIsTerminal.hom_ext _ _, @M.affine, ?_⟩
  intro i
  change LocallyOfFinitePresentation (toBase (M.diagram.obj i)) ∧
    QuasiCompact (toBase (M.diagram.obj i)) ∧ QuasiSeparated (toBase (M.diagram.obj i))
  let : LocallyOfFiniteType (toBase (M.diagram.obj i)) := M.finiteType i
  let : IsLocallyNoetherian (M.diagram.obj i) :=
    LocallyOfFiniteType.isLocallyNoetherian (toBase (M.diagram.obj i))
  exact ⟨inferInstance, (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr (M.compact i),
    inferInstance⟩

end PhilipponAbsoluteApproximation

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of (ULift.{u} ℤ))) :
    ∃ (I : Type u) (_ : Category.{u} I) (_ : IsCofiltered I)
      (D : I ⥤ Scheme.{u}) (c : Cone D)
      (g : D ⟶ (Functor.const I).obj (Spec (.of (ULift.{u} ℤ)))) (e : X ≅ c.pt),
      Nonempty (IsLimit c) ∧
      (∀ i, e.hom ≫ c.π.app i ≫ g.app i = f) ∧
      (∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)) ∧
      (∀ i, LocallyOfFinitePresentation (g.app i) ∧ QuasiCompact (g.app i) ∧ QuasiSeparated (g.app i)) := by
  exact PhilipponAbsoluteApproximation.exists_diagram X f

end

end
