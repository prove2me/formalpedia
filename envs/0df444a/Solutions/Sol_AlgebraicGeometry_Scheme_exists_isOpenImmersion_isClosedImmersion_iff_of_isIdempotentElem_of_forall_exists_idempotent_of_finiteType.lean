-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3f3a3ed3-1979-553d-972c-85e430b17f97

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace ClopenAux

section Idem

variable {B : Type} [CommRing B]

theorem idem_eq_of_mem_span {e e' : B} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (h1 : 1 - e ∈ Ideal.span ({1 - e'} : Set B)) (h2 : 1 - e' ∈ Ideal.span ({1 - e} : Set B)) : e = e' := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp h2
  have hu : IsIdempotentElem (1 - e) := he.one_sub
  have hu' : IsIdempotentElem (1 - e') := he'.one_sub
  have e1 : (1 - e) * (1 - e') = 1 - e := by
    conv_lhs => rw [← ha]
    rw [mul_assoc, hu'.eq, ha]
  have e2 : (1 - e') * (1 - e) = 1 - e' := by
    conv_lhs => rw [← hb]
    rw [mul_assoc, hu.eq, hb]
  have : (1 : B) - e = 1 - e' := by rw [← e1, mul_comm, e2]
  exact sub_right_injective this

theorem idem_eq_one_of_forall_not_mem {e : B} (he : IsIdempotentElem e)
    (h : ∀ 𝔭 : PrimeSpectrum B, e ∉ 𝔭.asIdeal) : e = 1 := by
  have hnil : IsNilpotent (1 - e) := by
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    have hJ' := h ⟨J, hJ⟩
    have : e * (1 - e) ∈ J := by rw [mul_sub, mul_one, he.eq, sub_self]; exact J.zero_mem
    exact (hJ.mem_or_mem this).resolve_left hJ'
  obtain ⟨n, hn⟩ := hnil
  have hu : IsIdempotentElem (1 - e) := he.one_sub
  have h0 : (1 : B) - e = 0 := by
    cases n with
    | zero =>
        rw [pow_zero] at hn
        calc (1 : B) - e = (1 - e) * 1 := (mul_one _).symm
          _ = 0 := by rw [hn, mul_zero]
    | succ n => rw [hu.pow_succ_eq] at hn; exact hn
  exact (sub_eq_zero.mp h0).symm

theorem idem_not_mem_iff {e : B} (he : IsIdempotentElem e) (𝔭 : PrimeSpectrum B) :
    e ∉ 𝔭.asIdeal ↔ 1 - e ∈ 𝔭.asIdeal := by
  have hprod : e * (1 - e) ∈ 𝔭.asIdeal := by rw [mul_sub, mul_one, he.eq, sub_self]; exact 𝔭.asIdeal.zero_mem
  constructor
  · intro hne; exact (𝔭.isPrime.mem_or_mem hprod).resolve_left hne
  · intro h1 he1
    have : (1 : B) ∈ 𝔭.asIdeal := by
      have := 𝔭.asIdeal.add_mem he1 h1; rwa [add_sub_cancel] at this
    exact 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)

end Idem

section Points

variable (R : Type) [CommRing R] (H : Scheme.{0}) (pH : H ⟶ Spec (CommRingCat.of R))

abbrev Pt (B : Type) [CommRing B] [Algebra R B] : Type :=
  {g : Spec (CommRingCat.of B) ⟶ H // g ≫ pH = Spec.map (CommRingCat.ofHom (algebraMap R B))}

variable {R H pH}

def Pt.map {B B' : Type} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B')
    (g : Pt R H pH B) : Pt R H pH B' :=
  ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g.1, by
    rw [Category.assoc, g.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe,
      AlgHom.comp_algebraMap]⟩

@[scoped simp] theorem Pt.map_val {B B' : Type} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B')
    (g : Pt R H pH B) : (Pt.map φ g).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g.1 := rfl

p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType.ClopenAux.Pt"
theorem Pt.map_comp {B B' B'' : Type} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] [CommRing B'']
    [Algebra R B''] (φ : B →ₐ[R] B') (ψ : B' →ₐ[R] B'') (g : Pt R H pH B) :
    Pt.map (ψ.comp φ) g = Pt.map ψ (Pt.map φ g) := by
  apply Subtype.ext
  simp only [Pt.map_val, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc]

variable (Q : ∀ (B : Type) [CommRing B] [Algebra R B], Pt R H pH B → Prop)

def IsWitness {B : Type} [CommRing B] [Algebra R B] (g : Pt R H pH B) (e : B) : Prop :=
  IsIdempotentElem e ∧ ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'), Q B' (Pt.map φ g) ↔ φ e = 1

variable {Q}

theorem IsWitness.map {B B' : Type} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] {g : Pt R H pH B} {e : B}
    (h : IsWitness Q g e) (φ : B →ₐ[R] B') : IsWitness Q (Pt.map φ g) (φ e) := by
  refine ⟨h.1.map φ.toRingHom.toMonoidHom, fun B'' _ _ ψ => ?_⟩
  rw [← Pt.map_comp, h.2 B'' (ψ.comp φ), AlgHom.comp_apply]

theorem IsWitness.self_iff {B : Type} [CommRing B] [Algebra R B] {g : Pt R H pH B} {e : B}
    (h : IsWitness Q g e) : Q B g ↔ e = 1 := by
  have := h.2 B (AlgHom.id R B)
  have hid : Pt.map (AlgHom.id R B) g = g := by
    apply Subtype.ext
    rw [Pt.map_val]
    change Spec.map (CommRingCat.ofHom (RingHom.id B)) ≫ g.1 = g.1
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  rwa [hid, AlgHom.id_apply] at this

theorem IsWitness.unique {B : Type} [CommRing B] [Algebra R B] {g : Pt R H pH B} {e e' : B}
    (h : IsWitness Q g e) (h' : IsWitness Q g e') : e = e' := by
  have key : ∀ {e e' : B}, IsWitness Q g e → IsWitness Q g e' → 1 - e ∈ Ideal.span ({1 - e'} : Set B) := by
    intro e e' h h'
    let J : Ideal B := Ideal.span ({1 - e'} : Set B)
    have h1 : Ideal.Quotient.mkₐ R J e' = 1 := by
      rw [Ideal.Quotient.mkₐ_eq_mk, ← (Ideal.Quotient.mk J).map_one, Ideal.Quotient.eq]
      have : e' - 1 = -(1 - e') := by ring
      rw [this]; exact J.neg_mem (Ideal.subset_span rfl)
    have h2 : Ideal.Quotient.mkₐ R J e = 1 := (h.2 _ (Ideal.Quotient.mkₐ R J)).mp ((h'.2 _ (Ideal.Quotient.mkₐ R J)).mpr h1)
    rw [Ideal.Quotient.mkₐ_eq_mk, ← (Ideal.Quotient.mk J).map_one, Ideal.Quotient.eq] at h2
    have : 1 - e = -(e - 1) := by ring
    rw [this]; exact J.neg_mem h2
  exact idem_eq_of_mem_span h.1 h'.1 (key h h') (key h' h)

end Points
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType.ClopenAux.Pt"

section Charts

variable {R : Type} [CommRing R] {H : Scheme.{0}} {pH : H ⟶ Spec (CommRingCat.of R)}

theorem exists_algHom_of_range_subset {A C : Type} [CommRing A] [Algebra R A] [CommRing C] [Algebra R C]
    (γ : Pt R H pH A) [IsOpenImmersion γ.1] (γC : Pt R H pH C) (h : Set.range γC.1.base ⊆ Set.range γ.1.base) :
    ∃ τ : A →ₐ[R] C, Pt.map τ γ = γC := by
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (IsOpenImmersion.lift γ.1 γC.1 h)
  have hcomp : Spec.map φ' ≫ γ.1 = γC.1 := by rw [hφ']; exact IsOpenImmersion.lift_fac _ _ _
  have h1 : Spec.map (CommRingCat.ofHom (φ'.hom.comp (algebraMap R A))) =
      Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, ← γ.2, ← Category.assoc, hcomp, γC.2]
  have hR : φ'.hom.comp (algebraMap R A) = algebraMap R C := by
    have := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    rwa [CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at this
  refine ⟨{ toRingHom := φ'.hom, commutes' := fun r => RingHom.congr_fun hR r }, Subtype.ext ?_⟩
  rw [Pt.map_val]
  change Spec.map (CommRingCat.ofHom φ'.hom) ≫ γ.1 = γC.1
  rw [CommRingCat.ofHom_hom, hcomp]

theorem exists_chart (hH : LocallyOfFiniteType pH) (h : H) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.FiniteType R A) (γ : Pt R H pH A),
      IsOpenImmersion γ.1 ∧ h ∈ Set.range γ.1.base := by
  haveI := hH
  obtain ⟨y, hy⟩ := H.affineCover.covers h
  let V : H.Opens := (H.affineCover.f (H.affineCover.idx h)).opensRange
  have hV : IsAffineOpen V := isAffineOpen_opensRange _
  have hle : V ≤ pH ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) := by
    rw [Scheme.Hom.preimage_top]; exact le_top
  let α : CommRingCat.of R ⟶ Γ(H, V) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ pH.appLE ⊤ V hle
  letI : Algebra R Γ(H, V) := α.hom.toAlgebra
  have hft : (pH.appLE ⊤ V hle).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType pH hH ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ hle
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.surjective
  have hft' : α.hom.FiniteType := by
    rw [CommRingCat.hom_comp]
    exact hft.comp (RingHom.FiniteType.of_surjective _ hsurj)
  have hγ : hV.fromSpec ≫ pH = Spec.map (CommRingCat.ofHom (algebraMap R Γ(H, V))) := by
    change hV.fromSpec ≫ pH = Spec.map (CommRingCat.ofHom α.hom)
    rw [CommRingCat.ofHom_hom, Spec.map_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec pH (isAffineOpen_top _) hV hle,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  refine ⟨Γ(H, V), inferInstance, inferInstance, hft', ⟨hV.fromSpec, hγ⟩, inferInstance, ?_⟩
  change h ∈ Set.range hV.fromSpec.base
  rw [IsAffineOpen.range_fromSpec]
  exact ⟨y, hy⟩

end Charts
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType.ClopenAux.Pt"

section Clopen

variable {R : Type} [CommRing R] {H : Scheme.{0}} {pH : H ⟶ Spec (CommRingCat.of R)}
  (Q : ∀ (B : Type) [CommRing B] [Algebra R B], Pt R H pH B → Prop)

def goodSet : Set H :=
  {h | ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (γ : Pt R H pH A) (_ : IsOpenImmersion γ.1) (e : A),
    IsWitness Q γ e ∧ h ∈ γ.1.base '' (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum A))}

def badSet : Set H :=
  {h | ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (γ : Pt R H pH A) (_ : IsOpenImmersion γ.1) (e : A),
    IsWitness Q γ e ∧ h ∈ γ.1.base '' (PrimeSpectrum.basicOpen (1 - e) : Set (PrimeSpectrum A))}

variable {Q}

theorem isOpen_goodSet : IsOpen (goodSet Q) := by
  rw [isOpen_iff_forall_mem_open]
  rintro h ⟨A, _, _, γ, hγ, e, hw, hh⟩
  refine ⟨γ.1.base '' (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum A)), ?_, ?_, hh⟩
  · rintro h' hh'
    exact ⟨A, _, _, γ, hγ, e, hw, hh'⟩
  · exact γ.1.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen e).2

theorem isOpen_badSet : IsOpen (badSet Q) := by
  rw [isOpen_iff_forall_mem_open]
  rintro h ⟨A, _, _, γ, hγ, e, hw, hh⟩
  refine ⟨γ.1.base '' (PrimeSpectrum.basicOpen (1 - e) : Set (PrimeSpectrum A)), ?_, ?_, hh⟩
  · rintro h' hh'
    exact ⟨A, _, _, γ, hγ, e, hw, hh'⟩
  · exact γ.1.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen (1 - e)).2

theorem refine_at {B A : Type} [CommRing B] [Algebra R B] [CommRing A] [Algebra R A]
    (g : Pt R H pH B) {e : B} (hw : IsWitness Q g e) (𝔭 : PrimeSpectrum B)
    (γ : Pt R H pH A) [IsOpenImmersion γ.1] {eA : A} (hwA : IsWitness Q γ eA)
    (hmem : g.1.base 𝔭 ∈ Set.range γ.1.base) :
    ∃ q : PrimeSpectrum A, γ.1.base q = g.1.base 𝔭 ∧ (eA ∉ q.asIdeal ↔ e ∉ 𝔭.asIdeal) := by
  classical

  have hO : IsOpen (g.1.base ⁻¹' Set.range γ.1.base) := γ.1.isOpenEmbedding.isOpen_range.preimage g.1.base.hom.continuous
  obtain ⟨_, ⟨s, rfl⟩, h𝔭s, hsO⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmem hO
  let C : Type := Localization.Away s
  let loc : B →ₐ[R] C := IsScalarTower.toAlgHom R B C
  let gC : Pt R H pH C := Pt.map loc g
  have hrange : Set.range (Spec.map (CommRingCat.ofHom (algebraMap B C))).base = (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum B)) := by
    have := PrimeSpectrum.localization_away_comap_range C s
    exact this
  have hsub : Set.range gC.1.base ⊆ Set.range γ.1.base := by
    rintro _ ⟨r, rfl⟩
    apply hsO
    show (Spec.map (CommRingCat.ofHom loc.toRingHom)).base r ∈ (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum B))
    rw [← hrange]
    exact ⟨r, rfl⟩
  obtain ⟨τ, hτ⟩ := exists_algHom_of_range_subset γ gC hsub

  have hw1 : IsWitness Q gC (loc e) := hw.map loc
  have hw2 : IsWitness Q gC (τ eA) := by rw [← hτ]; exact hwA.map τ
  have heq : loc e = τ eA := hw1.unique hw2

  obtain ⟨r, hr⟩ : ∃ r : PrimeSpectrum C, (Spec.map (CommRingCat.ofHom (algebraMap B C))).base r = 𝔭 := by
    have : 𝔭 ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap B C))).base := by rw [hrange]; exact h𝔭s
    exact this
  refine ⟨(Spec.map (CommRingCat.ofHom τ.toRingHom)).base r, ?_, ?_⟩
  · have h1 := congrArg Subtype.val hτ
    rw [Pt.map_val] at h1
    rw [← Scheme.Hom.comp_apply, h1]
    show (Spec.map (CommRingCat.ofHom loc.toRingHom) ≫ g.1).base r = g.1.base 𝔭
    rw [Scheme.Hom.comp_apply, ← hr]
    rfl
  · rw [← hr]
    simp only [Spec.map_apply, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, CommRingCat.hom_ofHom]
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ← heq]
    rfl

variable (Q)

def ChartsExist : Prop :=
  ∀ h : H, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (γ : Pt R H pH A) (_ : IsOpenImmersion γ.1) (e : A),
    IsWitness Q γ e ∧ h ∈ Set.range γ.1.base

variable {Q}

theorem good_union_bad (hex : ChartsExist Q) : goodSet Q ∪ badSet Q = Set.univ := by
  refine Set.eq_univ_of_forall fun h => ?_
  obtain ⟨A, _, _, γ, hγ, e, hw, ⟨q, rfl⟩⟩ := hex h
  by_cases hq : e ∈ q.asIdeal
  · right
    refine ⟨A, _, _, γ, hγ, e, hw, q, ?_, rfl⟩
    show (1 - e) ∉ q.asIdeal
    intro h1
    exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (by have := q.asIdeal.add_mem hq h1; rwa [add_sub_cancel] at this))
  · left
    exact ⟨A, _, _, γ, hγ, e, hw, q, hq, rfl⟩

theorem good_inter_bad : goodSet Q ∩ badSet Q = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun h ⟨⟨A, _, _, γ, hγ, e, hw, ⟨q₀, hq₀, hq₀h⟩⟩, ⟨A', _, _, γ', hγ', e', hw', ⟨q', hq', hq'h⟩⟩⟩ => ?_
  haveI := hγ; haveI := hγ'

  obtain ⟨q, hq, hiff⟩ := refine_at γ' hw' q' γ hw ⟨q₀, hq₀h.trans hq'h.symm⟩
  have : q = q₀ := γ.1.isOpenEmbedding.injective (hq.trans (hq'h.trans hq₀h.symm))
  subst this
  have he' : e' ∉ q'.asIdeal := hiff.mp hq₀

  have h2 := (idem_not_mem_iff hw'.1.one_sub q').mp hq'
  rw [sub_sub_cancel] at h2
  exact he' h2

theorem isClosed_goodSet (hex : ChartsExist Q) : IsClosed (goodSet Q) := by
  have : (goodSet Q)ᶜ = badSet Q := by
    apply Set.Subset.antisymm
    · intro h hh
      have := (Set.eq_univ_iff_forall.mp (good_union_bad hex)) h
      exact this.resolve_left hh
    · intro h hh hg
      exact (Set.eq_empty_iff_forall_notMem.mp good_inter_bad) h ⟨hg, hh⟩
  rw [← isOpen_compl_iff, this]
  exact isOpen_badSet

theorem forall_mem_goodSet_iff (hex : ChartsExist Q) {B : Type} [CommRing B] [Algebra R B]
    (g : Pt R H pH B) {e : B} (hw : IsWitness Q g e) :
    (∀ 𝔭 : PrimeSpectrum B, g.1.base 𝔭 ∈ goodSet Q) ↔ e = 1 := by
  constructor
  · intro hall
    apply idem_eq_one_of_forall_not_mem hw.1
    intro 𝔭
    obtain ⟨A, _, _, γ, hγ, eA, hwA, ⟨q₀, hq₀, hq₀h⟩⟩ := hall 𝔭
    haveI := hγ
    obtain ⟨q, hq, hiff⟩ := refine_at g hw 𝔭 γ hwA ⟨q₀, hq₀h⟩
    have : q = q₀ := γ.1.isOpenEmbedding.injective (hq.trans hq₀h.symm)
    subst this
    exact hiff.mp hq₀
  · intro he 𝔭
    subst he
    obtain ⟨A, _, _, γ, hγ, eA, hwA, hmem⟩ := hex (g.1.base 𝔭)
    haveI := hγ
    obtain ⟨q, hq, hiff⟩ := refine_at g hw 𝔭 γ hwA hmem
    refine ⟨A, _, _, γ, hγ, eA, hwA, q, ?_, hq⟩
    exact hiff.mpr fun h1 => 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

end Clopen
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType.ClopenAux.Pt"

end ClopenAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType.ClopenAux.Pt P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType.ClopenAux"

theorem solution
    (R : Type) [CommRing R]
    (F : ∀ (B : Type) [CommRing B] [Algebra R B], Type)
    (Fmap : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'], (B →ₐ[R] B') → F B → F B')
    (H : Scheme.{0}) (pH : H ⟶ Spec (CommRingCat.of R)) (hH : LocallyOfFiniteType pH)
    (pt : ∀ (B : Type) [CommRing B] [Algebra R B],
      F B ≃ {g : Spec (CommRingCat.of B) ⟶ H // g ≫ pH = Spec.map (CommRingCat.ofHom (algebraMap R B))})
    (hpt : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (φ : B →ₐ[R] B') (x : F B),
      (pt B' (Fmap B B' φ x)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt B x).1)
    (P : ∀ (B : Type) [CommRing B] [Algebra R B], F B → Prop)
    (hP : ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] (x : F B), ∃ e : B, IsIdempotentElem e ∧
      ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'), P B' (Fmap B B' φ x) ↔ φ e = 1) :
    ∃ (X : Scheme.{0}) (ι : X ⟶ H), IsOpenImmersion ι ∧ IsClosedImmersion ι ∧
      ∀ (B : Type) [CommRing B] [Algebra R B] (x : F B) (e : B), IsIdempotentElem e →
        (∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'), P B' (Fmap B B' φ x) ↔ φ e = 1) →
        (P B x ↔ ∃ g : Spec (CommRingCat.of B) ⟶ X, g ≫ ι = (pt B x).1) := by
  classical
  let Q : ∀ (B : Type) [CommRing B] [Algebra R B], ClopenAux.Pt R H pH B → Prop := fun B _ _ g => P B ((pt B).symm g)
  have hW : ∀ (B : Type) [CommRing B] [Algebra R B] (x : F B) (e : B), IsIdempotentElem e →
      (∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'), P B' (Fmap B B' φ x) ↔ φ e = 1) →
      ClopenAux.IsWitness Q (pt B x) e := by
    intro B _ _ x e he h
    refine ⟨he, fun B' _ _ φ => ?_⟩
    have hx : (pt B') (Fmap B B' φ x) = ClopenAux.Pt.map φ (pt B x) :=
      Subtype.ext (by rw [ClopenAux.Pt.map_val]; exact hpt B B' φ x)
    change P B' ((pt B').symm (ClopenAux.Pt.map φ (pt B x))) ↔ φ e = 1
    rw [← hx, Equiv.symm_apply_apply]
    exact h B' φ
  have hex : ClopenAux.ChartsExist Q := by
    intro h
    obtain ⟨A, _, _, _, γ, hγ, hh⟩ := ClopenAux.exists_chart hH h
    obtain ⟨e, he, hPe⟩ := hP A ((pt A).symm γ)
    refine ⟨A, _, _, γ, hγ, e, ?_, hh⟩
    have := hW A ((pt A).symm γ) e he hPe
    rwa [Equiv.apply_symm_apply] at this
  let U : H.Opens := ⟨ClopenAux.goodSet Q, ClopenAux.isOpen_goodSet⟩
  refine ⟨U, U.ι, inferInstance, ?_, ?_⟩
  · apply IsClosedImmersion.of_isPreimmersion
    rw [Scheme.Opens.range_ι]
    exact ClopenAux.isClosed_goodSet hex
  · intro B _ _ x e he hPe
    have hw := hW B x e he hPe
    have h1 : P B x ↔ e = 1 := by
      have := hw.self_iff
      change P B ((pt B).symm (pt B x)) ↔ e = 1 at this
      rwa [Equiv.symm_apply_apply] at this
    rw [h1, ← ClopenAux.forall_mem_goodSet_iff hex (pt B x) hw]
    constructor
    · intro hall
      refine ⟨IsOpenImmersion.lift U.ι (pt B x).1 ?_, IsOpenImmersion.lift_fac _ _ _⟩
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨𝔭, rfl⟩
      exact hall 𝔭
    · rintro ⟨g, hg⟩ 𝔭
      have : (pt B x).1.base 𝔭 ∈ Set.range U.ι.base := by
        rw [← hg, Scheme.Hom.comp_apply]
        exact ⟨_, rfl⟩
      rw [Scheme.Opens.range_ι] at this
      exact this

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType.ClopenAux.Pt P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType.ClopenAux"

end S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType (solution)
