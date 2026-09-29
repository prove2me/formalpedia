-- Prove2me | solution 1 for AlgebraicGeometry.ValuativeCommSq.exists_isAdicComplete_finite_residueField_hasLift_imp_hasLift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/6fbd0424-231d-56a1-9cc3-d6906a6533cc

import Mathlib
import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ValuativeCommSq_exists_isAdicComplete_finite_residueField_hasLift_imp_hasLift

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace CompleteDescentGC5

open IsLocalRing

theorem range_subset_of_closedPoint_mem {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (g : Spec (CommRingCat.of R) ⟶ X) (U : X.Opens) (h : g.base (closedPoint R) ∈ U) :
    Set.range g.base ⊆ (U : Set X) := by
  rintro _ ⟨p, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint p).map g.continuous).mem_open U.2 h

theorem eq_SpecMap_appTop {R : CommRingCat.{u}} {U : Scheme.{u}} [IsAffine U] (g : Spec R ⟶ U) :
    g = Spec.map (g.appTop ≫ (Scheme.ΓSpecIso R).hom) ≫ U.isoSpec.inv := by
  rw [Iso.eq_comp_inv, Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]

end CompleteDescentGC5

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) (S : ValuativeCommSq f)
    [IsDiscreteValuationRing S.R] [Finite (IsLocalRing.ResidueField S.R)] :
    ∃ S' : ValuativeCommSq f, IsDiscreteValuationRing S'.R ∧ IsAdicComplete (IsLocalRing.maximalIdeal S'.R) S'.R ∧
      Finite (IsLocalRing.ResidueField S'.R) ∧ (S'.commSq.HasLift → S.commSq.HasLift) := by
  classical

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.R
  obtain ⟨hdom, hdvr, hcpl, hirr, hfaith, hdense⟩ :=
    IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete S.R ϖ hϖ
  let Rh := AdicCompletion (IsLocalRing.maximalIdeal S.R) S.R
  letI : IsDomain Rh := hdom
  letI : IsDiscreteValuationRing Rh := hdvr
  let Kh := FractionRing Rh
  let ι : S.R →+* Rh := algebraMap S.R Rh
  have hι : Function.Injective ι := fun a b h => AdicCompletion.of_injective (IsLocalRing.maximalIdeal S.R) S.R h

  have hunit : ∀ y : nonZeroDivisors S.R, IsUnit (((algebraMap Rh Kh).comp ι) y) := fun y =>
    IsUnit.mk0 _ (by
      rw [RingHom.comp_apply, map_ne_zero_iff _ (IsFractionRing.injective Rh Kh), map_ne_zero_iff _ hι]
      exact nonZeroDivisors.ne_zero y.2)
  let j : S.K →+* Kh := IsLocalization.lift (M := nonZeroDivisors S.R) hunit
  have hj : ∀ r : S.R, j (algebraMap S.R S.K r) = algebraMap Rh Kh (ι r) := fun r => IsLocalization.lift_eq hunit r

  let S' : ValuativeCommSq f :=
    { R := Rh
      K := Kh
      i₁ := Spec.map (CommRingCat.ofHom j) ≫ S.i₁
      i₂ := Spec.map (CommRingCat.ofHom ι) ≫ S.i₂
      commSq := ⟨by
        have e : CommRingCat.ofHom (algebraMap S.R S.K) ≫ CommRingCat.ofHom j =
            CommRingCat.ofHom ι ≫ CommRingCat.ofHom (algebraMap Rh Kh) := by
          ext r; exact hj r
        rw [Category.assoc, S.commSq.w, ← Category.assoc, ← Spec.map_comp, e, Spec.map_comp, Category.assoc]⟩ }
  have hmax : IsLocalRing.maximalIdeal Rh = Ideal.span {ι ϖ} := hirr.maximalIdeal_eq
  have hmaxR : IsLocalRing.maximalIdeal S.R = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  refine ⟨S', hdvr, hcpl, ?_, ?_⟩
  ·
    show Finite (IsLocalRing.ResidueField Rh)
    let g : S.R →+* IsLocalRing.ResidueField Rh := (IsLocalRing.residue Rh).comp ι
    have hg : ∀ a ∈ IsLocalRing.maximalIdeal S.R, g a = 0 := by
      intro a ha
      show IsLocalRing.residue Rh (ι a) = 0
      rw [IsLocalRing.residue_eq_zero_iff, hmax]
      rw [hmaxR] at ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    have hsurj : Function.Surjective (Ideal.Quotient.lift (IsLocalRing.maximalIdeal S.R) g hg) := by
      intro q
      obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective q
      obtain ⟨c, hc⟩ := hdense 1 w
      refine ⟨Ideal.Quotient.mk _ c, ?_⟩
      rw [Ideal.Quotient.lift_mk]
      show IsLocalRing.residue Rh (ι c) = IsLocalRing.residue Rh w
      have : w - ι c ∈ IsLocalRing.maximalIdeal Rh := by rw [hmax]; simpa [pow_one] using hc
      rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact this
    haveI : Finite (S.R ⧸ IsLocalRing.maximalIdeal S.R) := ‹Finite (IsLocalRing.ResidueField S.R)›
    exact Finite.of_surjective _ hsurj
  · intro hL
    obtain ⟨lh, h1, h2⟩ := hL.exists_lift
    change Spec.map (CommRingCat.ofHom (algebraMap Rh Kh)) ≫ lh = Spec.map (CommRingCat.ofHom j) ≫ S.i₁ at h1
    change lh ≫ f = Spec.map (CommRingCat.ofHom ι) ≫ S.i₂ at h2

    haveI : IsLocalHom ι := by
      refine ⟨fun a ha => ?_⟩
      by_contra hna
      have ha' : a ∈ IsLocalRing.maximalIdeal S.R := (IsLocalRing.mem_maximalIdeal a).mpr hna
      rw [hmaxR] at ha'
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha'
      have : ι (b * ϖ) ∈ IsLocalRing.maximalIdeal Rh := by
        rw [hmax, map_mul]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      exact (IsLocalRing.mem_maximalIdeal _).mp this ha

    have hc : f.base (lh.base (IsLocalRing.closedPoint Rh)) = S.i₂.base (IsLocalRing.closedPoint S.R) := by
      rw [← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply]
      congr 1
      exact IsLocalRing.comap_closedPoint ι
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (S.i₂.base (IsLocalRing.closedPoint S.R))) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hcU, hUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show lh.base (IsLocalRing.closedPoint Rh) ∈ (f ⁻¹ᵁ V : Set X) from
        show f.base _ ∈ V from hc ▸ hyV) (f ⁻¹ᵁ V).2
    haveI : IsAffine U := hU
    haveI : IsAffine V := hV

    have hlhU : Set.range lh.base ⊆ Set.range (Scheme.Opens.ι U).base := by
      rw [Scheme.Opens.range_ι]; exact CompleteDescentGC5.range_subset_of_closedPoint_mem lh U hcU
    have hi₁U : Set.range S.i₁.base ⊆ Set.range (Scheme.Opens.ι U).base := by
      rintro _ ⟨p, rfl⟩
      obtain rfl : p = (Spec.map (CommRingCat.ofHom j)).base (IsLocalRing.closedPoint Kh) := Subsingleton.elim _ _
      apply hlhU
      refine ⟨(Spec.map (CommRingCat.ofHom (algebraMap Rh Kh))).base (IsLocalRing.closedPoint Kh), ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h1]
    let lhU := IsOpenImmersion.lift (Scheme.Opens.ι U) lh hlhU
    let i₁U := IsOpenImmersion.lift (Scheme.Opens.ι U) S.i₁ hi₁U
    have hlhU' : lhU ≫ (Scheme.Opens.ι U) = lh := IsOpenImmersion.lift_fac _ _ _
    have hi₁U' : i₁U ≫ (Scheme.Opens.ι U) = S.i₁ := IsOpenImmersion.lift_fac _ _ _

    let α : Γ(↑U, ⊤) ⟶ CommRingCat.of Rh := lhU.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Rh)).hom
    let β : Γ(↑U, ⊤) ⟶ CommRingCat.of S.K := i₁U.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of S.K)).hom
    have hlhU_eq : lhU = Spec.map α ≫ (↑U : Scheme.{u}).isoSpec.inv := CompleteDescentGC5.eq_SpecMap_appTop lhU
    have hi₁U_eq : i₁U = Spec.map β ≫ (↑U : Scheme.{u}).isoSpec.inv := CompleteDescentGC5.eq_SpecMap_appTop i₁U
    have hagree : α ≫ CommRingCat.ofHom (algebraMap Rh Kh) = β ≫ CommRingCat.ofHom j := by
      apply Spec.map_injective
      have e : Spec.map (CommRingCat.ofHom (algebraMap Rh Kh)) ≫ lhU = Spec.map (CommRingCat.ofHom j) ≫ i₁U := by
        rw [← cancel_mono (Scheme.Opens.ι U), Category.assoc, Category.assoc, hlhU', hi₁U', h1]
      rw [hlhU_eq, hi₁U_eq, ← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at e
      exact e
    have hagree' : ∀ a, algebraMap Rh Kh (α.hom a) = j (β.hom a) := fun a => by
      have := congrArg (fun φ : Γ(↑U, ⊤) ⟶ CommRingCat.of Kh => φ.hom a) hagree
      simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using this

    have hβR : ∀ a, β.hom a ∈ (algebraMap S.R S.K).range := by
      intro a
      obtain ⟨r, s, hs, hx⟩ := IsFractionRing.div_surjective (A := S.R) (β.hom a)
      have hs0 : (s : S.R) ≠ 0 := nonZeroDivisors.ne_zero hs
      obtain ⟨m, u, hsu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ

      have h3 : α.hom a * ι s = ι r := by
        apply IsFractionRing.injective Rh Kh
        rw [map_mul, hagree', ← hj, ← hj, ← map_mul, ← hx, div_mul_cancel₀]
        exact (map_ne_zero_iff _ (IsFractionRing.injective S.R S.K)).mpr hs0
      have h4 : ι r ∈ Ideal.span {ι ϖ ^ m} := by
        rw [← h3, hsu, map_mul, map_pow, ← mul_assoc]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      obtain ⟨r', hr'⟩ := Ideal.mem_span_singleton'.mp (hfaith m r h4)
      refine ⟨r' * ↑u⁻¹, ?_⟩
      rw [← hx, hsu, ← hr', eq_div_iff ((map_ne_zero_iff _ (IsFractionRing.injective S.R S.K)).mpr (hsu ▸ hs0)),
        ← map_mul]
      congr 1
      rw [mul_assoc, ← mul_assoc (↑u⁻¹ : S.R), Units.inv_mul, one_mul]

    have hinjRK : Function.Injective (algebraMap S.R S.K) := IsFractionRing.injective _ _
    let eR : S.R ≃+* (algebraMap S.R S.K).range :=
      RingEquiv.ofBijective (algebraMap S.R S.K).rangeRestrict
        ⟨fun x y h => hinjRK (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
    let φ : Γ(↑U, ⊤) →+* S.R := eR.symm.toRingHom.comp ((CommRingCat.Hom.hom β).codRestrict _ hβR)
    have hφK : ∀ a, algebraMap S.R S.K (φ a) = β.hom a := fun a => by
      have : ((eR (φ a)) : S.K) = β.hom a := by
        simp only [φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply]
        rfl
      exact this
    have hφR : ∀ a, ι (φ a) = α.hom a := fun a =>
      IsFractionRing.injective Rh Kh (by rw [← hj, hφK, ← hagree'])
    let l : Spec (CommRingCat.of S.R) ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ (↑U : Scheme.{u}).isoSpec.inv ≫ (Scheme.Opens.ι U)
    have hlU : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map β := by
      rw [← Spec.map_comp]; congr 1
      exact CommRingCat.hom_ext (RingHom.ext fun a => hφK a)
    have hlR : Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map α := by
      rw [← Spec.map_comp]; congr 1
      exact CommRingCat.hom_ext (RingHom.ext fun a => hφR a)
    have hιl : Spec.map (CommRingCat.ofHom ι) ≫ l = lh := by
      rw [← hlhU', hlhU_eq]
      simp only [l, ← Category.assoc, hlR]
    refine CommSq.HasLift.mk' ⟨l, ?_, ?_⟩
    ·
      rw [← hi₁U', hi₁U_eq]
      simp only [l, ← Category.assoc, hlU]
    ·
      have hlV : Set.range (l ≫ f).base ⊆ Set.range (Scheme.Opens.ι V).base := by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨p, rfl⟩
        rw [Scheme.Hom.comp_apply]
        show l.base p ∈ f ⁻¹ᵁ V
        apply hUV
        show (Spec.map (CommRingCat.ofHom φ) ≫ (↑U : Scheme.{u}).isoSpec.inv ≫ (Scheme.Opens.ι U)).base p ∈ (U : Set X)
        rw [← Scheme.Opens.range_ι]
        exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      have hi₂V : Set.range S.i₂.base ⊆ Set.range (Scheme.Opens.ι V).base := by
        rw [Scheme.Opens.range_ι]; exact CompleteDescentGC5.range_subset_of_closedPoint_mem S.i₂ V hyV
      suffices hlifts : IsOpenImmersion.lift (Scheme.Opens.ι V) (l ≫ f) hlV = IsOpenImmersion.lift (Scheme.Opens.ι V) S.i₂ hi₂V by
        calc l ≫ f = IsOpenImmersion.lift (Scheme.Opens.ι V) (l ≫ f) hlV ≫ (Scheme.Opens.ι V) :=
              (IsOpenImmersion.lift_fac _ _ _).symm
          _ = IsOpenImmersion.lift (Scheme.Opens.ι V) S.i₂ hi₂V ≫ (Scheme.Opens.ι V) := by rw [hlifts]
          _ = S.i₂ := IsOpenImmersion.lift_fac _ _ _
      have key : Spec.map (CommRingCat.ofHom ι) ≫ IsOpenImmersion.lift (Scheme.Opens.ι V) (l ≫ f) hlV =
          Spec.map (CommRingCat.ofHom ι) ≫ IsOpenImmersion.lift (Scheme.Opens.ι V) S.i₂ hi₂V := by
        rw [← cancel_mono (Scheme.Opens.ι V)]
        simp only [Category.assoc, IsOpenImmersion.lift_fac]
        rw [← Category.assoc, hιl, h2]
      rw [CompleteDescentGC5.eq_SpecMap_appTop (IsOpenImmersion.lift (Scheme.Opens.ι V) (l ≫ f) hlV),
        CompleteDescentGC5.eq_SpecMap_appTop (IsOpenImmersion.lift (Scheme.Opens.ι V) S.i₂ hi₂V)] at key ⊢
      rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at key
      have key' := Spec.map_injective key
      haveI : Mono (CommRingCat.ofHom ι) := ConcreteCategory.mono_of_injective _ hι
      rw [cancel_mono] at key'
      rw [key']

end S_AlgebraicGeometry_ValuativeCommSq_exists_isAdicComplete_finite_residueField_hasLift_imp_hasLift
end P2MW
export P2MW.S_AlgebraicGeometry_ValuativeCommSq_exists_isAdicComplete_finite_residueField_hasLift_imp_hasLift (solution)
