-- Prove2me | solution 1 for AlgebraicCurve.exists_section_localRing_apply_eq_of_ord_eq_one_of_mem_smoothLocus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/8f9e32d4-64ce-542f-b7d3-8d9881983e84

import Theorems.Thm_Algebra_IsSmoothAt_flat_localization_atPrime
import Theorems.Thm_RingHom_existsUnique_eq_smul_kaehlerDifferential_D_of_formallySmooth_of_maximalIdeal_eq_map_sup_span
import Theorems.Thm_AlgebraicCurve_exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus
import Theorems.Thm_HenselianLocalRing_moduleFinite_quotient_span_and_exists_pow_mem_of_isLocalizationAtPrime_of_mem_nonZeroDivisors
import Theorems.Thm_Algebra_FormallySmooth_quotient_span_singleton_of_existsUnique_eq_smul_D
import Theorems.Thm_IsLocalRing_exists_ringHom_comp_algebraMap_eq_and_ker_eq_span_of_injective_of_finite
import Theorems.Thm_AlgebraicCurve_exists_formallySmooth_isLocalizationAtPrime_localRing_of_mem_smoothLocus
import Theorems.Thm_AlgebraicCurve_exists_maximalIdeal_localRing_eq_map_sup_span_of_ord_eq_one_of_mem_smoothLocus
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_section_localRing_apply_eq_of_ord_eq_one_of_mem_smoothLocus

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    [HenselianLocalRing ↥A]
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x) (hxs : x ∈ toBase.smoothLocus)
    (η : X) (hηx : η ⤳ x) (hne : η ≠ x) (hη : toBase.base η = closedPoint ↥A)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hR : R.integers.toSubring = SemistableModel.localRing X φ η) :
    let S : Subring F := SemistableModel.localRing X φ x
    ∀ (hAS : ∀ a : ↥A, algebraMap L F (a : L) ∈ S)
      (Q : Place (ResidueField ↥A) Fbar), Q.IsRational →
      (∀ f : ↥S, ∃ hR : (f : F) ∈ R.integers, R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring) →
      (∀ (f : ↥S) (hR : (f : F) ∈ R.integers),
        IsUnit f ↔ Q.ord (R.residue ⟨(f : F), hR⟩) = 0 ∧ R.residue ⟨(f : F), hR⟩ ≠ 0) →
      ∀ (T : ↥S), (∃ hR : (T : F) ∈ R.integers, Q.ord (R.residue ⟨(T : F), hR⟩) = 1) →
      ∀ c : ↥A, c ∈ maximalIdeal ↥A →
        ∃ χ : ↥S →+* ↥A,
          (∀ a : ↥A, χ ⟨algebraMap L F (a : L), hAS a⟩ = a) ∧
          χ T = c ∧
          RingHom.ker χ = Ideal.span {T - ⟨algebraMap L F (c : L), hAS c⟩} := by
  intro S hAS Q hQrat hRES hUNITS T hTord c hc
  classical

  obtain ⟨ι, hι, B, _, _, _, 𝔫, _, hmainSM⟩ :=
    AlgebraicCurve.exists_formallySmooth_isLocalizationAtPrime_localRing_of_mem_smoothLocus A hrk hA X toBase φ hφ x hx hxc hxs η hηx hne hη R hR
  letI instAS : Algebra ↥A ↥S := ι.toAlgebra
  obtain ⟨hfp, hsmB, h𝔫, hst, hloc, hflat⟩ := hmainSM
  haveI := hfp; haveI := hsmB; haveI := hst; haveI := hloc; haveI := hflat
  haveI hSloc : IsLocalRing ↥S := IsLocalization.AtPrime.isLocalRing ↥S 𝔫
  have hιa : ∀ a : ↥A, ι a = ⟨algebraMap L F (a : L), hAS a⟩ := fun a => Subtype.ext (hι a)

  have hιuniq : ∀ ι' : ↥A →+* ↥S, (∀ a : ↥A, ((ι' a : ↥S) : F) = algebraMap L F (a : L)) → ι' = ι :=
    fun ι' h' => RingHom.ext fun a => Subtype.ext ((h' a).trans (hι a).symm)

  obtain ⟨ι₂, hι₂, hloc₂, hm, hTn, hres⟩ :=
    AlgebraicCurve.exists_maximalIdeal_localRing_eq_map_sup_span_of_ord_eq_one_of_mem_smoothLocus A hrk hA X toBase φ hφ x hx hxc hxs η hηx hne hη R hR
      hAS Q hQrat hRES hUNITS T hTord
  have eι : ι = ι₂ := (hιuniq ι₂ hι₂).symm
  subst eι

  set cS : ↥S := ⟨algebraMap L F (c : L), hAS c⟩ with hcS
  have hcS' : ι c = cS := hιa c
  set t : ↥S := T - cS with ht
  have hcmem : cS ∈ (maximalIdeal ↥A).map ι := hcS' ▸ Ideal.mem_map_of_mem _ hc
  have hsup : (maximalIdeal ↥A).map ι ⊔ Ideal.span {t} = (maximalIdeal ↥A).map ι ⊔ Ideal.span {T} := by
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      rw [Ideal.span_singleton_le_iff_mem]
      exact Submodule.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self T)) (Ideal.mem_sup_left hcmem)
    · refine sup_le le_sup_left ?_
      rw [Ideal.span_singleton_le_iff_mem]
      have : T = t + cS := by rw [ht, sub_add_cancel]
      rw [this]
      exact Submodule.add_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self t)) (Ideal.mem_sup_left hcmem)
  have hm_t : maximalIdeal ↥S = (maximalIdeal ↥A).map ι ⊔ Ideal.span {t} := by rw [hsup]; exact hm
  have ht_n : t ∉ (maximalIdeal ↥A).map ι := by
    intro h
    apply hTn
    have : T = t + cS := by rw [ht, sub_add_cancel]
    rw [this]; exact Submodule.add_mem _ h hcmem
  have ht_max : t ∈ maximalIdeal ↥S := hm_t ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self t)
  have ht_nu : ¬IsUnit t := (IsLocalRing.mem_maximalIdeal _).mp ht_max

  haveI hsmS : Algebra.FormallySmooth ↥A ↥S := by
    haveI : Algebra.FormallySmooth B ↥S := Algebra.FormallySmooth.of_isLocalization 𝔫.primeCompl
    exact Algebra.FormallySmooth.comp ↥A B ↥S
  haveI heftS : Algebra.EssFiniteType ↥A ↥S := by
    haveI : Algebra.EssFiniteType B ↥S := Algebra.EssFiniteType.of_isLocalization ↥S 𝔫.primeCompl
    exact Algebra.EssFiniteType.comp ↥A B ↥S
  have hi : ι.FormallySmooth := RingHom.formallySmooth_algebraMap.mpr hsmS
  have hif : ι.EssFiniteType := RingHom.essFiniteType_algebraMap.mpr heftS

  have hdt := RingHom.existsUnique_eq_smul_kaehlerDifferential_D_of_formallySmooth_of_maximalIdeal_eq_map_sup_span
    ι hi hif hres t hm_t ht_n
  haveI hsmQ : Algebra.FormallySmooth ↥A (↥S ⧸ Ideal.span ({t} : Set ↥S)) :=
    Algebra.FormallySmooth.quotient_span_singleton_of_existsUnique_eq_smul_D t hdt

  have hflatQ : Module.Flat ↥A (↥S ⧸ Ideal.span ({t} : Set ↥S)) := by

    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj 𝔫.primeCompl t
    have hsu : IsUnit (algebraMap B ↥S (s : B)) := IsLocalization.map_units ↥S s
    have hspan : Ideal.span ({t} : Set ↥S) = Ideal.span {algebraMap B ↥S b} := by
      rw [← hbs]; exact (Ideal.span_singleton_mul_right_unit hsu t).symm
    set I : Ideal B := Ideal.span {b} with hI
    have hImap : I.map (algebraMap B ↥S) = Ideal.span ({t} : Set ↥S) := by
      rw [hspan, hI, Ideal.map_span, Set.image_singleton]
    have hb𝔫 : b ∈ 𝔫 := by
      have : algebraMap B ↥S b ∈ maximalIdeal ↥S := by
        rw [← hbs]; exact Ideal.mul_mem_right _ _ ht_max
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff ↥S 𝔫 b).mp this
    have hI𝔫 : I ≤ 𝔫 := by rw [hI, Ideal.span_singleton_le_iff_mem]; exact hb𝔫

    haveI : Algebra.FinitePresentation ↥A (B ⧸ I) :=
      Algebra.FinitePresentation.quotient ⟨{b}, by simp [hI]⟩
    have hkermk : RingHom.ker (Ideal.Quotient.mk I) ≤ 𝔫 := by rw [Ideal.mk_ker]; exact hI𝔫
    haveI h𝔭 : (𝔫.map (Ideal.Quotient.mk I)).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hkermk
    set 𝔭 : Ideal (B ⧸ I) := 𝔫.map (Ideal.Quotient.mk I) with h𝔭def

    have hle : I ≤ (Ideal.span ({t} : Set ↥S)).comap (algebraMap B ↥S) := by
      rw [← hImap]; exact Ideal.le_comap_map
    letI algQ : Algebra (B ⧸ I) (↥S ⧸ Ideal.span ({t} : Set ↥S)) :=
      (Ideal.quotientMap (Ideal.span ({t} : Set ↥S)) (algebraMap B ↥S) hle).toAlgebra
    haveI : IsScalarTower ↥A (B ⧸ I) (↥S ⧸ Ideal.span ({t} : Set ↥S)) :=
      IsScalarTower.of_algebraMap_eq fun a => by
        change Ideal.Quotient.mk _ (algebraMap ↥A ↥S a) =
          Ideal.quotientMap _ (algebraMap B ↥S) hle (Ideal.Quotient.mk I (algebraMap ↥A B a))
        rw [Ideal.quotientMap_mk, ← IsScalarTower.algebraMap_apply]

    have hlocQ : IsLocalization (𝔫.primeCompl.map (Ideal.Quotient.mk I)) (↥S ⧸ Ideal.span ({t} : Set ↥S)) := by
      refine IsLocalization.of_surjective 𝔫.primeCompl ↥S (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
        (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective ?_ ?_
      · ext y; simp [algQ, RingHom.algebraMap_toAlgebra, Ideal.quotientMap_mk]
      · rw [Ideal.mk_ker, Ideal.mk_ker, hImap]
    have hsub : 𝔫.primeCompl.map (Ideal.Quotient.mk I) = 𝔭.primeCompl := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩ hy
        apply hz
        have hy' : Ideal.Quotient.mk I z ∈ 𝔫.map (Ideal.Quotient.mk I) := hy
        rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hy'
        obtain ⟨w, hw, hwz⟩ := hy'
        have : z - w ∈ I := by rw [← Ideal.mk_ker (I := I), RingHom.mem_ker, map_sub, hwz, sub_self]
        simpa using Ideal.add_mem _ hw (hI𝔫 this)
      · intro hy
        obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
        exact ⟨z, fun hz => hy (Ideal.mem_map_of_mem _ hz), rfl⟩
    haveI hlocQ' : IsLocalization.AtPrime (↥S ⧸ Ideal.span ({t} : Set ↥S)) 𝔭 := by
      change IsLocalization 𝔭.primeCompl _
      rw [← hsub]; exact hlocQ
    let e : Localization.AtPrime 𝔭 ≃ₐ[B ⧸ I] (↥S ⧸ Ideal.span ({t} : Set ↥S)) :=
      IsLocalization.algEquiv 𝔭.primeCompl _ _
    let eA := (e.restrictScalars ↥A).symm
    haveI : Algebra.IsSmoothAt ↥A 𝔭 := Algebra.FormallySmooth.of_equiv eA
    haveI : Module.Flat ↥A (Localization.AtPrime 𝔭) := Algebra.IsSmoothAt.flat_localization_atPrime ↥A (B ⧸ I) 𝔭
    exact Module.Flat.of_linearEquiv eA.toLinearEquiv

  have hinj : Function.Injective (algebraMap ↥A (↥S ⧸ Ideal.span ({t} : Set ↥S))) := by
    haveI := hflatQ
    have h10 : (1 : ↥S ⧸ Ideal.span ({t} : Set ↥S)) ≠ 0 := by
      rw [Ne, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, ← Ideal.eq_top_iff_one,
        Ideal.span_singleton_eq_top]
      exact ht_nu
    intro a₁ a₂ h12
    by_contra hne12
    have hr : a₁ - a₂ ∈ nonZeroDivisors ↥A := mem_nonZeroDivisors_of_ne_zero (sub_ne_zero.mpr hne12)
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := ↥S ⧸ Ideal.span ({t} : Set ↥S)) hr
    apply h10
    apply hreg
    change (a₁ - a₂) • (1 : ↥S ⧸ Ideal.span ({t} : Set ↥S)) = (a₁ - a₂) • (0 : ↥S ⧸ Ideal.span ({t} : Set ↥S))
    rw [smul_zero, ← Algebra.algebraMap_eq_smul_one, map_sub, h12, sub_self]

  have hfinQ : Module.Finite ↥A (↥S ⧸ Ideal.span ({t} : Set ↥S)) := by
    obtain ⟨hTR, hT1⟩ := hTord
    have hcR : algebraMap L F (c : L) ∈ R.integers := (R.algebraMap_mem_iff _).mpr c.2
    have htR : ((t : ↥S) : F) ∈ R.integers := by
      have : ((t : ↥S) : F) = (T : F) - algebraMap L F (c : L) := rfl
      rw [this]; exact R.integers.toSubring.sub_mem hTR hcR
    have hres_t : R.residue ⟨((t : ↥S) : F), htR⟩ ≠ 0 := by
      have e1 : (⟨((t : ↥S) : F), htR⟩ : ↥R.integers) = ⟨(T : F), hTR⟩ - ⟨algebraMap L F (c : L), hcR⟩ :=
        Subtype.ext rfl
      have e2 : R.residue ⟨algebraMap L F (c : L), hcR⟩ = 0 := by
        rw [R.residue_algebraMap c, (IsLocalRing.residue_eq_zero_iff _).mpr hc, map_zero]
      rw [e1, map_sub, e2, sub_zero]
      intro h0
      rw [h0, Place.ord_zero] at hT1
      exact zero_ne_one hT1
    have hunit : IsUnit (⟨((t : ↥S) : F), htR⟩ : ↥R.integers) := R.isUnit_of_residue_ne_zero hres_t
    have ht0 : ((t : ↥S) : F) ≠ 0 := by
      intro h
      apply hres_t
      have : (⟨((t : ↥S) : F), htR⟩ : ↥R.integers) = 0 := Subtype.ext h
      rw [this, map_zero]
    have htinv : ((t : ↥S) : F)⁻¹ ∈ R.integers := by
      obtain ⟨w, hw⟩ := hunit.exists_right_inv
      have hw' : ((t : ↥S) : F) * (w : F) = 1 := by
        have := congrArg Subtype.val hw; simpa using this
      rw [← eq_inv_of_mul_eq_one_right hw'] at *
      simpa [inv_inv] using w.2
    obtain ⟨ι₃, hι₃, B₃, _, _, _, 𝔫₃, _, hmain₃⟩ :=
      AlgebraicCurve.exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus A hrk hA X toBase φ hφ x hx hxc hxs η hηx hne hη R hR
    have e3 : ι = ι₃ := (hιuniq ι₃ hι₃).symm
    subst e3
    obtain ⟨hfp₃, h𝔫₃, hst₃, hloc₃, hflat₃, hh⟩ := hmain₃
    obtain ⟨hreg, hfin⟩ := hh ((t : ↥S) : F) t.2 ht0 htinv
    haveI := hfp₃; haveI := hst₃; haveI := hloc₃; haveI := hflat₃
    exact (HenselianLocalRing.moduleFinite_quotient_span_and_exists_pow_mem_of_isLocalizationAtPrime_of_mem_nonZeroDivisors
      𝔫₃ h𝔫₃ (S := ↥S) t t ht_nu hreg hfin).1

  have hfib : ∀ s : ↥S, ∃ a : ↥A,
      s - algebraMap ↥A ↥S a ∈ Ideal.span ({t} : Set ↥S) ⊔ (maximalIdeal ↥A).map (algebraMap ↥A ↥S) := by
    intro s
    obtain ⟨a, ha⟩ := hres (IsLocalRing.residue ↥S s)
    refine ⟨a, ?_⟩
    have : s - ι a ∈ maximalIdeal ↥S := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact ha.symm
    rw [hm_t, sup_comm] at this
    exact this

  haveI := hfinQ
  obtain ⟨χ, hχa, hker⟩ :=
    IsLocalRing.exists_ringHom_comp_algebraMap_eq_and_ker_eq_span_of_injective_of_finite (A := ↥A) (S := ↥S) t
      hinj hfib
  refine ⟨χ, fun a => ?_, ?_, hker⟩
  · rw [← hιa]; exact hχa a
  · have h0 : χ t = 0 := by rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self t
    have : T = t + cS := by rw [ht, sub_add_cancel]
    rw [this, map_add, h0, zero_add, ← hcS']
    exact hχa c

end S_AlgebraicCurve_exists_section_localRing_apply_eq_of_ord_eq_one_of_mem_smoothLocus
end P2MW
export P2MW.S_AlgebraicCurve_exists_section_localRing_apply_eq_of_ord_eq_one_of_mem_smoothLocus (solution)
