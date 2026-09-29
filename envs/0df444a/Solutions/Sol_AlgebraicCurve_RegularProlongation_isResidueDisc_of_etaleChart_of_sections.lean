-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.isResidueDisc_of_etaleChart_of_sections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4409f5d9-693f-54d1-8e83-24c6ca137be1

import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_isResidueDisc_of_etaleChart_of_sections

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace DiscGenBody

open AlgebraicCurve IsLocalRing

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_eq_of_residue_eq (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) {a : K}
    (h : residue ↥v.toValuationSubring ⟨f, hf⟩ = algebraMap K v.ResidueField a) : v.evalAt f = a :=
  v.algebraMap_residueField_injective (by rw [v.algebraMap_evalAt hv hf, h])

theorem residue_algebraMap_eq (v : Place K F) (a : K) :
    residue ↥v.toValuationSubring ⟨algebraMap K F a, v.algebraMap_mem' a⟩ = algebraMap K v.ResidueField a := by
  rw [IsScalarTower.algebraMap_apply K ↥v.toValuationSubring v.ResidueField]
  rfl

theorem evalAt_algebraMap (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a), residue_algebraMap_eq, v.residueInv_algebraMap]

theorem evalAt_add (v : Place K F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f + g) = v.evalAt f + v.evalAt g :=
  v.algebraMap_residueField_injective (by
    rw [v.algebraMap_evalAt hv (add_mem hf hg), map_add, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
      ← map_add]
    rfl)

theorem evalAt_sub (v : Place K F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f - g) = v.evalAt f - v.evalAt g :=
  v.algebraMap_residueField_injective (by
    rw [v.algebraMap_evalAt hv (sub_mem hf hg), map_sub, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
      ← map_sub]
    rfl)

theorem evalAt_zero (v : Place K F) : v.evalAt (0 : F) = 0 := by
  rw [← map_zero (algebraMap K F), evalAt_algebraMap]

noncomputable def sectionOfPlace {L : Type*} [Field L] {A : ValuationSubring L} [Algebra L F] (S : Subring F)
    (P : Place L F) (hrat : P.IsRational)
    (hreg : ∀ f : ↥S, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) : ↥S →+* ↥A where
  toFun f := ⟨P.evalAt (f : F), (hreg f).2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' f g := Subtype.ext (by
    show P.evalAt ((f * g : ↥S) : F) = P.evalAt (f : F) * P.evalAt (g : F)
    rw [Subring.coe_mul]; exact P.evalAt_mul hrat (hreg f).1 (hreg g).1)
  map_zero' := Subtype.ext (by show P.evalAt ((0 : ↥S) : F) = 0; rw [Subring.coe_zero]; exact evalAt_zero P)
  map_add' f g := Subtype.ext (by
    show P.evalAt ((f + g : ↥S) : F) = P.evalAt (f : F) + P.evalAt (g : F)
    rw [Subring.coe_add]; exact evalAt_add P hrat (hreg f).1 (hreg g).1)

theorem sectionOfPlace_apply {L : Type*} [Field L] {A : ValuationSubring L} [Algebra L F] (S : Subring F)
    (P : Place L F) (hrat : P.IsRational)
    (hreg : ∀ f : ↥S, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) (f : ↥S) :
    ((sectionOfPlace S P hrat hreg f : ↥A) : L) = P.evalAt (f : F) := rfl

end DiscGenBody

namespace DiscGenBody
open AlgebraicCurve IsLocalRing

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_eq_zero_of_isUnit (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : ↥v.toValuationSubring)) : v.ord f = 0 := by
  obtain ⟨u, hu⟩ := hu
  have : f = ((u : ↥v.toValuationSubring) : F) := by rw [hu]
  rw [this]; exact v.ord_coe_unit u

theorem isUnit_of_mul_eq_one_mem (v : Place K F) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) (h : f * g = 1) : IsUnit (⟨f, hf⟩ : ↥v.toValuationSubring) :=
  IsUnit.of_mul_eq_one (⟨g, hg⟩ : ↥v.toValuationSubring) (Subtype.ext h)

theorem ord_algebraMap (v : Place K F) {a : K} (ha : a ≠ 0) : v.ord (algebraMap K F a) = 0 :=
  ord_eq_zero_of_isUnit v (v.algebraMap_mem' a)
    (isUnit_of_mul_eq_one_mem v (v.algebraMap_mem' a) (v.algebraMap_mem' a⁻¹)
      (by rw [← map_mul, mul_inv_cancel₀ ha, map_one]))

theorem ord_eq_zero_of_evalAt_ne_zero (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  apply ord_eq_zero_of_isUnit v hf
  by_contra hu
  have hm : (⟨f, hf⟩ : ↥v.toValuationSubring) ∈ maximalIdeal _ := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)
  have h0 : residue _ (⟨f, hf⟩ : ↥v.toValuationSubring) = 0 := (residue_eq_zero_iff _).mpr hm
  rw [← v.algebraMap_evalAt hv hf, map_eq_zero_iff _ v.algebraMap_residueField_injective] at h0
  exact h h0

theorem ord_prod (v : Place K F) {ι : Type*} (s : Finset ι) (x : ι → F) (h : ∀ i ∈ s, x i ≠ 0) :
    v.ord (∏ i ∈ s, x i) = ∑ i ∈ s, v.ord (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      v.ord_mul (h a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.mpr fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

end DiscGenBody

open AlgebraicCurve IsLocalRing in

theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)

    (S : Subring F) (hAS : ∀ a : ↥A, algebraMap L F (a : L) ∈ S)
    (φ : Polynomial ↥A →+* ↥S) (hφs : φ.FormallySmooth) (hφu : φ.FormallyUnramified)
    (hφC : ∀ a : ↥A, ((φ (Polynomial.C a) : ↥S) : F) = algebraMap L F (a : L))
    (χ₀ : ↥S →+* ResidueField ↥A) (hχ₀C : ∀ a : ↥A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue ↥A a)
    (hχ₀t : χ₀ (φ Polynomial.X) = 0)

    (hchart : ∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
      ∃! χ : ↥S →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) ∧
        (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φ Polynomial.X) = c)

    (hSR : ∀ f : ↥S, (f : F) ∈ R.integers)
    (hres : ∀ f : ↥S, ∃ hm : R.residue ⟨(f : F), hSR f⟩ ∈ Q.toValuationSubring,
      IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hSR f⟩, hm⟩ =
        algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f))
    (hordQ : Q.ord (R.residue ⟨((φ Polynomial.X : ↥S) : F), hSR (φ Polynomial.X)⟩) = 1)

    (D : Set (Place L F))
    (hD : ∀ P ∈ D, P.IsRational ∧ (∀ f : ↥S, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
      (∀ f : ↥S, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₀ f = 0))

    (hsec : ∀ χ : ↥S →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) →
      (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) →
      ∃! P, P ∈ D ∧ ∀ f : ↥S, P.evalAt (f : F) = ((χ f : ↥A) : L))

    (hval : ∀ P ∈ D, ∀ f : F, f ∈ P.toValuationSubring ↔ ∃ g h : ↥S, P.evalAt (h : F) ≠ 0 ∧ f * (h : F) = (g : F))

    (hloc : ∀ f : F, f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
      ∃ (c : L) (u : (↥S)ˣ), c ≠ 0 ∧ algebraMap L F c * f = ((u : ↥S) : F))
    (hloc' : ∀ f : F, f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S) :
    R.IsResidueDisc Q D ((φ Polynomial.X : ↥S) : F) := by
  classical
  set t : F := ((φ Polynomial.X : ↥S) : F) with ht

  have key : ∀ P ∈ D, ∀ s : ↥S, ∃ h : P.evalAt (s : F) ∈ A, IsLocalRing.residue ↥A ⟨P.evalAt (s : F), h⟩ = χ₀ s := by
    intro P hP s
    obtain ⟨hrat, hreg, hsmall⟩ := hD P hP
    refine ⟨(hreg s).2, ?_⟩
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (χ₀ s)
    have hg0 : χ₀ (s - φ (Polynomial.C a)) = 0 := by rw [map_sub, hχ₀C, ha, sub_self]
    have hval : A.valuation (P.evalAt ((s - φ (Polynomial.C a) : ↥S) : F)) < 1 := (hsmall _).mpr hg0
    have hmem : (⟨P.evalAt ((s - φ (Polynomial.C a) : ↥S) : F), (hreg _).2⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A :=
      (A.valuation_lt_one_iff _).mpr hval
    have h0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    have hsub : (⟨P.evalAt ((s - φ (Polynomial.C a) : ↥S) : F), (hreg _).2⟩ : ↥A) =
        ⟨P.evalAt (s : F), (hreg s).2⟩ - a := by
      apply Subtype.ext
      show P.evalAt ((s - φ (Polynomial.C a) : ↥S) : F) = P.evalAt (s : F) - (a : L)
      rw [show ((s - φ (Polynomial.C a) : ↥S) : F) = (s : F) - (φ (Polynomial.C a) : F) from rfl,
        DiscGenBody.evalAt_sub P hrat (hreg s).1 (hreg _).1, hφC, DiscGenBody.evalAt_algebraMap]
    rw [hsub, map_sub, ha, sub_eq_zero] at h0
    exact h0
  have hexu : ∀ c : L, A.valuation c < 1 → ∃! P, P ∈ D ∧ P.evalAt ((φ Polynomial.X : ↥S) : F) = c := by
    intro c hc
    have hcA : c ∈ A := (A.valuation_le_one_iff c).mp hc.le
    have hc0 : IsLocalRing.residue ↥A ⟨c, hcA⟩ = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr ((A.valuation_lt_one_iff ⟨c, hcA⟩).mpr hc)
    obtain ⟨χ, ⟨hχC, hχres, hχt⟩, hχuniq⟩ := hchart ⟨c, hcA⟩ hc0
    obtain ⟨P, ⟨hPD, hPχ⟩, hPuniq⟩ := hsec χ hχC hχres
    refine ⟨P, ⟨hPD, by rw [hPχ, hχt]⟩, ?_⟩
    rintro P' ⟨hP'D, hP't⟩
    obtain ⟨hrat', hreg', hsmall'⟩ := hD P' hP'D
    set χ' := DiscGenBody.sectionOfPlace S P' hrat' hreg' with hχ'def
    have hχ'C : ∀ a : ↥A, χ' (φ (Polynomial.C a)) = a := fun a => Subtype.ext (by
      rw [DiscGenBody.sectionOfPlace_apply, hφC]; exact DiscGenBody.evalAt_algebraMap P' (a : L))
    have hχ'res : ∀ f : ↥S, IsLocalRing.residue ↥A (χ' f) = χ₀ f := by
      intro f
      obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (χ₀ f)

      have hg0 : χ₀ (f - φ (Polynomial.C a)) = 0 := by rw [map_sub, hχ₀C, ha, sub_self]
      have hval : A.valuation (P'.evalAt ((f - φ (Polynomial.C a) : ↥S) : F)) < 1 := (hsmall' _).mpr hg0
      have hmem : (χ' (f - φ (Polynomial.C a)) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A :=
        (A.valuation_lt_one_iff _).mpr (by rw [DiscGenBody.sectionOfPlace_apply]; exact hval)
      have h0 : IsLocalRing.residue ↥A (χ' (f - φ (Polynomial.C a))) = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).mpr hmem
      rw [map_sub, map_sub, hχ'C, ha, sub_eq_zero] at h0
      exact h0
    have hχ't : χ' (φ Polynomial.X) = ⟨c, hcA⟩ := Subtype.ext (by rw [DiscGenBody.sectionOfPlace_apply]; exact hP't)
    have heq : χ' = χ := hχuniq χ' ⟨hχ'C, hχ'res, hχ't⟩
    exact hPuniq P' ⟨hP'D, fun f => by rw [← heq]; rfl⟩

  have hunif : ∀ P ∈ D, P.ord (((φ Polynomial.X : ↥S) : F) - algebraMap L F (P.evalAt ((φ Polynomial.X : ↥S) : F))) = 1 := by
    intro P hP
    obtain ⟨hrat, hreg, hsmall⟩ := hD P hP
    set O := P.toValuationSubring with hOdef
    have hSO : ∀ f : ↥S, (f : F) ∈ O := fun f => (hreg f).1

    let ι : ↥S →+* ↥O :=
      { toFun := fun f => ⟨(f : F), hSO f⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun f g => Subtype.ext (by simp)
        map_zero' := Subtype.ext (by simp)
        map_add' := fun f g => Subtype.ext (by simp) }
    have hι : ∀ f : ↥S, ((ι f : ↥O) : F) = (f : F) := fun f => rfl
    let χ := DiscGenBody.sectionOfPlace S P hrat hreg
    have hχ : ∀ f : ↥S, ((χ f : ↥A) : L) = P.evalAt (f : F) := fun f => rfl

    have hresO : ∀ f : ↥S, IsLocalRing.residue ↥O (ι f) = algebraMap L P.ResidueField (P.evalAt (f : F)) :=
      fun f => (P.algebraMap_evalAt hrat (hSO f)).symm
    have halgO : ∀ a : L, IsLocalRing.residue ↥O (algebraMap L ↥O a) = algebraMap L P.ResidueField a := fun a =>
      (IsScalarTower.algebraMap_apply L ↥O P.ResidueField a).symm

    set m := IsLocalRing.maximalIdeal ↥O with hmdef
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥O
    obtain ⟨g, h, hh0, hgh⟩ := (hval P hP (ϖ : F)).mp ϖ.2
    have hhunit : IsUnit (ι h) := by
      by_contra hu
      have hm : ι h ∈ m := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)
      have h0 : IsLocalRing.residue ↥O (ι h) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hm
      rw [hresO, map_eq_zero_iff _ (algebraMap L P.ResidueField).injective] at h0
      exact hh0 h0
    have hgirr : Irreducible (ι g) := by
      have : ι g = ϖ * ι h := Subtype.ext (by rw [hι]; exact hgh.symm)
      rw [this]; exact (irreducible_mul_isUnit hhunit).mpr hϖ
    have hg0 : P.evalAt (g : F) = 0 := by
      apply DiscGenBody.evalAt_eq_of_residue_eq P hrat (hSO g)
      rw [map_zero, IsLocalRing.residue_eq_zero_iff]
      show ι g ∈ m
      rw [hmdef, hgirr.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self _

    set c := P.evalAt ((φ Polynomial.X : ↥S) : F) with hcdef
    have htO : ((φ Polynomial.X : ↥S) : F) - algebraMap L F c ∈ O := sub_mem (hSO _) (P.algebraMap_mem' c)
    have hnot2 : (⟨_, htO⟩ : ↥O) ∉ m ^ 2 := by
      intro H

      letI algS : Algebra (Polynomial ↥A) ↥S := φ.toAlgebra
      haveI : Algebra.FormallyUnramified (Polynomial ↥A) ↥S := hφu
      let mk2 := Ideal.Quotient.mk (m ^ 2)
      letI algB : Algebra (Polynomial ↥A) (↥O ⧸ m ^ 2) := (mk2.comp (ι.comp φ)).toAlgebra
      let g₁ : ↥S →ₐ[Polynomial ↥A] (↥O ⧸ m ^ 2) :=
        { toRingHom := mk2.comp ι, commutes' := fun p => rfl }
      let ρ : ↥S →+* ↥O := (algebraMap L ↥O).comp (A.subtype.comp χ)
      have hρC : ∀ a : ↥A, ρ (φ (Polynomial.C a)) = ι (φ (Polynomial.C a)) := by
        intro a; apply Subtype.ext
        show (algebraMap L ↥O ((χ (φ (Polynomial.C a)) : ↥A) : L) : F) = (φ (Polynomial.C a) : F)
        rw [hχ, hφC, DiscGenBody.evalAt_algebraMap, Place.coe_algebraMap]
      have hρX : mk2 (ρ (φ Polynomial.X)) = mk2 (ι (φ Polynomial.X)) := by
        rw [eq_comm, Ideal.Quotient.eq]
        convert H using 1
        rfl
      let g₂ : ↥S →ₐ[Polynomial ↥A] (↥O ⧸ m ^ 2) :=
        { toRingHom := mk2.comp ρ
          commutes' := fun p => by
            show (mk2.comp ρ) (φ p) = (mk2.comp (ι.comp φ)) p
            have : (mk2.comp ρ).comp φ = mk2.comp (ι.comp φ) := by
              apply Polynomial.ringHom_ext
              · intro a; show mk2 (ρ (φ (Polynomial.C a))) = mk2 (ι (φ (Polynomial.C a))); rw [hρC]
              · show mk2 (ρ (φ Polynomial.X)) = mk2 (ι (φ Polynomial.X)); exact hρX
            exact RingHom.congr_fun this p }

      let red : ↥O ⧸ m ^ 2 →+* ↥O ⧸ m := Ideal.Quotient.factor (Ideal.pow_le_self two_ne_zero)
      have hker : IsNilpotent (RingHom.ker red) := by
        refine ⟨2, ?_⟩
        have : RingHom.ker red = m.map mk2 := by
          ext x; obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
          show red (mk2 y) = 0 ↔ _
          rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
          constructor
          · intro hy; exact ⟨y, hy, rfl⟩
          · rintro ⟨z, hz, hzy⟩; rw [Ideal.Quotient.eq] at hzy;
            have : z - (z - y) ∈ m := sub_mem hz (Ideal.pow_le_self two_ne_zero hzy)
            simpa using this
        rw [this, ← Ideal.map_pow, Ideal.map_quotient_self]; rfl
      have hagree : ∀ x : ↥S, red (g₁ x) = red (g₂ x) := by
        intro x
        show red (mk2 (ι x)) = red (mk2 (ρ x))
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk]
        show IsLocalRing.residue ↥O (ι x) = IsLocalRing.residue ↥O (algebraMap L ↥O ((χ x : ↥A) : L))
        rw [hresO, halgO, hχ]
      have heq := Algebra.FormallyUnramified.ext' red hker g₁ g₂ hagree

      have hgm2 : mk2 (ι g) = mk2 (ρ g) := congrArg (fun φ' : ↥S →ₐ[Polynomial ↥A] (↥O ⧸ m ^ 2) => φ' g) heq
      have hρg : ρ g = 0 := by
        apply Subtype.ext
        show (algebraMap L ↥O ((χ g : ↥A) : L) : F) = 0
        rw [hχ, hg0, map_zero]; rfl
      rw [hρg, map_zero, Ideal.Quotient.eq_zero_iff_mem] at hgm2

      rw [hmdef, hgirr.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hgm2
      obtain ⟨z, hz⟩ := hgm2
      have h2 : ι g * (ι g * z) = ι g * 1 := by rw [mul_one, ← mul_assoc, ← pow_two]; exact hz.symm
      have h3 : ι g * z = 1 := mul_left_cancel₀ hgirr.ne_zero h2
      exact hgirr.not_isUnit (IsUnit.of_mul_eq_one _ h3)

    have hmem : (⟨_, htO⟩ : ↥O) ∈ m := by
      rw [hmdef, ← IsLocalRing.residue_eq_zero_iff]
      have := P.algebraMap_evalAt hrat htO
      rw [DiscGenBody.evalAt_sub P hrat (hSO _) (P.algebraMap_mem' c), DiscGenBody.evalAt_algebraMap, ← hcdef,
        sub_self, map_zero] at this
      exact this.symm
    have hne : (⟨_, htO⟩ : ↥O) ≠ 0 := fun h0 => hnot2 (h0.symm ▸ (m ^ 2).zero_mem)
    obtain ⟨n, u, hnu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
    have hn1 : n = 1 := by
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · interval_cases n
        · exfalso; rw [pow_zero, mul_one] at hnu
          exact (IsLocalRing.mem_maximalIdeal _ |>.mp hmem) (hnu ▸ u.isUnit)
        · rfl
      · exfalso; apply hnot2; rw [hnu, hmdef, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton.mpr ⟨ϖ ^ (n - 2), by rw [← pow_add, Nat.add_sub_cancel' hge]⟩)
    rw [hn1, pow_one] at hnu
    show P.ord (((φ Polynomial.X : ↥S) : F) - algebraMap L F c) = 1
    have : ((φ Polynomial.X : ↥S) : F) - algebraMap L F c = ((u : ↥O) : F) * ((ϖ : ↥O) : F) := by
      rw [← Subring.coe_mul]; exact congrArg Subtype.val hnu
    rw [this, P.ord_mul (by exact_mod_cast u.ne_zero) (by exact_mod_cast hϖ.ne_zero), P.ord_coe_unit, P.ord_coe_irreducible hϖ, zero_add]

  refine ⟨⟨?disc, ?rest⟩, ?pw, ?deg⟩
  ·
    intro P hP
    obtain ⟨hrat, hreg, hsmall⟩ := hD P hP
    exact ⟨hrat, (hreg (φ Polynomial.X)).1, (hsmall (φ Polynomial.X)).2 hχ₀t⟩
  · refine ⟨hSR (φ Polynomial.X), hordQ, ?exu, ?unif, ?unit⟩
    · exact hexu
    · exact hunif
    ·
      intro f hf0 hord
      obtain ⟨c, u, hc0, hcf⟩ := hloc f hf0 hord
      refine ⟨c⁻¹, inv_ne_zero hc0, fun P hP => ?_⟩
      obtain ⟨hrat, hreg, hsmall⟩ := hD P hP
      have hu := (hreg (u : ↥S)).1
      have hui := (hreg ((u⁻¹ : (↥S)ˣ) : ↥S)).1
      have hprod : P.evalAt (((u : (↥S)ˣ) : ↥S) : F) * P.evalAt (((u⁻¹ : (↥S)ˣ) : ↥S) : F) = 1 := by
        rw [← P.evalAt_mul hrat hu hui, ← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Subring.coe_one, Place.evalAt_one]
      have hvu : A.valuation (P.evalAt (((u : (↥S)ˣ) : ↥S) : F)) = 1 := by
        have ha : A.valuation (P.evalAt (((u : (↥S)ˣ) : ↥S) : F)) ≤ 1 := (A.valuation_le_one_iff _).mpr (hreg _).2
        have hb : A.valuation (P.evalAt (((u⁻¹ : (↥S)ˣ) : ↥S) : F)) ≤ 1 := (A.valuation_le_one_iff _).mpr (hreg _).2
        have h1 : A.valuation (P.evalAt (((u : (↥S)ˣ) : ↥S) : F)) * A.valuation (P.evalAt (((u⁻¹ : (↥S)ˣ) : ↥S) : F)) = 1 := by
          rw [← map_mul, hprod, map_one]
        refine le_antisymm ha ?_
        calc (1 : _) = _ := h1.symm
          _ ≤ A.valuation (P.evalAt (((u : (↥S)ˣ) : ↥S) : F)) * 1 := mul_le_mul_right hb _
          _ = _ := mul_one _
      have hf : f = algebraMap L F c⁻¹ * (((u : (↥S)ˣ) : ↥S) : F) := by
        rw [← hcf, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      rw [hf, P.evalAt_mul hrat (P.algebraMap_mem' _) hu, DiscGenBody.evalAt_algebraMap, map_mul, hvu, mul_one]
  ·
    intro P hP hrat f hf hw
    have hfS : f ∈ S := hloc' f hf hw
    obtain ⟨hm, hresQ⟩ := hres ⟨f, hfS⟩
    obtain ⟨hA, hkey⟩ := key P hP ⟨f, hfS⟩
    exact ⟨hm, hA, by rw [hkey]; exact hresQ.symm⟩
  ·
    intro f hf0 D' hon hoff
    have ht0Q : R.residue ⟨t, hSR (φ Polynomial.X)⟩ ≠ 0 := by
      intro h0; have h1 : Q.ord (R.residue ⟨t, hSR (φ Polynomial.X)⟩) = 1 := hordQ
      rw [h0, Place.ord_zero] at h1; exact zero_ne_one h1

    have hsuppD : ∀ P ∈ D'.support, P ∈ D := fun P hP => by
      by_contra h; exact (Finsupp.mem_support_iff.mp hP) (hoff P h)

    have hcA : ∀ P ∈ D, P.evalAt t ∈ A := fun P hP => ((hD P hP).2.1 (φ Polynomial.X)).2
    have hcm : ∀ P (hP : P ∈ D), IsLocalRing.residue ↥A ⟨P.evalAt t, hcA P hP⟩ = 0 := fun P hP =>
      (IsLocalRing.residue_eq_zero_iff _).mpr ((A.valuation_lt_one_iff _).mpr (((hD P hP).2.2 (φ Polynomial.X)).mpr hχ₀t))
    set ℓ : Place L F → F := fun P => t - algebraMap L F (P.evalAt t) with hℓdef
    have hℓS : ∀ P ∈ D, ℓ P ∈ S := fun P hP => S.sub_mem (φ Polynomial.X).2 (hAS ⟨_, hcA P hP⟩)
    have hℓR : ∀ P ∈ D, ℓ P ∈ R.integers := fun P hP => hSR ⟨_, hℓS P hP⟩
    have hresℓ : ∀ P (hP : P ∈ D), R.residue ⟨ℓ P, hℓR P hP⟩ = R.residue ⟨t, hSR (φ Polynomial.X)⟩ := by
      intro P hP
      have : (⟨ℓ P, hℓR P hP⟩ : ↥R.integers) = ⟨t, hSR (φ Polynomial.X)⟩ - ⟨algebraMap L F (P.evalAt t), (R.algebraMap_mem_iff _).mpr (hcA P hP)⟩ :=
        Subtype.ext rfl
      rw [this, map_sub, show (⟨algebraMap L F (P.evalAt t), _⟩ : ↥R.integers) = ⟨algebraMap L F ((⟨P.evalAt t, hcA P hP⟩ : ↥A) : L), (R.algebraMap_mem_iff _).mpr (hcA P hP)⟩ from rfl,
        R.residue_algebraMap ⟨P.evalAt t, hcA P hP⟩, hcm P hP, map_zero, sub_zero]
    have hℓunit : ∀ P (hP : P ∈ D), IsUnit (⟨ℓ P, hℓR P hP⟩ : ↥R.integers) := fun P hP =>
      R.isUnit_of_residue_ne_zero (by rw [hresℓ P hP]; exact ht0Q)
    have hℓ0 : ∀ P ∈ D, ℓ P ≠ 0 := fun P hP h0 => by
      have := (hℓunit P hP).ne_zero; exact this (Subtype.ext h0)
    have hordℓ : ∀ P ∈ D, ∀ P' ∈ D, P'.ord (ℓ P) = if P' = P then (1 : ℤ) else 0 := by
      intro P hP P' hP'
      split_ifs with h
      · subst h; exact hunif P' hP'
      · apply DiscGenBody.ord_eq_zero_of_evalAt_ne_zero P' (hD P' hP').1 ((hD P' hP').2.1 ⟨_, hℓS P hP⟩).1
        show P'.evalAt (t - algebraMap L F (P.evalAt t)) ≠ 0
        rw [DiscGenBody.evalAt_sub P' (hD P' hP').1 ((hD P' hP').2.1 (φ Polynomial.X)).1 (P'.algebraMap_mem' _),
          DiscGenBody.evalAt_algebraMap, sub_ne_zero]
        intro heq
        obtain ⟨P₀, -, huniq⟩ := hexu (P.evalAt t) (((hD P hP).2.2 (φ Polynomial.X)).mpr hχ₀t)
        exact h ((huniq P' ⟨hP', heq⟩).trans (huniq P ⟨hP, rfl⟩).symm)

    classical
    let ℓu : Place L F → (↥R.integers)ˣ := fun P => if hP : P ∈ D then (hℓunit P hP).unit else 1
    have hℓu : ∀ P (hP : P ∈ D), ((ℓu P : ↥R.integers) : F) = ℓ P := by
      intro P hP; simp only [ℓu, dif_pos hP, IsUnit.unit_spec]
    let W : (↥R.integers)ˣ := ∏ P ∈ D'.support, ℓu P ^ (D' P)
    set w : F := ∏ P ∈ D'.support, ℓ P ^ (D' P) with hwdef
    have hWw : ((W : ↥R.integers) : F) = w := by
      let e : (↥R.integers)ˣ →* Fˣ := Units.map (R.integers.subtype : ↥R.integers →* F)
      have h1 : ((e W : Fˣ) : F) = ((W : ↥R.integers) : F) := rfl
      rw [← h1, map_prod, Units.coe_prod]
      refine Finset.prod_congr rfl fun P hP => ?_
      rw [map_zpow, Units.val_zpow_eq_zpow_val]
      congr 1
      exact hℓu P (hsuppD P hP)
    have hw0 : w ≠ 0 := by rw [← hWw]; exact fun h => W.ne_zero (Subtype.ext h)
    have hordw : ∀ P' ∈ D, P'.ord w = D' P' := by
      intro P' hP'
      rw [hwdef, DiscGenBody.ord_prod _ _ _ (fun P hP => zpow_ne_zero _ (hℓ0 P (hsuppD P hP)))]
      simp_rw [Place.ord_zpow]
      rw [Finset.sum_congr rfl (fun P hP => by rw [hordℓ P (hsuppD P hP) P' hP'])]
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · exact (Finsupp.notMem_support_iff.mp h).symm

    have hf0' : (f : F) ≠ 0 := fun h => hf0 (by rw [show f = 0 from Subtype.ext h, map_zero])
    set g : F := (f : F) * w⁻¹ with hgdef
    have hg0 : g ≠ 0 := mul_ne_zero hf0' (inv_ne_zero hw0)
    have hordg : ∀ P ∈ D, P.ord g = 0 := fun P hP => by
      rw [hgdef, P.ord_mul hf0' (inv_ne_zero hw0), P.ord_inv, hordw P hP, hon P hP, add_neg_cancel]
    obtain ⟨c, u, hc0, hcg⟩ := hloc g hg0 hordg

    have huR : ((u : ↥S) : F) ∈ R.integers := hSR _
    have hfunit : IsUnit f := R.isUnit_of_residue_ne_zero hf0
    have hcR : algebraMap L F c ∈ R.integers := by
      have : algebraMap L F c = ((u : ↥S) : F) * w * (f : F)⁻¹ := by
        rw [← hcg, hgdef]; field_simp
      obtain ⟨v, hv⟩ := hfunit.exists_right_inv
      have hfinv : ((f : F))⁻¹ = (v : F) := (eq_inv_of_mul_eq_one_right (congrArg Subtype.val hv)).symm
      rw [this, hfinv]
      exact mul_mem (mul_mem huR (hWw ▸ (W : ↥R.integers).2)) v.2
    have heqR : (⟨algebraMap L F c, hcR⟩ : ↥R.integers) * f = ⟨(u : ↥S), huR⟩ * (W : ↥R.integers) := by
      apply Subtype.ext
      show algebraMap L F c * (f : F) = ((u : ↥S) : F) * ((W : ↥R.integers) : F)
      rw [hWw, ← hcg, hgdef]; field_simp
    have hcA' : c ∈ A := (R.algebraMap_mem_iff c).mp hcR
    have hres_eq := congrArg R.residue heqR
    rw [map_mul, map_mul, show (⟨algebraMap L F c, hcR⟩ : ↥R.integers) = ⟨algebraMap L F ((⟨c, hcA'⟩ : ↥A) : L), (R.algebraMap_mem_iff _).mpr hcA'⟩ from rfl,
      R.residue_algebraMap ⟨c, hcA'⟩] at hres_eq

    have hresW : R.residue (W : ↥R.integers) = ∏ P ∈ D'.support, (R.residue ⟨t, hSR (φ Polynomial.X)⟩) ^ (D' P) := by
      let r : (↥R.integers)ˣ →* Fbarˣ := Units.map R.residue.toMonoidHom
      have h1 : ((r W : Fbarˣ) : Fbar) = R.residue (W : ↥R.integers) := rfl
      rw [← h1, map_prod, Units.coe_prod]
      refine Finset.prod_congr rfl fun P hP => ?_
      rw [map_zpow, Units.val_zpow_eq_zpow_val]
      congr 1
      show R.residue ((ℓu P : ↥R.integers)) = _
      have : (ℓu P : ↥R.integers) = ⟨ℓ P, hℓR P (hsuppD P hP)⟩ := by
        apply Subtype.ext; exact hℓu P (hsuppD P hP)
      rw [this, hresℓ P (hsuppD P hP)]
    obtain ⟨hum, huresQ⟩ := hres (u : ↥S)
    obtain ⟨huim, huiresQ⟩ := hres ((u⁻¹ : (↥S)ˣ) : ↥S)
    have hprodS : ((u : ↥S) : F) * (((u⁻¹ : (↥S)ˣ) : ↥S) : F) = 1 :=
      congrArg Subtype.val u.mul_inv
    have hprodR : (⟨((u : ↥S) : F), huR⟩ : ↥R.integers) * ⟨(((u⁻¹ : (↥S)ˣ) : ↥S) : F), hSR _⟩ = 1 := Subtype.ext hprodS
    have hres1 : R.residue ⟨((u : ↥S) : F), huR⟩ * R.residue ⟨(((u⁻¹ : (↥S)ˣ) : ↥S) : F), hSR _⟩ = 1 := by
      rw [← map_mul, hprodR, map_one]
    have hresu0 : Q.ord (R.residue ⟨((u : ↥S) : F), huR⟩) = 0 :=
      DiscGenBody.ord_eq_zero_of_isUnit Q hum (DiscGenBody.isUnit_of_mul_eq_one_mem Q hum huim hres1)
    have hresune : R.residue ⟨((u : ↥S) : F), huR⟩ ≠ 0 := left_ne_zero_of_mul_eq_one hres1
    have hresW0 : R.residue (W : ↥R.integers) ≠ 0 := R.residue_ne_zero_of_isUnit W.isUnit
    have hresc0 : IsLocalRing.residue ↥A ⟨c, hcA'⟩ ≠ 0 := by
      intro h0; rw [h0, map_zero, zero_mul] at hres_eq; exact (mul_ne_zero hresune hresW0) hres_eq.symm

    have hordc : Q.ord (algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A ⟨c, hcA'⟩)) = 0 :=
      DiscGenBody.ord_algebraMap Q hresc0
    have key2 := congrArg Q.ord hres_eq
    rw [Q.ord_mul (by exact (map_ne_zero _).mpr hresc0) hf0, Q.ord_mul hresune hresW0, hordc, hresu0, zero_add, zero_add,
      hresW, DiscGenBody.ord_prod _ _ _ (fun P hP => zpow_ne_zero _ ht0Q)] at key2
    simp_rw [Place.ord_zpow] at key2
    have h1 : Q.ord (R.residue ⟨t, hSR (φ Polynomial.X)⟩) = 1 := hordQ
    simp_rw [h1, mul_one] at key2
    rw [key2]
    rfl

end S_AlgebraicCurve_RegularProlongation_isResidueDisc_of_etaleChart_of_sections
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_isResidueDisc_of_etaleChart_of_sections (solution)
