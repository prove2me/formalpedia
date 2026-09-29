-- Prove2me | solution 1 for AlgebraicCurve.Place.sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/1fe3fc7c-e048-5352-8341-e3431234c247

import Mathlib
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg
import Theorems.Thm_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq
import Theorems.Thm_AlgebraicCurve_Place_restrict_ofAlgAut_smul
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open AlgebraicCurve KaehlerDifferential Polynomial

namespace HilbertWildLB

section OrdCalc

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

def OrdGe (m : ℤ) (f : F) : Prop := f = 0 ∨ m ≤ v.ord f

theorem ordGe_zero (m : ℤ) : OrdGe v m 0 := Or.inl rfl

variable {v}

theorem ordGe_of_le {m : ℤ} {f : F} (h : m ≤ v.ord f) : OrdGe v m f := Or.inr h

theorem OrdGe.mono {m n : ℤ} {f : F} (h : OrdGe v n f) (hmn : m ≤ n) : OrdGe v m f := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (hmn.trans h)

theorem OrdGe.le_ord {m : ℤ} {f : F} (h : OrdGe v m f) (hf : f ≠ 0) : m ≤ v.ord f := by
  rcases h with h | h
  · exact (hf h).elim
  · exact h

theorem ord_neg' (f : F) : v.ord (-f) = v.ord f := by
  simp only [Place.ord, Valuation.map_neg]

theorem OrdGe.neg {m : ℤ} {f : F} (h : OrdGe v m f) : OrdGe v m (-f) := by
  rcases h with h | h
  · exact Or.inl (by rw [h, neg_zero])
  · exact Or.inr (by rwa [ord_neg'])

theorem OrdGe.add {m : ℤ} {f g : F} (hf : OrdGe v m f) (hg : OrdGe v m g) : OrdGe v m (f + g) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rwa [zero_add]
  rcases eq_or_ne g 0 with rfl | hg0
  · rwa [add_zero]
  rcases eq_or_ne (f + g) 0 with hfg | hfg
  · exact Or.inl hfg
  · have h := Place.min_ord_le_ord_add v hf0 hg0 hfg
    exact Or.inr (le_trans (le_min (hf.le_ord hf0) (hg.le_ord hg0)) h)

theorem OrdGe.sub {m : ℤ} {f g : F} (hf : OrdGe v m f) (hg : OrdGe v m g) : OrdGe v m (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem OrdGe.mul {m n : ℤ} {f g : F} (hf : OrdGe v m f) (hg : OrdGe v n g) :
    OrdGe v (m + n) (f * g) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [zero_mul]; exact ordGe_zero v _
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero]; exact ordGe_zero v _
  exact Or.inr (by rw [v.ord_mul hf0 hg0]; exact add_le_add (hf.le_ord hf0) (hg.le_ord hg0))

theorem OrdGe.sum {ι : Type*} (s : Finset ι) {m : ℤ} {f : ι → F} (h : ∀ i ∈ s, OrdGe v m (f i)) :
    OrdGe v m (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact ordGe_zero v m
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ord_add_eq_of_ordGe {m : ℤ} {f g : F} (hf0 : f ≠ 0) (hfm : v.ord f = m)
    (hg : OrdGe v (m + 1) g) : f + g ≠ 0 ∧ v.ord (f + g) = m := by
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [add_zero]; exact ⟨hf0, hfm⟩
  have hgm : m + 1 ≤ v.ord g := hg.le_ord hg0
  have hne : f + g ≠ 0 := by
    intro h
    have : f = -g := eq_neg_of_add_eq_zero_left h
    rw [this, ord_neg'] at hfm
    omega
  refine ⟨hne, le_antisymm ?_ ?_⟩
  · by_contra hlt
    push Not at hlt

    have h := Place.min_ord_le_ord_add v hne (neg_ne_zero.mpr hg0)
      (by rw [add_neg_cancel_right]; exact hf0)
    rw [add_neg_cancel_right, ord_neg', hfm] at h
    have : m < min (v.ord (f + g)) (v.ord g) := lt_min hlt (by omega)
    omega
  · have h := Place.min_ord_le_ord_add v hf0 hg0 hne
    rw [hfm] at h
    exact le_trans (le_min le_rfl (by omega)) h

theorem ord_prod {ι : Type*} (s : Finset ι) (f : ι → F) (h : ∀ i ∈ s, f i ≠ 0) :
    v.ord (∏ i ∈ s, f i) = ∑ i ∈ s, v.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      v.ord_mul (h a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem ord_pow' (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

theorem algebraMap_eq_zero_of_ordGe {c : K} (h : OrdGe v 1 (algebraMap K F c)) : c = 0 := by
  by_contra hc
  have h1 := h.le_ord ((_root_.map_ne_zero _).mpr hc)
  rw [Place.ord_algebraMap] at h1
  omega

theorem constant_unique {y : F} {a b : K} (ha : OrdGe v 1 (y - algebraMap K F a))
    (hb : OrdGe v 1 (y - algebraMap K F b)) : a = b := by
  have h : OrdGe v 1 (algebraMap K F (b - a)) := by
    have := ha.sub hb
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  have := algebraMap_eq_zero_of_ordGe h
  rwa [sub_eq_zero, eq_comm] at this

theorem mem_of_ordGe_zero {y : F} (h : OrdGe v 0 y) : y ∈ v.toValuationSubring := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact zero_mem _
  · exact (Place.mem_iff_ord_nonneg v hy).mpr (h.le_ord hy)

theorem ordGe_zero_of_mem {y : F} (h : y ∈ v.toValuationSubring) : OrdGe v 0 y := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact ordGe_zero v 0
  · exact Or.inr ((Place.mem_iff_ord_nonneg v hy).mp h)

theorem exists_constant (hrat : v.IsRational) {y : F} (hy : OrdGe v 0 y) :
    ∃ c : K, OrdGe v 1 (y - algebraMap K F c) := by
  have hmem := mem_of_ordGe_zero hy
  set y' : v.toValuationSubring := ⟨y, hmem⟩ with hy'
  obtain ⟨c, hc⟩ := hrat (IsLocalRing.residue v.toValuationSubring y')
  refine ⟨c, ?_⟩
  have hdiff : y' - algebraMap K v.toValuationSubring c ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [← Ideal.Quotient.eq]
    change IsLocalRing.residue _ y' = IsLocalRing.residue _ (algebraMap K v.toValuationSubring c)
    rw [← hc, IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField c]
    rfl
  have hcoe : ((y' - algebraMap K v.toValuationSubring c : v.toValuationSubring) : F) =
      y - algebraMap K F c := by
    push_cast
    rw [hy', Place.coe_algebraMap]
  rcases eq_or_ne (y - algebraMap K F c) 0 with h0 | h0
  · exact Or.inl h0
  · have hmem' : y - algebraMap K F c ∈ v.toValuationSubring := hcoe ▸ (y' - _).2
    have hEq : (⟨y - algebraMap K F c, hmem'⟩ : v.toValuationSubring) =
        y' - algebraMap K v.toValuationSubring c := Subtype.ext hcoe.symm
    have key : (⟨y - algebraMap K F c, hmem'⟩ : v.toValuationSubring) ∈
        IsLocalRing.maximalIdeal v.toValuationSubring := by
      rw [hEq]; exact hdiff
    exact Or.inr (Int.add_one_le_iff.mpr ((Place.mem_maximalIdeal_iff_ord_pos v h0 hmem').mp key))

theorem constant_ne_zero {y : F} {c : K} (hy0 : y ≠ 0) (hy : v.ord y = 0)
    (hc : OrdGe v 1 (y - algebraMap K F c)) : c ≠ 0 := by
  rintro rfl
  rw [map_zero, sub_zero] at hc
  have := hc.le_ord hy0
  omega

theorem transcendental_of_ord_ne_zero [IsAlgClosed K] {y : F} (hy : v.ord y ≠ 0) :
    Transcendental K y := by
  intro halg
  have hint : IsIntegral K y := halg.isIntegral
  have hirr := minpoly.irreducible hint
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible K hirr
  have hmonic := minpoly.monic hint
  have hform := Polynomial.eq_X_add_C_of_degree_eq_one hdeg
  rw [show (minpoly K y).leadingCoeff = 1 from hmonic, map_one, one_mul] at hform
  have h0 := minpoly.aeval K y
  rw [hform, map_add, aeval_X, aeval_C] at h0
  have hy' : y = algebraMap K F (-(minpoly K y).coeff 0) := by
    rw [map_neg]; exact eq_neg_of_add_eq_zero_left h0
  rw [hy', Place.ord_algebraMap] at hy
  exact hy rfl

end OrdCalc

section Transport

variable {K A B : Type*} [Field K] [Field A] [Field B] [Algebra K A] [Algebra K B] [Algebra A B]
  [IsScalarTower K A B]

def adjoinEquiv (y : A) :
    IntermediateField.adjoin K ({y} : Set A) ≃ₐ[K]
      IntermediateField.adjoin K ({algebraMap A B y} : Set B) :=
  (IntermediateField.equivMap (IntermediateField.adjoin K ({y} : Set A))
      (IsScalarTower.toAlgHom K A B)).trans
    (IntermediateField.equivOfEq (by
      rw [IntermediateField.adjoin_map, Set.image_singleton]; rfl))

theorem coe_adjoinEquiv (y : A) (r : IntermediateField.adjoin K ({y} : Set A)) :
    ((adjoinEquiv (K := K) (B := B) y r : IntermediateField.adjoin K ({algebraMap A B y} : Set B))
      : B) = algebraMap A B (r : A) := rfl

theorem finite_adjoin_left (y : A)
    [h : FiniteDimensional (IntermediateField.adjoin K ({algebraMap A B y} : Set B)) B] :
    Module.Finite (IntermediateField.adjoin K ({y} : Set A)) B := by
  set R := IntermediateField.adjoin K ({y} : Set A)
  set R' := IntermediateField.adjoin K ({algebraMap A B y} : Set B)
  obtain ⟨S, hS⟩ := h.fg_top
  refine ⟨⟨S, ?_⟩⟩
  rw [eq_top_iff]
  rintro b -
  have hb : b ∈ Submodule.span R' (S : Set B) := by rw [hS]; exact Submodule.mem_top
  induction hb using Submodule.span_induction with
  | mem b hb => exact Submodule.subset_span hb
  | zero => exact zero_mem _
  | add b b' _ _ ih ih' => exact add_mem ih ih'
  | smul r' b _ ih =>
    have hc : (r' : B) = algebraMap A B (((adjoinEquiv (K := K) (B := B) y).symm r' : R) : A) := by
      rw [← coe_adjoinEquiv, AlgEquiv.apply_symm_apply]
    have hr : r' • b = ((adjoinEquiv (K := K) (B := B) y).symm r') • b := by
      change (r' : B) * b = (((adjoinEquiv (K := K) (B := B) y).symm r' : R) : A) • b
      rw [Algebra.smul_def, hc]
    rw [hr]
    exact Submodule.smul_mem _ _ ih

theorem finiteDimensional_adjoin_of_tower (y : A)
    [FiniteDimensional (IntermediateField.adjoin K ({algebraMap A B y} : Set B)) B] :
    FiniteDimensional (IntermediateField.adjoin K ({y} : Set A)) A := by
  haveI := finite_adjoin_left (K := K) (B := B) y
  exact Module.Finite.of_injective
    (IsScalarTower.toAlgHom (IntermediateField.adjoin K ({y} : Set A)) A B).toLinearMap
    (RingHom.injective _)

theorem isSeparable_adjoin_right (y : A)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({y} : Set A)) B] :
    Algebra.IsSeparable (IntermediateField.adjoin K ({algebraMap A B y} : Set B)) B := by
  set R := IntermediateField.adjoin K ({y} : Set A)
  set R' := IntermediateField.adjoin K ({algebraMap A B y} : Set B)
  refine ⟨fun b => ?_⟩
  have hs : (minpoly R b).Separable := Algebra.IsSeparable.isSeparable R b
  set e := adjoinEquiv (K := K) (B := B) y
  have hcomp : (algebraMap R' B).comp (e : R →+* R') = algebraMap R B := by
    ext r
    change ((e r : R') : B) = algebraMap R B r
    rw [coe_adjoinEquiv, IsScalarTower.algebraMap_apply R A B]
    rfl
  have hq : ((minpoly R b).map (e : R →+* R')).Separable := hs.map
  have hqb : Polynomial.aeval b ((minpoly R b).map (e : R →+* R')) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.aeval_def]
    exact minpoly.aeval R b
  exact hq.of_dvd (minpoly.dvd R' b hqb)

end Transport

section Der

variable (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F]

def der (t f : F) : F := Place.diffCoeff t (D K F f)

variable {K}
variable [PerfectField K] (w : F) [FiniteDimensional (IntermediateField.adjoin K ({w} : Set F)) F]
  (v : Place K F) {t : F} (ht : v.ord t = 1)

include w ht

theorem der_spec (f : F) : D K F f = der K t f • D K F t := by
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({w} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  exact (Place.diffCoeff_smul_D_of_ord_eq_one (K := K) w v ht _).symm

theorem der_eq_of_eq_smul {f g : F} (h : D K F f = g • D K F t) : der K t f = g := by
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({w} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  rw [der, h, Place.diffCoeff_smul_D_eq_of_ord_eq_one (K := K) w v ht]

theorem der_add (f g : F) : der K t (f + g) = der K t f + der K t g :=
  der_eq_of_eq_smul w v ht (by rw [map_add, der_spec w v ht f, der_spec w v ht g, add_smul])

theorem der_sub (f g : F) : der K t (f - g) = der K t f - der K t g :=
  der_eq_of_eq_smul w v ht (by rw [map_sub, der_spec w v ht f, der_spec w v ht g, sub_smul])

theorem der_mul (f g : F) : der K t (f * g) = f * der K t g + g * der K t f :=
  der_eq_of_eq_smul w v ht (by
    rw [Derivation.leibniz, der_spec w v ht f, der_spec w v ht g, smul_smul, smul_smul, ← add_smul])

theorem der_algebraMap (c : K) : der K t (algebraMap K F c) = 0 :=
  der_eq_of_eq_smul w v ht (by rw [Derivation.map_algebraMap, zero_smul])

theorem der_zero : der K t (0 : F) = 0 := by
  have h := der_algebraMap w v ht 0
  rwa [map_zero] at h

theorem der_self : der K t t = 1 :=
  der_eq_of_eq_smul w v ht (by rw [one_smul])

theorem der_pow (f : F) (n : ℕ) : der K t (f ^ n) = n * f ^ (n - 1) * der K t f :=
  der_eq_of_eq_smul w v ht (by
    rw [Derivation.leibniz_pow, der_spec w v ht f, smul_smul, ← Nat.cast_smul_eq_nsmul F, smul_smul,
      ← mul_assoc])

theorem der_sum {ι : Type*} (s : Finset ι) (f : ι → F) :
    der K t (∑ i ∈ s, f i) = ∑ i ∈ s, der K t (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact der_zero w v ht
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, der_add w v ht, ih]

theorem ordGe_der {f : F} (hf : OrdGe v 0 f) : OrdGe v 0 (der K t f) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [der_zero w v ht]; exact ordGe_zero v 0
  · exact Or.inr (Place.ord_diffCoeff_D_nonneg_of_perfectField (K := K) w v ht (hf.le_ord hf0))

end Der

section Galois

variable (K E M : Type*) [Field K] [Field E] [Field M]
  [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]

def toSemilinear : (M ≃ₐ[E] M) →* SemilinearAut K M where
  toFun σ := SemilinearAut.ofAlgAut (σ.restrictScalars K)
  map_one' := by ext <;> rfl
  map_mul' _ _ := by ext <;> rfl

@[reducible] def placeAction : MulAction (M ≃ₐ[E] M) (Place K M) :=
  MulAction.compHom _ (toSemilinear K E M)

attribute [local instance] placeAction

variable {K E M}

theorem smul_place_def (σ : M ≃ₐ[E] M) (W : Place K M) :
    σ • W = SemilinearAut.ofAlgAut (σ.restrictScalars K) • W := rfl

theorem ord_smul_apply (σ : M ≃ₐ[E] M) (W : Place K M) (y : M) : (σ • W).ord (σ y) = W.ord y :=
  SemilinearAut.ord_smul (SemilinearAut.ofAlgAut (σ.restrictScalars K)) W y

theorem ord_apply_of_smul_eq {σ : M ≃ₐ[E] M} {W : Place K M} (h : σ • W = W) (y : M) :
    W.ord (σ y) = W.ord y := by
  conv_lhs => rw [← h]
  exact ord_smul_apply σ W y

theorem apply_algebraMap (σ : M ≃ₐ[E] M) (c : K) : σ (algebraMap K M c) = algebraMap K M c :=
  (σ.restrictScalars K).commutes c

variable [FiniteDimensional E M] [IsGalois E M]

theorem mem_fiberOver_iff_mem_orbit (P W : Place K M) :
    W ∈ (P.restrict E).fiberOver M ↔ W ∈ MulAction.orbit (M ≃ₐ[E] M) P := by
  rw [Place.mem_fiberOver, MulAction.mem_orbit_iff]
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := Place.exists_algEquiv_smul_eq_of_restrict_eq (K := K) (F' := E) P W h
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, rfl⟩
    exact Place.restrict_ofAlgAut_smul σ P

theorem card_stabilizer_mul_card_fiberOver (P : Place K M) :
    Nat.card (MulAction.stabilizer (M ≃ₐ[E] M) P) * ((P.restrict E).fiberOver M).card =
      Module.finrank E M := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (M ≃ₐ[E] M) P)
  rw [MulAction.index_stabilizer, IsGalois.card_aut_eq_finrank] at h1
  have h2 : (MulAction.orbit (M ≃ₐ[E] M) P).ncard = ((P.restrict E).fiberOver M).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext W
    rw [Finset.mem_coe, mem_fiberOver_iff_mem_orbit]
  rw [h2] at h1
  exact h1

omit [FiniteDimensional E M] [IsGalois E M] in

theorem inertiaDeg_eq_one_of_deg_eq_one {F' : Type*} [Field F'] [Algebra K F'] [Algebra F' M]
    [IsScalarTower K F' M] [Algebra.IsIntegral F' M] (W : Place K M) (hW : W.deg = 1) :
    W.inertiaDeg F' = 1 := by
  have h := W.deg_restrict_mul_inertiaDeg (F := F')
  rw [hW] at h
  exact Nat.eq_one_of_mul_eq_one_left h

theorem card_stabilizer_eq (P : Place K M) (hdeg : P.deg = 1) :
    Nat.card (MulAction.stabilizer (M ≃ₐ[E] M) P) = P.ramificationIndex E := by
  have h1 := card_stabilizer_mul_card_fiberOver (K := K) (E := E) P
  have h2 := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg (K := K) (P.restrict E) P rfl
  rw [inertiaDeg_eq_one_of_deg_eq_one P hdeg, mul_one] at h2
  have hpos : 0 < ((P.restrict E).fiberOver M).card :=
    Finset.card_pos.mpr ⟨P, Place.restrict_mem_fiberOver P⟩
  have : Nat.card (MulAction.stabilizer (M ≃ₐ[E] M) P) * ((P.restrict E).fiberOver M).card =
      P.ramificationIndex E * ((P.restrict E).fiberOver M).card := by
    rw [h1, mul_comm, h2]
  exact Nat.eq_of_mul_eq_mul_right hpos this

def ZK (P : Place K M) : IntermediateField K M :=
  (IntermediateField.fixedField (MulAction.stabilizer (M ≃ₐ[E] M) P)).restrictScalars K

theorem mem_ZK_iff (P : Place K M) (z : M) :
    z ∈ ZK (K := K) (E := E) P ↔ ∀ σ ∈ MulAction.stabilizer (M ≃ₐ[E] M) P, σ z = z := by
  rw [ZK, IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff]

theorem algebraMap_mem_ZK (P : Place K M) (c : K) : algebraMap K M c ∈ ZK (K := K) (E := E) P :=
  (mem_ZK_iff P _).mpr fun σ _ => apply_algebraMap σ c

theorem algebraMap_mem_ZK' (P : Place K M) (y : E) : algebraMap E M y ∈ ZK (K := K) (E := E) P :=
  (mem_ZK_iff P _).mpr fun σ _ => σ.commutes y

theorem finiteDimensional_ZK (P : Place K M) : FiniteDimensional (ZK (K := K) (E := E) P) M :=
  (inferInstance :
    FiniteDimensional (IntermediateField.fixedField (MulAction.stabilizer (M ≃ₐ[E] M) P)) M)

theorem isGalois_ZK (P : Place K M) : IsGalois (ZK (K := K) (E := E) P) M :=
  (inferInstance : IsGalois (IntermediateField.fixedField (MulAction.stabilizer (M ≃ₐ[E] M) P)) M)

theorem finrank_ZK (P : Place K M) :
    Module.finrank (ZK (K := K) (E := E) P) M = Nat.card (MulAction.stabilizer (M ≃ₐ[E] M) P) :=
  IntermediateField.finrank_fixedField_eq_card _

theorem fiberOver_ZK (P : Place K M) :
    haveI := finiteDimensional_ZK (K := K) (E := E) P
    haveI := isGalois_ZK (K := K) (E := E) P
    (P.restrict (ZK (K := K) (E := E) P)).fiberOver M = {P} := by
  haveI := finiteDimensional_ZK (K := K) (E := E) P
  haveI := isGalois_ZK (K := K) (E := E) P
  ext W
  rw [Finset.mem_singleton, Place.mem_fiberOver]
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ :=
      Place.exists_algEquiv_smul_eq_of_restrict_eq (K := K) (F' := ZK (K := K) (E := E) P) P W h

    have hcomm : ∀ y : E, (σ : M ≃+* M) (algebraMap E M y) = algebraMap E M y := fun y =>
      σ.commutes ⟨algebraMap E M y, algebraMap_mem_ZK' P y⟩
    set σE : M ≃ₐ[E] M := AlgEquiv.ofRingEquiv (f := (σ : M ≃+* M)) hcomm with hσE
    have hmem : σE ∈ MulAction.stabilizer (M ≃ₐ[E] M) P := by
      rw [← IntermediateField.fixingSubgroup_fixedField (MulAction.stabilizer (M ≃ₐ[E] M) P),
        IntermediateField.mem_fixingSubgroup_iff]
      intro z hz
      exact σ.commutes ⟨z, hz⟩
    have hfix : σE • P = P := MulAction.mem_stabilizer_iff.mp hmem
    have hres : σE.restrictScalars K = σ.restrictScalars K := AlgEquiv.ext fun _ => rfl
    rw [smul_place_def, hres] at hfix
    rw [← hσ, hfix]
  · rintro rfl; rfl

theorem ramificationIndex_ZK (P : Place K M) (hdeg : P.deg = 1) :
    P.ramificationIndex (ZK (K := K) (E := E) P) = Nat.card (MulAction.stabilizer (M ≃ₐ[E] M) P) := by
  haveI := finiteDimensional_ZK (K := K) (E := E) P
  haveI := isGalois_ZK (K := K) (E := E) P
  have h := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg (K := K)
    (P.restrict (ZK (K := K) (E := E) P)) P rfl
  rw [fiberOver_ZK P, Finset.card_singleton, one_mul, inertiaDeg_eq_one_of_deg_eq_one P hdeg,
    mul_one] at h
  rw [h]
  exact finrank_ZK P

theorem dvd_ord_of_mem_ZK (P : Place K M) (hdeg : P.deg = 1) {z : M}
    (hz : z ∈ ZK (K := K) (E := E) P) :
    (Nat.card (MulAction.stabilizer (M ≃ₐ[E] M) P) : ℤ) ∣ P.ord z := by
  haveI := finiteDimensional_ZK (K := K) (E := E) P
  have h := Place.ord_restrict (F := ZK (K := K) (E := E) P) P ⟨z, hz⟩
  rw [ramificationIndex_ZK P hdeg] at h
  exact ⟨_, h⟩

end Galois

section Vieta

variable {M : Type*} [CommRing M]

theorem map_univ_erase_one {G : Type*} [Group G] [Fintype G] [DecidableEq G] [DecidableEq M]
    (g : G → M) :
    ((Finset.univ : Finset G).val.map g).erase (g 1) = ((Finset.univ.erase (1 : G)).val).map g := by
  have h : (Finset.univ : Finset G).val = (1 : G) ::ₘ (Finset.univ.erase (1 : G)).val := by
    conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ (1 : G))]
    rw [Finset.insert_val_of_notMem (Finset.notMem_erase 1 _)]
  rw [h, Multiset.map_cons, Multiset.erase_cons_head]

theorem map_univ_mul_left {G : Type*} [Group G] [Fintype G] (g : G → M) (τ : G) :
    ((Finset.univ : Finset G).val.map fun σ => g (τ * σ)) = (Finset.univ : Finset G).val.map g := by
  have h := Finset.map_univ_equiv (Equiv.mulLeft τ)
  have h' : ((Finset.univ : Finset G).val.map (Equiv.mulLeft τ)) = (Finset.univ : Finset G).val := by
    conv_rhs => rw [← h]
    rw [Finset.map_val]
    rfl
  conv_rhs => rw [← h', Multiset.map_map]
  rfl

end Vieta

section Main

variable {K E M : Type*} [Field K] [IsAlgClosed K] [Field E] [Field M]
  [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
  [FiniteDimensional E M] [IsGalois E M]

attribute [local instance] placeAction

theorem main (p : ℕ) [Fact p.Prime] [CharP K p]
    (x : E) [FiniteDimensional (IntermediateField.adjoin K ({algebraMap E M x} : Set M)) M]
    (P : Place K M) (hx : (P.restrict E).ord x = 1)
    (a : ℕ) (ha : (p : ℤ) ^ a ∣ P.ord (algebraMap E M x)) :
    P.ord (algebraMap E M x) - 1 + ((p : ℤ) ^ a - 1) ≤
      P.ordDiff (D K M (algebraMap E M x)) := by
  classical
  set xM : M := algebraMap E M x with hxM_def
  set I : Subgroup (M ≃ₐ[E] M) := MulAction.stabilizer (M ≃ₐ[E] M) P with hI_def

  set e : ℕ := P.ramificationIndex E with he_def
  have hordx : P.ord xM = e := by
    rw [hxM_def, Place.ord_restrict, hx, mul_one]
  have he0 : 0 < e := Place.ramificationIndex_pos (F := E) P
  have hx0 : xM ≠ 0 := fun h => by
    rw [h, Place.ord_zero] at hordx; omega
  have htr : Transcendental K xM := transcendental_of_ord_ne_zero (v := P) (by rw [hordx]; omega)
  have hdeg : P.deg = 1 :=
    Place.deg_eq_one_of_isAlgClosed P (Place.deg_ne_zero_of_finiteDimensional_adjoin xM htr P)
  have hrat : P.IsRational := (Place.isRational_iff_deg_eq_one P).mpr hdeg
  have hcardI : Nat.card I = e := card_stabilizer_eq (K := K) (E := E) P hdeg
  haveI : Fintype I := Fintype.ofFinite I
  have hcardI' : Fintype.card I = e := by rw [← Nat.card_eq_fintype_card]; exact hcardI

  have hxZ : xM ∈ ZK (K := K) (E := E) P := algebraMap_mem_ZK' P x
  have hgap : ∀ z ∈ ZK (K := K) (E := E) P, (e : ℤ) ∣ P.ord z := fun z hz => by
    rw [← hcardI]; exact dvd_ord_of_mem_ZK P hdeg hz
  have hgap' : ∀ z ∈ ZK (K := K) (E := E) P, OrdGe P 1 z → OrdGe P e z := by
    intro z hz h1
    rcases eq_or_ne z 0 with rfl | hz0
    · exact ordGe_zero P _
    · have h1' := h1.le_ord hz0
      obtain ⟨k, hk⟩ := hgap z hz
      refine Or.inr ?_
      rw [hk] at h1' ⊢
      have : 0 < k := by
        by_contra hk0; push Not at hk0
        have : (e : ℤ) * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) hk0
        omega
      nlinarith
  have hordGe_x : OrdGe P e xM := ordGe_of_le hordx.ge
  have hordGe_xinv : OrdGe P (-(e : ℤ)) xM⁻¹ := ordGe_of_le (by rw [P.ord_inv, hordx])

  have hDx : D K M xM ≠ 0 := by
    haveI := finiteDimensional_adjoin_of_tower (K := K) (B := M) x
    haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set E)) E :=
      Algebra.IsAlgebraic.of_finite _ _
    haveI : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set E)) E :=
      Place.isSeparable_adjoin_of_ord_eq_one (K := K) x (P.restrict E) hx
    haveI : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set E)) M :=
      Algebra.IsSeparable.trans (IntermediateField.adjoin K ({x} : Set E)) E M
    haveI := isSeparable_adjoin_right (K := K) (B := M) x
    exact D_ne_zero_of_transcendental K xM htr

  set t : M := P.uniformizer_alt with ht_def
  have ht : P.ord t = 1 := Place.ord_uniformizer_alt P (Place.exists_ord_eq_one P)
  have ht0 : t ≠ 0 := fun h => by rw [h, Place.ord_zero] at ht; exact zero_ne_one ht
  have hordGe_t : OrdGe P 1 t := ordGe_of_le ht.ge

  have dspec := der_spec (K := K) xM P ht
  have dadd := der_add (K := K) xM P ht
  have dsub := der_sub (K := K) xM P ht
  have dmul := der_mul (K := K) xM P ht
  have dalg := der_algebraMap (K := K) xM P ht
  have dself := der_self (K := K) xM P ht
  have dpow := der_pow (K := K) xM P ht
  have dsum := fun {ι : Type} (s : Finset ι) (f : ι → M) => der_sum (K := K) xM P ht s f
  have dreg := fun {f : M} (hf : OrdGe P 0 f) => ordGe_der (K := K) xM P ht hf
  set h : M := der K t xM with hh_def
  have hgoal : P.ordDiff (D K M xM) = P.ord h := rfl
  have hh0 : h ≠ 0 := by
    intro h0
    apply hDx
    rw [dspec xM, ← hh_def, h0, zero_smul]
  set d : ℤ := P.ord h with hd_def
  have hd0 : 0 ≤ d := (dreg (hordGe_x.mono (by omega))).le_ord hh0
  have hordGe_h : OrdGe P d h := ordGe_of_le le_rfl

  have hR : ∀ n : ℕ, ∀ z ∈ ZK (K := K) (E := E) P, OrdGe P 0 z →
      OrdGe P (min (n : ℤ) d) (der K t z) := by
    intro n
    induction n with
    | zero =>
      intro z hz hz0
      exact (dreg hz0).mono (min_le_left _ _)
    | succ n ih =>
      intro z hz hz0
      obtain ⟨c, hc⟩ := exists_constant hrat hz0
      have hzc : z - algebraMap K M c ∈ ZK (K := K) (E := E) P :=
        sub_mem hz (algebraMap_mem_ZK P c)
      have hzc' : OrdGe P e (z - algebraMap K M c) := hgap' _ hzc hc
      set z' : M := (z - algebraMap K M c) * xM⁻¹ with hz'_def
      have hz' : z' ∈ ZK (K := K) (E := E) P := mul_mem hzc (inv_mem hxZ)
      have hz'0 : OrdGe P 0 z' := by
        have := hzc'.mul hordGe_xinv
        rwa [add_neg_cancel] at this
      have hzeq : z = algebraMap K M c + xM * z' := by
        rw [hz'_def]; field_simp; ring
      have hder : der K t z = xM * der K t z' + z' * h := by
        rw [hzeq, dadd, dalg, zero_add, dmul]
      rw [hder]
      refine OrdGe.add ?_ ?_
      · exact (hordGe_x.mul (ih z' hz' hz'0)).mono (by
          push_cast
          rcases le_total (n : ℤ) d with hnd | hnd
          · rw [min_eq_left hnd]; omega
          · rw [min_eq_right hnd]; omega)
      · exact (hz'0.mul hordGe_h).mono (by rw [zero_add]; exact min_le_right _ _)
  have hR' : ∀ z ∈ ZK (K := K) (E := E) P, OrdGe P 0 z → OrdGe P d (der K t z) := by
    intro z hz hz0
    have := hR d.toNat z hz hz0
    rwa [Int.toNat_of_nonneg hd0, min_self] at this

  set g : I → M := fun σ => (σ : M ≃ₐ[E] M) t with hg_def
  set R : Multiset M := (Finset.univ : Finset I).val.map g with hR_def
  set f : M[X] := (R.map fun r => X - C r).prod with hf_def
  have hcardR : R.card = e := by
    rw [hR_def, Multiset.card_map, Finset.card_val, Finset.card_univ, hcardI']
  have hnat : f.natDegree = e := by
    rw [hf_def, natDegree_multiset_prod_X_sub_C_eq_card, hcardR]
  have hg1 : g 1 = t := by rw [hg_def]; rfl
  have htR : t ∈ R := Multiset.mem_map.mpr ⟨1, Finset.mem_univ _, hg1⟩
  have hft : f.eval t = 0 := by
    rw [hf_def, eval_multiset_prod, Multiset.map_map]
    apply Multiset.prod_eq_zero
    exact Multiset.mem_map.mpr ⟨t, htR, by simp⟩

  have hordg : ∀ σ : I, P.ord (g σ) = 1 := fun σ => by
    rw [hg_def]
    exact (ord_apply_of_smul_eq (MulAction.mem_stabilizer_iff.mp σ.2) t).trans ht
  have hg0 : ∀ σ : I, g σ ≠ 0 := fun σ h0 => by
    have := hordg σ; rw [h0, Place.ord_zero] at this; exact zero_ne_one this

  have hmapf : ∀ τ : I, f.map ((τ : M ≃ₐ[E] M) : M →+* M) = f := by
    intro τ
    have hRτ : R.map ((τ : M ≃ₐ[E] M) : M → M) = R := by
      rw [hR_def, Multiset.map_map]
      exact map_univ_mul_left g τ
    rw [hf_def, Polynomial.map_multiset_prod, Multiset.map_map]
    conv_rhs => rw [← hRτ, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro r _
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hcoefZ : ∀ k, f.coeff k ∈ ZK (K := K) (E := E) P := fun k =>
    (mem_ZK_iff P _).mpr fun τ hτ => by
      have := congr_arg (fun q : M[X] => q.coeff k) (hmapf ⟨τ, hτ⟩)
      simp only [Polynomial.coeff_map] at this
      exact this

  have hcoefO : ∀ k, OrdGe P 0 (f.coeff k) := by
    intro k
    set O := P.toValuationSubring
    have hmemg : ∀ σ : I, g σ ∈ O := fun σ =>
      (Place.mem_iff_ord_nonneg P (hg0 σ)).mpr (by rw [hordg σ]; norm_num)
    set R₀ : Multiset O := (Finset.univ : Finset I).val.map fun σ => ⟨g σ, hmemg σ⟩ with hR₀
    set f₀ : O[X] := (R₀.map fun r => X - C r).prod with hf₀
    have hmap : f₀.map (algebraMap O M) = f := by
      rw [hf₀, Polynomial.map_multiset_prod, Multiset.map_map, hf_def, hR_def, hR₀, Multiset.map_map,
        Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro σ _
      simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rfl
    have : f.coeff k = ((f₀.coeff k : O) : M) := by rw [← hmap, Polynomial.coeff_map]; rfl
    rw [this]
    exact ordGe_zero_of_mem (f₀.coeff k).2

  have hRprod : R.prod = ∏ σ : I, g σ := rfl
  have hRprod0 : R.prod ≠ 0 := by
    rw [hRprod]; exact Finset.prod_ne_zero_iff.mpr fun σ _ => hg0 σ
  have hordRprod : P.ord R.prod = e := by
    rw [hRprod, ord_prod _ _ fun σ _ => hg0 σ]
    simp only [hordg, Finset.sum_const, Finset.card_univ, hcardI', Nat.smul_one_eq_cast]
  have hc0 : f.coeff 0 = (-1) ^ e * R.prod := by
    rw [coeff_zero_eq_eval_zero, hf_def, eval_multiset_prod, Multiset.map_map]
    have : (fun r : M => X - C r) ∘ (fun a => a) = fun r => X - C r := rfl
    have hcomp : (eval (0 : M)) ∘ (fun r : M => X - C r) = fun r => -r := by
      ext r; simp
    rw [hcomp, show (fun r : M => -r) = Neg.neg from rfl, Multiset.prod_map_neg, hcardR]
  have hc00 : f.coeff 0 ≠ 0 := by
    rw [hc0]; exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hRprod0
  have hordc0 : P.ord (f.coeff 0) = e := by
    rw [hc0, P.ord_mul (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hRprod0, hordRprod,
      show ((-1 : M)) ^ e = algebraMap K M ((-1) ^ e) by rw [map_pow, map_neg, map_one],
      Place.ord_algebraMap, zero_add]

  have hderc0 : der K t (f.coeff 0) ≠ 0 ∧ P.ord (der K t (f.coeff 0)) = d := by
    set c₀ := f.coeff 0 with hc₀_def
    set u : M := c₀ * xM⁻¹ with hu_def
    have huZ : u ∈ ZK (K := K) (E := E) P := mul_mem (hcoefZ 0) (inv_mem hxZ)
    have hu0 : u ≠ 0 := mul_ne_zero hc00 (inv_ne_zero hx0)
    have hordu : P.ord u = 0 := by
      rw [hu_def, P.ord_mul hc00 (inv_ne_zero hx0), P.ord_inv, hordc0, hordx]; ring
    obtain ⟨b, hb⟩ := exists_constant hrat (ordGe_of_le hordu.ge : OrdGe P 0 u)
    have hb0 : b ≠ 0 := constant_ne_zero hu0 hordu hb
    have hubZ : u - algebraMap K M b ∈ ZK (K := K) (E := E) P := sub_mem huZ (algebraMap_mem_ZK P b)
    have hub : OrdGe P e (u - algebraMap K M b) := hgap' _ hubZ hb
    set u' : M := (u - algebraMap K M b) * xM⁻¹ with hu'_def
    have hu'Z : u' ∈ ZK (K := K) (E := E) P := mul_mem hubZ (inv_mem hxZ)
    have hu'0 : OrdGe P 0 u' := by
      have := hub.mul hordGe_xinv
      rwa [add_neg_cancel] at this
    have hc₀eq : c₀ = xM * (algebraMap K M b + xM * u') := by
      rw [hu'_def, hu_def]; field_simp; ring
    have hder : der K t c₀ = algebraMap K M b * h +
        (xM * xM * der K t u' + xM * u' * h + xM * u' * h) := by
      rw [hc₀eq, dmul, dadd, dalg, zero_add, dmul, ← hh_def]
      ring
    rw [hder]
    refine ord_add_eq_of_ordGe (mul_ne_zero ((_root_.map_ne_zero _).mpr hb0) hh0)
      (by rw [P.ord_mul ((_root_.map_ne_zero _).mpr hb0) hh0, Place.ord_algebraMap, zero_add]) ?_
    refine OrdGe.add (OrdGe.add ?_ ?_) ?_
    · exact ((hordGe_x.mul hordGe_x).mul (hR' u' hu'Z hu'0)).mono (by omega)
    · exact ((hordGe_x.mul hu'0).mul hordGe_h).mono (by omega)
    · exact ((hordGe_x.mul hu'0).mul hordGe_h).mono (by omega)

  set A : M := ∑ k ∈ Finset.range (e + 1), t ^ k * der K t (f.coeff k) with hA_def
  have hderiv : f.derivative.eval t = -A := by
    have hexp : f.eval t = ∑ k ∈ Finset.range (e + 1), f.coeff k * t ^ k := by
      rw [eval_eq_sum_range, hnat]
    have hexp' : f.derivative.eval t =
        ∑ k ∈ Finset.range (e + 1), f.coeff k * k * t ^ (k - 1) := by
      rw [derivative_eval, Polynomial.sum_over_range' _ _ (e + 1) (by rw [hnat]; exact Nat.lt_succ_self e)]
      intro n; rw [zero_mul, zero_mul]
    have h0 : der K t (f.eval t) = 0 := by rw [hft]; exact der_zero (K := K) xM P ht
    rw [hexp, dsum] at h0
    have hterm : ∀ k ∈ Finset.range (e + 1), der K t (f.coeff k * t ^ k) =
        f.coeff k * k * t ^ (k - 1) + t ^ k * der K t (f.coeff k) := by
      intro k _
      rw [dmul, dpow, dself, mul_one]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← hexp', ← hA_def] at h0
    exact eq_neg_of_add_eq_zero_left h0

  have hA : A ≠ 0 ∧ P.ord A = d := by
    have hsplit : A = der K t (f.coeff 0) +
        ∑ k ∈ Finset.range e, t ^ (k + 1) * der K t (f.coeff (k + 1)) := by
      rw [hA_def, Finset.sum_range_succ', pow_zero, one_mul, add_comm]
    rw [hsplit]
    refine ord_add_eq_of_ordGe hderc0.1 hderc0.2 (OrdGe.sum _ fun k _ => ?_)
    have h1 : OrdGe P ((k : ℤ) + 1) (t ^ (k + 1)) := ordGe_of_le (by rw [ord_pow', ht]; push_cast; omega)
    exact (h1.mul (hR' _ (hcoefZ (k + 1)) (hcoefO (k + 1)))).mono (by omega)

  have hderiv' : f.derivative.eval t = ∏ σ ∈ Finset.univ.erase (1 : I), (t - g σ) := by
    rw [hf_def, eval_multiset_prod_X_sub_C_derivative htR, hR_def, ← hg1, map_univ_erase_one g,
      Multiset.map_map]
    rfl
  have hprod0 : ∏ σ ∈ Finset.univ.erase (1 : I), (t - g σ) ≠ 0 := by
    rw [← hderiv', hderiv]; exact neg_ne_zero.mpr hA.1
  have hfac0 : ∀ σ ∈ Finset.univ.erase (1 : I), t - g σ ≠ 0 := fun σ hσ =>
    (Finset.prod_ne_zero_iff.mp hprod0) σ hσ
  have hdsum : d = ∑ σ ∈ Finset.univ.erase (1 : I), P.ord (t - g σ) := by
    rw [← ord_prod _ _ hfac0, ← hderiv', hderiv, ord_neg', hA.2]

  have hi1 : ∀ σ ∈ Finset.univ.erase (1 : I), 1 ≤ P.ord (t - g σ) := fun σ hσ =>
    (hordGe_t.sub (ordGe_of_le (hordg σ).ge)).le_ord (hfac0 σ hσ)

  have hu : ∀ σ : I, g σ * t⁻¹ ≠ 0 ∧ P.ord (g σ * t⁻¹) = 0 := fun σ =>
    ⟨mul_ne_zero (hg0 σ) (inv_ne_zero ht0), by
      rw [P.ord_mul (hg0 σ) (inv_ne_zero ht0), P.ord_inv, hordg σ, ht]; ring⟩
  have hexa : ∀ σ : I, ∃ b : K, OrdGe P 1 (g σ * t⁻¹ - algebraMap K M b) := fun σ =>
    exists_constant hrat (ordGe_of_le (hu σ).2.ge)
  choose χ₀ hχ₀ using hexa
  have hχ₀0 : ∀ σ : I, χ₀ σ ≠ 0 := fun σ => constant_ne_zero (hu σ).1 (hu σ).2 (hχ₀ σ)

  have hχmul : ∀ σ τ : I, χ₀ (σ * τ) = χ₀ σ * χ₀ τ := by
    intro σ τ
    refine constant_unique (hχ₀ (σ * τ)) ?_

    have hστ : g (σ * τ) * t⁻¹ = (σ : M ≃ₐ[E] M) (g τ * t⁻¹) * (g σ * t⁻¹) := by
      have e1 : g (σ * τ) = (σ : M ≃ₐ[E] M) (g τ) := rfl
      have e2 : (σ : M ≃ₐ[E] M) t = g σ := rfl
      rw [e1, map_mul, map_inv₀, e2, mul_assoc, inv_mul_cancel_left₀ (hg0 σ)]
    have hid : g (σ * τ) * t⁻¹ - algebraMap K M (χ₀ σ * χ₀ τ) =
        ((σ : M ≃ₐ[E] M) (g τ * t⁻¹) - algebraMap K M (χ₀ τ)) * (g σ * t⁻¹) +
          algebraMap K M (χ₀ τ) * (g σ * t⁻¹ - algebraMap K M (χ₀ σ)) := by
      rw [hστ, map_mul (algebraMap K M) (χ₀ σ) (χ₀ τ)]; ring
    rw [hid]
    refine OrdGe.add ?_ ?_
    · have h1 : OrdGe P 1 ((σ : M ≃ₐ[E] M) (g τ * t⁻¹) - algebraMap K M (χ₀ τ)) := by
        rw [← apply_algebraMap (σ : M ≃ₐ[E] M) (χ₀ τ), ← map_sub]
        rcases hχ₀ τ with h0 | h0
        · exact Or.inl (by rw [h0, map_zero])
        · exact Or.inr (by rwa [ord_apply_of_smul_eq (MulAction.mem_stabilizer_iff.mp σ.2)])
      exact (h1.mul (ordGe_of_le (hu σ).2.ge : OrdGe P 0 _)).mono (by omega)
    · exact ((ordGe_of_le (by rw [Place.ord_algebraMap]) : OrdGe P 0 (algebraMap K M (χ₀ τ))).mul
        (hχ₀ σ)).mono (by omega)
  have hχone : χ₀ 1 = 1 := by
    refine constant_unique (hχ₀ 1) ?_
    rw [hg1, mul_inv_cancel₀ ht0, map_one, sub_self]; exact ordGe_zero P 1
  set χ : I →* Kˣ :=
    { toFun := fun σ => Units.mk0 (χ₀ σ) (hχ₀0 σ)
      map_one' := Units.ext hχone
      map_mul' := fun σ τ => Units.ext (hχmul σ τ) } with hχ_def

  have hker : ∀ σ : I, σ ∈ χ.ker → OrdGe P 2 (t - g σ) := by
    intro σ hσ
    have h1 : χ₀ σ = 1 := by
      have := congr_arg (fun u : Kˣ => (u : K)) (MonoidHom.mem_ker.mp hσ)
      simpa [hχ_def] using this
    have h2 := hχ₀ σ
    rw [h1, map_one] at h2
    have hid : t - g σ = -(t * (g σ * t⁻¹ - 1)) := by field_simp; ring
    rw [hid]
    exact ((hordGe_t.mul h2).mono (by norm_num)).neg

  have hrange : ¬ p ∣ Nat.card χ.range := by
    intro hdvd
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := χ.range) p hdvd
    obtain ⟨hζp, hζ1⟩ := (orderOf_eq_prime_iff.mp hζ)
    apply hζ1
    have hval : ((ζ : Kˣ) : K) ^ p = 1 := by
      have := congr_arg (fun u : χ.range => ((u : Kˣ) : K)) hζp
      simpa using this
    have hsub : (((ζ : Kˣ) : K) - 1) ^ p = 0 := by rw [sub_pow_char, hval, one_pow, sub_self]
    have hone : ((ζ : Kˣ) : K) = 1 := sub_eq_zero.mp (pow_eq_zero_iff (Nat.Prime.ne_zero Fact.out) |>.mp hsub)
    exact Subtype.ext (Units.ext hone)

  have hker_card : p ^ a ∣ Nat.card χ.ker := by
    have h1 : Nat.card χ.ker * Nat.card χ.range = e := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index, hcardI]
    have hae : p ^ a ∣ e := by
      have := ha; rw [hordx] at this; exact_mod_cast this
    have hcop : (p ^ a).Coprime (Nat.card χ.range) :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hrange)
    exact hcop.dvd_of_dvd_mul_right (h1 ▸ hae)
  haveI : Fintype χ.ker := Fintype.ofFinite _
  have hker_le : p ^ a ≤ Fintype.card χ.ker :=
    Nat.le_of_dvd Fintype.card_pos (by rw [← Nat.card_eq_fintype_card]; exact hker_card)

  have hcount : ((e : ℤ) - 1) + ((Fintype.card χ.ker : ℤ) - 1) ≤
      ∑ σ ∈ Finset.univ.erase (1 : I), P.ord (t - g σ) := by
    have hpt : ∀ σ ∈ Finset.univ.erase (1 : I),
        (1 : ℤ) + (if σ ∈ χ.ker then 1 else 0) ≤ P.ord (t - g σ) := by
      intro σ hσ
      split_ifs with hk
      · exact (hker σ hk).le_ord (hfac0 σ hσ)
      · rw [add_zero]; exact hi1 σ hσ
    have hfk : (Finset.univ.filter fun σ : I => σ ∈ χ.ker).card = Fintype.card χ.ker := by
      rw [← Fintype.card_subtype]
    have h1 : 1 ≤ e := he0
    have h2 : 1 ≤ Fintype.card χ.ker := Fintype.card_pos
    have hsum_lb : ∑ σ ∈ Finset.univ.erase (1 : I), ((1 : ℤ) + (if σ ∈ χ.ker then 1 else 0)) =
        ((e : ℤ) - 1) + ((Fintype.card χ.ker : ℤ) - 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, hcardI', Finset.sum_boole, Finset.filter_erase,
        Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, χ.ker.one_mem⟩), hfk,
        nsmul_eq_mul, Nat.cast_sub h1, Nat.cast_sub h2]
      push_cast
      ring
    rw [← hsum_lb]
    exact Finset.sum_le_sum hpt

  rw [hgoal, hordx, hdsum]
  calc (e : ℤ) - 1 + ((p : ℤ) ^ a - 1) ≤ ((e : ℤ) - 1) + ((Fintype.card χ.ker : ℤ) - 1) := by
        have : ((p : ℤ) ^ a) ≤ (Fintype.card χ.ker : ℤ) := by exact_mod_cast hker_le
        omega
    _ ≤ _ := hcount

end Main

end HilbertWildLB

theorem solution
    {K E M : Type*} [Field K] [IsAlgClosed K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional E M] [IsGalois E M]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (x : E) [FiniteDimensional (IntermediateField.adjoin K ({algebraMap E M x} : Set M)) M]
    (P : Place K M) (hx : (P.restrict E).ord x = 1)
    (a : ℕ) (ha : (p : ℤ) ^ a ∣ P.ord (algebraMap E M x)) :
    P.ord (algebraMap E M x) - 1 + ((p : ℤ) ^ a - 1) ≤
      P.ordDiff (D K M (algebraMap E M x)) :=
  HilbertWildLB.main p x P hx a ha

end

end S_AlgebraicCurve_Place_sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois
end P2MW
export P2MW.S_AlgebraicCurve_Place_sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois (solution)
