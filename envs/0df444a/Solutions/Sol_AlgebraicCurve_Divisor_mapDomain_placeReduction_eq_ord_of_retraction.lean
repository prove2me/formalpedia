-- Prove2me | solution 1 for AlgebraicCurve.Divisor.mapDomain_placeReduction_eq_ord_of_retraction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/b4fbc53b-5758-58ca-b1c3-1f50eec6b857

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_placeOfPoint_ne_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_X
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardNormFormula_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_linearIndependent_pow_of_transcendental
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction
import Theorems.Thm_AlgebraicCurve_residue_norm_eq_norm_residue_of_retraction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_mapDomain_placeReduction_eq_ord_of_retraction
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul"
p2m_attr_erase "simp" "ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
open scoped Polynomial

namespace DeuringPrincipalDivisorReduction

section RatAlg

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

@[reducible] noncomputable def polyAlg (x : F) : Algebra K[X] F :=
  (Polynomial.aeval x).toRingHom.toAlgebra

theorem faithful_polyAlg {x : F} (hx : Transcendental K x) :
    letI := polyAlg (K := K) x
    FaithfulSMul K[X] F := by
  letI := polyAlg (K := K) x
  exact (faithfulSMul_iff_algebraMap_injective K[X] F).mpr (transcendental_iff_injective.mp hx)

open scoped RatFunc in

@[reducible] noncomputable def ratAlg {x : F} (hx : Transcendental K x) : Algebra (RatFunc K) F :=
  letI := polyAlg (K := K) x
  haveI := faithful_polyAlg (K := K) hx
  inferInstance

theorem ratAlg_tower {x : F} (hx : Transcendental K x) :
    letI := ratAlg (K := K) hx
    IsScalarTower K (RatFunc K) F := by
  letI := polyAlg (K := K) x
  haveI := faithful_polyAlg (K := K) hx
  letI := ratAlg (K := K) hx
  have : IsScalarTower K K[X] F := IsScalarTower.of_algebraMap_eq fun k => by
    show _ = (Polynomial.aeval x).toRingHom (algebraMap K K[X] k)
    simp
  infer_instance

theorem ratAlg_X {x : F} (hx : Transcendental K x) :
    letI := ratAlg (K := K) hx
    algebraMap (RatFunc K) F RatFunc.X = x := by
  letI := polyAlg (K := K) x
  haveI := faithful_polyAlg (K := K) hx
  letI := ratAlg (K := K) hx
  have h1 : algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) Polynomial.X) =
      algebraMap K[X] F Polynomial.X :=
    (IsScalarTower.algebraMap_apply K[X] (RatFunc K) F _).symm
  rw [RatFunc.algebraMap_X] at h1
  rw [h1]
  show (Polynomial.aeval x).toRingHom Polynomial.X = x
  simp

open IntermediateField in
theorem ratAlg_finite {x : F} (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    letI := ratAlg (K := K) hx
    FiniteDimensional (RatFunc K) F := by
  letI := ratAlg (K := K) hx
  haveI := ratAlg_tower (K := K) hx
  set ψ : RatFunc K →ₐ[K] F := IsScalarTower.toAlgHom K (RatFunc K) F with hψ
  have hψX : ψ RatFunc.X = x := ratAlg_X hx
  have hrange : ψ.fieldRange = IntermediateField.adjoin K ({x} : Set F) := by
    rw [AlgHom.fieldRange_eq_map, ← RatFunc.adjoin_X, IntermediateField.adjoin_map]
    simp [hψX]
  haveI : FiniteDimensional ψ.fieldRange F := by rw [hrange]; exact hfin
  have hinj : Function.Injective ψ.toRingHom.rangeRestrictField :=
    RingHom.injective _
  have hsurj : Function.Surjective ψ.toRingHom.rangeRestrictField := by
    rintro ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := (AlgHom.mem_fieldRange).mp hy
    exact ⟨a, rfl⟩
  let e : RatFunc K ≃+* ψ.fieldRange := RingEquiv.ofBijective _ ⟨hinj, hsurj⟩
  refine Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl F) (RingHom.ext fun a => ?_)
  obtain ⟨b, rfl⟩ := e.surjective a
  simp only [RingHom.comp_apply]
  erw [RingEquiv.symm_apply_apply]
  rfl

open IntermediateField in
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin in

theorem finiteDimensional_adjoin_of_transcendental'
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional K⟮x⟯ F)
    {x : F} (hx : Transcendental K x) : FiniteDimensional K⟮x⟯ F := by
  obtain ⟨x₀, hx₀, hfin₀⟩ := hfg
  haveI := hfin₀
  haveI : Algebra.EssFiniteType K F :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx₀ hfin₀
  have halg₀ : Algebra.IsAlgebraic (Algebra.adjoin K ({x₀} : Set F)) F :=
    Algebra.IsAlgebraic.trans (R := Algebra.adjoin K ({x₀} : Set F)) (S := K⟮x₀⟯) (A := F)
  have htr : Algebra.trdeg K F ≤ 1 := by
    have h := Algebra.IsAlgebraic.trdeg_le_cardinalMk (R := K) (s := ({x₀} : Set F)) (A := F)
    simpa using h
  have hind : AlgebraicIndependent K (fun _ : Fin 1 => x) := by
    rw [algebraicIndependent_unique_type_iff]; exact hx
  have hbasis : IsTranscendenceBasis K (fun _ : Fin 1 => x) := by
    refine hind.isTranscendenceBasis_of_lift_trdeg_le_of_finite ?_
    simpa using htr
  have halg : Algebra.IsAlgebraic (adjoin K (Set.range fun _ : Fin 1 => x)) F :=
    hbasis.isAlgebraic_field
  have hrange : Set.range (fun _ : Fin 1 => x) = {x} := by
    ext y; simp [eq_comm]
  rw [hrange] at halg
  haveI := halg
  haveI : Algebra.EssFiniteType K⟮x⟯ F := Algebra.EssFiniteType.of_comp K K⟮x⟯ F
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic (F := K⟮x⟯) (E := F)

theorem transcendental_of_linearIndependent_pow {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {x : A} (h : LinearIndependent R (fun j : ℕ => x ^ j)) : Transcendental R x := by
  rw [transcendental_iff]
  intro p hpx
  let l : ℕ →₀ R := Finsupp.onFinset p.support p.coeff fun n hn => Polynomial.mem_support_iff.mpr hn
  have hl : ∀ n, l n = p.coeff n := fun n => Finsupp.onFinset_apply
  have key : Finsupp.linearCombination R (fun j : ℕ => x ^ j) l = Polynomial.aeval x p := by
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset l Finsupp.support_onFinset_subset (fun i a => a • x ^ i)
        (fun n _ => zero_smul R _),
      Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hl, Algebra.smul_def]
  have := linearIndependent_iff.mp h l (by rw [key, hpx])
  ext n
  rw [← hl n, this, Finsupp.zero_apply, Polynomial.coeff_zero]

end RatAlg

section RatFuncPlaces

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

theorem X_not_mem_placeInfty [DecidableEq (RatFunc k)] :
    (RatFunc.X : RatFunc k) ∉ (placeInfty k).toValuationSubring := by
  intro h
  have h1 := (Place.mem_iff_ord_nonneg (placeInfty k) (RatFunc.X_ne_zero (K := k))).mp h
  rw [ord_placeInfty_X] at h1
  norm_num at h1

theorem X_mem_placeOfPoint (a : k) :
    (RatFunc.X : RatFunc k) ∈ (placeOfPoint k a).toValuationSubring := by
  rw [placeOfPoint_eq_ofHeightOneSpectrum, ← RatFunc.algebraMap_X]
  exact algebraMap_mem_ofHeightOneSpectrum k _ _

variable [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [Algebra.IsIntegral (RatFunc k) L]

theorem restrict_eq_placeInfty_iff [IsAlgClosed k] [DecidableEq (RatFunc k)] (w : Place k L) :
    w.restrict (RatFunc k) = placeInfty k ↔
      algebraMap (RatFunc k) L RatFunc.X ∉ w.toValuationSubring := by
  constructor
  · intro h hX
    have : (RatFunc.X : RatFunc k) ∈ (w.restrict (RatFunc k)).toValuationSubring :=
      (Place.mem_restrict_iff w).mpr hX
    rw [h] at this
    exact X_not_mem_placeInfty this
  · intro hX
    rcases eq_placeOfPoint_or_eq_placeInfty k (w.restrict (RatFunc k)) with ⟨a, ha⟩ | h
    · exact absurd ((Place.mem_restrict_iff w).mp (ha ▸ X_mem_placeOfPoint a)) hX
    · exact h

theorem valuation_X_sub_lt_one_of_restrict_eq_placeOfPoint (w : Place k L) (β : k)
    (h : w.restrict (RatFunc k) = placeOfPoint k β) :
    w.toValuationSubring.valuation (algebraMap (RatFunc k) L RatFunc.X - algebraMap k L β) < 1 := by

  set y : RatFunc k := algebraMap k[X] (RatFunc k) (Polynomial.X - Polynomial.C β) with hy
  have hy0 : (Polynomial.X - Polynomial.C β : k[X]) ≠ 0 := Polynomial.X_sub_C_ne_zero β
  have hyne : y ≠ 0 := by
    rw [hy]; exact (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hy0
  have hord : (placeOfPoint k β).ord y = 1 := by
    rw [hy, ord_placeOfPoint_algebraMap β hy0, Polynomial.rootMultiplicity_X_sub_C_self]
    rfl
  have hymem : y ∈ (placeOfPoint k β).toValuationSubring :=
    (Place.mem_iff_ord_nonneg _ hyne).mpr (by omega)
  have hyinv : y⁻¹ ∉ (placeOfPoint k β).toValuationSubring := by
    intro hmem
    have := (Place.mem_iff_ord_nonneg _ (inv_ne_zero hyne)).mp hmem
    rw [Place.ord_inv, hord] at this
    norm_num at this

  have hwmem : algebraMap (RatFunc k) L y ∈ w.toValuationSubring :=
    (Place.mem_restrict_iff w).mp (h ▸ hymem)
  have hwinv : (algebraMap (RatFunc k) L y)⁻¹ ∉ w.toValuationSubring := by
    intro hmem
    rw [← map_inv₀] at hmem
    exact hyinv (h ▸ (Place.mem_restrict_iff w).mpr hmem)
  have himg : algebraMap (RatFunc k) L y = algebraMap (RatFunc k) L RatFunc.X - algebraMap k L β := by
    rw [hy, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_sub, ← RatFunc.algebraMap_eq_C,
      ← IsScalarTower.algebraMap_apply]
  rw [← himg]
  have hnu : ¬ IsUnit (⟨algebraMap (RatFunc k) L y, hwmem⟩ : w.toValuationSubring) := by
    intro hu
    obtain ⟨u, hu⟩ := hu
    apply hwinv
    have h1 := congrArg (fun z : w.toValuationSubring => (z : L)) u.mul_inv
    simp only [Subring.coe_one, hu] at h1
    push_cast at h1
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact SetLike.coe_mem _
  have := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
  exact (ValuationSubring.valuation_lt_one_iff _ _).mp this

end RatFuncPlaces

section Fibre

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem valuation_algebraMap_eq_one (v : Place K F) {c : K} (hc : c ≠ 0) :
    v.toValuationSubring.valuation (algebraMap K F c) = 1 := by
  have h1 : v.toValuationSubring.valuation (algebraMap K F c) ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff _ _).mpr (v.algebraMap_mem' c)
  have h2 : v.toValuationSubring.valuation (algebraMap K F c)⁻¹ ≤ 1 := by
    rw [← map_inv₀]
    exact (ValuationSubring.valuation_le_one_iff _ _).mpr (v.algebraMap_mem' c⁻¹)
  have hne : v.toValuationSubring.valuation (algebraMap K F c) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr ((map_ne_zero _).mpr hc)
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hne)] at h2
  exact le_antisymm h1 h2

end Fibre

section FibreE

variable {E FE : Type*} [Field E] [Field FE] [Algebra E FE]
  [Algebra (RatFunc E) FE] [IsScalarTower E (RatFunc E) FE] [Algebra.IsIntegral (RatFunc E) FE]

theorem not_exists_lt_one_iff [IsAlgClosed E] [DecidableEq (RatFunc E)]
    (A : ValuationSubring E) (P : Place E FE) :
    (¬ ∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap (RatFunc E) FE RatFunc.X - algebraMap E FE a) < 1) ↔
      (P.restrict (RatFunc E) = placeInfty E ∨
        ∃ β : E, β ∉ A ∧ P.restrict (RatFunc E) = placeOfPoint E β) := by
  rcases eq_placeOfPoint_or_eq_placeInfty E (P.restrict (RatFunc E)) with ⟨β, hβ⟩ | hinf
  ·
    have hlt := valuation_X_sub_lt_one_of_restrict_eq_placeOfPoint P β hβ
    have hR : (P.restrict (RatFunc E) = placeInfty E ∨
        ∃ β' : E, β' ∉ A ∧ P.restrict (RatFunc E) = placeOfPoint E β') ↔ β ∉ A := by
      constructor
      · rintro (h | ⟨β', hβ'A, h'⟩)
        · exact absurd (hβ.symm.trans h) (placeOfPoint_ne_placeInfty E β)
        · rwa [placeOfPoint_injective E (hβ.symm.trans h')]
      · exact fun h => Or.inr ⟨β, h, hβ⟩
    rw [hR]
    constructor
    · intro hL hβA
      exact hL ⟨β, hβA, hlt⟩
    · rintro hβA ⟨a, haA, ha⟩
      have hne : β - a ≠ 0 := by
        intro h0
        rw [sub_eq_zero] at h0
        exact hβA (h0 ▸ haA)
      have h1 := valuation_algebraMap_eq_one P hne
      have h2 : P.toValuationSubring.valuation (algebraMap E FE (β - a)) < 1 := by
        have : algebraMap E FE (β - a) =
            (algebraMap (RatFunc E) FE RatFunc.X - algebraMap E FE a) -
              (algebraMap (RatFunc E) FE RatFunc.X - algebraMap E FE β) := by
          rw [map_sub]; ring
        rw [this]
        exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha hlt)
      rw [h1] at h2
      exact lt_irrefl _ h2
  ·
    have hX := (restrict_eq_placeInfty_iff P).mp hinf
    constructor
    · exact fun _ => Or.inl hinf
    · rintro - ⟨a, -, ha⟩
      apply hX
      have hmem : algebraMap (RatFunc E) FE RatFunc.X - algebraMap E FE a ∈ P.toValuationSubring :=
        (ValuationSubring.valuation_le_one_iff _ _).mp ha.le
      have := add_mem hmem (P.algebraMap_mem' a)
      simpa using this

end FibreE

section PoleSum

open scoped Classical

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable def poleSum (x : F) (D : Divisor K F) : ℤ :=
  D.sum fun w n => if x ∉ w.toValuationSubring then n else 0

theorem poleSum_eq_sum (x : F) (D : Divisor K F) :
    poleSum x D = ∑ w ∈ D.support, if x ∉ w.toValuationSubring then D w else 0 := rfl

theorem poleSum_sub (x : F) (D D' : Divisor K F) :
    poleSum x (D - D') = poleSum x D - poleSum x D' := by
  unfold poleSum
  exact Finsupp.sum_sub_index fun w b₁ b₂ => by split_ifs <;> simp

theorem poleSum_mapDomain {ι : Type*} (x : F) (r : ι → Place K F) (D : ι →₀ ℤ) :
    poleSum x (Finsupp.mapDomain r D) =
      ∑ i ∈ D.support, if x ∉ (r i).toValuationSubring then D i else 0 := by
  unfold poleSum
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp)]
  rfl

theorem sum_support_ite_eq (D : Divisor K F) (p : Place K F → Prop) [DecidablePred p]
    (U : Finset (Place K F)) (hU : D.support ⊆ U) :
    (∑ w ∈ D.support, if p w then D w else 0) = ∑ w ∈ U, if p w then D w else 0 := by
  refine Finset.sum_subset hU fun w _ hw => ?_
  rw [Finsupp.notMem_support_iff.mp hw]
  simp

end PoleSum

section Push

variable {k L : Type*} [Field k] [Field L] [Algebra k L] [IsAlgClosed k] [CharZero k]
  [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FiniteDimensional (RatFunc k) L]

theorem sum_restrict_eq_ord_norm [DecidableEq (Place k (RatFunc k))] {f : L} (hf : f ≠ 0)
    (D : Divisor k L) (hD : ∀ w, D w = w.ord f) (v : Place k (RatFunc k)) :
    (∑ w ∈ D.support, if w.restrict (RatFunc k) = v then D w else 0) =
      v.ord (Algebra.norm (RatFunc k) f) := by
  have H := Divisor.pushforwardNormFormula_of_finiteDimensional
    (K := k) (F := RatFunc k) (F' := L) f hf D hD v
  rw [Divisor.pushforward_apply] at H
  rw [← H]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs with h
  · rw [Place.inertiaDeg_eq_one_of_isRational w (Place.isRational_of_isAlgClosed w)
      (Place.isRational_of_isAlgClosed _)]
    simp
  · rfl

end Push

section Core

variable {K F E FE : Type*} [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra (RatFunc E) FE] [IsScalarTower E (RatFunc E) FE]

theorem algebraMap_polynomial_map
    (hX : algebraMap (RatFunc E) FE RatFunc.X = algebraMap F FE (algebraMap (RatFunc K) F RatFunc.X))
    (p : K[X]) :
    algebraMap (RatFunc E) FE (algebraMap E[X] (RatFunc E) (p.map (algebraMap K E))) =
      algebraMap F FE (algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) p)) := by
  set fL : K[X] →+* FE := (algebraMap (RatFunc E) FE).comp
    ((algebraMap E[X] (RatFunc E)).comp (Polynomial.mapRingHom (algebraMap K E))) with hfL
  set fR : K[X] →+* FE := (algebraMap F FE).comp
    ((algebraMap (RatFunc K) F).comp (algebraMap K[X] (RatFunc K))) with hfR
  have hLR : fL = fR := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [hfL, hfR, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        RatFunc.algebraMap_C]
      rw [← RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_eq_C,
        ← IsScalarTower.algebraMap_apply E (RatFunc E) FE,
        ← IsScalarTower.algebraMap_apply K E FE, ← IsScalarTower.algebraMap_apply K (RatFunc K) F,
        ← IsScalarTower.algebraMap_apply K F FE]
    · simp only [hfL, hfR, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
        RatFunc.algebraMap_X, hX]
  have := DFunLike.congr_fun hLR p
  simpa [hfL, hfR] using this

theorem isUnit_iff_inv_mem {L : Type*} [Field L] (O : ValuationSubring L) (z : O) (hz : (z : L) ≠ 0) :
    IsUnit z ↔ (z : L)⁻¹ ∈ O := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 := congrArg (fun w : O => (w : L)) u.mul_inv
    simp only [Subring.coe_one, hu] at h1
    push_cast at h1
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact SetLike.coe_mem _
  · intro h
    exact ⟨⟨z, ⟨(z : L)⁻¹, h⟩, Subtype.ext (mul_inv_cancel₀ hz), Subtype.ext (inv_mul_cancel₀ hz)⟩, rfl⟩

variable [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    [FiniteDimensional (RatFunc K) F] [FiniteDimensional (RatFunc E) FE]

theorem core
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hX : algebraMap (RatFunc E) FE RatFunc.X = algebraMap F FE (algebraMap (RatFunc K) F RatFunc.X))
    (A : ValuationSubring E) (r : Place E FE → Place K F)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1)
    (O : ValuationSubring FE) (ρ : O →+* F)
    (hO : ∀ c : E, algebraMap E FE c ∈ O ↔ c ∈ A)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
    (hρ : ∀ f : F, ∃ h : algebraMap F FE f ∈ O, ρ ⟨algebraMap F FE f, h⟩ = f)
    (g : O) (hg : ρ g ≠ 0) (Dg : Divisor E FE) (hDg : ∀ P : Place E FE, Dg P = P.ord (g : FE))
    (Df : Divisor K F) (hDf : ∀ v, Df v = v.ord (ρ g)) :
    poleSum (algebraMap (RatFunc K) F RatFunc.X) (Finsupp.mapDomain r Dg) =
      poleSum (algebraMap (RatFunc K) F RatFunc.X) Df := by
  classical
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  have hg0 : (g : FE) ≠ 0 := by
    intro h0
    apply hg
    have : g = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hNf0 : Algebra.norm (RatFunc K) (ρ g) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hg

  have hR : poleSum (algebraMap (RatFunc K) F RatFunc.X) Df =
      (placeInfty K).ord (Algebra.norm (RatFunc K) (ρ g)) := by
    rw [poleSum_eq_sum, ← sum_restrict_eq_ord_norm hg Df hDf (placeInfty K)]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [(restrict_eq_placeInfty_iff w).symm]

  set B : Place E FE → Prop := fun P => ∃ β : E, β ∉ A ∧ P.restrict (RatFunc E) = placeOfPoint E β
    with hB_def
  have hL1 : poleSum (algebraMap (RatFunc K) F RatFunc.X) (Finsupp.mapDomain r Dg) =
      (∑ P ∈ Dg.support, if P.restrict (RatFunc E) = placeInfty E then Dg P else 0) +
        ∑ P ∈ Dg.support, if B P then Dg P else 0 := by
    rw [poleSum_mapDomain, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun P _ => ?_
    have hfib : algebraMap (RatFunc K) F RatFunc.X ∉ (r P).toValuationSubring ↔
        (P.restrict (RatFunc E) = placeInfty E ∨ B P) := by
      rw [hr P, ← not_exists_lt_one_iff A P, hX]
    have hexcl : ¬ (P.restrict (RatFunc E) = placeInfty E ∧ B P) := by
      rintro ⟨h1, β, -, h2⟩
      exact placeOfPoint_ne_placeInfty E β (h2.symm.trans h1)
    by_cases h1 : P.restrict (RatFunc E) = placeInfty E
    · have h2 : ¬ B P := fun h2 => hexcl ⟨h1, h2⟩
      rw [if_pos (hfib.mpr (Or.inl h1)), if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : B P
      · rw [if_pos (hfib.mpr (Or.inr h2)), if_neg h1, if_pos h2, zero_add]
      · rw [if_neg h1, if_neg h2, add_zero, if_neg]
        rw [hfib]; rintro (h | h) <;> contradiction

  have hS1 : (∑ P ∈ Dg.support, if P.restrict (RatFunc E) = placeInfty E then Dg P else 0) =
      (placeInfty E).ord (Algebra.norm (RatFunc E) (g : FE)) :=
    sum_restrict_eq_ord_norm hg0 Dg hDg (placeInfty E)

  let ptOf : Place E FE → E := fun P =>
    if h : ∃ β : E, P.restrict (RatFunc E) = placeOfPoint E β then h.choose else 0
  have ptOf_eq : ∀ (P : Place E FE) (β : E), P.restrict (RatFunc E) = placeOfPoint E β → ptOf P = β := by
    intro P β h
    have hex : ∃ β : E, P.restrict (RatFunc E) = placeOfPoint E β := ⟨β, h⟩
    have h1 : ptOf P = hex.choose := dif_pos hex
    rw [h1]
    exact placeOfPoint_injective E (hex.choose_spec.symm.trans h)
  set s : Finset (Place E FE) := Dg.support.filter B with hs_def
  set S : Finset E := s.image ptOf with hS_def
  have hSA : ∀ β ∈ S, β ∉ A := by
    intro β hβ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hβ
    obtain ⟨β', hβ'A, hP'⟩ := (Finset.mem_filter.mp hP).2
    rwa [ptOf_eq P β' hP']
  have hfibre : ∀ β : E, (∑ P ∈ Dg.support, if P.restrict (RatFunc E) = placeOfPoint E β then Dg P else 0)
      = (placeOfPoint E β).ord (Algebra.norm (RatFunc E) (g : FE)) := fun β =>
    sum_restrict_eq_ord_norm hg0 Dg hDg (placeOfPoint E β)
  have hS : ∀ β : E, β ∉ A → (placeOfPoint E β).ord (Algebra.norm (RatFunc E) (g : FE)) ≠ 0 → β ∈ S := by
    intro β hβA hne
    rw [← hfibre β] at hne
    obtain ⟨P, hP, hP'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hPβ : P.restrict (RatFunc E) = placeOfPoint E β := by
      by_contra h; rw [if_neg h] at hP'; exact hP' rfl
    have hPs : P ∈ s := Finset.mem_filter.mpr ⟨hP, β, hβA, hPβ⟩
    exact Finset.mem_image.mpr ⟨P, hPs, ptOf_eq P β hPβ⟩
  have hS2 : (∑ P ∈ Dg.support, if B P then Dg P else 0) =
      ∑ β ∈ S, (placeOfPoint E β).ord (Algebra.norm (RatFunc E) (g : FE)) := by
    rw [hS_def, Finset.sum_image' (fun P => Dg P), Finset.sum_filter]
    intro P₀ hP₀
    obtain ⟨β₀, hβ₀A, hP₀'⟩ := (Finset.mem_filter.mp hP₀).2
    rw [ptOf_eq P₀ β₀ hP₀', ← hfibre β₀, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun P hP => ?_
    have hiff : P.restrict (RatFunc E) = placeOfPoint E β₀ ↔ (B P ∧ ptOf P = β₀) := by
      constructor
      · intro h; exact ⟨⟨β₀, hβ₀A, h⟩, ptOf_eq P β₀ h⟩
      · rintro ⟨⟨β, -, hβ⟩, h2⟩
        rw [hβ, ← h2, ptOf_eq P β hβ]
    by_cases h : P.restrict (RatFunc E) = placeOfPoint E β₀
    · rw [if_pos h, if_pos (hiff.mp h).1, if_pos (hiff.mp h).2]
    · by_cases hB : B P
      · rw [if_neg h, if_pos hB, if_neg]
        exact fun h2 => h (hiff.mpr ⟨hB, h2⟩)
      · rw [if_neg h, if_neg hB]

  set O' : ValuationSubring (RatFunc E) := O.comap (algebraMap (RatFunc E) FE) with hO'_def
  set ρ' : O' →+* F := ρ.comp ((algebraMap (RatFunc E) FE).restrict O'.toSubring O.toSubring
    fun z hz => (ValuationSubring.mem_comap.mp hz)) with hρ'_def
  have hO' : ∀ c : E, algebraMap E (RatFunc E) c ∈ O' ↔ c ∈ A := by
    intro c
    rw [hO'_def, ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply, hO]
  have hker' : RingHom.ker ρ' = IsLocalRing.maximalIdeal O' := by
    ext z
    rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have hzO : algebraMap (RatFunc E) FE z ∈ O := ValuationSubring.mem_comap.mp z.2
    have h1 : ρ' z = ρ ⟨algebraMap (RatFunc E) FE z, hzO⟩ := rfl
    rw [h1, ← RingHom.mem_ker, hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rcases eq_or_ne (z : RatFunc E) 0 with hz | hz
    · have hz' : z = 0 := Subtype.ext hz
      have h0 : (⟨algebraMap (RatFunc E) FE z, hzO⟩ : O) = 0 := Subtype.ext (by simp [hz])
      rw [h0, hz']
      simp
    · have hz1 : (algebraMap (RatFunc E) FE z) ≠ 0 := (map_ne_zero _).mpr hz
      rw [isUnit_iff_inv_mem O ⟨_, hzO⟩ hz1, isUnit_iff_inv_mem O' z hz]
      simp only [hO'_def, ValuationSubring.mem_comap, map_inv₀]
  have hρ' : ∀ p : K[X],
      ∃ h : algebraMap E[X] (RatFunc E) (p.map (algebraMap K E)) ∈ O',
        ρ' ⟨_, h⟩ = algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) p) := by
    intro p
    have key := algebraMap_polynomial_map hX p
    obtain ⟨h, hh⟩ := hρ (algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) p))
    have h' : algebraMap (RatFunc E) FE (algebraMap E[X] (RatFunc E) (p.map (algebraMap K E))) ∈ O := by
      rw [key]; exact h
    refine ⟨ValuationSubring.mem_comap.mpr h', ?_⟩
    calc ρ' ⟨_, ValuationSubring.mem_comap.mpr h'⟩
        = ρ ⟨algebraMap (RatFunc E) FE (algebraMap E[X] (RatFunc E) (p.map (algebraMap K E))), h'⟩ := rfl
      _ = ρ ⟨_, h⟩ := by congr 1; exact Subtype.ext key
      _ = _ := hh

  obtain ⟨hNgO, hρNg⟩ := AlgebraicCurve.residue_norm_eq_norm_residue_of_retraction K F E FE hfg hfgE
    hgen hX A hKA hArat O ρ hO hker hρ g hg
  have hGmem : Algebra.norm (RatFunc E) (g : FE) ∈ O' := ValuationSubring.mem_comap.mpr hNgO
  have hGN : ρ' ⟨Algebra.norm (RatFunc E) (g : FE), hGmem⟩ =
      algebraMap (RatFunc K) F (Algebra.norm (RatFunc K) (ρ g)) := hρNg
  have hXchild := ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction K E F A hKA
    hArat O' ρ' hO' hker' hρ' ⟨Algebra.norm (RatFunc E) (g : FE), hGmem⟩
    (Algebra.norm (RatFunc K) (ρ g)) hNf0 hGN S hSA hS

  rw [hR, hL1, hS1, hS2, hXchild]

end Core

end DeuringPrincipalDivisorReduction

open DeuringPrincipalDivisorReduction in

theorem solution
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (A : ValuationSubring E) (r : Place E FE → Place K F)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1)
    (O : ValuationSubring FE) (ρ : O →+* F)
    (hO : ∀ c : E, algebraMap E FE c ∈ O ↔ c ∈ A)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
    (hρ : ∀ f : F, ∃ h : algebraMap F FE f ∈ O, ρ ⟨algebraMap F FE f, h⟩ = f)
    (g : O) (hg : ρ g ≠ 0) (Dg : Divisor E FE) (hDg : ∀ P : Place E FE, Dg P = P.ord (g : FE))
    (v : Place K F) :
    Finsupp.mapDomain r Dg v = v.ord (ρ g) := by
  classical
  obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) (ρ g) hg
  rw [← hDf v]
  by_contra hne
  set Λ : Divisor K F := Finsupp.mapDomain r Dg - Df with hΛ_def
  have hΛv : Λ v ≠ 0 := by
    rw [hΛ_def, Finsupp.sub_apply]
    exact sub_ne_zero.mpr hne
  have hv : v ∈ Λ.support := Finsupp.mem_support_iff.mpr hΛv

  obtain ⟨x, hx0, hxord⟩ :=
    Place.exists_forall_ord_eq Λ.support (fun w => if w = v then (-1 : ℤ) else 0)
  have hxv : v.ord x = -1 := by simpa using hxord v hv
  have hx : Transcendental K x := by
    intro halg
    obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one K x
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halg.isIntegral))
    have h0 := Place.ord_algebraMap v c
    rw [hc, hxv] at h0
    norm_num at h0
  have hpole : poleSum x Λ = Λ v := by
    rw [poleSum_eq_sum]
    have hcongr : ∀ w ∈ Λ.support,
        (if x ∉ w.toValuationSubring then Λ w else 0) = if w = v then Λ w else 0 := by
      intro w hw
      have hordw := hxord w hw
      by_cases hwv : w = v
      · rw [if_pos hwv] at hordw
        rw [if_pos hwv, if_pos]
        rw [Place.mem_iff_ord_nonneg _ hx0, hordw]
        norm_num
      · rw [if_neg hwv] at hordw
        rw [if_neg hwv, if_neg]
        rw [not_not, Place.mem_iff_ord_nonneg _ hx0, hordw]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq', if_pos hv]

  letI iK := ratAlg (K := K) hx
  haveI := ratAlg_tower (K := K) hx
  haveI := ratAlg_finite (K := K) hx (finiteDimensional_adjoin_of_transcendental' hfg hx)
  have hx' : Transcendental E (algebraMap F FE x) := by
    apply transcendental_of_linearIndependent_pow
    have h := AlgebraicCurve.linearIndependent_of_constantFieldExtension K F E FE hfg hfgE hgen
      (AlgebraicCurve.linearIndependent_pow_of_transcendental hx)
    simpa only [map_pow] using h
  letI iE := ratAlg (K := E) hx'
  haveI := ratAlg_tower (K := E) hx'
  haveI := ratAlg_finite (K := E) hx' (finiteDimensional_adjoin_of_transcendental' hfgE hx')
  have hX : algebraMap (RatFunc E) FE RatFunc.X = algebraMap F FE (algebraMap (RatFunc K) F RatFunc.X) := by
    rw [ratAlg_X hx, ratAlg_X hx']
  have hcore := core hfg hfgE hgen hX A r hKA hArat hr O ρ hO hker hρ g hg Dg hDg Df hDf
  rw [ratAlg_X hx] at hcore
  have h0 : poleSum x Λ = 0 := by rw [hΛ_def, poleSum_sub, hcore, sub_self]
  exact hΛv (hpole.symm.trans h0)

end S_AlgebraicCurve_Divisor_mapDomain_placeReduction_eq_ord_of_retraction
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_mapDomain_placeReduction_eq_ord_of_retraction (solution)
