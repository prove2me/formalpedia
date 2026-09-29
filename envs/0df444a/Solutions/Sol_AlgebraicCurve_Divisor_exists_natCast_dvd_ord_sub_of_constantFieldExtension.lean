-- Prove2me | solution 1 for AlgebraicCurve.Divisor.exists_natCast_dvd_ord_sub_of_constantFieldExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/21f6c37c-2f04-5f45-ba0f-c0f46663383f

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_exists_placeMap_mapDomain_eq_ord_of_good_constantReduction
import Theorems.Thm_AlgebraicCurve_exists_constantReduction_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_exists_genus_riemannIndex_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_exists_natCast_dvd_ord_sub_of_constantFieldExtension
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Divisor_exists_natCast_dvd_ord_sub_of_constantFieldExtension.AlgebraicCurve IsLocalRing Module"
open scoped IntermediateField.algebraAdjoinAdjoin

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.ord_mul Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic HasPrincipalDivisors.exists_divisor Place.toValuationSubring IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed genusFF LSpace ell mem_lSpace_iff_ord algebraMap_mem_lSpace_zero ConstantsAreBase indexOfSpecialty linearIndependent_of_constantFieldExtension Place.exists_comap_algebraMap_eq_of_constantFieldExtension Place.exists_toValuationSubring_eq_comap_ringHom isCurveOver_of_transcendental_of_isSeparable genusFF_eq_of_constantFieldExtension_of_isAlgClosed exists_placeMap_mapDomain_eq_ord_of_good_constantReduction exists_constantReduction_of_constantFieldExtension exists_genus_riemannIndex_of_isCurveOver essFiniteType_of_transcendental_of_finiteDimensional Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed"
namespace DivisibilityDescent
p2m_open "AlgebraicCurve"

open Polynomial in

theorem linearIndependent_adjoin_simple_of_pow_mul {K' L : Type*} [Field K'] [Field L]
    [Algebra K' L] (x : L) {ι : Type*} (u : ι → L)
    (h : LinearIndependent K' fun p : ℕ × ι => x ^ p.1 * u p.2) :
    LinearIndependent (IntermediateField.adjoin K' ({x} : Set L)) u := by
  classical
  have hR : LinearIndependent (Algebra.adjoin K' ({x} : Set L)) u := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have hp : ∀ i, ∃ p : K'[X], ((g i : Algebra.adjoin K' ({x} : Set L)) : L) = aeval x p := by
      intro i
      have hmem : ((g i : Algebra.adjoin K' ({x} : Set L)) : L) ∈
          (aeval (R := K') x).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (g i).2
      obtain ⟨p, hp⟩ := hmem
      exact ⟨p, hp.symm⟩
    choose p hp using hp
    set D : ℕ := (s.sup fun i => (p i).natDegree) + 1 with hD
    have hdeg : ∀ i ∈ s, (p i).natDegree < D := fun i hi =>
      Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (p i).natDegree) hi)
    rw [linearIndependent_iff'] at h
    have key := h (Finset.range D ×ˢ s) (fun q => (p q.2).coeff q.1) ?_
    · have hpi : p i = 0 := by
        ext k
        by_cases hk : k < D
        · simpa using key (k, i) (Finset.mk_mem_product (Finset.mem_range.mpr hk) hi)
        · rw [coeff_zero]
          exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg i hi) (not_lt.mp hk))
      apply Subtype.ext
      rw [hp i, hpi, map_zero]; rfl
    · rw [Finset.sum_product_right]
      rw [← hg]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Subalgebra.smul_def, hp j, aeval_eq_sum_range' (hdeg j hj), Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [smul_eq_mul, smul_mul_assoc]
  exact hR.localization (IntermediateField.adjoin K' ({x} : Set L))
    (nonZeroDivisors (Algebra.adjoin K' ({x} : Set L)))

open Polynomial in

theorem linearIndependent_pow_of_transcendental {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {x : A} (hx : Transcendental R x) : LinearIndependent R fun k : ℕ => x ^ k := by
  rw [linearIndependent_iff]
  intro l hl
  set p : R[X] := l.sum fun n a => Polynomial.monomial n a with hp
  have hcoeff : ∀ n, p.coeff n = l n := fun n => by
    rw [hp, Finsupp.sum, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · exact (Finsupp.notMem_support_iff.mp h).symm
  have h1 : Polynomial.aeval x p = Finsupp.linearCombination R (fun k : ℕ => x ^ k) l := by
    rw [hp, Finsupp.sum, map_sum, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.aeval_monomial, Algebra.smul_def]
  have h2 := (transcendental_iff.mp hx) p (h1.trans hl)
  ext n
  rw [← hcoeff, h2, Polynomial.coeff_zero, Finsupp.zero_apply]

theorem algebraMap_mem_adjoin_simple {K A K' B : Type*} [Field K] [Field A] [Field K'] [Field B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    [Algebra K' B] [Algebra K K'] [IsScalarTower K K' B] (x : A)
    {e : A} (he : e ∈ IntermediateField.adjoin K ({x} : Set A)) :
    algebraMap A B e ∈ IntermediateField.adjoin K' ({algebraMap A B x} : Set B) := by
  have hle : (IntermediateField.adjoin K ({x} : Set A)).map (IsScalarTower.toAlgHom K A B) ≤
      (IntermediateField.adjoin K' ({algebraMap A B x} : Set B)).restrictScalars K := by
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact IntermediateField.mem_adjoin_simple_self K' (algebraMap A B x)
  exact hle ⟨e, he, rfl⟩

section Degree

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F']
    [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

theorem finrank_adjoin_algebraMap_eq [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {x : F} (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    finrank (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F' =
      finrank (IntermediateField.adjoin K ({x} : Set F)) F := by
  classical
  haveI := hfin
  set E : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hE
  set x' : F' := algebraMap F F' x with hx'
  set E' : IntermediateField K' F' := IntermediateField.adjoin K' ({x'} : Set F') with hE'
  set m := finrank E F with hm_def
  let bF := Module.finBasis E F

  let xE : E := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  have hxEt : Transcendental K xE := by
    have : Function.Injective (algebraMap E F) := (algebraMap E F).injective
    rw [← transcendental_algebraMap_iff this]
    exact hx
  have hpow : LinearIndependent K fun k : ℕ => xE ^ k := linearIndependent_pow_of_transcendental hxEt
  have h1 : LinearIndependent K fun q : ℕ × Fin m => (xE ^ q.1 • bF q.2 : F) :=
    linearIndependent_smul hpow bF.linearIndependent

  have hW := AlgebraicCurve.linearIndependent_of_constantFieldExtension K F K' F' hfg hfg' hgen h1
  have hW' : LinearIndependent K' fun p : ℕ × Fin m => x' ^ p.1 * algebraMap F F' (bF p.2) := by
    convert hW using 1
    funext p
    simp only [hx', IntermediateField.algebraMap_apply, Algebra.smul_def, map_mul, map_pow, xE]

  set b' : Fin m → F' := fun i => algebraMap F F' (bF i) with hb'
  have hu : LinearIndependent E' b' := linearIndependent_adjoin_simple_of_pow_mul x' b' hW'

  set V : Submodule E' F' := Submodule.span E' (Set.range b') with hV_def
  have hEE' : ∀ e : E, algebraMap F F' (e : F) ∈ E' := fun e =>
    algebraMap_mem_adjoin_simple (K' := K') x e.2
  have hFV : ∀ f : F, algebraMap F F' f ∈ V := by
    intro f
    rw [← bF.sum_repr f, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : algebraMap F F' (bF.repr f i • bF i) =
        (⟨algebraMap F F' (bF.repr f i : F), hEE' _⟩ : E') • b' i := by
      rw [IntermediateField.smul_def, IntermediateField.smul_def, smul_eq_mul, map_mul,
        smul_eq_mul]
    rw [this]
    exact V.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hVV : V * V ≤ V := by
    rw [hV_def, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    show b' i * b' j ∈ V
    rw [hb']; dsimp only; rw [← map_mul]; exact hFV _
  have h1V : (1 : F') ∈ V := by simpa using hFV 1
  let A : Subalgebra E' F' :=
    { carrier := V
      mul_mem' := fun ha hb => hVV (Submodule.mul_mem_mul ha hb)
      one_mem' := h1V
      add_mem' := fun ha hb => V.add_mem ha hb
      zero_mem' := V.zero_mem
      algebraMap_mem' := fun e' => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact V.smul_mem _ h1V }
  have hAfg : (Subalgebra.toSubmodule A).FG := Submodule.fg_span (Set.finite_range b')
  have hinv : ∀ z ∈ A, z⁻¹ ∈ A := fun z hz =>
    A.inv_mem_of_algebraic (x := ⟨z, hz⟩) (IsIntegral.of_mem_of_fg A hAfg z hz).isAlgebraic
  let IF : IntermediateField K' F' := (A.restrictScalars K').toIntermediateField hinv
  have hIF : IF = ⊤ := by
    rw [eq_top_iff, ← hgen, IntermediateField.adjoin_le_iff]
    rintro _ ⟨f, rfl⟩
    exact hFV f
  have hVtop : V = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ IF := hIF ▸ IntermediateField.mem_top
    exact hz
  haveI : Module.Finite E' F' := ⟨hVtop ▸ Submodule.fg_span (Set.finite_range b')⟩
  have hle : Module.finrank E' F' ≤ m := by
    have := finrank_range_le_card (R := E') b'
    unfold Set.finrank at this
    rw [← hV_def, hVtop, finrank_top, Fintype.card_fin] at this
    exact this

  refine le_antisymm hle ?_
  simpa using hu.fintype_card_le_finrank

end Degree

theorem ord_eq_zero_of_mem_of_inv_mem {k L : Type*} [Field k] [Field L] [Algebra k L]
    (w : Place k L) {z : L} (hz : z ∈ w.toValuationSubring)
    (hzi : z⁻¹ ∈ w.toValuationSubring) : w.ord z = 0 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · exact w.ord_zero
  · let u : w.toValuationSubringˣ :=
      ⟨⟨z, hz⟩, ⟨z⁻¹, hzi⟩, Subtype.ext (mul_inv_cancel₀ hz0), Subtype.ext (inv_mul_cancel₀ hz0)⟩
    exact w.ord_coe_unit u

theorem ord_algebraMap_base {k L : Type*} [Field k] [Field L] [Algebra k L]
    (w : Place k L) (a : k) : w.ord (algebraMap k L a) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero]; exact w.ord_zero
  · refine ord_eq_zero_of_mem_of_inv_mem w (w.algebraMap_mem' a) ?_
    rw [← map_inv₀]
    exact w.algebraMap_mem' _

def rebase {k K L : Type*} [Field k] [Field K] [Field L] [Algebra K L] [Algebra k L]
    (v : Place K L) (h : ∀ a : k, algebraMap k L a ∈ v.toValuationSubring) : Place k L where
  toValuationSubring := v.toValuationSubring
  algebraMap_mem' := h
  ne_top' := v.ne_top'
  isPrincipalIdealRing' := v.isPrincipalIdealRing'

theorem ord_rebase {k K L : Type*} [Field k] [Field K] [Field L] [Algebra K L] [Algebra k L]
    (v : Place K L) (h : ∀ a : k, algebraMap k L a ∈ v.toValuationSubring) (f : L) :
    (rebase v h).ord f = v.ord f := rfl

theorem transfer_fg {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L]
    [Algebra k L] [IsScalarTower k K L] (hk : Function.Surjective (algebraMap k K))
    {x : L} (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set L)) L) :
    Transcendental k x ∧ FiniteDimensional (IntermediateField.adjoin k ({x} : Set L)) L ∧
      Module.finrank (IntermediateField.adjoin k ({x} : Set L)) L =
        Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L := by
  have hxk : Transcendental k x := hx.restrictScalars (algebraMap k K).injective
  have hrange : Set.range (algebraMap k L) = Set.range (algebraMap K L) := by
    rw [IsScalarTower.algebraMap_eq k K L, RingHom.coe_comp, Set.range_comp, hk.range_eq,
      Set.image_univ]
  have hmem : ∀ y : L, y ∈ IntermediateField.adjoin k ({x} : Set L) ↔
      y ∈ IntermediateField.adjoin K ({x} : Set L) := fun y => by
    rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield, hrange,
      ← IntermediateField.adjoin_toSubfield, IntermediateField.mem_toSubfield]
  let j : IntermediateField.adjoin k ({x} : Set L) ≃+* IntermediateField.adjoin K ({x} : Set L) :=
    { toFun := fun y => ⟨y, (hmem y).mp y.2⟩
      invFun := fun y => ⟨y, (hmem y).mpr y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have hc : (algebraMap (IntermediateField.adjoin K ({x} : Set L)) L).comp j.toRingHom =
      (RingEquiv.refl L).toRingHom.comp
        (algebraMap (IntermediateField.adjoin k ({x} : Set L)) L) :=
    RingHom.ext fun _ => rfl
  haveI := hfin
  refine ⟨hxk, ?_, Algebra.finrank_eq_of_equiv_equiv j (RingEquiv.refl L) hc⟩
  exact Module.Finite.of_equiv_equiv j.symm (RingEquiv.refl L) (RingHom.ext fun _ => rfl)

section Residue

variable {L : Type*} [Field L] {A : ValuationSubring L}

open Polynomial in

theorem mem_of_isRoot_monic {P : A[X]} (hP : P.Monic) {x : L}
    (hx : (P.map (algebraMap A L)).IsRoot x) : x ∈ A := by
  have hint : IsIntegral A x := ⟨P, hP, by rwa [← eval_map, ← IsRoot.def]⟩
  have : IsIntegrallyClosed A := inferInstance
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff L).mp this hint
  rw [← hy]
  exact y.2

open Polynomial in

theorem isAlgClosed_residueField [IsAlgClosed L] : IsAlgClosed (ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue A) := Ideal.Quotient.mk_surjective
  obtain ⟨P, hPp, hPdeg, hPmon⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic (mem_lifts_of_surjective hsurj p) hp
  have hdeg : (P.map (algebraMap A L)).degree ≠ 0 := by
    rw [hPmon.degree_map, hPdeg]
    exact fun h0 => hirr.not_isUnit (isUnit_iff_degree_eq_zero.mpr h0) |>.elim
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
  have hxA : x ∈ A := mem_of_isRoot_monic hPmon hx
  refine ⟨IsLocalRing.residue A ⟨x, hxA⟩, ?_⟩
  have hPx : P.eval ⟨x, hxA⟩ = 0 := by
    have h1 : (P.map (algebraMap A L)).eval x = 0 := hx
    rw [eval_map] at h1
    have h2 : algebraMap A L (P.eval ⟨x, hxA⟩) = 0 := by
      rw [← eval₂_at_apply]; exact h1
    exact (map_eq_zero_iff _ (IsFractionRing.injective A L)).mp h2
  rw [← hPp, eval_map, eval₂_at_apply, hPx, map_zero]

end Residue

section Pole

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_range_of_forall_ord_nonneg [IsAlgClosed K] [IsCurveOver K F]
    (j : F) (hj : Transcendental K j)
    [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F]
    {f : F} (hf0 : f ≠ 0) (hord : ∀ v : Place K F, 0 ≤ v.ord f) :
    f ∈ (algebraMap K F).range := by
  classical
  obtain ⟨Df, hDf, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have hzero : ∀ v : Place K F, v.ord f = 0 := by
    rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum] at hdeg
    have hnonneg : ∀ v ∈ Df.support,
        (0 : ℤ) ≤ (AddMonoidHom.mulRight (v.deg : ℤ)) (Df v) := by
      intro v _
      simp only [AddMonoidHom.coe_mulRight, IsCurveOver.deg_eq_one_of_isAlgClosed v,
        Nat.cast_one, mul_one, hDf]
      exact hord v
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hdeg
    intro v
    by_cases hv : v ∈ Df.support
    · have := hall v hv
      simpa [IsCurveOver.deg_eq_one_of_isAlgClosed v, hDf] using this
    · have : Df v = 0 := Finsupp.notMem_support_iff.mp hv
      rwa [hDf] at this
  exact Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed j hj hzero

theorem constantsAreBase_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F]
    (j : F) (hj : Transcendental K j)
    [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F] :
    ConstantsAreBase K F := by
  refine le_antisymm ?_ ?_
  · intro f hf
    rcases eq_or_ne f 0 with rfl | hf0
    · exact zero_mem _
    have hord : ∀ v : Place K F, 0 ≤ v.ord f := fun v => by
      simpa using ((mem_lSpace_iff_ord.mp hf).resolve_left hf0) v
    obtain ⟨c, hc⟩ := mem_range_of_forall_ord_nonneg j hj hf0 hord
    exact ⟨c, hc⟩
  · rintro _ ⟨c, rfl⟩
    exact algebraMap_mem_lSpace_zero c

theorem exists_riemann_inequality [IsAlgClosed K] [IsCurveOver K F]
    (j : F) (hj : Transcendental K j)
    [hfd : FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F] :
    ∃ γ : ℤ, ∀ D : Divisor K F, Divisor.degree D + 1 - γ ≤ (ell D : ℤ) := by
  haveI : Algebra.EssFiniteType K F :=
    essFiniteType_of_transcendental_of_finiteDimensional hj hfd
  obtain ⟨γ, hγ⟩ :=
    exists_genus_riemannIndex_of_isCurveOver (K := K) (F := F) (constantsAreBase_of_isAlgClosed j hj)
  refine ⟨γ, fun D => ?_⟩
  have h := (hγ D).2
  have h0 : (0 : ℤ) ≤ (indexOfSpecialty D : ℤ) := Int.natCast_nonneg _
  linarith

theorem exists_ord_neg_and_forall_ord_nonneg [IsAlgClosed K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (v : Place K F) :
    ∃ t : F, t ≠ 0 ∧ v.ord t < 0 ∧ ∀ w : Place K F, w ≠ v → 0 ≤ w.ord t := by
  classical
  obtain ⟨j, hj, hfd⟩ := hfg
  haveI := hfd
  obtain ⟨γ, hγ⟩ := exists_riemann_inequality (K := K) (F := F) j hj

  obtain ⟨m, hm⟩ : ∃ m : ℕ, γ + 1 ≤ (m : ℤ) := ⟨(γ + 1).toNat, Int.self_le_toNat _⟩
  have hell : (2 : ℤ) ≤ (ell (Finsupp.single v (m : ℤ) : Divisor K F) : ℤ) := by
    have h := hγ (Finsupp.single v (m : ℤ))
    rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed v, Nat.cast_one,
      mul_one] at h
    linarith

  have hnot : ¬ (LSpace (Finsupp.single v (m : ℤ) : Divisor K F) ≤
      LinearMap.range (Algebra.linearMap K F)) := by
    intro hle
    have h1 : Module.finrank K (LSpace (Finsupp.single v (m : ℤ) : Divisor K F)) ≤ 1 := by
      calc Module.finrank K (LSpace (Finsupp.single v (m : ℤ) : Divisor K F))
          ≤ Module.finrank K (LinearMap.range (Algebra.linearMap K F)) :=
            Submodule.finrank_mono hle
        _ = 1 := by
            rw [LinearMap.finrank_range_of_inj (f := Algebra.linearMap K F)
              (algebraMap K F).injective, Module.finrank_self]
    have : (ell (Finsupp.single v (m : ℤ) : Divisor K F) : ℤ) ≤ 1 := by exact_mod_cast h1
    linarith
  obtain ⟨t, htD, htc⟩ := SetLike.not_le_iff_exists.mp hnot
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact htc (zero_mem _)
  have hordD := (mem_lSpace_iff_ord.mp htD).resolve_left ht0
  have hw : ∀ w : Place K F, w ≠ v → 0 ≤ w.ord t := fun w hwv => by
    have := hordD w
    rwa [Finsupp.single_eq_of_ne hwv, neg_zero] at this
  refine ⟨t, ht0, ?_, hw⟩
  by_contra hv
  push Not at hv
  have hall : ∀ w : Place K F, 0 ≤ w.ord t := fun w => by
    by_cases hwv : w = v
    · rw [hwv]; exact hv
    · exact hw w hwv
  obtain ⟨c, hc⟩ := mem_range_of_forall_ord_nonneg j hj ht0 hall
  exact htc ⟨c, hc⟩

end Pole

section Main

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F']
    [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

section Lift

variable [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
  (hfg : ∃ x : F, Transcendental K x ∧
    FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
  (hfg' : ∃ x : F', Transcendental K' x ∧
    FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
  (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)

noncomputable def liftPlace (P : Place K F) : Place K' F' :=
  Classical.choose
    (AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension
      K F K' F' hfg hfg' hgen P)

theorem liftPlace_spec (P : Place K F) :
    (liftPlace hfg hfg' hgen P).toValuationSubring.comap (algebraMap F F') =
        P.toValuationSubring ∧
      (∀ f : F, (liftPlace hfg hfg' hgen P).ord (algebraMap F F' f) = P.ord f) ∧
      ∀ Q' : Place K' F', Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
        Q' = liftPlace hfg hfg' hgen P :=
  Classical.choose_spec
    (AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension
      K F K' F' hfg hfg' hgen P)

theorem liftPlace_comap (P : Place K F) :
    (liftPlace hfg hfg' hgen P).toValuationSubring.comap (algebraMap F F') =
      P.toValuationSubring :=
  (liftPlace_spec hfg hfg' hgen P).1

theorem ord_liftPlace (P : Place K F) (f : F) :
    (liftPlace hfg hfg' hgen P).ord (algebraMap F F' f) = P.ord f :=
  (liftPlace_spec hfg hfg' hgen P).2.1 f

theorem eq_liftPlace {P : Place K F} {Q' : Place K' F'}
    (h : Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring) :
    Q' = liftPlace hfg hfg' hgen P :=
  (liftPlace_spec hfg hfg' hgen P).2.2 Q' h

theorem liftPlace_injective :
    Function.Injective (liftPlace (K := K) (F := F) (K' := K') (F' := F') hfg hfg' hgen) := by
  intro P Q h
  apply Place.ext
  rw [← liftPlace_comap hfg hfg' hgen P, h, liftPlace_comap]

theorem ord_algebraMap_eq_zero_of_forall_ne (w : Place K' F')
    (hw : ∀ P : Place K F, w ≠ liftPlace hfg hfg' hgen P) (f : F) :
    w.ord (algebraMap F F' f) = 0 := by
  by_contra hne
  obtain ⟨x, hx, hfin⟩ := id hfg
  haveI := hfin
  have hwK : ∀ a : K, algebraMap F F' (algebraMap K F a) ∈ w.toValuationSubring := fun a => by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K K' F']
    exact w.algebraMap_mem' _
  have hwx : ∃ y : F, algebraMap F F' y ∉ w.toValuationSubring := by
    by_contra hall
    push Not at hall
    exact hne (ord_eq_zero_of_mem_of_inv_mem w (hall f) (by rw [← map_inv₀]; exact hall _))
  obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom
    (K := K) x (algebraMap F F') w.toValuationSubring hwK hwx
  exact hw v (eq_liftPlace hfg hfg' hgen hv.symm)

end Lift

theorem dvd_ord_algebraMap [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {n : ℤ} {g : F} (hg : ∀ v : Place K F, n ∣ v.ord g)
    (v' : Place K' F') : n ∣ v'.ord (algebraMap F F' g) := by
  by_cases hv : ∃ v : Place K F, v' = liftPlace hfg hfg' hgen v
  · obtain ⟨v, rfl⟩ := hv
    rw [ord_liftPlace]
    exact hg v
  · push Not at hv
    rw [ord_algebraMap_eq_zero_of_forall_ne hfg hfg' hgen v' hv]
    exact dvd_zero _

theorem exists_of_conorm [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (_hn : n ≠ 0) (D : Divisor K F) (D' : Divisor K' F')
    (hD'over : ∀ (v' : Place K' F') (v : Place K F),
      v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring → D' v' = D v)
    (hD'off : ∀ v' : Place K' F',
      (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        D' v' = 0)
    (f' : F') (hf'0 : f' ≠ 0) (hdiv' : ∀ v' : Place K' F', (n : ℤ) ∣ v'.ord f' - D' v') :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, (n : ℤ) ∣ v.ord f - D v := by
  classical
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  obtain ⟨x₀, hx₀, hfin₀⟩ := id hfg

  obtain ⟨O, ρ, hρF, hker, hreg, hconstK⟩ :=
    AlgebraicCurve.exists_constantReduction_of_constantFieldExtension K F K' F' hfg hfg' hgen
  have hFO : ∀ f : F, algebraMap F F' f ∈ O := fun f => by
    obtain ⟨h, -⟩ := hρF f; exact h
  have hρF' : ∀ (f : F) (h : algebraMap F F' f ∈ O), ρ ⟨algebraMap F F' f, h⟩ = f := fun f h => by
    obtain ⟨h', e⟩ := hρF f; exact e
  have hsurj : Function.Surjective ρ := fun f => ⟨_, hρF' f (hFO f)⟩
  have hres_unit : ∀ y : O, IsUnit y → ρ y ≠ 0 := fun y hy h0 => by
    have hmem : y ∈ RingHom.ker ρ := RingHom.mem_ker.mpr h0
    rw [hker] at hmem
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) hy
  have hunit : ∀ y : O, ρ y ≠ 0 → IsUnit y := fun y hy => by
    by_contra h
    have hmem : y ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr h
    rw [← hker] at hmem
    exact hy (RingHom.mem_ker.mp hmem)

  set A' : ValuationSubring K' := O.comap (algebraMap K' F') with hA'
  have hOA : ∀ c : K', algebraMap K' F' c ∈ O ↔ c ∈ A' := fun c => Iff.rfl
  let ι : A' →+* O :=
    ((algebraMap K' F').comp A'.subtype).codRestrict O (fun a => (hOA a).mpr a.2)
  let ρA : A' →+* F := ρ.comp ι
  have hmax : ∀ a : A', ρA a = 0 → a ∈ IsLocalRing.maximalIdeal A' := fun a ha => by
    by_contra hna
    have hu : IsUnit a := by
      by_contra hnu
      exact hna ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
    exact hres_unit (ι a) (hu.map ι) ha
  have hKA : ∀ c : K, algebraMap K K' c ∈ A' := fun c => by
    show algebraMap K' F' (algebraMap K K' c) ∈ O
    rw [← IsScalarTower.algebraMap_apply K K' F' c, IsScalarTower.algebraMap_apply K F F' c]
    exact hFO _
  let ιK : K →+* A' := (algebraMap K K').codRestrict A' hKA
  have hρK : ∀ c : K, ρA (ιK c) = algebraMap K F c := fun c => by
    have : (ι (ιK c) : O) = ⟨algebraMap F F' (algebraMap K F c), hFO _⟩ := Subtype.ext (by
      show algebraMap K' F' (algebraMap K K' c) = algebraMap F F' (algebraMap K F c)
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply])
    show ρ (ι (ιK c)) = _
    rw [this, hρF']
  have hφA : ∀ a : A', ∃ c₀ : K, algebraMap K F c₀ = ρA a ∧
      IsLocalRing.residue A' a = IsLocalRing.residue A' (ιK c₀) := fun a => by
    obtain ⟨c₀, hc₀⟩ := hconstK a ((hOA a).mpr a.2)
    refine ⟨c₀, hc₀, ?_⟩
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    refine hmax _ ?_
    rw [map_sub, hρK, sub_eq_zero]
    exact hc₀.symm
  let φ : K →+* ResidueField A' := (IsLocalRing.residue A').comp ιK
  have hφ : Function.Bijective φ := by
    refine ⟨φ.injective, fun r => ?_⟩
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨c₀, -, hc₀⟩ := hφA a
    exact ⟨c₀, hc₀.symm⟩
  let e : K ≃+* ResidueField A' := RingEquiv.ofBijective φ hφ

  letI iK : Algebra (ResidueField A') K := e.symm.toRingHom.toAlgebra
  letI iF : Algebra (ResidueField A') F := ((algebraMap K F).comp e.symm.toRingHom).toAlgebra
  haveI : IsScalarTower (ResidueField A') K F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI iK' : Algebra (ResidueField A') K' := ((algebraMap K K').comp e.symm.toRingHom).toAlgebra
  letI iF' : Algebra (ResidueField A') F' := ((algebraMap K F').comp e.symm.toRingHom).toAlgebra
  haveI : IsScalarTower (ResidueField A') K' F' :=
    IsScalarTower.of_algebraMap_eq (fun c => IsScalarTower.algebraMap_apply K K' F' (e.symm c))
  haveI : IsScalarTower (ResidueField A') F F' :=
    IsScalarTower.of_algebraMap_eq (fun c => IsScalarTower.algebraMap_apply K F F' (e.symm c))
  have hconst : ∀ a : A', ρ ⟨algebraMap K' F' a, (hOA a).mpr a.2⟩ =
      algebraMap (ResidueField A') F (IsLocalRing.residue A' a) := fun a => by
    obtain ⟨c₀, hc₀, hres⟩ := hφA a
    have h1 : IsLocalRing.residue A' a = e c₀ := hres
    show ρA a = algebraMap K F (e.symm (IsLocalRing.residue A' a))
    rw [h1, RingEquiv.symm_apply_apply, hc₀]
  haveI : IsAlgClosed (ResidueField A') := isAlgClosed_residueField
  haveI : CharZero (ResidueField A') := e.symm.toRingHom.charZero
  have hkK : Function.Surjective (algebraMap (ResidueField A') K) := e.symm.surjective
  obtain ⟨hx₀k, hfink, hfinrk⟩ := transfer_fg hkK hx₀ hfin₀
  haveI : IsCurveOver (ResidueField A') F := by
    haveI := hfink
    haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
    haveI : CharZero (IntermediateField.adjoin (ResidueField A') ({x₀} : Set F)) :=
      (algebraMap (IntermediateField.adjoin (ResidueField A') ({x₀} : Set F)) F).charZero
    exact AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable (ResidueField A') F x₀
      hx₀k hfink inferInstance
  have hfgk : ∃ x : F, Transcendental (ResidueField A') x ∧
      FiniteDimensional (IntermediateField.adjoin (ResidueField A') ({x} : Set F)) F :=
    ⟨x₀, hx₀k, hfink⟩

  have hgood : genusFF (ResidueField A') F = genusFF K' F' :=
    (AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_isAlgClosed (ResidueField A') F K' F'
      hfgk hfg' hgen).symm

  have hreg' : ∃ x : O, Transcendental (ResidueField A') (ρ x) ∧
      0 < finrank (IntermediateField.adjoin (ResidueField A') ({ρ x} : Set F)) F ∧
      finrank (IntermediateField.adjoin K' ({(x : F')} : Set F')) F' =
        finrank (IntermediateField.adjoin (ResidueField A') ({ρ x} : Set F)) F := by
    refine ⟨⟨algebraMap F F' x₀, hFO x₀⟩, ?_, ?_, ?_⟩
    · rw [hρF']; exact hx₀k
    · rw [hρF']; haveI := hfink; exact finrank_pos
    · rw [hρF']
      show finrank (IntermediateField.adjoin K' ({algebraMap F F' x₀} : Set F')) F' = _
      rw [finrank_adjoin_algebraMap_eq hfg hfg' hgen hx₀ hfin₀, hfinrk]

  obtain ⟨r, hr⟩ :=
    AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction
      A' O ρ hOA hsurj hker hconst hreg hreg' hgood

  let rb : Place K F → Place (ResidueField A') F := fun v =>
    rebase v (fun a => v.algebraMap_mem' (e.symm a))
  have hrb_inj : Function.Injective rb := fun v w h => by
    apply Place.ext
    have h' := congrArg Place.toValuationSubring h
    exact h'

  have hcon : ∀ (t : F) (Dt : Divisor K' F') (Dt₀ : Divisor K F),
      (∀ v', Dt v' = v'.ord (algebraMap F F' t)) → (∀ w, Dt₀ w = w.ord t) →
        Dt = Finsupp.mapDomain (liftPlace hfg hfg' hgen) Dt₀ := by
    intro t Dt Dt₀ hDt hDt₀
    ext v'
    rw [hDt]
    by_cases hv : ∃ w, v' = liftPlace hfg hfg' hgen w
    · obtain ⟨w, rfl⟩ := hv
      rw [Finsupp.mapDomain_apply (liftPlace_injective hfg hfg' hgen), hDt₀, ord_liftPlace]
    · push Not at hv
      rw [Finsupp.mapDomain_notin_range _ _ (fun ⟨w, hw⟩ => hv w hw.symm),
        ord_algebraMap_eq_zero_of_forall_ne hfg hfg' hgen v' hv]
  have hsec : ∀ v : Place K F, r (liftPlace hfg hfg' hgen v) = rb v := by
    intro v
    obtain ⟨t, ht0, htv, htw⟩ :=
      exists_ord_neg_and_forall_ord_nonneg (K := K) (F := F) hfg v
    have halgt : algebraMap F F' t ≠ 0 := (map_ne_zero _).mpr ht0
    obtain ⟨Dt, hDt, -⟩ := HasPrincipalDivisors.exists_divisor (K := K') (algebraMap F F' t) halgt
    obtain ⟨Dt₀, hDt₀, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) t ht0
    have hrest : ρ ⟨algebraMap F F' t, hFO t⟩ ≠ 0 := by rw [hρF']; exact ht0
    have hrt := hr ⟨algebraMap F F' t, hFO t⟩ hrest Dt hDt (rb v)
    rw [hρF', hcon t Dt Dt₀ hDt hDt₀, ← Finsupp.mapDomain_comp] at hrt
    by_contra hne
    have hlhs : 0 ≤ Finsupp.mapDomain (r ∘ liftPlace hfg hfg' hgen) Dt₀ (rb v) := by
      rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
      refine Finset.sum_nonneg fun w _ => ?_
      rw [Finsupp.single_apply]
      split_ifs with h
      · have hwv : w ≠ v := by
          rintro rfl
          exact hne h
        rw [hDt₀]
        exact htw w hwv
      · exact le_refl _
    rw [hrt] at hlhs
    have : (rb v).ord t = v.ord t := rfl
    rw [this] at hlhs
    exact absurd htv (not_lt.mpr hlhs)
  have hcomp : r ∘ liftPlace hfg hfg' hgen = rb := funext fun v => hsec v

  have hD'eq : D' = Finsupp.mapDomain (liftPlace hfg hfg' hgen) D := by
    ext v'
    by_cases hv : ∃ v, v' = liftPlace hfg hfg' hgen v
    · obtain ⟨v, rfl⟩ := hv
      rw [Finsupp.mapDomain_apply (liftPlace_injective hfg hfg' hgen),
        hD'over _ v (liftPlace_comap hfg hfg' hgen v)]
    · push Not at hv
      rw [Finsupp.mapDomain_notin_range _ _ (fun ⟨w, hw⟩ => hv w hw.symm)]
      exact hD'off v' fun v h => hv v (eq_liftPlace hfg hfg' hgen h)

  obtain ⟨c, hcO, hcres⟩ := hreg f' hf'0
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hcres
    have : (⟨(0 : K') • f', hcO⟩ : O) = 0 := Subtype.ext (by simp)
    rw [this, map_zero]
  have hc' : algebraMap K' F' c ≠ 0 := (map_ne_zero _).mpr hc0
  set u : O := ⟨c • f', hcO⟩ with hu_def
  have hu0 : (u : F') ≠ 0 := smul_ne_zero hc0 hf'0
  have hu_ord : ∀ v' : Place K' F', v'.ord (u : F') = v'.ord f' := fun v' => by
    show v'.ord (c • f') = _
    rw [Algebra.smul_def, Place.ord_mul _ hc' hf'0, ord_algebraMap_base, zero_add]
  set f : F := ρ u with hf_def
  have hf0 : f ≠ 0 := hcres

  obtain ⟨Du, hDu, -⟩ := HasPrincipalDivisors.exists_divisor (K := K') (u : F') hu0
  let E' : Divisor K' F' :=
    Finsupp.mapRange (fun z => z / (n : ℤ)) (Int.zero_ediv _) (Du - D')
  have hE' : Du = D' + (n : ℤ) • E' := by
    ext v'
    have hdvd : (n : ℤ) ∣ (Du - D') v' := by
      rw [Finsupp.sub_apply, hDu, hu_ord]
      exact hdiv' v'
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, E', Finsupp.mapRange_apply]
    rw [Int.mul_ediv_cancel' hdvd, Finsupp.sub_apply]
    ring

  have hru := hr u hcres Du hDu
  refine ⟨f, hf0, fun v => ⟨Finsupp.mapDomain r E' (rb v), ?_⟩⟩
  have h := hru (rb v)
  rw [hE', Finsupp.mapDomain_add, Finsupp.mapDomain_smul, hD'eq, ← Finsupp.mapDomain_comp, hcomp,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.mapDomain_apply hrb_inj] at h
  have hrbo : (rb v).ord (ρ u) = v.ord f := rfl
  rw [hrbo] at h
  linarith

end Main

end AlgebraicCurve.DivisibilityDescent

open AlgebraicCurve.DivisibilityDescent in
theorem solution (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (hn : n ≠ 0) (D : Divisor K F) (D' : Divisor K' F')
    (hD'over : ∀ (v' : Place K' F') (v : Place K F),
      v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring → D' v' = D v)
    (hD'off : ∀ v' : Place K' F',
      (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) → D' v' = 0)
    (hdiv' : ∃ f' : F', f' ≠ 0 ∧ ∀ v' : Place K' F', (n : ℤ) ∣ v'.ord f' - D' v') :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, (n : ℤ) ∣ v.ord f - D v := by
  obtain ⟨f', hf'0, hdiv'⟩ := hdiv'
  exact exists_of_conorm hfg hfg' hgen n hn D D' hD'over hD'off f' hf'0 hdiv'

end
end S_AlgebraicCurve_Divisor_exists_natCast_dvd_ord_sub_of_constantFieldExtension
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_exists_natCast_dvd_ord_sub_of_constantFieldExtension (solution)
