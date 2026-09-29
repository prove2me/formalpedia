-- Prove2me | solution 1 for AlgebraicCurve.constantsAreBase_of_apply_algebraMap_eq_pow_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/bf922d8b-d034-5e1b-b14a-c778002cdf38

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_constantsAreBase_of_apply_algebraMap_eq_pow_card
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace P2mConstDown

section Comap

variable {K F₀ F : Type*} [Field K] [Field F₀] [Field F] [Algebra K F] [Algebra F₀ F]
  (W : Place K F)

theorem map_ne_zero' {f : F₀} (hf : f ≠ 0) : algebraMap F₀ F f ≠ 0 := by simpa using hf

variable {W} in
theorem mem_comap_iff_ord_nonneg {f : F₀} (hf : f ≠ 0) :
    f ∈ W.toValuationSubring.comap (algebraMap F₀ F) ↔ 0 ≤ W.ord (algebraMap F₀ F f) := by
  rw [ValuationSubring.mem_comap]
  exact W.mem_iff_ord_nonneg (map_ne_zero' hf)

variable {W} in
theorem isUnit_mk_comap_iff {f : F₀} (hf : f ≠ 0)
    (hmem : f ∈ W.toValuationSubring.comap (algebraMap F₀ F)) :
    IsUnit (⟨f, hmem⟩ : W.toValuationSubring.comap (algebraMap F₀ F)) ↔
      W.ord (algebraMap F₀ F f) = 0 := by
  constructor
  · rintro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp h
    have hb' : f * (b : F₀) = 1 := by simpa [Subtype.ext_iff] using hb
    have hbne : (b : F₀) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hb'
      exact zero_ne_one hb'
    have hsum : W.ord (algebraMap F₀ F f) + W.ord (algebraMap F₀ F (b : F₀)) = 0 := by
      rw [← W.ord_mul (map_ne_zero' hf) (map_ne_zero' hbne), ← map_mul, hb', map_one, W.ord_one]
    have h1 : 0 ≤ W.ord (algebraMap F₀ F f) := (mem_comap_iff_ord_nonneg hf).mp hmem
    have h2 : 0 ≤ W.ord (algebraMap F₀ F (b : F₀)) := (mem_comap_iff_ord_nonneg hbne).mp b.2
    omega
  · intro h0
    have hinv : f⁻¹ ∈ W.toValuationSubring.comap (algebraMap F₀ F) :=
      (mem_comap_iff_ord_nonneg (inv_ne_zero hf)).mpr (by rw [map_inv₀, W.ord_inv]; omega)
    exact ⟨⟨⟨f, hmem⟩, ⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf),
      Subtype.ext (inv_mul_cancel₀ hf)⟩, rfl⟩

variable (hex : ∃ f : F₀, f ≠ 0 ∧ 0 < W.ord (algebraMap F₀ F f))
include hex

theorem e_pos : 0 < Place.ramificationIndex (F := F₀) W := by
  have hne : {n : ℕ | 0 < n ∧ ∃ f : F₀, f ≠ 0 ∧ W.ord (algebraMap F₀ F f) = n}.Nonempty := by
    obtain ⟨f, hf0, hf⟩ := hex
    exact ⟨(W.ord (algebraMap F₀ F f)).toNat, by omega, f, hf0, by omega⟩
  exact (Nat.sInf_mem hne).1

theorem exists_ord_eq_e :
    ∃ f : F₀, f ≠ 0 ∧ W.ord (algebraMap F₀ F f) = Place.ramificationIndex (F := F₀) W := by
  have hne : {n : ℕ | 0 < n ∧ ∃ f : F₀, f ≠ 0 ∧ W.ord (algebraMap F₀ F f) = n}.Nonempty := by
    obtain ⟨f, hf0, hf⟩ := hex
    exact ⟨(W.ord (algebraMap F₀ F f)).toNat, by omega, f, hf0, by omega⟩
  exact (Nat.sInf_mem hne).2

theorem e_dvd_ord {f : F₀} (hf : f ≠ 0) :
    (Place.ramificationIndex (F := F₀) W : ℤ) ∣ W.ord (algebraMap F₀ F f) := by
  obtain ⟨g, hg0, hge⟩ := exists_ord_eq_e W hex
  set e : ℤ := (Place.ramificationIndex (F := F₀) W : ℤ) with he
  have hepos : 0 < e := by
    have := e_pos W hex
    omega
  set m : ℤ := W.ord (algebraMap F₀ F f) with hm
  set q : ℤ := m / e with hq
  have hgq : algebraMap F₀ F (g ^ (-q)) = (algebraMap F₀ F g) ^ (-q) := map_zpow₀ _ _ _
  have hr : W.ord (algebraMap F₀ F (f * g ^ (-q))) = m - e * q := by
    rw [map_mul, W.ord_mul (map_ne_zero' hf)
      (by rw [hgq]; exact zpow_ne_zero _ (map_ne_zero' hg0)), hgq, W.ord_zpow, hge, ← hm]
    ring
  have hmod := Int.emod_nonneg m (by omega : e ≠ 0)
  have hmod' := Int.emod_lt_of_pos m hepos
  have hbridge : m % e = m - e * q := by
    rw [hq]
    exact Int.emod_def m e
  rcases eq_or_lt_of_le (show (0 : ℤ) ≤ m - e * q by omega) with heq | hlt
  · exact ⟨q, by omega⟩
  · exfalso
    have hfg : f * g ^ (-q) ≠ 0 := mul_ne_zero hf (zpow_ne_zero _ hg0)
    have hle := W.ramificationIndex_le_ord (F := F₀) hfg (by omega)
    rw [hr, ← he] at hle
    omega

theorem irreducible_mk_comap {g : F₀} (hg0 : g ≠ 0)
    (hmem : g ∈ W.toValuationSubring.comap (algebraMap F₀ F))
    (hge : W.ord (algebraMap F₀ F g) = Place.ramificationIndex (F := F₀) W) :
    Irreducible (⟨g, hmem⟩ : W.toValuationSubring.comap (algebraMap F₀ F)) := by
  have hepos : 0 < Place.ramificationIndex (F := F₀) W := e_pos W hex
  constructor
  · rw [isUnit_mk_comap_iff hg0 hmem, hge]
    omega
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hab' : g = a * b := by simpa [Subtype.ext_iff] using hab
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hg0 (by simpa using hab')
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hg0 (by simpa using hab')
    have hsum : W.ord (algebraMap F₀ F a) + W.ord (algebraMap F₀ F b)
        = Place.ramificationIndex (F := F₀) W := by
      rw [← W.ord_mul (map_ne_zero' ha0) (map_ne_zero' hb0), ← map_mul, ← hab', hge]
    have ha' : 0 ≤ W.ord (algebraMap F₀ F a) := (mem_comap_iff_ord_nonneg ha0).mp ha
    have hb' : 0 ≤ W.ord (algebraMap F₀ F b) := (mem_comap_iff_ord_nonneg hb0).mp hb
    rcases eq_or_lt_of_le ha' with ha0' | hapos
    · exact Or.inl ((isUnit_mk_comap_iff ha0 ha).mpr ha0'.symm)
    rcases eq_or_lt_of_le hb' with hb0' | hbpos
    · exact Or.inr ((isUnit_mk_comap_iff hb0 hb).mpr hb0'.symm)
    exfalso
    have h1 := W.ramificationIndex_le_ord (F := F₀) ha0 hapos
    have h2 := W.ramificationIndex_le_ord (F := F₀) hb0 hbpos
    omega

theorem isPrincipalIdealRing_comap :
    IsPrincipalIdealRing (W.toValuationSubring.comap (algebraMap F₀ F)) := by
  obtain ⟨g, hg0, hge⟩ := exists_ord_eq_e W hex
  have hepos : 0 < Place.ramificationIndex (F := F₀) W := e_pos W hex
  have hgmem : g ∈ W.toValuationSubring.comap (algebraMap F₀ F) :=
    (mem_comap_iff_ord_nonneg hg0).mpr (by omega)
  refine (IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨⟨g, hgmem⟩, irreducible_mk_comap W hex hg0 hgmem hge, ?_⟩).toIsPrincipalIdealRing
  rintro ⟨f, hmem⟩ hx
  have hf : f ≠ 0 := by simpa [Subtype.ext_iff] using hx
  obtain ⟨c, hc⟩ := e_dvd_ord W hex hf
  have hnonneg : 0 ≤ W.ord (algebraMap F₀ F f) := (mem_comap_iff_ord_nonneg hf).mp hmem
  have hcnonneg : 0 ≤ c := by
    by_contra hneg
    have hcle : c ≤ -1 := by omega
    have : (Place.ramificationIndex (F := F₀) W : ℤ) * c
        ≤ (Place.ramificationIndex (F := F₀) W : ℤ) * -1 :=
      mul_le_mul_of_nonneg_left hcle (by omega)
    omega
  set n : ℕ := c.toNat with hn
  have hcn : (n : ℤ) = c := Int.toNat_of_nonneg hcnonneg
  refine ⟨n, ?_⟩
  have hgn : g ^ n ≠ 0 := pow_ne_zero _ hg0
  have hdiv0 : f / g ^ n ≠ 0 := div_ne_zero hf hgn
  have hu0 : W.ord (algebraMap F₀ F (f / g ^ n)) = 0 := by
    have hkey : algebraMap F₀ F (f / g ^ n)
        = algebraMap F₀ F f * (algebraMap F₀ F g) ^ (-(n : ℤ)) := by
      rw [div_eq_mul_inv, map_mul, map_inv₀, map_pow, ← zpow_natCast (algebraMap F₀ F g) n,
        ← zpow_neg]
    rw [hkey, W.ord_mul (map_ne_zero' hf) (zpow_ne_zero _ (map_ne_zero' hg0)),
      W.ord_zpow, hge, hc, ← hcn]
    ring
  have humem : f / g ^ n ∈ W.toValuationSubring.comap (algebraMap F₀ F) :=
    (mem_comap_iff_ord_nonneg hdiv0).mpr (le_of_eq hu0.symm)
  have hu : IsUnit (⟨f / g ^ n, humem⟩ : W.toValuationSubring.comap (algebraMap F₀ F)) :=
    (isUnit_mk_comap_iff hdiv0 humem).mpr hu0
  refine ⟨hu.unit, ?_⟩
  refine Subtype.ext ?_
  have hcoe : ((hu.unit : W.toValuationSubring.comap (algebraMap F₀ F)) : F₀) = f / g ^ n := by
    rw [IsUnit.unit_spec]
  push_cast
  rw [hcoe, mul_comm, div_mul_cancel₀]
  exact hgn

theorem comap_ne_top : W.toValuationSubring.comap (algebraMap F₀ F) ≠ ⊤ := by
  obtain ⟨f, hf0, hf⟩ := hex
  intro htop
  have hmem : f⁻¹ ∈ W.toValuationSubring.comap (algebraMap F₀ F) := htop ▸ trivial
  have := (mem_comap_iff_ord_nonneg (inv_ne_zero hf0)).mp hmem
  rw [map_inv₀, W.ord_inv] at this
  omega

omit hex in

def comapPlace (k : Type*) [Field k] [Algebra k F₀] [Algebra k K] [Algebra k F]
    [IsScalarTower k K F] [IsScalarTower k F₀ F]
    (hex : ∃ f : F₀, f ≠ 0 ∧ 0 < W.ord (algebraMap F₀ F f)) : Place k F₀ where
  toValuationSubring := W.toValuationSubring.comap (algebraMap F₀ F)
  algebraMap_mem' a := by
    show algebraMap F₀ F (algebraMap k F₀ a) ∈ W.toValuationSubring
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k K F]
    exact W.algebraMap_mem' _
  ne_top' := comap_ne_top W hex
  isPrincipalIdealRing' := isPrincipalIdealRing_comap W hex

omit hex in
@[scoped simp] theorem comapPlace_toValuationSubring (k : Type*) [Field k] [Algebra k F₀] [Algebra k K]
    [Algebra k F] [IsScalarTower k K F] [IsScalarTower k F₀ F]
    (hex : ∃ f : F₀, f ≠ 0 ∧ 0 < W.ord (algebraMap F₀ F f)) :
    (comapPlace W k hex).toValuationSubring = W.toValuationSubring.comap (algebraMap F₀ F) :=
  rfl

end Comap

section Constants

variable {k K F₀ F : Type*} [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]

theorem exists_constantEmbedding :
    ∃ j : k →+* K, ∀ a : k, algebraMap K F (j a) = algebraMap F₀ F (algebraMap k F₀ a) := by
  letI : Fintype k := Fintype.ofFinite k
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hmem : ∀ a : k, algebraMap F₀ F (algebraMap k F₀ a) ∈ (algebraMap K F).range := by
    intro a
    set y := algebraMap F₀ F (algebraMap k F₀ a) with hydef
    have hy : y ^ Fintype.card k = y := by
      rw [hydef, ← map_pow, ← map_pow, FiniteField.pow_card]
    have hint : IsIntegral K y := by
      refine ⟨Polynomial.X ^ Fintype.card k - Polynomial.X, ?_, ?_⟩
      · exact (Polynomial.monic_X_pow _).sub_of_left
          (by rw [Polynomial.degree_X_pow, Polynomial.degree_X]; exact_mod_cast hq)
      · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, hy, sub_self]
    have hdeg : (minpoly K y).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
    exact minpoly.mem_range_of_degree_eq_one K y hdeg
  choose j hj using fun a => RingHom.mem_range.mp (hmem a)
  have hinj := (algebraMap K F).injective
  refine ⟨{ toFun := j, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hj⟩
  · apply hinj
    rw [hj, map_one, map_one, map_one]
  · intro a b
    apply hinj
    rw [map_mul, hj, hj, hj, map_mul, map_mul]
  · apply hinj
    rw [hj, map_zero, map_zero, map_zero]
  · intro a b
    apply hinj
    rw [map_add, hj, hj, hj, map_add, map_add]

omit [IsAlgClosed K] [Algebra K F] [Algebra F₀ F] in

theorem mem_range_algebraMap_of_pow_card_eq {L : Type*} [Field L] [Algebra k L] {y : L}
    (hy : y ^ Nat.card k = y) : y ∈ Set.range (algebraMap k L) := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  have hq : 1 < Nat.card k := by rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  by_contra hy'
  set Z : Finset L := insert y (Finset.univ.image (algebraMap k L)) with hZ
  have hyZ : y ∉ Finset.univ.image (algebraMap k L) := by
    intro h
    apply hy'
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h
    exact ⟨a, ha⟩
  have hcardZ : Z.card = Nat.card k + 1 := by
    rw [hZ, Finset.card_insert_of_notMem hyZ,
      Finset.card_image_of_injective _ (algebraMap k L).injective, Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hsub : Z.val ⊆ (Polynomial.X ^ Nat.card k - Polynomial.X : Polynomial L).roots := by
    intro z hz
    rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ hq)]
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      sub_eq_zero]
    rcases Finset.mem_insert.mp (Finset.mem_val.mp hz) with rfl | hz''
    · exact hy
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz''
      rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hq, hcardZ] at hle
  omega

end Constants

section Upstairs

variable {k K F₀ F : Type*} [Field k] [Field K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
  [Algebra k K] [Algebra k F] [IsScalarTower k K F] [IsScalarTower k F₀ F]

theorem essFiniteType_of_gen
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤) :
    Algebra.EssFiniteType K F := by
  classical
  obtain ⟨s, hs⟩ := hfg
  rw [← IntermediateField.fg_top_iff]
  refine ⟨s.image (algebraMap F₀ F), ?_⟩
  apply le_antisymm le_top
  rw [← hgen]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨y, rfl⟩

  let ι' : F₀ →ₐ[k] F := IsScalarTower.toAlgHom k F₀ F
  have hy : y ∈ IntermediateField.adjoin k (s : Set F₀) := by rw [hs]; trivial
  have h1 : ι' y ∈ (IntermediateField.adjoin k (s : Set F₀)).map ι' := ⟨y, hy, rfl⟩
  rw [IntermediateField.adjoin_map] at h1
  have h2 : IntermediateField.adjoin k (ι' '' (s : Set F₀))
      ≤ (IntermediateField.adjoin K ((s.image (algebraMap F₀ F) : Finset F) : Set F)).restrictScalars k := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨z, hz, rfl⟩
    exact IntermediateField.subset_adjoin K _ (by
      rw [Finset.coe_image]
      exact ⟨z, hz, rfl⟩)
  exact h2 h1

end Upstairs

section ConstantsAreBaseDown

variable {k K F₀ F : Type*} [Field k] [Finite k] [Field K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
  [Algebra k K] [Algebra k F] [IsScalarTower k K F] [IsScalarTower k F₀ F]

theorem constantsAreBase_down (hCF : ConstantsAreBase K F) (φ : F →ₐ[K] F)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k)) :
    ConstantsAreBase k F₀ := by
  classical
  apply le_antisymm
  ·
    intro y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · exact ⟨0, by simp⟩

    have hyF : algebraMap F₀ F y ∈ LSpace (0 : Divisor K F) := by
      rw [mem_lSpace_iff_ord]
      refine Or.inr fun W => ?_
      simp only [Finsupp.coe_zero, Pi.zero_apply, neg_zero]
      by_contra hneg
      push Not at hneg

      have hex : ∃ f : F₀, f ≠ 0 ∧ 0 < W.ord (algebraMap F₀ F f) :=
        ⟨y⁻¹, inv_ne_zero hy0, by rw [map_inv₀, W.ord_inv]; omega⟩
      set v : Place k F₀ := comapPlace W k hex with hvdef
      have hyv : y ∈ v.toValuationSubring := by
        rw [mem_lSpace_iff_ord] at hy
        rcases hy with h | h
        · exact absurd h hy0
        · have := h v
          simp only [Finsupp.coe_zero, Pi.zero_apply, neg_zero] at this
          exact (v.mem_iff_ord_nonneg hy0).mpr this
      have hyW : algebraMap F₀ F y ∈ W.toValuationSubring := by
        rw [hvdef, comapPlace_toValuationSubring] at hyv
        exact ValuationSubring.mem_comap.mp hyv
      have := (W.mem_iff_ord_nonneg (map_ne_zero' hy0)).mp hyW
      omega

    have hyK : algebraMap F₀ F y ∈ LinearMap.range (Algebra.linearMap K F) := by
      rw [← hCF]; exact hyF
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hyK
    have h1 : φ (algebraMap F₀ F y) = algebraMap F₀ F y := by
      rw [← hc, Algebra.linearMap_apply]
      exact φ.commutes c
    have hfix : y ^ Nat.card k = y := by
      apply (algebraMap F₀ F).injective
      rw [← hφ y, h1]
    obtain ⟨a, ha⟩ := mem_range_algebraMap_of_pow_card_eq (k := k) hfix
    exact LinearMap.mem_range.mpr ⟨a, ha⟩
  ·
    intro x hx
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hx
    rw [Algebra.linearMap_apply, mem_lSpace_iff_ord]
    rcases eq_or_ne a 0 with rfl | ha0
    · exact Or.inl (map_zero _)
    · refine Or.inr fun v => ?_
      simp only [Finsupp.coe_zero, Pi.zero_apply, neg_zero]
      exact (v.mem_iff_ord_nonneg ((map_ne_zero _).mpr ha0)).mp (v.algebraMap_mem' a)

end ConstantsAreBaseDown

end P2mConstDown
p2m_reactivate "P2MW.S_AlgebraicCurve_constantsAreBase_of_apply_algebraMap_eq_pow_card.P2mConstDown"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_constantsAreBase_of_apply_algebraMap_eq_pow_card.P2mConstDown"

open AlgebraicCurve P2mConstDown in

theorem solution
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k)) :
    AlgebraicCurve.ConstantsAreBase k F₀ := by
  classical

  obtain ⟨j, hj⟩ := exists_constantEmbedding (k := k) (K := K) (F₀ := F₀) (F := F)
  letI : Algebra k K := j.toAlgebra
  letI : Algebra k F := ((algebraMap K F).comp j).toAlgebra
  haveI : IsScalarTower k K F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k F₀ F := IsScalarTower.of_algebraMap_eq fun a => hj a

  haveI hEss : Algebra.EssFiniteType K F := essFiniteType_of_gen (k := k) hfg hgen
  have hCF : ConstantsAreBase K F := by
    obtain ⟨x, hx, hfin, -⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
    haveI := hfin
    exact constantsAreBase_of_isAlgClosed_of_transcendental x hx
  exact constantsAreBase_down (k := k) hCF φ hφ

end S_AlgebraicCurve_constantsAreBase_of_apply_algebraMap_eq_pow_card
end P2MW
export P2MW.S_AlgebraicCurve_constantsAreBase_of_apply_algebraMap_eq_pow_card (solution)
