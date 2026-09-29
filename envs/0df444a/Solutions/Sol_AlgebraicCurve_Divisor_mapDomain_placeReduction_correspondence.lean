-- Prove2me | solution 1 for AlgebraicCurve.Divisor.mapDomain_placeReduction_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/30e310cc-4a82-50f1-9560-5f27966433f0

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_existsUnique_valuation_sub_lt_one_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
import Theorems.Thm_AlgebraicCurve_Place_ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_mapDomain_placeReduction_correspondence
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Divisor_mapDomain_placeReduction_correspondence.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along isIntegral_along FundamentalIdentityAlong FiniteAlong NormFormulaAlong finrankAlong Divisor.pushforwardAlong Divisor.correspondence Divisor.correspondence_apply Place.ord_restrictAlong Divisor.pushforwardAlong_single Place.fiberAlong Place.mem_fiberAlong Divisor.pullbackAlong_single Place.restrict_toValuationSubring Place.mem_restrict_iff FundamentalIdentity FundamentalIdentity.sum_ramificationIndex_mul_deg Place Place.ext Place.coe_algebraMap Divisor HasPrincipalDivisors IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed IsCurveOver.finiteResidue Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension Place.exists_comap_algebraMap_eq_of_constantFieldExtension Place.exists_of_valuationSubring Place.exists_toValuationSubring_eq_comap_ringHom isCurveOver_of_transcendental_of_isSeparable Place.ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong"
namespace PlaceReductionCorrespondence
p2m_open "AlgebraicCurve"

section General

variable {E L : Type*} [Field E] [Field L] [Algebra E L]

theorem mem_of_valuation_lt_one (P : Place E L) {y : L}
    (hy : P.toValuationSubring.valuation y < 1) : y ∈ P.toValuationSubring :=
  (ValuationSubring.valuation_le_one_iff _ _).mp hy.le

theorem eq_zero_of_valuation_algebraMap_lt_one (P : Place E L) {c : E}
    (hc : P.toValuationSubring.valuation (algebraMap E L c) < 1) : c = 0 := by
  by_contra h
  have hu : IsUnit (algebraMap E P.toValuationSubring c) := (IsUnit.mk0 c h).map _
  have h1 := (ValuationSubring.valuation_eq_one_iff _ _).mp hu
  rw [Place.coe_algebraMap] at h1
  exact hc.ne h1

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [Algebra K E] [Algebra F L]

theorem centre_unique (P : Place E L) {σ τ : F →ₐ[K] E}
    (hσ : ∀ f : F, P.toValuationSubring.valuation (algebraMap F L f - algebraMap E L (σ f)) < 1)
    (hτ : ∀ f : F, P.toValuationSubring.valuation (algebraMap F L f - algebraMap E L (τ f)) < 1) :
    σ = τ := by
  ext f
  have h : P.toValuationSubring.valuation (algebraMap E L (τ f - σ f)) < 1 := by
    have := Valuation.map_sub P.toValuationSubring.valuation
      (algebraMap F L f - algebraMap E L (σ f)) (algebraMap F L f - algebraMap E L (τ f))
    rw [sub_sub_sub_cancel_left, ← map_sub] at this
    exact this.trans_lt (max_lt (hσ f) (hτ f))
  exact (sub_eq_zero.mp (eq_zero_of_valuation_algebraMap_lt_one P h)).symm

theorem algebraMap_mem_of_centred (P : Place E L) {σ : F →ₐ[K] E}
    (hσ : ∀ f : F, P.toValuationSubring.valuation (algebraMap F L f - algebraMap E L (σ f)) < 1)
    (f : F) : algebraMap F L f ∈ P.toValuationSubring := by
  have h := add_mem (mem_of_valuation_lt_one P (hσ f)) (P.algebraMap_mem' (σ f))
  rwa [sub_add_cancel] at h

theorem exists_mem_valuation_sub_lt_one_iff_of_centred (P : Place E L) {σ : F →ₐ[K] E}
    (hσ : ∀ f : F, P.toValuationSubring.valuation (algebraMap F L f - algebraMap E L (σ f)) < 1)
    (A : ValuationSubring E) (f : F) :
    (∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap F L f - algebraMap E L a) < 1) ↔ σ f ∈ A := by
  constructor
  · rintro ⟨a, haA, ha⟩
    have h : P.toValuationSubring.valuation (algebraMap E L (σ f - a)) < 1 := by
      have := Valuation.map_sub P.toValuationSubring.valuation
        (algebraMap F L f - algebraMap E L a) (algebraMap F L f - algebraMap E L (σ f))
      rw [sub_sub_sub_cancel_left, ← map_sub] at this
      exact this.trans_lt (max_lt ha (hσ f))
    rwa [sub_eq_zero.mp (eq_zero_of_valuation_algebraMap_lt_one P h)]
  · intro h
    exact ⟨σ f, h, hσ f⟩

end General

section Transport

theorem valuation_lt_one_iff_inv_not_mem {L : Type*} [Field L] (A : ValuationSubring L) {z : L}
    (hz : z ≠ 0) : A.valuation z < 1 ↔ z⁻¹ ∉ A := by
  rw [← A.valuation_le_one_iff, map_inv₀, inv_le_one₀ ((Valuation.pos_iff _).mpr hz), not_le]

theorem valuation_comap_lt_one_iff {L L' : Type*} [Field L] [Field L'] (A : ValuationSubring L')
    (g : L →+* L') (z : L) :
    (A.comap g).valuation z < 1 ↔ A.valuation (g z) < 1 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [valuation_lt_one_iff_inv_not_mem _ hz,
      valuation_lt_one_iff_inv_not_mem _ (map_ne_zero_iff g g.injective |>.mpr hz),
      ValuationSubring.mem_comap, map_inv₀]

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem valuation_restrictAlong_lt_one_iff (χ : F →ₐ[K] F') (h : χ.toRingHom.IsIntegral)
    [HasPrincipalDivisors K F'] (W : Place K F') (z : F) :
    (W.restrictAlong χ h).toValuationSubring.valuation z < 1 ↔
      W.toValuationSubring.valuation (χ z) < 1 := by
  letI := algebraAlong χ
  haveI := isScalarTower_along χ
  haveI := isIntegral_along χ h
  show (W.restrict F).toValuationSubring.valuation z < 1 ↔ _
  rw [Place.restrict_toValuationSubring]
  exact valuation_comap_lt_one_iff _ _ z

theorem mem_restrictAlong_iff (χ : F →ₐ[K] F') (h : χ.toRingHom.IsIntegral)
    [HasPrincipalDivisors K F'] (W : Place K F') (z : F) :
    z ∈ (W.restrictAlong χ h).toValuationSubring ↔ χ z ∈ W.toValuationSubring := by
  letI := algebraAlong χ
  haveI := isScalarTower_along χ
  haveI := isIntegral_along χ h
  show z ∈ (W.restrict F).toValuationSubring ↔ _
  rw [Place.mem_restrict_iff]
  rfl

theorem comap_ne_top_of_transcendental {L E : Type*} [Field L] [Field E] [Algebra K L]
    [Algebra K E] (A : ValuationSubring E)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (σ : L →ₐ[K] E) {x : L} (hx : Transcendental K x) : A.comap σ.toRingHom ≠ ⊤ := by
  intro htop
  have hall : ∀ y : L, σ y ∈ A := fun y => by
    have hy : y ∈ A.comap σ.toRingHom := by rw [htop]; exact ValuationSubring.mem_top y
    exact hy
  obtain ⟨k, hk⟩ := hArat (σ x) (hall x)
  have hy0 : x - algebraMap K L k ≠ 0 := fun h => hx (by
    rw [sub_eq_zero.mp h]
    exact isAlgebraic_algebraMap k)
  have hval : A.valuation (σ (x - algebraMap K L k)) < 1 := by
    rwa [map_sub, AlgHom.commutes]
  have hσ0 : σ (x - algebraMap K L k) ≠ 0 := (map_ne_zero σ).mpr hy0
  exact (valuation_lt_one_iff_inv_not_mem A hσ0).mp hval (by rw [← map_inv₀]; exact hall _)

end Transport

section NotIntegral

variable {K L E LE : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed K] [IsCurveOver K L]
  [Field E] [Field LE] [Algebra K E] [Algebra E LE] [Algebra L LE] [Algebra K LE]
  [IsScalarTower K E LE] [IsScalarTower K L LE]

theorem exists_mem_valuation_sub_lt_one_iff_of_comap (Q : Place E LE) (q : Place K L)
    (hq : q.toValuationSubring = Q.toValuationSubring.comap (algebraMap L LE))
    (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A) (g : L) :
    (∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap L LE g - algebraMap E LE a) < 1) ↔
      algebraMap L LE g ∈ Q.toValuationSubring := by
  constructor
  · rintro ⟨a, -, ha⟩
    have h := add_mem (mem_of_valuation_lt_one Q ha) (Q.algebraMap_mem' a)
    rwa [sub_add_cancel] at h
  · intro hg
    have hgq : g ∈ q.toValuationSubring := by rw [hq]; exact hg
    haveI : Module.Finite K q.ResidueField := IsCurveOver.finiteResidue q
    haveI : Algebra.IsIntegral K q.ResidueField := Algebra.IsIntegral.of_finite K q.ResidueField
    have hsurj : Function.Surjective (algebraMap K q.ResidueField) :=
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := q.ResidueField)).2
    obtain ⟨k, hk⟩ := hsurj (IsLocalRing.residue _ ⟨g, hgq⟩)
    have hmem : (⟨g, hgq⟩ : q.toValuationSubring) - algebraMap K q.toValuationSubring k ∈
        IsLocalRing.maximalIdeal q.toValuationSubring := by
      rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      change IsLocalRing.residue _ _ = IsLocalRing.residue _ _
      rw [← hk, IsScalarTower.algebraMap_apply K q.toValuationSubring q.ResidueField]
      rfl
    have hlt : q.toValuationSubring.valuation (g - algebraMap K L k) < 1 := by
      have h := (ValuationSubring.valuation_lt_one_iff _ _).mp hmem
      simpa only [AddSubgroupClass.coe_sub, Place.coe_algebraMap] using h
    rw [hq, valuation_comap_lt_one_iff] at hlt
    refine ⟨algebraMap K E k, hKA k, ?_⟩
    rwa [map_sub, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K E LE] at hlt

end NotIntegral

theorem span_eq_top_of_adjoin_eq_top {E L M : Type*} [Field E] [Field L] [Field M] [Algebra E L]
    [Algebra L M] [Algebra E M] [IsScalarTower E L M] {ι : Type*} [Finite ι] (b : ι → M)
    (hmul : ∀ i j, b i * b j ∈ Submodule.span L (Set.range b))
    (h1 : (1 : M) ∈ Submodule.span L (Set.range b))
    {T : Set M} (hT : T ⊆ Submodule.span L (Set.range b))
    (hgen : IntermediateField.adjoin E T = ⊤) : Submodule.span L (Set.range b) = ⊤ := by
  set S := Submodule.span L (Set.range b) with hS
  haveI : FiniteDimensional L S := FiniteDimensional.span_of_finite L (Set.finite_range b)
  have hmul' : ∀ s ∈ S, ∀ s' ∈ S, s * s' ∈ S := by
    refine Submodule.mul_le.mp ?_
    rw [hS, Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact hmul i j
  have hinv : ∀ s ∈ S, s⁻¹ ∈ S := by
    intro s hs
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [inv_zero]; exact S.zero_mem
    let m : S →ₗ[L] S :=
      { toFun := fun y => ⟨s * y, hmul' s hs y y.2⟩
        map_add' := fun y y' => Subtype.ext (mul_add _ _ _)
        map_smul' := fun r y => Subtype.ext (by simp) }
    have hinj : Function.Injective m := fun y y' h =>
      Subtype.ext (mul_left_cancel₀ hs0 (congrArg Subtype.val h))
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨1, h1⟩
    have hy' : s * y = 1 := congrArg Subtype.val hy
    rw [inv_eq_of_mul_eq_one_right hy']
    exact y.2
  let S' : IntermediateField E M :=
    { carrier := S
      mul_mem' := fun ha hb => hmul' _ ha _ hb
      one_mem' := h1
      add_mem' := S.add_mem
      zero_mem' := S.zero_mem
      algebraMap_mem' := fun c => by
        rw [IsScalarTower.algebraMap_apply E L M, Algebra.algebraMap_eq_smul_one]
        exact S.smul_mem _ h1
      inv_mem' := hinv }
  have hle : (⊤ : IntermediateField E M) ≤ S' := by
    rw [← hgen]
    exact IntermediateField.adjoin_le_iff.mpr hT
  exact eq_top_iff.mpr fun y _ => hle (IntermediateField.mem_top (x := y))

section Extend

variable {K F E FE F' F'E : Type*} [Field K] [Field F] [Algebra K F] [Field E] [Field FE]
  [Algebra E FE] [Algebra F FE] [Field F'] [Algebra K F'] [Field F'E] [Algebra E F'E]
  [Algebra F' F'E]

theorem finite_extension (χ : F →ₐ[K] F') (hfin : FiniteAlong K χ) (χE : FE →ₐ[E] F'E)
    (hχE : ∀ f : F, χE (algebraMap F FE f) = algebraMap F' F'E (χ f))
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤) :
    ∃ _ : FiniteAlong E χE, finrankAlong E χE ≤ finrankAlong K χ := by
  classical
  letI iF : Algebra F F' := algebraAlong χ
  haveI : Module.Finite F F' := hfin
  letI iE : Algebra FE F'E := algebraAlong χE
  haveI : IsScalarTower E FE F'E := isScalarTower_along χE
  set n := Module.finrank F F' with hn
  let b := Module.finBasis F F'
  let b' : Fin n → F'E := fun i => algebraMap F' F'E (b i)
  have hT : ∀ y : F', algebraMap F' F'E y ∈ Submodule.span FE (Set.range b') := by
    intro y
    rw [← b.sum_repr y, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def, map_mul]
    have : algebraMap F' F'E (algebraMap F F' (b.repr y i)) =
        algebraMap FE F'E (algebraMap F FE (b.repr y i)) := (hχE _).symm
    rw [this, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span FE (Set.range b') = ⊤ :=
    span_eq_top_of_adjoin_eq_top (E := E) b'
      (fun i j => by simpa only [b', ← map_mul] using hT (b i * b j))
      (by simpa only [map_one] using hT 1)
      (T := Set.range (algebraMap F' F'E)) (by rintro _ ⟨y, rfl⟩; exact hT y) hgen'
  have hfinE : Module.Finite FE F'E :=
    Module.finite_def.mpr (by rw [← hspan]; exact Submodule.fg_span (Set.finite_range b'))
  refine ⟨hfinE, ?_⟩
  have h := finrank_range_le_card (R := FE) b'
  rw [Fintype.card_fin] at h
  change Module.finrank FE (Submodule.span FE (Set.range b')) ≤ n at h
  rwa [hspan, finrank_top] at h

end Extend

section Bookkeeping

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem essFiniteType_of_fg
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Algebra.EssFiniteType K F := by
  obtain ⟨x, -, hfin⟩ := hfg
  have h1 : Algebra.EssFiniteType K (IntermediateField.adjoin K ({x} : Set F)) :=
    IntermediateField.essFiniteType_iff.2
      (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x))
  have h2 : Algebra.EssFiniteType (IntermediateField.adjoin K ({x} : Set F)) F := inferInstance
  exact Algebra.EssFiniteType.comp K (IntermediateField.adjoin K ({x} : Set F)) F

theorem finiteAlong_of_isIntegral [Algebra.EssFiniteType K F'] (χ : F →ₐ[K] F')
    (hχ : χ.toRingHom.IsIntegral) : FiniteAlong K χ := by
  letI : Algebra F F' := algebraAlong χ
  haveI : IsScalarTower K F F' := isScalarTower_along χ
  obtain ⟨s, hs⟩ := IntermediateField.fg_top K F'
  haveI : Finite (s : Set F') := s.finite_toSet.to_subtype
  have hfin : FiniteDimensional F (IntermediateField.adjoin F (s : Set F')) :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (hχ z : IsIntegral F z)
  have htop : IntermediateField.adjoin F (s : Set F') = ⊤ := by
    rw [← IntermediateField.restrictScalars_eq_top_iff (K := K), ← top_le_iff, ← hs]
    exact IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin F _)
  rw [htop] at hfin
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv (F := F) (E := F')).toLinearEquiv

theorem fg_of_finiteAlong (χ : F →ₐ[K] F') (hfin : FiniteAlong K χ) {x : F}
    (hx : Transcendental K x)
    (hfinx : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Transcendental K (χ x) ∧
      FiniteDimensional (IntermediateField.adjoin K ({χ x} : Set F')) F' := by
  have hinj : Function.Injective χ := χ.toRingHom.injective
  refine ⟨fun h => hx ((isAlgebraic_algHom_iff χ hinj).mp h), ?_⟩
  letI : Algebra F F' := algebraAlong χ
  haveI : IsScalarTower K F F' := isScalarTower_along χ
  haveI : Module.Finite F F' := hfin
  let Kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F)
  haveI : FiniteDimensional Kx F := hfinx
  letI : Algebra Kx F' := ((algebraMap F F').comp (algebraMap Kx F)).toAlgebra
  haveI : IsScalarTower Kx F F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite Kx F' := Module.Finite.trans F F'
  let L : IntermediateField K F' := IntermediateField.adjoin K ({χ x} : Set F')
  have hmap : ∀ y ∈ IntermediateField.adjoin K ({x} : Set F), χ y ∈ L := by
    intro y hy
    have h1 : χ y ∈ (IntermediateField.adjoin K ({x} : Set F)).map χ := ⟨y, hy, rfl⟩
    rwa [IntermediateField.adjoin_map, Set.image_singleton] at h1
  have hmem : ∀ c : Kx, χ (c : F) ∈ L := fun c => hmap c c.2
  letI : Algebra Kx L :=
    (((χ : F →+* F').comp (algebraMap Kx F)).codRestrict L fun c => hmem c).toAlgebra
  haveI : IsScalarTower Kx L F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite Kx L F'

end Bookkeeping

section Restrict

variable {E FE F'E : Type*} [Field E] [Field FE] [Algebra E FE] [Field F'E] [Algebra E F'E]

theorem centred_restrictAlong {K F F' : Type*} [Field K] [Field F] [Algebra K F] [Field F']
    [Algebra K F'] [Algebra K E] [Algebra F FE] [Algebra F' F'E]
    [HasPrincipalDivisors E F'E] (χ : F →ₐ[K] F') (χE : FE →ₐ[E] F'E)
    (h : χE.toRingHom.IsIntegral)
    (hχE : ∀ f : F, χE (algebraMap F FE f) = algebraMap F' F'E (χ f))
    {W : Place E F'E} {σ : F' →ₐ[K] E}
    (hW : ∀ y : F', W.toValuationSubring.valuation
      (algebraMap F' F'E y - algebraMap E F'E (σ y)) < 1) (f : F) :
    (W.restrictAlong χE h).toValuationSubring.valuation
      (algebraMap F FE f - algebraMap E FE (σ (χ f))) < 1 := by
  rw [valuation_restrictAlong_lt_one_iff, map_sub, hχE, AlgHom.commutes]
  exact hW (χ f)

theorem inertiaDegAlong_eq_one [IsAlgClosed E] [IsCurveOver E FE] [IsCurveOver E F'E]
    (χE : FE →ₐ[E] F'E) (h : χE.toRingHom.IsIntegral) (W : Place E F'E) :
    W.inertiaDegAlong χE h = 1 := by
  letI := algebraAlong χE
  haveI := isScalarTower_along χE
  haveI := isIntegral_along χE h
  have h1 := W.deg_restrict_mul_inertiaDeg (F := FE)
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed,
    one_mul] at h1
  exact h1

theorem reduction_restrictAlong {K F F' : Type*} [Field K] [Field F] [Algebra K F] [Field F']
    [Algebra K F'] [Algebra K E] [Algebra F FE] [Algebra F' F'E]
    [HasPrincipalDivisors E F'E] [HasPrincipalDivisors K F']
    (χ : F →ₐ[K] F') (hχ : χ.toRingHom.IsIntegral) (χE : FE →ₐ[E] F'E)
    (hχE : χE.toRingHom.IsIntegral)
    (hcomm : ∀ f : F, χE (algebraMap F FE f) = algebraMap F' F'E (χ f))
    (A : ValuationSubring E)
    (r : Place E FE → Place K F)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧ P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1)
    (r' : Place E F'E → Place K F')
    (hr' : ∀ (Q : Place E F'E) (g : F'), g ∈ (r' Q).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap F' F'E g - algebraMap E F'E a) < 1)
    (W : Place E F'E) :
    r (W.restrictAlong χE hχE) = (r' W).restrictAlong χ hχ := by
  refine Place.ext (SetLike.ext fun f => ?_)
  rw [mem_restrictAlong_iff, hr, hr']
  refine exists_congr fun a => and_congr_right fun _ => ?_
  rw [valuation_restrictAlong_lt_one_iff, map_sub, hcomm, AlgHom.commutes]

end Restrict

theorem sum_single_fiberwise {ι κ Pl : Type*} [DecidableEq κ] (S : Finset ι) (T : Finset κ)
    (θ : ι → κ) (g : κ → Pl) (a : ι → ℤ) (b : κ → ℤ) (n : ℤ)
    (hθ : ∀ i ∈ S, θ i ∈ T) (hfib : ∀ k ∈ T, ∑ i ∈ S with θ i = k, a i = b k) :
    ∑ i ∈ S, Finsupp.single (g (θ i)) (n * a i) =
      ∑ k ∈ T, (Finsupp.single (g k) (n * b k) : Pl →₀ ℤ) := by
  rw [← Finset.sum_fiberwise_of_maps_to hθ]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← hfib k hk, Finset.mul_sum, Finsupp.single_finsetSum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

section Reduction

variable {K L E LE : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed K] [CharZero K]
  [IsCurveOver K L]
  [Field E] [Field LE] [Algebra K E] [Algebra E LE] [Algebra L LE] [Algebra K LE]
  [IsScalarTower K E LE] [IsScalarTower K L LE] [IsAlgClosed E] [IsCurveOver E LE]

theorem exists_reduction
    (hfg : ∃ x : L, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set L)) L)
    (hfgE : ∃ x : LE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set LE)) LE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap L LE)) = ⊤)
    (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1) :
    ∃ r : Place E LE → Place K L, ∀ (Q : Place E LE) (g : L), g ∈ (r Q).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap L LE g - algebraMap E LE a) < 1 := by
  classical
  have C1 := Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension
    K L hfg E LE hfgE hgen
  obtain ⟨x, hx, hfinx⟩ := hfg
  haveI := hfinx
  suffices h : ∀ Q : Place E LE, ∃ q : Place K L, ∀ g : L, g ∈ q.toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap L LE g - algebraMap E LE a) < 1 by
    choose r hr using h
    exact ⟨r, hr⟩
  intro Q
  by_cases hint : ∀ g : L, algebraMap L LE g ∈ Q.toValuationSubring
  ·
    obtain ⟨σ, hσ⟩ := C1.2 Q hint
    have hAK : ∀ k : K, algebraMap K L k ∈ A.comap σ.toRingHom := fun k => by
      rw [ValuationSubring.mem_comap]
      change σ (algebraMap K L k) ∈ A
      rw [AlgHom.commutes]
      exact hKA k
    have hne : A.comap σ.toRingHom ≠ ⊤ := comap_ne_top_of_transcendental A hArat σ hx
    obtain ⟨q, hq⟩ := Place.exists_of_valuationSubring x (A.comap σ.toRingHom) hAK hne
    refine ⟨q, fun g => ?_⟩
    rw [hq, ValuationSubring.mem_comap, exists_mem_valuation_sub_lt_one_iff_of_centred Q hσ A g]
    rfl
  ·
    push Not at hint
    obtain ⟨g₀, hg₀⟩ := hint
    have hwK : ∀ k : K, algebraMap L LE (algebraMap K L k) ∈ Q.toValuationSubring := fun k => by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K E LE]
      exact Q.algebraMap_mem' _
    obtain ⟨q, hq⟩ := Place.exists_toValuationSubring_eq_comap_ringHom x (algebraMap L LE)
      Q.toValuationSubring hwK ⟨g₀, hg₀⟩
    refine ⟨q, fun g => ?_⟩
    rw [exists_mem_valuation_sub_lt_one_iff_of_comap Q q hq A hKA g, hq,
      ValuationSubring.mem_comap]

omit [IsAlgClosed E] [IsCurveOver E LE] in

theorem reduction_eq_comap_of_not_forall_mem
    (hfg : ∃ x : L, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set L)) L)
    (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (r : Place E LE → Place K L)
    (hr : ∀ (Q : Place E LE) (g : L), g ∈ (r Q).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap L LE g - algebraMap E LE a) < 1)
    {Q : Place E LE} (hQ : ¬ ∀ g : L, algebraMap L LE g ∈ Q.toValuationSubring) :
    (r Q).toValuationSubring = Q.toValuationSubring.comap (algebraMap L LE) := by
  obtain ⟨x, -, hfinx⟩ := hfg
  haveI := hfinx
  push Not at hQ
  obtain ⟨g₀, hg₀⟩ := hQ
  have hwK : ∀ k : K, algebraMap L LE (algebraMap K L k) ∈ Q.toValuationSubring := fun k => by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K E LE]
    exact Q.algebraMap_mem' _
  obtain ⟨q, hq⟩ := Place.exists_toValuationSubring_eq_comap_ringHom x (algebraMap L LE)
    Q.toValuationSubring hwK ⟨g₀, hg₀⟩
  refine SetLike.ext fun g => ?_
  rw [hr, exists_mem_valuation_sub_lt_one_iff_of_comap Q q hq A hKA g, ValuationSubring.mem_comap]

omit [IsAlgClosed K] [CharZero K] [IsCurveOver K L] [Algebra K LE] [IsScalarTower K E LE]
  [IsScalarTower K L LE] [IsAlgClosed E] [IsCurveOver E LE] in

theorem mem_reduction_iff_of_centred
    (A : ValuationSubring E) (r : Place E LE → Place K L)
    (hr : ∀ (Q : Place E LE) (g : L), g ∈ (r Q).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap L LE g - algebraMap E LE a) < 1)
    {Q : Place E LE} {σ : L →ₐ[K] E}
    (hσ : ∀ g : L, Q.toValuationSubring.valuation (algebraMap L LE g - algebraMap E LE (σ g)) < 1)
    (g : L) : g ∈ (r Q).toValuationSubring ↔ σ g ∈ A := by
  rw [hr, exists_mem_valuation_sub_lt_one_iff_of_centred Q hσ A g]

end Reduction

section Fibre

variable {K F E FE F' F'E : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
  [IsCurveOver K F]
  [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
  [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
  [Field F'] [Algebra K F'] [IsCurveOver K F']
  [Field F'E] [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
  [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E]

theorem fibre_centred
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hfg' : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F')
    (hfgE' : ∃ x : F'E, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (χ : F →ₐ[K] F') (hfin : FiniteAlong K χ)
    (χE : FE →ₐ[E] F'E) (hχEi : χE.toRingHom.IsIntegral)
    (hχE : ∀ f : F, χE (algebraMap F FE f) = algebraMap F' F'E (χ f))
    (hFI : FundamentalIdentityAlong E χE hχEi)
    {P : Place E FE} {e : F →ₐ[K] E}
    (hP : ∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) :
    (∀ W ∈ Place.fiberAlong χE hχEi P, W.ramificationIndexAlong χE = 1) ∧
    (∀ W ∈ Place.fiberAlong χE hχEi P, ∃ σ : F' →ₐ[K] E, σ.comp χ = e ∧
      ∀ y : F', W.toValuationSubring.valuation
        (algebraMap F' F'E y - algebraMap E F'E (σ y)) < 1) ∧
    (∀ (σ : F' →ₐ[K] E) (W : Place E F'E), σ.comp χ = e →
      (∀ y : F', W.toValuationSubring.valuation
        (algebraMap F' F'E y - algebraMap E F'E (σ y)) < 1) →
      W ∈ Place.fiberAlong χE hχEi P) ∧
    {σ : F' →ₐ[K] E | σ.comp χ = e}.Finite := by
  classical
  have C1F := Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension
    K F hfg E FE hfgE hgen
  have C1F' := Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension
    K F' hfg' E F'E hfgE' hgen'

  have huF : ∀ (Q : Place E FE), (∀ f : F, Q.toValuationSubring.valuation
      (algebraMap F FE f - algebraMap E FE (e f)) < 1) → Q = P := fun Q hQ => by
    obtain ⟨R, -, hR⟩ := C1F.1 e
    exact (hR Q hQ).trans (hR P hP).symm

  choose Qc hQc hQu using C1F'.1

  have hc : ∀ (σ : F' →ₐ[K] E) (W : Place E F'E), σ.comp χ = e →
      (∀ y : F', W.toValuationSubring.valuation
        (algebraMap F' F'E y - algebraMap E F'E (σ y)) < 1) →
      W ∈ Place.fiberAlong χE hχEi P := by
    intro σ W hσ hW
    rw [Place.mem_fiberAlong]
    refine huF _ fun f => ?_
    have h := centred_restrictAlong χ χE hχEi hχE hW f
    rwa [← AlgHom.comp_apply, hσ] at h

  have hinj : Function.Injective Qc := fun σ τ h =>
    centre_unique (Qc σ) (hQc σ) (fun y => by rw [h]; exact hQc τ y)

  letI iF : Algebra F F' := algebraAlong χ
  haveI : IsScalarTower K F F' := isScalarTower_along χ
  haveI : Module.Finite F F' := hfin

  letI iE : Algebra F E := e.toRingHom.toAlgebra
  haveI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun k => (e.commutes k).symm
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  haveI : Algebra.IsSeparable F F' := Algebra.IsSeparable.of_integral F F'
  have hcard : Fintype.card (F' →ₐ[F] E) = finrankAlong K χ := AlgHom.card F F' E
  let T : Finset (F' →ₐ[K] E) := Finset.univ.image fun σ' : F' →ₐ[F] E => σ'.restrictScalars K
  have hTmem : ∀ σ, σ ∈ T ↔ σ.comp χ = e := by
    intro σ
    constructor
    · intro hσ
      obtain ⟨σ', -, rfl⟩ := Finset.mem_image.mp hσ
      ext f
      exact σ'.commutes f
    · intro hσ
      refine Finset.mem_image.mpr ⟨⟨σ.toRingHom, fun f => ?_⟩, Finset.mem_univ _, ?_⟩
      · exact AlgHom.congr_fun hσ f
      · ext y; rfl
  have hTcard : T.card = finrankAlong K χ := by
    rw [Finset.card_image_of_injective _ (AlgHom.restrictScalars_injective K), Finset.card_univ,
      hcard]
  have hSfin : {σ : F' →ₐ[K] E | σ.comp χ = e}.Finite :=
    T.finite_toSet.subset fun σ hσ => Finset.mem_coe.mpr ((hTmem σ).mpr hσ)

  set Z := Place.fiberAlong χE hχEi P with hZ
  have hsum : ∑ W ∈ Z, (W.ramificationIndexAlong χE : ℤ) = (finrankAlong E χE : ℤ) := by
    letI := algebraAlong χE
    haveI := isScalarTower_along χE
    haveI := isIntegral_along χE hχEi
    haveI : FundamentalIdentity E FE F'E := hFI
    have h := FundamentalIdentity.sum_ramificationIndex_mul_deg (K := E) (F := FE) (F' := F'E) P
    simp only [IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one] at h
    exact h
  have hpos : ∀ W ∈ Z, 1 ≤ W.ramificationIndexAlong χE := fun W _ => by
    letI := algebraAlong χE
    haveI := isScalarTower_along χE
    haveI := isIntegral_along χE hχEi
    exact W.ramificationIndex_pos (F := FE)
  obtain ⟨-, hle⟩ := finite_extension χ hfin χE hχE hgen'

  have hsub : T.image Qc ⊆ Z := by
    intro W hW
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hW
    exact hc σ _ ((hTmem σ).mp hσ) (hQc σ)
  have hTZ : T.card ≤ Z.card := by
    rw [← Finset.card_image_of_injective T hinj]
    exact Finset.card_le_card hsub

  have hZsum : (Z.card : ℤ) ≤ ∑ W ∈ Z, (W.ramificationIndexAlong χE : ℤ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    exact Finset.sum_le_sum fun W hW => by exact_mod_cast hpos W hW
  have hsumZ : ∑ W ∈ Z, (W.ramificationIndexAlong χE : ℤ) ≤ (Z.card : ℤ) := by
    rw [hsum]
    calc (finrankAlong E χE : ℤ) ≤ finrankAlong K χ := by exact_mod_cast hle
      _ = T.card := by rw [hTcard]
      _ ≤ Z.card := by exact_mod_cast hTZ

  have ha : ∀ W ∈ Z, W.ramificationIndexAlong χE = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨W₀, hW₀, hne⟩ := hcon
    have hlt : (Z.card : ℤ) < ∑ W ∈ Z, (W.ramificationIndexAlong χE : ℤ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_lt_sum (fun W hW => by exact_mod_cast hpos W hW) ⟨W₀, hW₀, ?_⟩
      have h1 := hpos W₀ hW₀
      have h2 : 1 < W₀.ramificationIndexAlong χE := lt_of_le_of_ne h1 (Ne.symm hne)
      exact_mod_cast h2
    omega

  have himg : T.image Qc = Z := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [Finset.card_image_of_injective T hinj]
    have : (Z.card : ℤ) ≤ T.card := by rw [hTcard]; exact hZsum.trans (hsum ▸ by exact_mod_cast hle)
    exact_mod_cast this

  have hb : ∀ W ∈ Z, ∃ σ : F' →ₐ[K] E, σ.comp χ = e ∧
      ∀ y : F', W.toValuationSubring.valuation
        (algebraMap F' F'E y - algebraMap E F'E (σ y)) < 1 := by
    intro W hW
    rw [← himg] at hW
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hW
    exact ⟨σ, (hTmem σ).mp hσ, hQc σ⟩
  exact ⟨ha, hb, hc, hSfin⟩

theorem fibre_identity_of_forall_mem
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hfg' : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F')
    (hfgE' : ∃ x : F'E, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfinφ : FiniteAlong K φ)
    (φE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hFIE : FundamentalIdentityAlong E φE hφE)
    (A : ValuationSubring E)
    (r : Place E FE → Place K F)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧ P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1)
    (r' : Place E F'E → Place K F')
    (hr' : ∀ (Q : Place E F'E) (g : F'), g ∈ (r' Q).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap F' F'E g - algebraMap E F'E a) < 1)
    {P : Place E FE} (hint : ∀ f : F, algebraMap F FE f ∈ P.toValuationSubring)
    {q : Place K F'} (hq : q ∈ Place.fiberAlong φ hφ (r P)) [DecidableEq (Place K F')] :
    ∑ W ∈ (Place.fiberAlong φE hφE P).filter (fun W => r' W = q),
        (W.ramificationIndexAlong φE : ℤ) = q.ramificationIndexAlong φ := by

  obtain ⟨e, hP⟩ := (Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension
    K F hfg E FE hfgE hgen).2 P hint
  have C1F' := Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension
    K F' hfg' E F'E hfgE' hgen'
  choose Qc hQc hQu using C1F'.1
  obtain ⟨ha, hb, hc, hSfin⟩ :=
    fibre_centred hfg hfgE hgen hfg' hfgE' hgen' φ hfinφ φE hφE hφcomm hFIE hP

  have hev₀ : ∀ f : F, f ∈ (r P).toValuationSubring ↔ e f ∈ A := fun f =>
    mem_reduction_iff_of_centred A r hr hP f

  have hcount := Place.ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong K F F' hfg φ hφ
    hfinφ E A e (r P) hev₀ q (Place.mem_fiberAlong.mp hq)
  set Sq : Set (F' →ₐ[K] E) := {σ | σ.comp φ = e ∧
    ∀ g : F', g ∈ q.toValuationSubring ↔ σ g ∈ A} with hSq

  have hinj : Function.Injective Qc := fun σ τ h =>
    centre_unique (Qc σ) (hQc σ) (fun y => by rw [h]; exact hQc τ y)
  have himage : (((Place.fiberAlong φE hφE P).filter (fun W => r' W = q) : Finset (Place E F'E)) :
      Set (Place E F'E)) = Qc '' Sq := by
    ext W
    rw [Finset.coe_filter, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hW, hWq⟩
      obtain ⟨σ, hσ, hWσ⟩ := hb W hW
      refine ⟨σ, ⟨hσ, fun g => ?_⟩, (hQu σ W hWσ).symm⟩
      rw [← hWq]
      exact mem_reduction_iff_of_centred A r' hr' hWσ g
    · rintro ⟨σ, ⟨hσ, hσq⟩, rfl⟩
      refine ⟨hc σ _ hσ (hQc σ), Place.ext (SetLike.ext fun g => ?_)⟩
      rw [mem_reduction_iff_of_centred A r' hr' (hQc σ) g, hσq g]

  have hone : ∀ W ∈ (Place.fiberAlong φE hφE P).filter (fun W => r' W = q),
      (W.ramificationIndexAlong φE : ℤ) = 1 := fun W hW => by
    rw [ha W (Finset.mem_filter.mp hW).1, Nat.cast_one]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one, ← hcount,
    ← Set.ncard_coe_finset, himage, Set.ncard_image_of_injective _ hinj]

omit [CharZero K] [IsAlgClosed K] [IsCurveOver K F] [Algebra K E] [Algebra K FE] [IsScalarTower K E FE]
  [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE] [IsCurveOver K F'] [Algebra K F'E]
  [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E] in

theorem ramificationIndexAlong_eq_of_ord_eq [HasPrincipalDivisors K F']
    [HasPrincipalDivisors E F'E]
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (φE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    {P : Place E FE} {v₀ : Place K F} (hPord : ∀ f : F, P.ord (algebraMap F FE f) = v₀.ord f)
    {q : Place K F'} (hq : q.restrictAlong φ hφ = v₀)
    {W : Place E F'E} (hWord : ∀ g : F', W.ord (algebraMap F' F'E g) = q.ord g)
    (hWP : W.restrictAlong φE hφE = P) :
    W.ramificationIndexAlong φE = q.ramificationIndexAlong φ := by

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v₀.toValuationSubring
  have hg : v₀.ord (π : F) = 1 := v₀.ord_coe_irreducible hπ
  have h1 : q.ord (φ π) = q.ramificationIndexAlong φ := by
    rw [Place.ord_restrictAlong φ hφ, hq, hg, mul_one]
  have h2 : W.ord (φE (algebraMap F FE π)) = W.ramificationIndexAlong φE := by
    rw [Place.ord_restrictAlong φE hφE, hWP, hPord, hg, mul_one]
  have h3 : (W.ramificationIndexAlong φE : ℤ) = q.ramificationIndexAlong φ := by
    rw [← h1, ← h2, hφcomm, hWord]
  exact_mod_cast h3

omit [IsAlgClosed E] [IsCurveOver E FE] in

theorem fibre_identity_of_not_forall_mem
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hfg' : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F')
    (hfgE' : ∃ x : F'E, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (φE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (r : Place E FE → Place K F)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧ P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1)
    (r' : Place E F'E → Place K F')
    (hr' : ∀ (Q : Place E F'E) (g : F'), g ∈ (r' Q).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap F' F'E g - algebraMap E F'E a) < 1)
    {P : Place E FE} (hint : ¬ ∀ f : F, algebraMap F FE f ∈ P.toValuationSubring)
    {q : Place K F'} (hq : q ∈ Place.fiberAlong φ hφ (r P)) [DecidableEq (Place K F')] :
    ∑ W ∈ (Place.fiberAlong φE hφE P).filter (fun W => r' W = q),
        (W.ramificationIndexAlong φE : ℤ) = q.ramificationIndexAlong φ := by

  have hrP : (r P).toValuationSubring = P.toValuationSubring.comap (algebraMap F FE) :=
    reduction_eq_comap_of_not_forall_mem hfg A hKA r hr hint
  obtain ⟨P', -, hP'ord, hP'u⟩ :=
    Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F E FE hfg hfgE hgen (r P)
  have hPP' : P = P' := hP'u P hrP.symm
  have hPord : ∀ f : F, P.ord (algebraMap F FE f) = (r P).ord f := fun f => by
    rw [← hP'ord f, hPP']

  obtain ⟨Wq, hWq, hWqord, hWqu⟩ :=
    Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F' E F'E hfg' hfgE' hgen' q
  have hqv : q.restrictAlong φ hφ = r P := Place.mem_fiberAlong.mp hq

  have hWqP : Wq.restrictAlong φE hφE = P := by
    rw [hPP']
    refine hP'u _ (SetLike.ext fun f => ?_)
    rw [ValuationSubring.mem_comap, mem_restrictAlong_iff, hφcomm, ← hqv, mem_restrictAlong_iff,
      ← hWq, ValuationSubring.mem_comap]

  have hrWq : r' Wq = q := by
    refine Place.ext (SetLike.ext fun g => ?_)
    rw [hr', exists_mem_valuation_sub_lt_one_iff_of_comap Wq q hWq.symm A hKA g, ← hWq,
      ValuationSubring.mem_comap]

  obtain ⟨f₀, hf₀⟩ : ∃ f : F, algebraMap F FE f ∉ P.toValuationSubring := by
    push Not at hint
    exact hint
  have huniq : ∀ W ∈ (Place.fiberAlong φE hφE P).filter (fun W => r' W = q), W = Wq := by
    intro W hW
    obtain ⟨hWZ, hWq'⟩ := Finset.mem_filter.mp hW
    have hWP : W.restrictAlong φE hφE = P := Place.mem_fiberAlong.mp hWZ

    have hWint : ¬ ∀ g : F', algebraMap F' F'E g ∈ W.toValuationSubring := fun h => hf₀ (by
      rw [← hWP, mem_restrictAlong_iff, hφcomm]
      exact h (φ f₀))
    have hW' : (r' W).toValuationSubring = W.toValuationSubring.comap (algebraMap F' F'E) :=
      reduction_eq_comap_of_not_forall_mem hfg' A hKA r' hr' hWint
    rw [hWq'] at hW'
    exact hWqu W hW'.symm

  have he : Wq.ramificationIndexAlong φE = q.ramificationIndexAlong φ :=
    ramificationIndexAlong_eq_of_ord_eq φ hφ φE hφE hφcomm hPord hqv hWqord hWqP

  have hmem : Wq ∈ (Place.fiberAlong φE hφE P).filter (fun W => r' W = q) :=
    Finset.mem_filter.mpr ⟨Place.mem_fiberAlong.mpr hWqP, hrWq⟩
  have hsingle : (Place.fiberAlong φE hφE P).filter (fun W => r' W = q) = {Wq} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem, huniq⟩
  rw [hsingle, Finset.sum_singleton, he]

theorem mapDomain_correspondence_single
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hfg' : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F')
    (hfgE' : ∃ x : F'E, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfinφ : FiniteAlong K φ)
    (φE ψE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral) (hψE : ψE.toRingHom.IsIntegral)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hψcomm : ∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f))
    (hFIE : FundamentalIdentityAlong E φE hφE)
    (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (r : Place E FE → Place K F)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧ P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1)
    (r' : Place E F'E → Place K F')
    (hr' : ∀ (Q : Place E F'E) (g : F'), g ∈ (r' Q).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap F' F'E g - algebraMap E F'E a) < 1)
    (P : Place E FE) (n : ℤ) :
    Finsupp.mapDomain r (Divisor.correspondence φE ψE hφE hψE (Finsupp.single P n)) =
      Divisor.correspondence φ ψ hφ hψ (Finsupp.mapDomain r (Finsupp.single P n)) := by
  classical

  have hR : ∀ q ∈ Place.fiberAlong φ hφ (r P),
      Divisor.pushforwardAlong ψ hψ (Finsupp.single q (n * (q.ramificationIndexAlong φ : ℤ))) =
        Finsupp.single (q.restrictAlong ψ hψ) (n * (q.ramificationIndexAlong φ : ℤ)) := by
    intro q _
    rw [Divisor.pushforwardAlong_single, inertiaDegAlong_eq_one, Nat.cast_one, mul_one]
  have hRHS : Divisor.correspondence φ ψ hφ hψ (Finsupp.mapDomain r (Finsupp.single P n)) =
      ∑ q ∈ Place.fiberAlong φ hφ (r P),
        Finsupp.single (q.restrictAlong ψ hψ) (n * (q.ramificationIndexAlong φ : ℤ)) := by
    rw [Finsupp.mapDomain_single, Divisor.correspondence_apply, Divisor.pullbackAlong_single,
      map_sum]
    exact Finset.sum_congr rfl hR

  have hL : ∀ W ∈ Place.fiberAlong φE hφE P,
      Finsupp.mapDomain r (Divisor.pushforwardAlong ψE hψE
        (Finsupp.single W (n * (W.ramificationIndexAlong φE : ℤ)))) =
        Finsupp.single ((r' W).restrictAlong ψ hψ) (n * (W.ramificationIndexAlong φE : ℤ)) := by
    intro W _
    rw [Divisor.pushforwardAlong_single, inertiaDegAlong_eq_one, Nat.cast_one, mul_one,
      Finsupp.mapDomain_single, reduction_restrictAlong ψ hψ ψE hψE hψcomm A r hr r' hr' W]
  have hLHS : Finsupp.mapDomain r (Divisor.correspondence φE ψE hφE hψE (Finsupp.single P n)) =
      ∑ W ∈ Place.fiberAlong φE hφE P,
        Finsupp.single ((r' W).restrictAlong ψ hψ) (n * (W.ramificationIndexAlong φE : ℤ)) := by
    rw [Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum,
      Finsupp.mapDomain_finsetSum]
    exact Finset.sum_congr rfl hL
  rw [hLHS, hRHS]

  refine sum_single_fiberwise (Place.fiberAlong φE hφE P) (Place.fiberAlong φ hφ (r P)) r'
    (fun q => q.restrictAlong ψ hψ) (fun W => (W.ramificationIndexAlong φE : ℤ))
    (fun q => (q.ramificationIndexAlong φ : ℤ)) n (fun W hW => ?_) (fun q hq => ?_)
  ·
    rw [Place.mem_fiberAlong, ← reduction_restrictAlong φ hφ φE hφE hφcomm A r hr r' hr' W,
      Place.mem_fiberAlong.mp hW]
  ·
    by_cases hint : ∀ f : F, algebraMap F FE f ∈ P.toValuationSubring
    · exact fibre_identity_of_forall_mem hfg hfgE hgen hfg' hfgE' hgen' φ hφ hfinφ φE hφE
        hφcomm hFIE A r hr r' hr' hint hq
    · exact fibre_identity_of_not_forall_mem hfg hfgE hgen hfg' hfgE' hgen' φ hφ φE hφE hφcomm
        A hKA r hr r' hr' hint hq

end Fibre

end AlgebraicCurve.PlaceReductionCorrespondence

open AlgebraicCurve.PlaceReductionCorrespondence in
theorem solution
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (F' : Type*) [Field F'] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ)
    (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (F'E : Type*) [Field F'E] [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
    [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E]
    (hfgE' : ∃ x' : F'E, Transcendental E x' ∧
      FiniteDimensional (IntermediateField.adjoin E ({x'} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φE ψE : FE →ₐ[E] F'E)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hψcomm : ∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f))
    (hφE : φE.toRingHom.IsIntegral) (hψE : ψE.toRingHom.IsIntegral)
    (hFIE : FundamentalIdentityAlong E φE hφE)
    (hfinE : FiniteAlong E ψE) (hNE : NormFormulaAlong E ψE hfinE)
    (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (r : Place E FE → Place K F)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧ P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1)
    (D : Divisor E FE) :
    Finsupp.mapDomain r (Divisor.correspondence φE ψE hφE hψE D) =
      Divisor.correspondence φ ψ hφ hψ (Finsupp.mapDomain r D) := by
  classical

  have _hN := hN
  have _hNE := hNE
  clear _hN _hNE
  obtain ⟨x, hx, hfinx⟩ := id hfg

  have hroof := fg_of_finiteAlong ψ hfin hx hfinx
  have hfg' : ∃ x' : F', Transcendental K x' ∧
      FiniteDimensional (IntermediateField.adjoin K ({x'} : Set F')) F' :=
    ⟨ψ x, hroof.1, hroof.2⟩
  haveI : CharZero F' := charZero_of_injective_algebraMap (algebraMap K F').injective
  haveI hCF' : IsCurveOver K F' := by
    haveI := hroof.2
    haveI : Algebra.IsSeparable (IntermediateField.adjoin K ({ψ x} : Set F')) F' :=
      Algebra.IsSeparable.of_integral _ _
    exact isCurveOver_of_transcendental_of_isSeparable K F' (ψ x) hroof.1 hroof.2 inferInstance
  haveI : Algebra.EssFiniteType K F' := essFiniteType_of_fg hfg'
  have hfinφ : FiniteAlong K φ := finiteAlong_of_isIntegral φ hφ

  obtain ⟨r', hr'⟩ := exists_reduction (K := K) (L := F') (E := E) (LE := F'E)
    hfg' hfgE' hgen' A hKA hArat

  suffices h : (Finsupp.mapDomain.addMonoidHom r).comp
      (Divisor.correspondence φE ψE hφE hψE) =
      (Divisor.correspondence φ ψ hφ hψ).comp (Finsupp.mapDomain.addMonoidHom r) from
    DFunLike.congr_fun h D
  refine Finsupp.addHom_ext fun P n => ?_
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.mapDomain.addMonoidHom_apply]
  exact mapDomain_correspondence_single hfg hfgE hgen hfg' hfgE' hgen' φ ψ hφ hψ hfinφ φE ψE
    hφE hψE hφcomm hψcomm hFIE A hKA r hr r' hr' P n

end S_AlgebraicCurve_Divisor_mapDomain_placeReduction_correspondence
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_mapDomain_placeReduction_correspondence (solution)
