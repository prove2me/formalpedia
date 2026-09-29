-- Prove2me | solution 1 for AlgebraicCurve.algHom_eq_of_forall_restrictAlong_eq_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/2a006614-e230-5c27-b318-7e424c04ef59

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_sub_algebraMap_pos_of_transcendental
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Theorems.Thm_AlgebraicCurve_Place_exists_sub_algebraMap_mem_nonunits_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_algHom_eq_of_forall_restrictAlong_eq_of_charZero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

open AlgebraicCurve
open scoped IntermediateField

namespace RigidEmb

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem ord_pos_of_mem_nonunits (v : Place K F) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring.nonunits) : 0 < v.ord f := by
  have hmem : f ∈ v.toValuationSubring := v.toValuationSubring.nonunits_subset hf
  have h0 : 0 ≤ v.ord f := ord_nonneg_of_mem v hmem
  by_contra hle
  have hz : v.ord f = 0 := by omega
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    mem_of_ord_nonneg v (inv_ne_zero hf0) (by rw [v.ord_inv, hz, neg_zero])
  have hunit : IsUnit (⟨f, hmem⟩ : v.toValuationSubring) :=
    ⟨⟨⟨f, hmem⟩, ⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf0), Subtype.ext (inv_mul_cancel₀ hf0)⟩, rfl⟩
  have hmax : (⟨f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
    ValuationSubring.coe_mem_nonunits_iff.mp hf
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmax)) hunit

theorem ord_algebraMap (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hmem : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hinv : algebraMap K F c⁻¹ ∈ v.toValuationSubring := v.algebraMap_mem' c⁻¹
  let u : v.toValuationSubringˣ :=
    ⟨⟨_, hmem⟩, ⟨_, hinv⟩, Subtype.ext (by simp [hc]), Subtype.ext (by simp [hc])⟩
  exact v.ord_coe_unit u

theorem ord_sub_pos (v : Place K F) {f g : F} (hf0 : f ≠ 0) (hg0 : g ≠ 0) (hfg : f - g ≠ 0)
    (hf : 0 < v.ord f) (hg : 0 < v.ord g) : 0 < v.ord (f - g) := by
  have h := AlgebraicCurve.Place.min_ord_le_ord_add v hf0 (neg_ne_zero.mpr hg0) (by rwa [← sub_eq_add_neg])
  rw [AlgebraicCurve.Place.ord_neg, ← sub_eq_add_neg] at h
  exact lt_of_lt_of_le (lt_min hf hg) h

theorem transcendental_of_not_mem_range [IsAlgClosed K] {x : F} (hx : x ∉ (algebraMap K F).range) :
    Transcendental K x := by
  intro halg
  have hint : IsIntegral K x := halg.isIntegral
  have h1 : (minpoly K x).degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
  exact hx (minpoly.mem_range_of_degree_eq_one K x h1)

theorem infinite_place [IsAlgClosed K] [CharZero K] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    {t : F} (ht : Transcendental K t) : Infinite (Place K F) := by
  haveI := AlgebraicCurve.IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType (K := K) ht
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  haveI : Algebra.IsSeparable K⟮t⟯ F := inferInstance
  classical
  choose g hg using fun c : K => AlgebraicCurve.Place.exists_ord_sub_algebraMap_pos_of_transcendental t ht c
  refine Infinite.of_injective g fun c c' hcc' => ?_
  by_contra hne
  have h1 : 0 < (g c).ord (t - algebraMap K F c) := hg c
  have h2 : 0 < (g c).ord (t - algebraMap K F c') := hcc' ▸ hg c'
  have h10 : t - algebraMap K F c ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at h1; exact lt_irrefl _ h1
  have h20 : t - algebraMap K F c' ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at h2; exact lt_irrefl _ h2
  have hsub : (t - algebraMap K F c) - (t - algebraMap K F c') = algebraMap K F (c' - c) := by
    rw [map_sub]; ring
  have hne' : (t - algebraMap K F c) - (t - algebraMap K F c') ≠ 0 := by
    rw [hsub]; intro h0
    exact hne (((algebraMap K F).injective (by rw [h0, map_zero] : algebraMap K F (c' - c) = algebraMap K F 0) |> sub_eq_zero.mp)).symm
  have := ord_sub_pos (g c) h10 h20 hne' h1 h2
  rw [hsub, ord_algebraMap] at this
  exact lt_irrefl _ this

theorem ramificationIndexAlong_pos {F' : Type*} [Field F'] [Algebra K F'] (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (w : Place K F') : 0 < Place.ramificationIndexAlong φ w := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.ramificationIndex_pos (F := F)

end RigidEmb

open RigidEmb in
theorem solution
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    (F₀ F₁ : Type) [Field F₀] [Field F₁] [Algebra K F₀] [Algebra K F₁]
    [IsCurveOver K F₀] [Algebra.EssFiniteType K F₀] [IsCurveOver K F₁] [Algebra.EssFiniteType K F₁]
    (φ₁ φ₂ : F₀ →ₐ[K] F₁) (h₁ : φ₁.IsIntegral) (h₂ : φ₂.IsIntegral)
    (h : ∀ w : Place K F₁, w.restrictAlong φ₁ h₁ = w.restrictAlong φ₂ h₂) :
    φ₁ = φ₂ := by
  classical
  by_contra hne
  obtain ⟨f, hf⟩ : ∃ f : F₀, φ₁ f ≠ φ₂ f := by
    by_contra hall; push Not at hall; exact hne (AlgHom.ext hall)
  set d : F₁ := φ₁ f - φ₂ f with hd
  have hd0 : d ≠ 0 := sub_ne_zero.mpr hf
  have hf0 : f ≠ 0 := by rintro rfl; exact hf (by simp)
  have hφf0 : φ₁ f ≠ 0 := by simpa using hf0
  haveI : HasPrincipalDivisors K F₁ := IsCurveOver.hasPrincipalDivisors
  obtain ⟨Dd, hDd, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) d hd0
  obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (φ₁ f) hφf0
  have key : ∀ w : Place K F₁, w ∈ Dd.support ∪ Df.support := by
    intro w
    by_cases hw : φ₁ f ∈ w.toValuationSubring
    · apply Finset.mem_union_left
      rw [Finsupp.mem_support_iff, hDd]
      set v : Place K F₀ := w.restrictAlong φ₁ h₁ with hv
      have hv₂ : v = w.restrictAlong φ₂ h₂ := h w
      have hfv : f ∈ v.toValuationSubring := hw
      obtain ⟨c, hc⟩ := AlgebraicCurve.Place.exists_sub_algebraMap_mem_nonunits_of_isAlgClosed v f hfv
      have hfc : f - algebraMap K F₀ c ≠ 0 := by
        intro h0
        apply hf
        rw [sub_eq_zero.mp h0, AlgHom.commutes, AlgHom.commutes]
      have hpos : 0 < v.ord (f - algebraMap K F₀ c) := ord_pos_of_mem_nonunits v hfc hc
      have hord₁ : 0 < w.ord (φ₁ f - algebraMap K F₁ c) := by
        have e := Place.ord_restrictAlong φ₁ h₁ w (f - algebraMap K F₀ c)
        rw [map_sub, AlgHom.commutes] at e
        rw [e]
        exact mul_pos (Int.natCast_pos.mpr (ramificationIndexAlong_pos φ₁ h₁ w)) hpos
      have hord₂ : 0 < w.ord (φ₂ f - algebraMap K F₁ c) := by
        have e := Place.ord_restrictAlong φ₂ h₂ w (f - algebraMap K F₀ c)
        rw [map_sub, AlgHom.commutes, ← hv₂] at e
        rw [e]
        exact mul_pos (Int.natCast_pos.mpr (ramificationIndexAlong_pos φ₂ h₂ w)) hpos
      have hne₁ : φ₁ f - algebraMap K F₁ c ≠ 0 := by
        intro h0; rw [h0, Place.ord_zero] at hord₁; exact lt_irrefl _ hord₁
      have hne₂ : φ₂ f - algebraMap K F₁ c ≠ 0 := by
        intro h0; rw [h0, Place.ord_zero] at hord₂; exact lt_irrefl _ hord₂
      have hdd : d = (φ₁ f - algebraMap K F₁ c) - (φ₂ f - algebraMap K F₁ c) := by rw [hd]; ring
      have hpos' := ord_sub_pos w hne₁ hne₂ (hdd ▸ hd0) hord₁ hord₂
      rw [← hdd] at hpos'
      exact hpos'.ne'
    · apply Finset.mem_union_right
      rw [Finsupp.mem_support_iff, hDf]
      intro h0
      exact hw (mem_of_ord_nonneg w hφf0 (le_of_eq h0.symm))
  have hfin : Finite (Place K F₁) := by
    have hsub : (Set.univ : Set (Place K F₁)) ⊆ ↑(Dd.support ∪ Df.support) := fun w _ => key w
    exact Set.finite_univ_iff.mp ((Finset.finite_toSet _).subset hsub)

  have hfK : f ∉ (algebraMap K F₀).range := by
    rintro ⟨c, rfl⟩; exact hf (by rw [AlgHom.commutes, AlgHom.commutes])
  have htf : Transcendental K f := transcendental_of_not_mem_range hfK
  have ht : Transcendental K (φ₁ f) := by
    intro halg; apply htf
    exact (isAlgebraic_algHom_iff φ₁ φ₁.toRingHom.injective).mp halg
  exact (not_finite_iff_infinite.mpr (RigidEmb.infinite_place (K := K) (F := F₁) ht)) hfin

end S_AlgebraicCurve_algHom_eq_of_forall_restrictAlong_eq_of_charZero
end P2MW
export P2MW.S_AlgebraicCurve_algHom_eq_of_forall_restrictAlong_eq_of_charZero (solution)
