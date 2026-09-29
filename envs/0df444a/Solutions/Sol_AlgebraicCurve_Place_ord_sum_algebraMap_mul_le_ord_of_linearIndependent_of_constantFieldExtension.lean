-- Prove2me | solution 1 for AlgebraicCurve.Place.ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d6f09882-448e-5b92-9c54-27289f65783c

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option maxHeartbeats 4800000

open AlgebraicCurve IsLocalRing

namespace W7XChildL

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_digit [IsAlgClosed K] (v : Place K F) [Module.Finite K v.ResidueField]
    {π : v.toValuationSubring} (hπ : Irreducible π) (o : v.toValuationSubring) :
    ∃ a : K, ∃ o' : v.toValuationSubring, o = algebraMap K v.toValuationSubring a + π * o' := by
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K _
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨a, ha⟩ := hbij.2 (IsLocalRing.residue v.toValuationSubring o)
  have hmem : o - algebraMap K v.toValuationSubring a ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← ha,
      IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq]
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
  obtain ⟨b, hb⟩ := hmem
  exact ⟨a, b, by rw [mul_comm, hb]; ring⟩

end W7XChildL

open W7XChildL

theorem solution
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (v : Place K F) {ι : Type*} (B : ι → K') (hB : LinearIndependent K B)
    (g : ι →₀ F) (hg : g ≠ 0) :
    (∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j)) ≠ 0 ∧
    ∀ j ∈ g.support,
      (lift v).ord (∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j)) ≤
        v.ord (g j) := by
  classical
  set Tot := ∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j) with hTot
  have hsne : g.support.Nonempty := Finsupp.support_nonempty_iff.mpr hg
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  obtain ⟨j₁, hj₁, hj₁m⟩ := g.support.exists_mem_eq_inf' hsne (fun j => v.ord (g j))
  set m := g.support.inf' hsne (fun j => v.ord (g j)) with hm
  have hmle : ∀ j ∈ g.support, m ≤ v.ord (g j) := fun j hj => Finset.inf'_le _ hj
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hπord : v.ord (π : F) = 1 := v.ord_coe_irreducible hπ
  have hgj0 : ∀ j ∈ g.support, g j ≠ 0 := fun j hj => Finsupp.mem_support_iff.mp hj
  have haj_ne : ∀ j ∈ g.support, (π : F)^(-m) * g j ≠ 0 := fun j hj =>
    mul_ne_zero (zpow_ne_zero _ hπ0) (hgj0 j hj)
  have haj_ord : ∀ j ∈ g.support, v.ord ((π : F)^(-m) * g j) = v.ord (g j) - m := by
    intro j hj
    rw [v.ord_mul (zpow_ne_zero _ hπ0) (hgj0 j hj), v.ord_zpow, hπord]; ring
  have haj_mem : ∀ j ∈ g.support, (π : F)^(-m) * g j ∈ v.toValuationSubring := fun j hj =>
    (v.mem_iff_ord_nonneg (haj_ne j hj)).mpr (by rw [haj_ord j hj]; linarith [hmle j hj])

  have hdig : ∀ j, ∀ hj : j ∈ g.support, ∃ cj : K, ∃ o' : v.toValuationSubring,
      (⟨_, haj_mem j hj⟩ : v.toValuationSubring) =
        algebraMap K v.toValuationSubring cj + π * o' :=
    fun j hj => exists_digit v hπ ⟨_, haj_mem j hj⟩
  choose c o' hco using hdig

  have hcj1 : c j₁ hj₁ ≠ 0 := by
    intro hc0
    have heq : (π : F)^(-m) * g j₁ = (π : F) * ((o' j₁ hj₁ : v.toValuationSubring) : F) := by
      have h := congrArg (Subtype.val (p := (· ∈ v.toValuationSubring))) (hco j₁ hj₁)
      simp only [hc0, map_zero, zero_add, MulMemClass.coe_mul] at h
      exact h
    have haj1ord : v.ord ((π:F)^(-m) * g j₁) = 0 := by rw [haj_ord j₁ hj₁, ← hj₁m]; ring
    rcases eq_or_ne ((o' j₁ hj₁ : v.toValuationSubring) : F) 0 with ho0 | ho0
    · rw [heq, ho0, mul_zero] at haj1ord
      exact haj_ne j₁ hj₁ (by rw [heq, ho0, mul_zero])
    · rw [heq, v.ord_mul hπ0 ho0, hπord] at haj1ord
      have := v.ord_nonneg_of_mem (o' j₁ hj₁).2
      omega

  let c' : ι → K := fun j => if hj : j ∈ g.support then c j hj else 0
  have hc'eq : ∀ j (hj : j ∈ g.support), c' j = c j hj := fun j hj => dif_pos hj
  let e' : ι → F := fun j => if hj : j ∈ g.support then ((o' j hj : v.toValuationSubring) : F) else 0
  have he'eq : ∀ j (hj : j ∈ g.support), e' j = ((o' j hj : v.toValuationSubring) : F) :=
    fun j hj => dif_pos hj
  have he'mem : ∀ j ∈ g.support, e' j ∈ v.toValuationSubring := fun j hj =>
    (he'eq j hj) ▸ (o' j hj).2

  let d : K' := ∑ j ∈ g.support, c' j • B j
  have hd : d ≠ 0 := by
    intro hd0
    have := linearIndependent_iff'.1 hB g.support c' hd0 j₁ hj₁
    rw [hc'eq j₁ hj₁] at this
    exact hcj1 this

  have hcoe : ∀ j (hj : j ∈ g.support), (π:F)^(-m) * g j =
      algebraMap K F (c' j) + (π:F) * (e' j) := by
    intro j hj
    have h := congrArg (Subtype.val (p := (· ∈ v.toValuationSubring))) (hco j hj)
    simp only [AddMemClass.coe_add, MulMemClass.coe_mul, Place.coe_algebraMap] at h
    rw [hc'eq j hj, he'eq j hj]; exact h

  let R : F' := ∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (e' j)

  have hfact : (algebraMap F F' (π:F))^(-m) * Tot =
      algebraMap K' F' d + algebraMap F F' (π:F) * R := by
    rw [hTot, Finset.mul_sum]
    simp only [d, R, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [show (algebraMap F F' (π:F))^(-m) * (algebraMap K' F' (B j) * algebraMap F F' (g j))
        = algebraMap K' F' (B j) * algebraMap F F' ((π:F)^(-m) * g j) by
      rw [map_mul, ← map_zpow₀]; ring]
    rw [hcoe j hj, map_add, map_mul, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply K K' F', ← IsScalarTower.algebraMap_apply K F F']
    ring

  have hφπ0 : algebraMap F F' (π:F) ≠ 0 := by
    simpa using (algebraMap F F').injective.ne hπ0
  have hφπord : (lift v).ord (algebraMap F F' (π:F)) = 1 := by rw [hlift_ord]; exact hπord
  have hRmem : R ∈ (lift v).toValuationSubring := by
    refine Subring.sum_mem _ fun j hj => mul_mem ((lift v).algebraMap_mem' _) ?_
    rcases eq_or_ne (e' j) 0 with h0 | h0
    · rw [h0, map_zero]; exact zero_mem _
    · refine ((lift v).mem_iff_ord_nonneg ?_).mpr ?_
      · simpa using (algebraMap F F').injective.ne h0
      · rw [hlift_ord]; exact v.ord_nonneg_of_mem (he'mem j hj)
  have hd' : algebraMap K' F' d ≠ 0 := by
    simpa using (algebraMap K' F').injective.ne hd
  have hdord : (lift v).ord (algebraMap K' F' d) = 0 := by
    have h1 := (lift v).ord_nonneg_of_mem ((lift v).algebraMap_mem' d)
    have h2 := (lift v).ord_nonneg_of_mem ((lift v).algebraMap_mem' d⁻¹)
    rw [map_inv₀, (lift v).ord_inv] at h2; omega
  set S := algebraMap K' F' d + algebraMap F F' (π:F) * R with hS
  have hSmem : S ∈ (lift v).toValuationSubring :=
    add_mem ((lift v).algebraMap_mem' d)
      (mul_mem (((lift v).mem_iff_ord_nonneg hφπ0).mpr (by omega)) hRmem)

  have hSne : S ≠ 0 := by
    intro h0
    have heq : (algebraMap F F' (π:F))⁻¹ * algebraMap K' F' d = -R := by
      have h1 : algebraMap K' F' d = -(algebraMap F F' (π:F) * R) := by
        rw [eq_neg_iff_add_eq_zero]; exact hS ▸ h0
      rw [h1, mul_neg, ← mul_assoc, inv_mul_cancel₀ hφπ0, one_mul]
    have hmem : (algebraMap F F' (π:F))⁻¹ * algebraMap K' F' d ∈ (lift v).toValuationSubring := by
      rw [heq]; exact neg_mem hRmem
    have := (lift v).ord_nonneg_of_mem hmem
    rw [(lift v).ord_mul (inv_ne_zero hφπ0) hd', (lift v).ord_inv, hφπord, hdord] at this
    omega

  have hSord : (lift v).ord S = 0 := by
    have hge := (lift v).ord_nonneg_of_mem hSmem
    by_contra hne
    have hSge1 : 1 ≤ (lift v).ord S := by omega
    have hπinvS : (algebraMap F F' (π:F))⁻¹ * S ∈ (lift v).toValuationSubring := by
      refine ((lift v).mem_iff_ord_nonneg (mul_ne_zero (inv_ne_zero hφπ0) hSne)).mpr ?_
      rw [(lift v).ord_mul (inv_ne_zero hφπ0) hSne, (lift v).ord_inv, hφπord]; omega
    have hπinvd : (algebraMap F F' (π:F))⁻¹ * algebraMap K' F' d
        ∈ (lift v).toValuationSubring := by
      have heq : (algebraMap F F' (π:F))⁻¹ * algebraMap K' F' d =
          (algebraMap F F' (π:F))⁻¹ * S - R := by
        rw [hS]; field_simp; ring
      rw [heq]; exact sub_mem hπinvS hRmem
    have := (lift v).ord_nonneg_of_mem hπinvd
    rw [(lift v).ord_mul (inv_ne_zero hφπ0) hd', (lift v).ord_inv, hφπord, hdord] at this
    omega

  have hTotne : Tot ≠ 0 := fun h0 => hSne (by rw [← hfact, h0, mul_zero])
  have hTotord : (lift v).ord Tot = m := by
    have h := hSord
    rw [← hfact, (lift v).ord_mul (zpow_ne_zero _ hφπ0) hTotne,
      (lift v).ord_zpow, hφπord] at h
    linarith
  exact ⟨hTotne, fun j hj => hTotord ▸ hmle j hj⟩

end S_AlgebraicCurve_Place_ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension
end P2MW
export P2MW.S_AlgebraicCurve_Place_ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension (solution)
