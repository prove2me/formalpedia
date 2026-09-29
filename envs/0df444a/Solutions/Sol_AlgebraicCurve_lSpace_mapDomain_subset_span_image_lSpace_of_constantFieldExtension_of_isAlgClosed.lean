-- Prove2me | solution 1 for AlgebraicCurve.lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/3ff2149c-0891-52bc-a2fa-1265d075fe39

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
import Theorems.Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option maxHeartbeats 4000000

open AlgebraicCurve

namespace W7XChildJ

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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

theorem one_le_ord_of_mem_of_inv_not_mem {f : F} (h1 : f ∈ v.toValuationSubring)
    (h2 : f⁻¹ ∉ v.toValuationSubring) : 1 ≤ v.ord f := by
  have hf0 : f ≠ 0 := by rintro rfl; exact h2 (by simp)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ
  have h0 := ord_nonneg_of_mem v h1
  by_contra hlt
  have hz : v.ord f = 0 := by omega
  apply h2
  have hmul : ((u : v.toValuationSubring) : F) *
      (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  rw [hu, hz, zpow_zero, mul_one, ← eq_inv_of_mul_eq_one_right hmul]
  exact SetLike.coe_mem _

theorem mem_iff_ord_nonneg (f : F) : f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by
  refine ⟨ord_nonneg_of_mem v, fun h => ?_⟩
  by_contra hmem
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem f).resolve_left hmem
  have := one_le_ord_of_mem_of_inv_not_mem v hinv (by simpa using hmem)
  rw [v.ord_inv] at this
  omega

end W7XChildJ

open W7XChildJ

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
    (hlift_inj : Function.Injective lift)
    (hlift_new : ∀ v' : Place K' F', (∀ v, lift v ≠ v') →
      ∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring)
    (D : Divisor K F) {f' : F'}
    (hf' : f' ∈ LSpace (K := K') (Finsupp.mapDomain lift D)) :
    f' ∈ Submodule.span K' ((algebraMap F F') '' (LSpace (K := K) D : Set F)) := by
  classical

  have hnew : ∀ v' : Place K' F', (∀ v : Place K F,
      v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
      f' ∈ v'.toValuationSubring := by
    intro v' hv'
    have hnr : ∀ v, lift v ≠ v' := fun v hev => hv' v (by
      rw [← hev]; ext g
      rw [ValuationSubring.mem_comap, mem_iff_ord_nonneg, mem_iff_ord_nonneg, hlift_ord])
    have hD0 : (Finsupp.mapDomain lift D) v' = 0 :=
      Finsupp.mapDomain_notin_range D v' (by simpa [Set.range] using hnr)
    rcases mem_lSpace_iff_ord.mp hf' with rfl | hord
    · exact zero_mem _
    · rw [mem_iff_ord_nonneg]; have := hord v'; rw [hD0, neg_zero] at this; exact this
  have hspan' : f' ∈ Submodule.span K' (Set.range (algebraMap F F')) :=
    mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed
      K F K' F' hfg hfg' hgen f' hnew

  let B := Module.Basis.ofVectorSpace K K'
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hspan'

  let g : Module.Basis.ofVectorSpaceIndex K K' →₀ F :=
    (Finsupp.ofSupportFinite
      (fun j => ∑ f ∈ c.support, (B.repr (c f) j) • f)
      ((c.support.finite_toSet.biUnion fun f _ => (B.repr (c f)).support.finite_toSet).subset
        (fun j hj => by
          simp only [Function.mem_support, ne_eq] at hj
          simp only [Set.mem_iUnion, Finset.mem_coe, Finsupp.mem_support_iff, ne_eq]
          by_contra h; push_neg at h
          exact hj (Finset.sum_eq_zero fun f hf => by
            rw [h f (Finsupp.mem_support_iff.mp hf), zero_smul]))))
  have hf'eq : f' = ∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j) := by
    have hgj : ∀ j, (g j : F) = ∑ f ∈ c.support, B.repr (c f) j • f := fun _ => rfl
    let S : Finset _ := c.support.biUnion fun f => (B.repr (c f)).support
    have hgsub : g.support ⊆ S := by
      intro j hj
      rw [Finsupp.mem_support_iff, hgj] at hj
      simp only [S, Finset.mem_biUnion, Finsupp.mem_support_iff]
      by_contra h; push_neg at h
      exact hj (Finset.sum_eq_zero fun f hf => by
        rw [h f (Finsupp.mem_support_iff.mp hf), zero_smul])
    have hcf_S : ∀ f ∈ c.support, c f = ∑ j ∈ S, B.repr (c f) j • B j := by
      intro f hf
      conv_lhs => rw [← B.linearCombination_repr (c f), Finsupp.linearCombination_apply,
        Finsupp.sum]
      refine Finset.sum_subset ?_ fun j _ hj => by
        rw [Finsupp.notMem_support_iff.mp hj, zero_smul]
      exact Finset.subset_biUnion_of_mem (fun f => (B.repr (c f)).support) hf
    have hterm : ∀ (j : Module.Basis.ofVectorSpaceIndex K K') (f : F),
        algebraMap K' F' (B.repr (c f) j • B j) * algebraMap F F' f =
        algebraMap K' F' (B j) * algebraMap F F' (B.repr (c f) j • f) := by
      intro j f
      rw [Algebra.smul_def (R := K) (A := K'), map_mul,
        Algebra.smul_def (R := K) (A := F), map_mul,
        ← IsScalarTower.algebraMap_apply K K' F',
        ← IsScalarTower.algebraMap_apply K F F']
      ring
    calc f' = ∑ f ∈ c.support, c f • algebraMap F F' f := by
          rw [← hc]; rfl
      _ = ∑ f ∈ c.support, ∑ j ∈ S,
            algebraMap K' F' (B.repr (c f) j • B j) * algebraMap F F' f := by
          refine Finset.sum_congr rfl fun f hf => ?_
          conv_lhs => rw [Algebra.smul_def, hcf_S f hf]
          rw [map_sum, Finset.sum_mul]
      _ = ∑ j ∈ S, ∑ f ∈ c.support,
            algebraMap K' F' (B j) * algebraMap F F' (B.repr (c f) j • f) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun f _ => hterm j f
      _ = ∑ j ∈ S, algebraMap K' F' (B j) * algebraMap F F' (g j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.mul_sum, ← map_sum, ← hgj]
      _ = ∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j) :=
          (Finset.sum_subset hgsub fun j _ hj => by
            rw [Finsupp.notMem_support_iff.mp hj, map_zero, mul_zero]).symm

  have hgD : ∀ j, g j ∈ LSpace (K := K) D :=
    AlgebraicCurve.mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain
      K F K' F' hfg hfg' hgen lift hlift_ord hlift_inj D B B.linearIndependent g
      (hf'eq ▸ hf')

  rw [hf'eq]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g j, hgD j, rfl⟩)

end S_AlgebraicCurve_lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed (solution)
