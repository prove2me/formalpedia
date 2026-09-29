-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/98458b5f-5f96-5192-ae88-4667e1691183

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_eq_ramificationIdx_fiberCenter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open IntermediateField AlgebraicCurve Polynomial

attribute [local instance 0] AlgebraicCurve.Place.valuationSubringAlgebra

namespace S12CT

theorem ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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

theorem mem_of_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem exists_ord_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    ∃ π : F, v.ord π = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  exact ⟨ϖ, v.ord_coe_irreducible hϖ⟩

scoped instance instIsScalarTowerIntermediateFieldBase {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra F F'] [Algebra K F'] [IsScalarTower K F F'] (L : IntermediateField F F') :
    IsScalarTower K L F' :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem minpoly_eq_map_of_constants {K F L : Type*} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range) {α : L} (hα : IsIntegral K α) :
    minpoly F α = (minpoly K α).map (algebraMap K F) := by
  have hαF : IsIntegral F α := hα.tower_top
  have hgmon : (minpoly F α).Monic := minpoly.monic hαF
  have hfmon : (minpoly K α).Monic := minpoly.monic hα
  have hdvd : minpoly F α ∣ (minpoly K α).map (algebraMap K F) := minpoly.dvd_map_of_isScalarTower K F α
  have hlift : minpoly F α ∈ Polynomial.lifts (algebraMap K F) := by
    have h1 := integralClosure.mem_lifts_of_monic_of_dvd_map F hfmon hgmon hdvd
    rw [Polynomial.lifts_iff_coeff_lifts] at h1 ⊢
    intro n
    obtain ⟨c, hc⟩ := h1 n
    have halg : IsAlgebraic K ((minpoly F α).coeff n) := by
      rw [← hc]
      exact (show IsIntegral K (c : F) from c.2).isAlgebraic
    exact hconst _ halg
  obtain ⟨g₀, hg₀map, -, hg₀mon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hgmon
  have hg₀α : Polynomial.aeval α g₀ = 0 := by
    have : Polynomial.aeval α (minpoly F α) = 0 := minpoly.aeval F α
    rwa [← hg₀map, Polynomial.aeval_map_algebraMap] at this
  have hfdvd : minpoly K α ∣ g₀ := minpoly.dvd K α hg₀α
  have hdeg : ((minpoly K α).map (algebraMap K F)).natDegree ≤ (minpoly F α).natDegree := by
    rw [Polynomial.natDegree_map, ← hg₀map, Polynomial.natDegree_map]
    exact Polynomial.natDegree_le_of_dvd hfdvd hg₀mon.ne_zero
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hgmon (hfmon.map _) hdvd hdeg).symm

section FiniteLayer

variable {K F L : Type*} [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L]

scoped instance instIsScalarTowerValuationSubringLayer (v : Place K F) :
    IsScalarTower K v.toValuationSubring L :=
  IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap K L a = algebraMap F L (algebraMap v.toValuationSubring F (algebraMap K v.toValuationSubring a))
    rw [← IsScalarTower.algebraMap_apply K v.toValuationSubring F, ← IsScalarTower.algebraMap_apply]

theorem isUnit_aeval_derivative_minpoly
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    {α : L} (hα : IsIntegral K α) (hsep : (minpoly K α).Separable) (v : Place K F) :
    IsUnit (Polynomial.aeval (⟨α, hα.tower_top⟩ : Place.integralClosureAt L v)
      (Polynomial.derivative (minpoly v.toValuationSubring (⟨α, hα.tower_top⟩ : Place.integralClosureAt L v)))) := by
  classical
  have hαint : IsIntegral v.toValuationSubring α := hα.tower_top
  set αC : Place.integralClosureAt L v := ⟨α, hαint⟩ with hαCdef
  set d : Place.integralClosureAt L v :=
    Polynomial.aeval αC (Polynomial.derivative (minpoly v.toValuationSubring αC)) with hddef
  have hmineq : minpoly v.toValuationSubring αC = minpoly v.toValuationSubring α :=
    (minpoly.algHom_eq (IsScalarTower.toAlgHom v.toValuationSubring (Place.integralClosureAt L v) L)
      Subtype.val_injective αC).symm
  have hmin : (minpoly v.toValuationSubring αC).map (algebraMap v.toValuationSubring L)
      = (minpoly K α).map (algebraMap K L) := by
    rw [hmineq, IsScalarTower.algebraMap_eq v.toValuationSubring F L, ← Polynomial.map_map,
      ← minpoly.isIntegrallyClosed_eq_field_fractions' (R := v.toValuationSubring) F hαint,
      minpoly_eq_map_of_constants hconst hα, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hdim : (d : L) = Polynomial.aeval α (Polynomial.derivative (minpoly K α)) := by
    show algebraMap (Place.integralClosureAt L v) L d = _
    rw [hddef, ← Polynomial.aeval_algebraMap_apply,
      show algebraMap (Place.integralClosureAt L v) L αC = α from rfl,
      Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, ← Polynomial.derivative_map, hmin,
      Polynomial.derivative_map, Polynomial.eval_map, ← Polynomial.aeval_def]
  have hdne : (d : L) ≠ 0 := by
    rw [hdim]; exact Polynomial.Separable.aeval_derivative_ne_zero hsep (minpoly.aeval K α)

  have hdmem : (d : L) ∈ K⟮α⟯ := by
    rw [hdim, show Polynomial.aeval α (Polynomial.derivative (minpoly K α))
        = algebraMap K⟮α⟯ L (Polynomial.aeval (IntermediateField.AdjoinSimple.gen K α)
            (Polynomial.derivative (minpoly K α))) from by
          rw [← Polynomial.aeval_algebraMap_apply]; rfl]
    exact Subtype.coe_prop _
  have hint_of_mem : ∀ y : L, y ∈ K⟮α⟯ → IsIntegral v.toValuationSubring y := by
    intro y hy
    haveI := IntermediateField.isAlgebraic_adjoin_simple hα
    have h1 : IsIntegral K (⟨y, hy⟩ : K⟮α⟯) := Algebra.IsIntegral.isIntegral _
    have h2 : IsIntegral K y := h1.map (IsScalarTower.toAlgHom K K⟮α⟯ L)
    exact h2.tower_top
  have hdinv_int : IsIntegral v.toValuationSubring ((d : L)⁻¹) :=
    hint_of_mem _ (inv_mem hdmem)
  exact ⟨⟨d, ⟨_, hdinv_int⟩,
    Subtype.ext (mul_inv_cancel₀ hdne), Subtype.ext (inv_mul_cancel₀ hdne)⟩, rfl⟩

theorem differentIdeal_integralClosureAt_eq_top
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    {α : L} (hα : IsIntegral K α) (hsep : (minpoly K α).Separable)
    (htop : Algebra.adjoin F ({α} : Set L) = ⊤) (v : Place K F) :
    differentIdeal v.toValuationSubring (Place.integralClosureAt L v) = ⊤ := by
  classical
  have hadj : Algebra.adjoin F {algebraMap (Place.integralClosureAt L v) L ⟨α, hα.tower_top⟩} = ⊤ := htop
  have hmem := aeval_derivative_mem_differentIdeal v.toValuationSubring F L _ hadj
  exact Ideal.eq_top_of_isUnit_mem _ hmem (isUnit_aeval_derivative_minpoly hconst hα hsep v)

theorem ramificationIndex_eq_one_finiteLayer
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    {α : L} (hα : IsIntegral K α) (hsep : (minpoly K α).Separable)
    (htop : Algebra.adjoin F ({α} : Set L) = ⊤) (W : Place K L) :
    W.ramificationIndex F = 1 := by
  classical
  haveI : Algebra.IsIntegral F L := Algebra.IsIntegral.of_finite F L
  set v : Place K F := W.restrict F with hvdef
  have hw : W.restrict F = v := rfl
  rw [Place.ramificationIndex_eq_ramificationIdx_fiberCenter v hw]
  set P := Place.fiberCenter L v hw
  set e : ℕ := (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx' P.asIdeal with he
  have hle : (IsLocalRing.maximalIdeal v.toValuationSubring).map
      (algebraMap v.toValuationSubring (Place.integralClosureAt L v)) ≤ P.asIdeal ^ e :=
    Ideal.le_pow_of_le_ramificationIdx (le_refl e)
  have hepos : 0 < e := by
    rw [he, ← Place.ramificationIndex_eq_ramificationIdx_fiberCenter v hw]
    exact W.ramificationIndex_pos
  have hdiff := differentIdeal_integralClosureAt_eq_top (L := L) hconst hα hsep htop v
  have hdvd : P.asIdeal ^ (e - 1) ∣ (⊤ : Ideal _) := by
    rw [← hdiff]
    exact pow_sub_one_dvd_differentIdeal_aux v.toValuationSubring F L P.asIdeal
      hepos.ne' (Place.maximalIdeal_ne_bot v) (Ideal.dvd_iff_le.mpr hle)
  have htop' : P.asIdeal ^ (e - 1) = ⊤ := top_le_iff.mp (Ideal.dvd_iff_le.mp hdvd)
  by_contra hne
  have : P.asIdeal = ⊤ :=
    top_le_iff.mp (htop' ▸ Ideal.pow_le_self (I := P.asIdeal) (n := e - 1) (by omega))
  exact P.isPrime.ne_top this

end FiniteLayer

section Square

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsAlgebraic K K']

theorem exists_finset_mem_adjoin {t : F'} (ht : t ∈ Algebra.adjoin F (Set.range (algebraMap K' F'))) :
    ∃ S : Finset K', t ∈ Algebra.adjoin F ((algebraMap K' F') '' (S : Set K')) := by
  classical
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨{k}, Algebra.subset_adjoin ⟨k, by simp, rfl⟩⟩
  | algebraMap r => exact ⟨∅, Subalgebra.algebraMap_mem _ r⟩
  | add x y _ _ hx hy =>
    obtain ⟨S₁, h₁⟩ := hx
    obtain ⟨S₂, h₂⟩ := hy
    refine ⟨S₁ ∪ S₂, add_mem (Algebra.adjoin_mono ?_ h₁) (Algebra.adjoin_mono ?_ h₂)⟩
    · exact Set.image_mono (by simp)
    · exact Set.image_mono (by simp)
  | mul x y _ _ hx hy =>
    obtain ⟨S₁, h₁⟩ := hx
    obtain ⟨S₂, h₂⟩ := hy
    refine ⟨S₁ ∪ S₂, mul_mem (Algebra.adjoin_mono ?_ h₁) (Algebra.adjoin_mono ?_ h₂)⟩
    · exact Set.image_mono (by simp)
    · exact Set.image_mono (by simp)

end Square

section LayerInSquare

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsAlgebraic K K'] [Algebra.IsIntegral F F']

theorem isIntegral_gen {b : F'} (hbint : IsIntegral K b) :
    IsIntegral K (IntermediateField.AdjoinSimple.gen F b) := by
  refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom K F⟮b⟯ F') (algebraMap F⟮b⟯ F').injective).mp ?_
  show IsIntegral K (algebraMap F⟮b⟯ F' (IntermediateField.AdjoinSimple.gen F b))
  rw [IntermediateField.AdjoinSimple.algebraMap_gen]; exact hbint

theorem minpoly_gen {b : F'} :
    minpoly K (IntermediateField.AdjoinSimple.gen F b) = minpoly K b := by
  have h := minpoly.algebraMap_eq (A := K) (algebraMap F⟮b⟯ F').injective
    (IntermediateField.AdjoinSimple.gen F b)
  rw [IntermediateField.AdjoinSimple.algebraMap_gen] at h
  exact h.symm

private theorem _root_.S12CT.adjoin_gen_eq_top {b : F'} (hbint : IsIntegral K b) :
    Algebra.adjoin F ({IntermediateField.AdjoinSimple.gen F b} : Set F⟮b⟯) = ⊤ := by
  have := PowerBasis.adjoin_gen_eq_top (IntermediateField.adjoin.powerBasis (hbint.tower_top (A := F)))
  rwa [IntermediateField.adjoin.powerBasis_gen] at this

p2m_export "S12CT" "adjoin_gen_eq_top"
end LayerInSquare

section Main

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K'] [Algebra.IsIntegral F F']

theorem adjoin_finset_eq_adjoin_simple {S : Finset K'}
    {β : IntermediateField.adjoin K (S : Set K')} (hβ : K⟮β⟯ = ⊤) :
    IntermediateField.adjoin K (S : Set K') = K⟮(β : K')⟯ :=
  calc IntermediateField.adjoin K (S : Set K')
      = IntermediateField.lift (⊤ : IntermediateField K (IntermediateField.adjoin K (S : Set K'))) :=
        (IntermediateField.lift_top K (IntermediateField.adjoin K (S : Set K'))).symm
    _ = IntermediateField.lift K⟮β⟯ := by rw [hβ]
    _ = K⟮(β : K')⟯ := IntermediateField.lift_adjoin_simple K (IntermediateField.adjoin K (S : Set K')) β

theorem image_subset_adjoin {S : Finset K'}
    {β : IntermediateField.adjoin K (S : Set K')} (hβ : K⟮β⟯ = ⊤) :
    (algebraMap K' F') '' (S : Set K') ⊆ (F⟮algebraMap K' F' (β : K')⟯ : Set F') := by
  rintro _ ⟨s, hs, rfl⟩
  have hs' : s ∈ K⟮(β : K')⟯ := by
    rw [← adjoin_finset_eq_adjoin_simple hβ]; exact IntermediateField.subset_adjoin K _ hs
  rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic (β : K')), Algebra.adjoin_singleton_eq_range_aeval] at hs'
  obtain ⟨p, hp⟩ := hs'
  have h1 : algebraMap K' F' s = Polynomial.aeval (algebraMap K' F' (β : K')) p := by
    rw [← hp]
    exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K K' F') (β : K') p).symm
  rw [h1]
  have h2 : Polynomial.aeval (algebraMap K' F' (β : K')) p
      = (F⟮algebraMap K' F' (β : K')⟯.val.restrictScalars K)
          (Polynomial.aeval (IntermediateField.AdjoinSimple.gen F (algebraMap K' F' (β : K'))) p) := by
    rw [← Polynomial.aeval_algHom_apply]; rfl
  rw [h2]
  exact Subtype.coe_prop _

theorem adjoin_image_le {S : Finset K'}
    {β : IntermediateField.adjoin K (S : Set K')} (hβ : K⟮β⟯ = ⊤) :
    Algebra.adjoin F ((algebraMap K' F') '' (S : Set K'))
      ≤ F⟮algebraMap K' F' (β : K')⟯.toSubalgebra :=
  Algebra.adjoin_le (image_subset_adjoin hβ)

end Main

section Extension

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K'] [Algebra.IsIntegral F F']

theorem mem_valuationSubring_of_monic {R L : Type*} [CommRing R] [Field L] (O : ValuationSubring L)
    (φ : R →+* L) (hφ : ∀ r, φ r ∈ O) {x : L}
    (hx : ∃ p : Polynomial R, p.Monic ∧ p.eval₂ φ x = 0) : x ∈ O := by
  obtain ⟨p, hpm, hpx⟩ := hx
  set φ' : R →+* O := φ.codRestrict O.toSubring hφ with hφ'def
  have hcomp : (algebraMap O L).comp φ' = φ := RingHom.ext fun _ => rfl
  have hint : IsIntegral O x := ⟨p.map φ', hpm.map φ', by rw [Polynomial.eval₂_map, hcomp]; exact hpx⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]; exact y.2

theorem inv_mem_of_isUnit {L : Type*} [Field L] (O : ValuationSubring L) {z : L} (hz : z ∈ O)
    (h : IsUnit (⟨z, hz⟩ : O)) : z⁻¹ ∈ O := by
  obtain ⟨u, hu⟩ := h
  have h1 : z * ((u⁻¹ : Oˣ) : O) = 1 := by
    have := congrArg (fun t : O => (t : L)) u.mul_inv
    simpa [hu] using this
  rw [← eq_inv_of_mul_eq_one_right h1]
  exact ((u⁻¹ : Oˣ) : O).2

theorem exists_forgetConstants_restrict_eq
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    {M : Type*} [Field M] [Algebra F M] [Algebra M F'] [IsScalarTower F M F']
    [Algebra K M] [IsScalarTower K M F'] [Algebra.IsIntegral M F']
    (V : Place K M) :
    ∃ W : Place K' F', (W.forgetConstants (K := K)).restrict M = V := by
  classical
  haveI : IsScalarTower K F M := IsScalarTower.of_algebraMap_eq fun c =>
    (algebraMap M F').injective (by
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply])
  haveI : Algebra.IsIntegral F M := ⟨fun x =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom F M F') (algebraMap M F').injective).mp
      (Algebra.IsIntegral.isIntegral _)⟩

  set f : V.toValuationSubring →+* F' :=
    (algebraMap M F').comp (algebraMap V.toValuationSubring M) with hfdef
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  have hfA : ∀ x : V.toValuationSubring, f x ∈ A := hA
  have hnonunit : ∀ x : V.toValuationSubring, ¬ IsUnit x → ¬ IsUnit (⟨f x, hfA x⟩ : A) :=
    fun x hx hu => hx (hloc.map_nonunit x hu)

  set w : Place K F := V.restrict F with hwdef
  obtain ⟨π, hπ⟩ := exists_ord_eq_one w
  have hπ0 : π ≠ 0 := fun h => by rw [h, w.ord_zero] at hπ; exact zero_ne_one hπ
  have hπw : π ∈ w.toValuationSubring := mem_of_ord_nonneg w hπ0 (by rw [hπ]; exact zero_le_one)
  have hπV : algebraMap F M π ∈ V.toValuationSubring := (V.mem_restrict_iff (F := F)).mp hπw
  set πV : V.toValuationSubring := ⟨algebraMap F M π, hπV⟩ with hπVdef
  have hπVnu : ¬ IsUnit πV := by
    intro hu
    have h1 := V.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec, show ((πV : V.toValuationSubring) : M) = algebraMap F M π from rfl] at h1
    have h2 := V.ord_restrict (F := F) π
    rw [h1, hπ, mul_one] at h2
    have h3 := V.ramificationIndex_pos (F := F)
    omega
  set πF : F' := algebraMap F F' π with hπFdef
  have hfπ : f πV = πF := by
    rw [hfdef, hπFdef, RingHom.comp_apply, IsScalarTower.algebraMap_apply F M F']; rfl
  have hπA : πF ∈ A := hfπ ▸ hfA πV
  have hπAnu : ¬ IsUnit (⟨πF, hπA⟩ : A) := by
    have := hnonunit πV hπVnu
    rwa [show (⟨f πV, hfA πV⟩ : A) = ⟨πF, hπA⟩ from Subtype.ext hfπ] at this
  have hπF0 : πF ≠ 0 := by rw [hπFdef]; exact (_root_.map_ne_zero _).mpr hπ0
  have hπinv : πF⁻¹ ∉ A := by
    intro h
    apply hπAnu
    have h1 : (⟨πF, hπA⟩ : A) * ⟨πF⁻¹, h⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hπF0)
    exact IsUnit.of_mul_eq_one _ h1

  have hwA : ∀ g : F, g ∈ w.toValuationSubring → algebraMap F F' g ∈ A := by
    intro g hg
    have h1 : algebraMap F M g ∈ V.toValuationSubring := (V.mem_restrict_iff (F := F)).mp hg
    have := hfA ⟨_, h1⟩
    rwa [hfdef, RingHom.comp_apply, show (algebraMap V.toValuationSubring M ⟨_, h1⟩ : M)
      = algebraMap F M g from rfl, ← IsScalarTower.algebraMap_apply] at this
  set p : A := ⟨πF, hπA⟩ with hpdef
  have hp0 : p ≠ 0 := fun h => hπF0 (congrArg Subtype.val h)

  have hfact : ∀ (x : F') (hxA : x ∈ A), x ≠ 0 → ∃ (n : ℕ) (U : Aˣ), (⟨x, hxA⟩ : A) = U * p ^ n := by
    intro x hxA hx0

    have hxmem : x ∈ Algebra.adjoin F (Set.range (algebraMap K' F')) := by rw [hgen]; trivial
    obtain ⟨S, hS⟩ := exists_finset_mem_adjoin (F := F) hxmem
    haveI : FiniteDimensional K (IntermediateField.adjoin K (S : Set K')) :=
      IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
    haveI : Algebra.IsSeparable K (IntermediateField.adjoin K (S : Set K')) :=
      Algebra.isSeparable_tower_bot_of_isSeparable K _ K'
    obtain ⟨β, hβ⟩ := Field.exists_primitive_element K (IntermediateField.adjoin K (S : Set K'))
    set b : F' := algebraMap K' F' (β : K') with hbdef
    have hβint : IsIntegral K (β : K') := Algebra.IsIntegral.isIntegral _
    have hbint : IsIntegral K b := hβint.map (IsScalarTower.toAlgHom K K' F')
    have hminb : minpoly K b = minpoly K (β : K') :=
      minpoly.algebraMap_eq (algebraMap K' F').injective (β : K')
    have hbsep : (minpoly K b).Separable := by
      rw [hminb]; exact Algebra.IsSeparable.isSeparable K (β : K')
    have hbintF : IsIntegral F b := hbint.tower_top
    haveI hfdL : FiniteDimensional F F⟮b⟯ := IntermediateField.adjoin.finiteDimensional hbintF
    haveI hsepL : Algebra.IsSeparable F F⟮b⟯ := by
      rw [IntermediateField.isSeparable_adjoin_simple_iff_isSeparable]
      show (minpoly F b).Separable
      exact (hbsep.map).of_dvd (minpoly.dvd_map_of_isScalarTower K F b)
    haveI : Algebra.IsIntegral F⟮b⟯ F' := Algebra.IsIntegral.tower_top (R := F)
    have hxL : x ∈ F⟮b⟯ := adjoin_image_le hβ hS

    set O₂ : ValuationSubring F⟮b⟯ := A.comap (algebraMap F⟮b⟯ F') with hO₂def
    have hmemO₂ : ∀ y : F⟮b⟯, y ∈ O₂ ↔ (y : F') ∈ A := fun y => ValuationSubring.mem_comap

    set C := Place.integralClosureAt F⟮b⟯ w with hCdef
    have hCA : ∀ c : C, ((c : F⟮b⟯) : F') ∈ A := by
      intro c
      obtain ⟨q, hqm, hqc⟩ := c.2
      refine mem_valuationSubring_of_monic A
        ((algebraMap F⟮b⟯ F').comp (algebraMap w.toValuationSubring F⟮b⟯))
        (fun r => ?_) ⟨q, hqm, ?_⟩
      · rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply w.toValuationSubring F F⟮b⟯,
          ← IsScalarTower.algebraMap_apply F F⟮b⟯ F']
        exact hwA _ r.2
      · show Polynomial.eval₂ _ (algebraMap F⟮b⟯ F' (c : F⟮b⟯)) q = 0
        rw [← Polynomial.hom_eval₂]
        exact (congrArg (algebraMap F⟮b⟯ F') hqc).trans (map_zero _)
    set ψ : C →+* A :=
      ((algebraMap F⟮b⟯ F').comp (algebraMap C F⟮b⟯)).codRestrict A.toSubring hCA with hψdef
    have hψ : ∀ c : C, (ψ c : F') = ((c : F⟮b⟯) : F') := fun c => rfl
    set P : Ideal C := (IsLocalRing.maximalIdeal A).comap ψ with hPdef
    haveI hPprime : P.IsPrime := Ideal.comap_isPrime ψ _
    set πL : F⟮b⟯ := algebraMap F F⟮b⟯ π with hπLdef
    have hπLF : ((πL : F⟮b⟯) : F') = πF := by
      rw [hπLdef, hπFdef, IsScalarTower.algebraMap_apply F F⟮b⟯ F']; rfl
    set πw : w.toValuationSubring := ⟨π, hπw⟩ with hπwdef
    have hπCval : ((algebraMap w.toValuationSubring C πw : C) : F⟮b⟯) = algebraMap F F⟮b⟯ π := rfl
    have hπC : algebraMap w.toValuationSubring C πw ∈ P := by
      rw [hPdef, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      have : ψ (algebraMap w.toValuationSubring C πw) = p := Subtype.ext (by
        rw [hψ, hπCval]; exact hπLF)
      rw [this]; exact hπAnu
    have hPne : P ≠ ⊥ := by
      intro h
      have h1 : algebraMap w.toValuationSubring C πw = 0 := by
        rw [← Ideal.mem_bot, ← h]; exact hπC
      have h2 : πw = 0 := Place.algebraMap_integralClosureAt_injective w (by rw [h1, map_zero])
      exact hπ0 (congrArg Subtype.val h2)
    set Q : IsDedekindDomain.HeightOneSpectrum C := ⟨P, hPprime, hPne⟩ with hQdef
    set W₂ : Place K F⟮b⟯ := Place.placeOfPrime Q with hW₂def
    have hW₂w : W₂.restrict F = w := Place.restrict_placeOfPrime Q

    have hle : W₂.toValuationSubring ≤ O₂ := by
      rintro y ⟨a, s, hs, rfl⟩
      rw [hO₂def, ValuationSubring.mem_comap, map_mul, map_inv₀]
      refine mul_mem (hCA a) (inv_mem_of_isUnit A (hCA s) ?_)
      by_contra hsu
      exact hs (show s ∈ P by
        rw [hPdef, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hsu)
    have hO₂ne : O₂ ≠ ⊤ := by
      intro h
      have hπL : πL⁻¹ ∈ O₂ := by rw [h]; exact ValuationSubring.mem_top _
      rw [hmemO₂] at hπL
      apply hπinv
      have : ((πL⁻¹ : F⟮b⟯) : F') = πF⁻¹ := by
        rw [← hπLF]; exact map_inv₀ (algebraMap F⟮b⟯ F') _
      rwa [this] at hπL
    have hO₂eq : O₂ = W₂.toValuationSubring :=
      (ValuationSubring.eq_of_le_of_ne_top _ hle hO₂ne).symm

    have he : W₂.ramificationIndex F = 1 :=
      ramificationIndex_eq_one_finiteLayer (L := F⟮b⟯) hconst (isIntegral_gen hbint)
        (by rw [minpoly_gen]; exact hbsep) (adjoin_gen_eq_top hbint) W₂
    have hordπ : W₂.ord πL = 1 := by
      have h := W₂.ord_restrict (F := F) π
      rw [he, hW₂w, hπ] at h
      exact_mod_cast h
    have hπL0 : πL ≠ 0 := (_root_.map_ne_zero _).mpr hπ0
    have hπLO : πL ∈ W₂.toValuationSubring := mem_of_ord_nonneg W₂ hπL0 (by rw [hordπ]; exact zero_le_one)
    set πo : W₂.toValuationSubring := ⟨πL, hπLO⟩ with hπodef
    have hπo0 : πo ≠ 0 := fun h => hπL0 (congrArg Subtype.val h)
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W₂.toValuationSubring
    obtain ⟨m, u, hm⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπo0 hϖ
    have hm1 : m = 1 := by
      have h1 := W₂.ord_unit_smul_zpow u hϖ (m : ℤ)
      rw [zpow_natCast] at h1
      have h2 : (πo : F⟮b⟯) = (u : W₂.toValuationSubring) * (ϖ : F⟮b⟯) ^ m := by
        have := congrArg Subtype.val hm; push_cast at this; exact this
      rw [← h2, show (πo : F⟮b⟯) = πL from rfl, hordπ] at h1
      exact_mod_cast h1.symm
    have hπoirr : Irreducible πo := by
      refine (Associated.irreducible ⟨u, ?_⟩ hϖ)
      rw [hm, hm1, pow_one, mul_comm]
    set xo : W₂.toValuationSubring := ⟨⟨x, hxL⟩, by rw [← hO₂eq, hmemO₂]; exact hxA⟩ with hxodef
    have hxo0 : xo ≠ 0 := fun h => hx0 (congrArg Subtype.val (congrArg Subtype.val h))
    obtain ⟨n, uo, hxo⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hxo0 hπoirr

    set θ : W₂.toValuationSubring →+* A :=
      ((algebraMap F⟮b⟯ F').comp (algebraMap W₂.toValuationSubring F⟮b⟯)).codRestrict A.toSubring
        (fun y => (hmemO₂ y).mp (by rw [hO₂eq]; exact y.2)) with hθdef
    have hθ : ∀ y : W₂.toValuationSubring, (θ y : F') = ((y : F⟮b⟯) : F') := fun y => rfl
    have hθx : θ xo = ⟨x, hxA⟩ := Subtype.ext (by rw [hθ])
    have hθπ : θ πo = p := Subtype.ext (by rw [hθ, hpdef]; exact hπLF)
    refine ⟨n, Units.map θ.toMonoidHom uo, ?_⟩
    rw [← hθx, hxo, map_mul, map_pow, hθπ]
    rfl

  have hdvd : ∀ y : A, ¬ IsUnit y → p ∣ y := by
    intro y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · exact dvd_zero p
    obtain ⟨n, U, h⟩ := hfact y y.2 (fun h0 => hy0 (Subtype.ext h0))
    rw [Subtype.coe_eta] at h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exfalso; apply hy; rw [h, hn, pow_zero, mul_one]; exact Units.isUnit U
    · refine ⟨U * p ^ (n - 1), ?_⟩
      rw [h, mul_comm p, mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]
  have hirr : Irreducible p := by
    refine irreducible_iff.mpr ⟨hπAnu, fun a c hac => ?_⟩
    by_contra h
    obtain ⟨ha, hc⟩ := not_or.mp h
    obtain ⟨a', ha'⟩ := hdvd a ha
    obtain ⟨c', hc'⟩ := hdvd c hc
    apply hπAnu
    have : p * 1 = p * (p * (a' * c')) := by
      rw [mul_one]; conv_lhs => rw [hac, ha', hc']
      ring
    exact IsUnit.of_mul_eq_one (a' * c') (mul_left_cancel₀ hp0 this).symm
  haveI hDVR : IsDiscreteValuationRing A :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨p, hirr, fun {y} hy => by
      obtain ⟨n, U, h⟩ := hfact y y.2 (fun h0 => hy (Subtype.ext h0))
      rw [Subtype.coe_eta] at h
      exact ⟨n, U, by rw [h, mul_comm]⟩⟩

  have hKA : ∀ k : K, algebraMap K F' k ∈ A := fun k => by
    have := hfA (algebraMap K V.toValuationSubring k)
    rwa [hfdef, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply K V.toValuationSubring M,
      ← IsScalarTower.algebraMap_apply K M F'] at this
  have hK'A : ∀ c : K', algebraMap K' F' c ∈ A := fun c =>
    mem_valuationSubring_of_monic A (algebraMap K F') hKA
      ⟨minpoly K c, minpoly.monic (Algebra.IsIntegral.isIntegral c), by
        rw [← Polynomial.aeval_def, Polynomial.aeval_algebraMap_apply, minpoly.aeval, map_zero]⟩

  refine ⟨{ toValuationSubring := A, algebraMap_mem' := hK'A,
            ne_top' := fun h => hπinv (by rw [h]; exact ValuationSubring.mem_top _),
            isPrincipalIdealRing' := inferInstance }, Place.ext ?_⟩
  symm
  refine ValuationSubring.eq_of_le_of_ne_top _ (fun y hy => ?_) (Place.ne_top' _)
  rw [Place.restrict_toValuationSubring, ValuationSubring.mem_comap]
  exact hfA ⟨y, hy⟩

end Extension

end S12CT
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension.S12CT"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension.S12CT"

theorem solution
    {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K'] [Algebra.IsIntegral F F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    {M : Type*} [Field M] [Algebra F M] [Algebra M F'] [IsScalarTower F M F']
    [Algebra K M] [IsScalarTower K M F'] [Algebra.IsIntegral M F']
    (V : AlgebraicCurve.Place K M) :
    ∃ W : AlgebraicCurve.Place K' F', (W.forgetConstants (K := K)).restrict M = V := by
  exact S12CT.exists_forgetConstants_restrict_eq hgen hconst V

end S_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension (solution)
