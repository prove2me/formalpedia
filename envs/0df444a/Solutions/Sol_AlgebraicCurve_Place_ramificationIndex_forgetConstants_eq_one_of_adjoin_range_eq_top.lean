-- Prove2me | solution 1 for AlgebraicCurve.Place.ramificationIndex_forgetConstants_eq_one_of_adjoin_range_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c152792d-5332-56e1-a721-9f8f57aae9c6

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_eq_ramificationIdx_fiberCenter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_adjoin_range_eq_top
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open IntermediateField AlgebraicCurve Polynomial

attribute [local instance 0] AlgebraicCurve.Place.valuationSubringAlgebra

namespace S28CF

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

section FiniteLayer

variable {K F L : Type*} [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L]

theorem isScalarTower_valuationSubring (v : Place K F) :
    IsScalarTower K v.toValuationSubring L :=
  IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap K L a = algebraMap F L (algebraMap v.toValuationSubring F (algebraMap K v.toValuationSubring a))
    rw [← IsScalarTower.algebraMap_apply K v.toValuationSubring F, ← IsScalarTower.algebraMap_apply]

theorem differentIdeal_integralClosureAt_eq_top
    {α : L} (hα : IsIntegral K α) (hsep : (minpoly K α).Separable)
    (htop : Algebra.adjoin F ({α} : Set L) = ⊤) (v : Place K F) :
    differentIdeal v.toValuationSubring (Place.integralClosureAt L v) = ⊤ := by
  classical
  haveI := isScalarTower_valuationSubring (L := L) v
  have hαint : IsIntegral v.toValuationSubring α := hα.tower_top
  set αC : Place.integralClosureAt L v := ⟨α, hαint⟩ with hαCdef
  have hadj : Algebra.adjoin F {algebraMap (Place.integralClosureAt L v) L αC} = ⊤ := htop
  have hmem := aeval_derivative_mem_differentIdeal v.toValuationSubring F L αC hadj
  refine Ideal.eq_top_of_isUnit_mem _ hmem ?_
  set d : Place.integralClosureAt L v :=
    Polynomial.aeval αC (Polynomial.derivative (minpoly v.toValuationSubring αC)) with hddef
  have hmineq : minpoly v.toValuationSubring αC = minpoly v.toValuationSubring α :=
    (minpoly.algHom_eq (IsScalarTower.toAlgHom v.toValuationSubring (Place.integralClosureAt L v) L)
      Subtype.val_injective αC).symm

  have hαF : IsIntegral F α := hα.tower_top
  have hgmon : (minpoly F α).Monic := minpoly.monic hαF
  have hfmon : (minpoly K α).Monic := minpoly.monic hα
  have hdvd : minpoly F α ∣ (minpoly K α).map (algebraMap K F) := minpoly.dvd_map_of_isScalarTower K F α
  have hsepF : (minpoly F α).Separable := hsep.map.of_dvd hdvd
  have hmin : (minpoly v.toValuationSubring αC).map (algebraMap v.toValuationSubring L)
      = (minpoly F α).map (algebraMap F L) := by
    rw [hmineq, IsScalarTower.algebraMap_eq v.toValuationSubring F L, ← Polynomial.map_map,
      ← minpoly.isIntegrallyClosed_eq_field_fractions' (R := v.toValuationSubring) F hαint]
  have hdim : (d : L) = Polynomial.aeval α (Polynomial.derivative (minpoly F α)) := by
    show algebraMap (Place.integralClosureAt L v) L d = _
    rw [hddef, ← Polynomial.aeval_algebraMap_apply,
      show algebraMap (Place.integralClosureAt L v) L αC = α from rfl,
      Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, ← Polynomial.derivative_map, hmin,
      Polynomial.derivative_map, Polynomial.eval_map, ← Polynomial.aeval_def]
  have hdne : (d : L) ≠ 0 := by
    rw [hdim]; exact Polynomial.Separable.aeval_derivative_ne_zero hsepF (minpoly.aeval F α)

  have hlift : minpoly F α ∈ Polynomial.lifts (algebraMap (integralClosure K F) F) :=
    integralClosure.mem_lifts_of_monic_of_dvd_map F hfmon hgmon hdvd
  obtain ⟨g₀, hg₀⟩ := (Polynomial.mem_lifts _).mp hlift
  have hdint : IsIntegral K (d : L) := by
    rw [hdim, ← hg₀, Polynomial.derivative_map, Polynomial.aeval_def, Polynomial.eval₂_map]
    refine Polynomial.induction_on' (Polynomial.derivative g₀) (fun p q hp hq => ?_) (fun m c => ?_)
    · rw [Polynomial.eval₂_add]
      exact hp.add hq
    · rw [Polynomial.eval₂_monomial, RingHom.comp_apply]
      refine IsIntegral.mul ?_ (hα.pow m)
      have hc : IsIntegral K (algebraMap F L (c : F)) := (c.2 : IsIntegral K (c : F)).algebraMap
      exact hc

  have hint_of_mem : ∀ y : L, y ∈ K⟮(d : L)⟯ → IsIntegral v.toValuationSubring y := by
    intro y hy
    haveI := IntermediateField.isAlgebraic_adjoin_simple hdint
    have h1 : IsIntegral K (⟨y, hy⟩ : K⟮(d : L)⟯) := Algebra.IsIntegral.isIntegral _
    have h2 : IsIntegral K y := h1.map (IsScalarTower.toAlgHom K K⟮(d : L)⟯ L)
    exact h2.tower_top
  have hdinv_int : IsIntegral v.toValuationSubring ((d : L)⁻¹) :=
    hint_of_mem _ (inv_mem (IntermediateField.mem_adjoin_simple_self K (d : L)))
  exact ⟨⟨d, ⟨_, hdinv_int⟩,
    Subtype.ext (mul_inv_cancel₀ hdne), Subtype.ext (inv_mul_cancel₀ hdne)⟩, rfl⟩

theorem ramificationIndex_eq_one_finiteLayer
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
  have hdiff := differentIdeal_integralClosureAt_eq_top (L := L) hα hsep htop v
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

section Reduction

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [Algebra K F] [Algebra F F'] [IsScalarTower K F F']

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

theorem main [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K'] [Algebra.IsIntegral F F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (W : Place K' F') :
    (W.forgetConstants (K := K)).ramificationIndex F = 1 := by
  classical
  set W' : Place K F' := W.forgetConstants (K := K) with hW'def

  obtain ⟨t, ht1'⟩ := exists_ord_eq_one W
  have ht1 : W'.ord t = 1 := ht1'

  have htmem : t ∈ Algebra.adjoin F (Set.range (algebraMap K' F')) := by rw [hgen]; trivial
  obtain ⟨S, hS⟩ := exists_finset_mem_adjoin (F := F) htmem

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
    have hdvd : minpoly F b ∣ (minpoly K b).map (algebraMap K F) := minpoly.dvd_map_of_isScalarTower K F b
    exact (hbsep.map).of_dvd hdvd
  haveI : Algebra.IsIntegral F⟮b⟯ F' := Algebra.IsIntegral.tower_top (R := F)
  haveI : IsScalarTower K F⟮b⟯ F' := IsScalarTower.of_algebraMap_eq fun _ => rfl

  have hSL : (algebraMap K' F') '' (S : Set K') ⊆ (F⟮b⟯ : Set F') := by
    rintro _ ⟨s, hs, rfl⟩
    have hsK₁ : (⟨s, IntermediateField.subset_adjoin K _ hs⟩ : IntermediateField.adjoin K (S : Set K'))
        ∈ K⟮β⟯ := by rw [hβ]; exact IntermediateField.mem_top
    rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (IsIntegral.isAlgebraic (Algebra.IsIntegral.isIntegral β))] at hsK₁
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hsK₁
    obtain ⟨p, hp⟩ := hsK₁
    have hs1 : (s : K') = ((Polynomial.aeval β p : IntermediateField.adjoin K (S : Set K')) : K') := by
      have := congrArg (fun z : IntermediateField.adjoin K (S : Set K') => (z : K')) hp
      exact this.symm
    have hs2 : ((Polynomial.aeval β p : IntermediateField.adjoin K (S : Set K')) : K')
        = Polynomial.aeval (β : K') p :=
      (Polynomial.aeval_algHom_apply (IntermediateField.val _) β p).symm
    have hs' : algebraMap K' F' s = Polynomial.aeval b p := by
      rw [hs1, hs2, hbdef]
      exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K K' F') (β : K') p).symm
    rw [hs']
    have : Polynomial.aeval b p = (F⟮b⟯.val.restrictScalars K) (Polynomial.aeval (IntermediateField.AdjoinSimple.gen F b) p) := by
      rw [← Polynomial.aeval_algHom_apply]; rfl
    rw [this]
    exact Subtype.coe_prop _
  have htL : t ∈ F⟮b⟯ := by
    have : Algebra.adjoin F ((algebraMap K' F') '' (S : Set K')) ≤ F⟮b⟯.toSubalgebra :=
      Algebra.adjoin_le hSL
    exact this hS

  set W₁ : Place K F⟮b⟯ := W'.restrict F⟮b⟯ with hW₁def

  have hgen' : (minpoly K (IntermediateField.AdjoinSimple.gen F b)) = minpoly K b := by
    have h := minpoly.algebraMap_eq (A := K) (algebraMap F⟮b⟯ F').injective (IntermediateField.AdjoinSimple.gen F b)
    rw [IntermediateField.AdjoinSimple.algebraMap_gen] at h
    exact h.symm
  have hαint : IsIntegral K (IntermediateField.AdjoinSimple.gen F b) := by
    refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom K F⟮b⟯ F') (algebraMap F⟮b⟯ F').injective).mp ?_
    show IsIntegral K (algebraMap F⟮b⟯ F' (IntermediateField.AdjoinSimple.gen F b))
    rw [IntermediateField.AdjoinSimple.algebraMap_gen]; exact hbint
  have hsepgen : (minpoly K (IntermediateField.AdjoinSimple.gen F b)).Separable := by
    rw [hgen']; exact hbsep
  have htopL : Algebra.adjoin F ({IntermediateField.AdjoinSimple.gen F b} : Set F⟮b⟯) = ⊤ := by
    have := PowerBasis.adjoin_gen_eq_top (IntermediateField.adjoin.powerBasis hbintF)
    rwa [IntermediateField.adjoin.powerBasis_gen] at this
  have e1 : W₁.ramificationIndex F = 1 :=
    ramificationIndex_eq_one_finiteLayer (L := F⟮b⟯) hαint hsepgen htopL W₁

  have ht0 : t ≠ 0 := fun h => by rw [h, W'.ord_zero] at ht1; exact zero_ne_one ht1
  have htmemO : t ∈ W'.toValuationSubring := mem_of_ord_nonneg W' ht0 (by rw [ht1]; exact zero_le_one)
  have hn : 0 ≤ W₁.ord (⟨t, htL⟩ : F⟮b⟯) :=
    ord_nonneg_of_mem W₁ ((W'.mem_restrict_iff (F := F⟮b⟯)).mpr htmemO)
  have heL : (W'.ramificationIndex F⟮b⟯ : ℤ) = 1 := by
    have h1 := W'.ord_restrict (F := F⟮b⟯) ⟨t, htL⟩
    rw [show algebraMap F⟮b⟯ F' ⟨t, htL⟩ = t from rfl, ht1] at h1
    exact Int.eq_one_of_mul_eq_one_right (by positivity) h1.symm

  have hvv : W₁.restrict F = W'.restrict F := by
    apply Place.ext
    rw [Place.restrict_toValuationSubring, Place.restrict_toValuationSubring,
      Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq F F⟮b⟯ F']

  obtain ⟨π, hπ⟩ := exists_ord_eq_one (W'.restrict F)
  have h2 := W'.ord_restrict (F := F) π
  have h3 : W'.ord (algebraMap F F' π) = 1 := by
    rw [IsScalarTower.algebraMap_apply F F⟮b⟯ F' π, W'.ord_restrict (F := F⟮b⟯) (algebraMap F F⟮b⟯ π),
      heL, one_mul, W₁.ord_restrict (F := F) π, e1, hvv, hπ]
    simp
  rw [h3, hπ, mul_one] at h2
  exact_mod_cast h2.symm

end Reduction

end S28CF

end

theorem solution
    {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K'] [Algebra.IsIntegral F F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (W : AlgebraicCurve.Place K' F') :
    (W.forgetConstants (K := K)).ramificationIndex F = 1 := by
  exact S28CF.main hgen W

end S_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_adjoin_range_eq_top
end P2MW
export P2MW.S_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_adjoin_range_eq_top (solution)
