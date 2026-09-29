-- Prove2me | solution 1 for AlgebraicCurve.lSpace_pullbackConstants_eq_span_of_isConstantFieldExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/64b23de3-fd2f-502c-997c-03db38fbade1

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_lSpace_pullbackConstants_eq_span_of_isConstantFieldExtension
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open AlgebraicCurve Polynomial

namespace P2mConormLSpace

section Basic

variable {k L : Type*} [Field k] [Field L] [Algebra k L] (w : Place k L)

theorem ord_nonneg_of_mem {f : L} (hf : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  exact (w.adicValuation_le_one_iff.mp (w.adicValuation_le_one_of_mem hf)).resolve_left hf0

theorem mem_of_ord_nonneg {f : L} (hf : 0 ≤ w.ord f) : f ∈ w.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf0 hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hf
  rw [hu, hn, zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem π.2 n)

theorem ord_algebraMap (a : k) : w.ord (algebraMap k L a) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have h1 := ord_nonneg_of_mem w (w.algebraMap_mem' a)
  have h2 := ord_nonneg_of_mem w (w.algebraMap_mem' a⁻¹)
  rw [map_inv₀, w.ord_inv] at h2
  omega

theorem exists_ord_eq (n : ℤ) : ∃ t : L, t ≠ 0 ∧ w.ord t = n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπ0 : (π : L) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  exact ⟨(π : L) ^ n, zpow_ne_zero n hπ0, by rw [w.ord_zpow, w.ord_coe_irreducible hπ, mul_one]⟩

end Basic

section RestrictRestrict

variable {k L M N : Type*} [Field k] [Field L] [Field M] [Field N]
  [Algebra k L] [Algebra k M] [Algebra k N]
  [Algebra L M] [Algebra M N] [Algebra L N] [IsScalarTower L M N]
  [IsScalarTower k M N] [IsScalarTower k L N] [IsScalarTower k L M]
  [Algebra.IsIntegral M N] [Algebra.IsIntegral L N] [Algebra.IsIntegral L M]

theorem restrict_restrict (W : Place k N) : (W.restrict M).restrict L = W.restrict L := by
  apply Place.ext
  simp only [Place.restrict_toValuationSubring]
  rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq]

end RestrictRestrict

namespace CFE

section

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']

theorem minpoly_algebraMap_eq_map [FiniteDimensional K K']
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range) (θ : K') :
    minpoly F (algebraMap K' F' θ) = (minpoly K θ).map (algebraMap K F) := by
  set θ' := algebraMap K' F' θ with hθ'
  have hθint : IsIntegral K θ := Algebra.IsIntegral.isIntegral θ
  have hp : (minpoly K θ).Monic := minpoly.monic hθint
  have hP : ((minpoly K θ).map (algebraMap K F)).Monic := hp.map _
  have hθ'root : aeval θ' ((minpoly K θ).map (algebraMap K F)) = 0 := by
    rw [aeval_map_algebraMap, hθ', aeval_algebraMap_apply, minpoly.aeval, map_zero]
  have hθ'int : IsIntegral F θ' := ⟨_, hP, by rwa [← aeval_def]⟩
  have hq : (minpoly F θ').Monic := minpoly.monic hθ'int
  have hdvd : minpoly F θ' ∣ (minpoly K θ).map (algebraMap K F) := minpoly.dvd F θ' hθ'root
  have hcoeff : ∀ i, (minpoly F θ').coeff i ∈ (algebraMap K F).range := fun i =>
    hconst _ (isIntegral_coeff_of_dvd (minpoly K θ) (minpoly F θ') hp hq hdvd i).isAlgebraic
  have hlifts : minpoly F θ' ∈ Polynomial.lifts (algebraMap K F) :=
    (lifts_iff_coeff_lifts _).mpr fun i => hcoeff i
  obtain ⟨q0, hq0map, -, hq0monic⟩ := lifts_and_degree_eq_and_monic hlifts hq
  have hq0θ : aeval θ q0 = 0 := by
    apply (algebraMap K' F').injective
    rw [map_zero, ← aeval_algebraMap_apply, ← hθ', ← aeval_map_algebraMap F, hq0map,
      minpoly.aeval]
  have hpdvd : minpoly K θ ∣ q0 := minpoly.dvd K θ hq0θ
  have hdeg1 : (minpoly K θ).natDegree ≤ (minpoly F θ').natDegree := by
    have := natDegree_le_of_dvd hpdvd hq0monic.ne_zero
    rwa [← hq0map, natDegree_map]
  symm
  exact eq_of_monic_of_dvd_of_natDegree_le hq hP hdvd (by rwa [natDegree_map])

variable [FiniteDimensional K K'] [Algebra.IsSeparable K K']

omit [FiniteDimensional K K'] [Algebra.IsSeparable K K'] in

private theorem _root_.P2mConormLSpace.CFE.adjoin_gen_eq_top (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (pb : PowerBasis K K') :
    Algebra.adjoin F {algebraMap K' F' pb.gen} = ⊤ := by
  apply top_le_iff.mp
  rw [← hgen]
  apply Algebra.adjoin_le
  rintro _ ⟨k, rfl⟩
  have hk : k ∈ Algebra.adjoin K {pb.gen} := by rw [pb.adjoin_gen_eq_top]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hk
  obtain ⟨r, rfl⟩ := hk
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, SetLike.mem_coe]
  rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap F]
  exact aeval_mem_adjoin_singleton F _

p2m_export "P2mConormLSpace.CFE" "adjoin_gen_eq_top"
include K in
omit [Algebra.IsSeparable K K'] in
theorem isIntegral_algebraMap' (θ : K') : IsIntegral F (algebraMap K' F' θ) :=
  ((Algebra.IsIntegral.isIntegral (R := K) θ).map (IsScalarTower.toAlgHom K K' F')).tower_top

noncomputable def pbF (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (pb : PowerBasis K K') : PowerBasis F F' :=
  PowerBasis.ofAdjoinEqTop (isIntegral_algebraMap' (K := K) pb.gen) (adjoin_gen_eq_top hgen pb)

omit [Algebra.IsSeparable K K'] in
theorem pbF_gen (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (pb : PowerBasis K K') : (pbF hgen pb).gen = algebraMap K' F' pb.gen :=
  rfl

omit [Algebra.IsSeparable K K'] in
theorem pbF_dim (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    (pb : PowerBasis K K') : (pbF hgen pb).dim = pb.dim := by
  rw [pbF, PowerBasis.ofAdjoinEqTop_dim, minpoly_algebraMap_eq_map hconst, natDegree_map,
    pb.natDegree_minpoly]

include K in

theorem finiteDimensional' (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤) :
    FiniteDimensional F F' :=
  (pbF hgen (Field.powerBasisOfFiniteOfSeparable K K')).finite

theorem isSeparable' (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range) :
    Algebra.IsSeparable F F' := by
  set pb := Field.powerBasisOfFiniteOfSeparable K K'
  have hθ'int : IsIntegral F (algebraMap K' F' pb.gen) := isIntegral_algebraMap' (K := K) pb.gen
  have hsep : IsSeparable F (algebraMap K' F' pb.gen) := by
    rw [IsSeparable, minpoly_algebraMap_eq_map hconst]
    exact Polynomial.Separable.map (Algebra.IsSeparable.isSeparable K pb.gen)
  have htop : IntermediateField.adjoin F {algebraMap K' F' pb.gen} = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθ'int.isAlgebraic,
      adjoin_gen_eq_top hgen pb, IntermediateField.top_toSubalgebra]
  haveI := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F F').mpr hsep
  rw [htop] at this
  exact AlgEquiv.Algebra.isSeparable (IntermediateField.topEquiv (F := F) (E := F'))

noncomputable def bF (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    (pb : PowerBasis K K') : Module.Basis (Fin pb.dim) F F' :=
  (pbF hgen pb).basis.reindex (finCongr (pbF_dim hgen hconst pb))

omit [Algebra.IsSeparable K K'] in
theorem bF_apply (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    (pb : PowerBasis K K') (i : Fin pb.dim) :
    bF hgen hconst pb i = algebraMap K' F' (pb.basis i) := by
  simp only [bF, Module.Basis.reindex_apply, finCongr_symm, finCongr_apply, PowerBasis.coe_basis,
    Fin.val_cast, map_pow, pbF_gen]

omit [Algebra.IsSeparable K K'] in

theorem bF_repr_algebraMap (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    (pb : PowerBasis K K') (k : K') (i : Fin pb.dim) :
    (bF hgen hconst pb).repr (algebraMap K' F' k) i = algebraMap K F (pb.basis.repr k i) := by
  set b := bF hgen hconst pb
  have hk : algebraMap K' F' k = ∑ j, algebraMap K F (pb.basis.repr k j) • b j := by
    conv_lhs => rw [← pb.basis.sum_repr k]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, bF_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  rw [hk, ← b.equivFun_symm_apply, ← b.equivFun_apply, b.equivFun.apply_symm_apply]

theorem trace_algebraMap' (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range) (k : K') :
    Algebra.trace F F' (algebraMap K' F' k) = algebraMap K F (Algebra.trace K K' k) := by
  classical
  set pb := Field.powerBasisOfFiniteOfSeparable K K'
  set b := bF hgen hconst pb
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace pb.basis, Matrix.trace,
    Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, bF_apply, ← map_mul, bF_repr_algebraMap]

theorem dualBasis_bF_apply (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (pb : PowerBasis K K') (j : Fin pb.dim) :
    (Algebra.traceForm F F').dualBasis (traceForm_nondegenerate F F') (bF hgen hconst pb) j =
      algebraMap K' F' ((Algebra.traceForm K K').dualBasis (traceForm_nondegenerate K K')
        pb.basis j) := by
  classical
  have key : ∀ i j, Algebra.traceForm F F' (algebraMap K' F'
      ((Algebra.traceForm K K').dualBasis (traceForm_nondegenerate K K') pb.basis i))
        (bF hgen hconst pb j) = if j = i then 1 else 0 := by
    intro i j
    rw [Algebra.traceForm_apply, bF_apply, ← map_mul, trace_algebraMap' hgen hconst,
      ← Algebra.traceForm_apply, LinearMap.BilinForm.apply_dualBasis_left]
    split_ifs <;> simp
  have := (LinearMap.BilinForm.dualBasis_eq_iff (traceForm_nondegenerate F F')
    (bF hgen hconst pb) _).mpr key
  exact congrFun this j

end

end CFE

open IsDedekindDomain

namespace CFE

section

variable {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']

theorem mem_integralClosureAt_of_forall_mem (v : Place K F) (x : F')
    (hx : ∀ w : Place K F', w.restrict F = v → x ∈ w.toValuationSubring) :
    x ∈ integralClosure v.toValuationSubring F' := by
  have h : ∀ P : HeightOneSpectrum (Place.integralClosureAt F' v), P.valuation F' x ≤ 1 := by
    intro P
    have := hx (Place.placeOfPrime P) (Place.restrict_placeOfPrime P)
    rwa [Place.placeOfPrime_toValuationSubring,
      HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff] at this
  obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F' x h
  rw [← hc]
  exact c.2

omit [FiniteDimensional F F'] [Algebra.IsSeparable F F'] in

theorem isScalarTower_valuationSubring (v : Place K F) :
    IsScalarTower K v.toValuationSubring F' :=
  IsScalarTower.of_algebraMap_eq fun k => by
    rw [IsScalarTower.algebraMap_apply v.toValuationSubring F F',
      ← IsScalarTower.algebraMap_apply K v.toValuationSubring F,
      ← IsScalarTower.algebraMap_apply K F F']

end

section

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional K K']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']

theorem repr_mem_valuationSubring {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι F F') (e : ι → K') (hb : ∀ i, b i = algebraMap K' F' (e i))
    (d : ι → K')
    (hd : ∀ j, (Algebra.traceForm F F').dualBasis (traceForm_nondegenerate F F') b j =
      algebraMap K' F' (d j))
    (hrepr : ∀ (k : K') (i : ι), b.repr (algebraMap K' F' k) i ∈ (algebraMap K F).range)
    (v : Place K F) (x : F')
    (hx : ∀ w : Place K F', w.restrict F = v → x ∈ w.toValuationSubring) (i : ι) :
    b.repr x i ∈ v.toValuationSubring := by
  haveI := isScalarTower_valuationSubring (K := K) (F := F) (F' := F') v
  have hint : x ∈ Subalgebra.toSubmodule (integralClosure v.toValuationSubring F') :=
    mem_integralClosureAt_of_forall_mem v x hx
  have hb_int : ∀ i, IsIntegral v.toValuationSubring (b i) := fun i => by
    rw [hb]
    exact (((Algebra.IsIntegral.isIntegral (R := K) (e i)).map
      (IsScalarTower.toAlgHom K K' F')).tower_top (A := v.toValuationSubring))
  have hspan := integralClosure_le_span_dualBasis (A := v.toValuationSubring) (K := F) b hb_int
    hint
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hspan
  rw [← hc, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine sum_mem fun j _ => ?_
  rw [← IsScalarTower.algebraMap_smul F (c j), map_smul, Finsupp.smul_apply, hd,
    smul_eq_mul]
  obtain ⟨a, ha⟩ := hrepr (d j) i
  rw [← ha]
  exact mul_mem (c j).2 (v.algebraMap_mem' a)

end

end CFE

section Layer

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra F F']

variable (F F') in

def layer (K₁ : IntermediateField K K') : IntermediateField F F' :=
  IntermediateField.adjoin F (algebraMap K' F' '' (K₁ : Set K'))

variable (K₁ : IntermediateField K K')

theorem algebraMap_mem_layer (x : K₁) : algebraMap K' F' (x : K') ∈ layer F F' K₁ :=
  IntermediateField.subset_adjoin F _ ⟨x, x.2, rfl⟩

def toLayer : K₁ →+* layer F F' K₁ where
  toFun x := ⟨algebraMap K' F' (x : K'), algebraMap_mem_layer K₁ x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

scoped instance instAlgebraLayer : Algebra K₁ (layer F F' K₁) := (toLayer (F := F) (F' := F') K₁).toAlgebra

@[scoped simp]
theorem coe_algebraMap_layer (x : K₁) :
    ((algebraMap K₁ (layer F F' K₁) x : layer F F' K₁) : F') = algebraMap K' F' (x : K') :=
  rfl

variable [Algebra K F'] [IsScalarTower K K' F'] [Algebra K F] [IsScalarTower K F F']

scoped instance instIsScalarTowerLayer₁ : IsScalarTower K K₁ (layer F F' K₁) :=
  IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (by
    rw [coe_algebraMap_layer, IntermediateField.coe_algebraMap_apply,
      ← IsScalarTower.algebraMap_apply K K' F' c]
    rfl)

omit [IsScalarTower K K' F'] in
scoped instance instIsScalarTowerLayer₂ : IsScalarTower K (layer F F' K₁) F' :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem adjoin_range_layer_eq_top [Algebra.IsAlgebraic K K'] :
    Algebra.adjoin F (Set.range (algebraMap K₁ (layer F F' K₁))) = ⊤ := by
  apply Subalgebra.map_injective (f := (layer F F' K₁).val) Subtype.val_injective
  rw [← Algebra.adjoin_image, Algebra.map_top, IntermediateField.range_val]
  unfold layer
  rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic]
  · congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨algebraMap K₁ (layer F F' K₁) ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  · rintro _ ⟨x, _, rfl⟩
    exact (((Algebra.IsIntegral.isIntegral (R := K) x).map
      (IsScalarTower.toAlgHom K K' F')).tower_top (A := F)).isAlgebraic

end Layer

section Main

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']

theorem exists_finsupp_of_adjoin_eq_top
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤) (z : F') :
    ∃ l : K' →₀ F, z = l.sum fun c a => algebraMap F F' a * algebraMap K' F' c := by
  have h1 : z ∈ Subalgebra.toSubmodule (Algebra.adjoin F (Set.range (algebraMap K' F'))) := by
    rw [Subalgebra.mem_toSubmodule, hgen]
    trivial
  have h2 : Submonoid.closure (Set.range (algebraMap K' F')) =
      MonoidHom.mrange (algebraMap K' F') := by
    rw [← MonoidHom.coe_mrange, Submonoid.closure_eq]
  rw [Algebra.adjoin_eq_span, h2, MonoidHom.coe_mrange] at h1
  obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h1
  refine ⟨l, ?_⟩
  rw [← hl]
  simp only [Algebra.smul_def]

variable [Algebra.IsIntegral F F'] [HasPrincipalDivisors K' F']

theorem span_le_lSpace_pullbackConstants (D : Divisor K F) :
    Submodule.span K' (algebraMap F F' '' (LSpace D : Set F)) ≤
      LSpace (Divisor.pullbackConstants K' F' D) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  rw [SetLike.mem_coe, mem_lSpace_iff_ord] at hf ⊢
  rcases eq_or_ne f 0 with rfl | hf0
  · left
    simp
  right
  intro W
  rw [Divisor.pullbackConstants_apply, Place.ord_restrictConstants (K := K) W f, neg_mul_eq_mul_neg]
  exact mul_le_mul_of_nonneg_left ((hf.resolve_left hf0) _) (by positivity)

variable [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K']

theorem mem_span_of_mem_lSpace_pullbackConstants
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    (D : Divisor K F) {z : F'} (hz : z ∈ LSpace (Divisor.pullbackConstants K' F' D)) :
    z ∈ Submodule.span K' (algebraMap F F' '' (LSpace D : Set F)) := by
  classical
  rcases eq_or_ne z 0 with rfl | hz0
  · exact zero_mem _
  obtain ⟨l, rfl⟩ := exists_finsupp_of_adjoin_eq_top hgen z

  let K₁ : IntermediateField K K' := IntermediateField.adjoin K (l.support : Set K')
  haveI : FiniteDimensional K K₁ :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : Algebra.IsSeparable K K₁ := Algebra.isSeparable_tower_bot_of_isSeparable K K₁ K'
  set z : F' := l.sum fun c a => algebraMap F F' a * algebraMap K' F' c with hzdef
  have hzmem : z ∈ layer F F' K₁ := by
    rw [hzdef, Finsupp.sum]
    refine sum_mem fun c hc => ?_
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (algebraMap_mem_layer K₁ ⟨c, IntermediateField.subset_adjoin K _ hc⟩)
  let z₁ : layer F F' K₁ := ⟨z, hzmem⟩

  have hgen₁ := adjoin_range_layer_eq_top (F := F) (F' := F') K₁
  haveI : FiniteDimensional F (layer F F' K₁) := CFE.finiteDimensional' (K := K) hgen₁
  haveI : Algebra.IsSeparable F (layer F F' K₁) := CFE.isSeparable' hgen₁ hconst
  haveI : Algebra.IsIntegral (layer F F' K₁) F' := Algebra.IsIntegral.tower_top (R := F)
  let pb := Field.powerBasisOfFiniteOfSeparable K K₁
  let b := CFE.bF hgen₁ hconst pb

  have hcoord : ∀ i, b.repr z₁ i ∈ LSpace D := by
    intro i
    rw [mem_lSpace_iff_ord]
    refine or_iff_not_imp_left.mpr fun hy0 v => ?_
    obtain ⟨t, ht0, ht⟩ := exists_ord_eq v (D v)
    have hmem : t * b.repr z₁ i ∈ v.toValuationSubring := by
      have hrepr : b.repr (t • z₁) i = t * b.repr z₁ i := by
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      rw [← hrepr]
      refine CFE.repr_mem_valuationSubring (K := K) b pb.basis (CFE.bF_apply hgen₁ hconst pb)
        (fun j => (Algebra.traceForm K K₁).dualBasis (traceForm_nondegenerate K K₁) pb.basis j)
        (CFE.dualBasis_bF_apply hgen₁ hconst pb)
        (fun k j => RingHom.mem_range.mpr ⟨_, (CFE.bF_repr_algebraMap hgen₁ hconst pb k j).symm⟩)
        v (t • z₁) (fun w hw => ?_) i

      obtain ⟨W, hW⟩ :=
        AlgebraicCurve.Place.exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
          hgen hconst (M := layer F F' K₁) w
      rw [← hW, Place.mem_restrict_iff, IntermediateField.algebraMap_apply,
        Place.forgetConstants_toValuationSubring, IntermediateField.coe_smul, Algebra.smul_def]
      apply mem_of_ord_nonneg
      have hv : Place.restrictConstants F (K := K) W = v := by
        rw [← hw, ← hW, Place.restrictConstants, restrict_restrict]
      have htW : W.ord (algebraMap F F' t) =
          ((Place.forgetConstants (K := K) W).ramificationIndex F : ℤ) * D v := by
        rw [Place.ord_restrictConstants (K := K) W t, hv, ht]
      have hzW : -(((Place.forgetConstants (K := K) W).ramificationIndex F : ℤ) * D v) ≤
          W.ord z := by
        have := (mem_lSpace_iff_ord.mp hz).resolve_left hz0 W
        rwa [Divisor.pullbackConstants_apply, hv] at this
      have ht0' : algebraMap F F' t ≠ 0 := by simpa using ht0
      change 0 ≤ W.ord (algebraMap F F' t * (z₁ : F'))
      rw [W.ord_mul ht0' hz0, htW]
      linarith
    have h0 := ord_nonneg_of_mem v hmem
    rw [v.ord_mul ht0 hy0, ht] at h0
    linarith

  have hsum : z = ∑ i, ((pb.basis i : K₁) : K') • algebraMap F F' (b.repr z₁ i) := by
    have h1 : (z₁ : F') = z := rfl
    have h2 : (z₁ : F') = ((∑ i, b.repr z₁ i • b i : layer F F' K₁) : F') := by
      rw [b.sum_repr z₁]
    rw [← h1, h2, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IntermediateField.coe_smul, CFE.bF_apply, coe_algebraMap_layer, Algebra.smul_def,
      Algebra.smul_def, mul_comm]
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_image_of_mem _ (hcoord i)))

theorem lSpace_pullbackConstants_eq_span
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    (D : Divisor K F) :
    LSpace (Divisor.pullbackConstants K' F' D) =
      Submodule.span K' (algebraMap F F' '' (LSpace D : Set F)) :=
  le_antisymm (fun _ hz => mem_span_of_mem_lSpace_pullbackConstants hgen hconst D hz)
    (span_le_lSpace_pullbackConstants D)

end Main

end P2mConormLSpace
p2m_reactivate "P2MW.S_AlgebraicCurve_lSpace_pullbackConstants_eq_span_of_isConstantFieldExtension.P2mConormLSpace"

open P2mConormLSpace in
theorem solution
    {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K'] [Algebra.IsIntegral F F']
    [AlgebraicCurve.HasPrincipalDivisors K' F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    (D : AlgebraicCurve.Divisor K F) :
    AlgebraicCurve.LSpace (AlgebraicCurve.Divisor.pullbackConstants K' F' D) =
      Submodule.span K' (algebraMap F F' '' (AlgebraicCurve.LSpace D : Set F)) :=
  lSpace_pullbackConstants_eq_span hgen hconst D

end S_AlgebraicCurve_lSpace_pullbackConstants_eq_span_of_isConstantFieldExtension
end P2MW
export P2MW.S_AlgebraicCurve_lSpace_pullbackConstants_eq_span_of_isConstantFieldExtension (solution)
