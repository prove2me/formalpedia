-- Prove2me | solution 1 for AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/48cd0877-2c5f-5270-be78-226d12aa8af3

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finiteDimensional

set_option autoImplicit false

open Polynomial

namespace GenusCFE

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

private theorem _root_.GenusCFE.adjoin_gen_eq_top (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
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

p2m_export "GenusCFE" "adjoin_gen_eq_top"
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

theorem finrank_eq' (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range) :
    Module.finrank F F' = Module.finrank K K' := by
  rw [(pbF hgen (Field.powerBasisOfFiniteOfSeparable K K')).finrank, pbF_dim hgen hconst,
    (Field.powerBasisOfFiniteOfSeparable K K').finrank]

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

end GenusCFE

open AlgebraicCurve IsDedekindDomain

namespace GenusCFE

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

end GenusCFE

open AlgebraicCurve WithZero

namespace GenusCFE

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem finite_setOf_not_le_one_const [HasPrincipalDivisors K F] (f : F) :
    {v : Place K F | ¬ v.adicValuation f ≤ 1}.Finite := by
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  refine D.support.finite_toSet.subset fun v hv => ?_
  rw [Set.mem_setOf_eq, Place.not_adicValuation_le_one_iff] at hv
  rw [Finset.mem_coe, Finsupp.mem_support_iff, hD]
  exact hv.ne

theorem finite_setOf_not_le_one [HasPrincipalDivisors K F] {α : Place K F → F}
    (hα : α ∈ repartitions K F) :
    {v : Place K F | ¬ v.adicValuation (α v) ≤ 1}.Finite := by
  induction hα using Algebra.adjoin_induction with
  | mem x hx => exact hx
  | algebraMap f =>
    simp only [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    exact finite_setOf_not_le_one_const f
  | add x y _ _ hx hy =>
    refine (hx.union hy).subset fun v hv => ?_
    simp only [Set.mem_setOf_eq, Set.mem_union, Pi.add_apply] at hv ⊢
    by_contra h
    push Not at h
    exact hv (((v.adicValuation).map_add _ _).trans (max_le h.1 h.2))
  | mul x y _ _ hx hy =>
    refine (hx.union hy).subset fun v hv => ?_
    simp only [Set.mem_setOf_eq, Set.mem_union, Pi.mul_apply] at hv ⊢
    by_contra h
    push Not at h
    exact hv (((v.adicValuation).map_mul _ _).trans_le (mul_le_one' h.1 h.2))

theorem exists_sub_le_one (S : Finset (Place K F)) (a : Place K F → F) :
    ∃ y : F, ∀ w ∈ S, w.adicValuation (y - a w) ≤ 1 := by
  classical

  obtain ⟨M, hM0, hMle⟩ : ∃ M : ℤ, 0 < M ∧ ∀ w ∈ S, ∀ w' ∈ S, -M ≤ w.ord (a w') := by
    obtain ⟨M₀, hM₀⟩ := Finset.bddBelow
      ((S ×ˢ S).image fun p : Place K F × Place K F => p.1.ord (a p.2))
    refine ⟨max 1 (-M₀), by omega, fun w hw w' hw' => ?_⟩
    have : M₀ ≤ w.ord (a w') :=
      hM₀ (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(w, w'), Finset.mk_mem_product hw hw', rfl⟩))
    omega
  have ha : ∀ w ∈ S, ∀ w' ∈ S, w.adicValuation (a w') ≤ exp M := by
    intro w hw w' hw'
    rw [Place.adicValuation_le_exp_iff]
    exact or_iff_not_imp_left.mpr fun _ => hMle w hw w' hw'

  have he : ∀ w₀ : Place K F, ∃ e : F, w₀.adicValuation (e - 1) ≤ exp (-M) ∧
      ∀ w ∈ S, w ≠ w₀ → w.adicValuation e ≤ exp (-M) := by
    intro w₀
    obtain ⟨h, hh0, hh⟩ := AlgebraicCurve.Place.exists_forall_ord_eq (insert w₀ S)
      (fun w => if w = w₀ then M else -M)
    have hw₀ : w₀.adicValuation h = exp (-M) := by
      rw [Place.adicValuation_eq_exp_neg_ord _ hh0, hh w₀ (Finset.mem_insert_self _ _), if_pos rfl]
    have hlt : w₀.adicValuation h < 1 := by
      rw [hw₀, ← exp_zero, exp_lt_exp]; omega
    have h1h : w₀.adicValuation (1 + h) = 1 := Valuation.map_one_add_of_lt _ hlt
    have hne : 1 + h ≠ 0 := fun h0 => by
      rw [h0, map_zero] at h1h
      exact zero_ne_one h1h
    refine ⟨(1 + h)⁻¹, ?_, ?_⟩
    · have : (1 + h)⁻¹ - 1 = -h * (1 + h)⁻¹ := by field_simp; ring
      rw [this, Valuation.map_mul, Valuation.map_neg, map_inv₀, h1h, inv_one, mul_one, hw₀]
    · intro w hw hww
      have hw' : w.adicValuation h = exp M := by
        rw [Place.adicValuation_eq_exp_neg_ord _ hh0, hh w (Finset.mem_insert_of_mem hw),
          if_neg hww, neg_neg]
      have hgt : 1 < w.adicValuation h := by
        rw [hw', ← exp_zero, exp_lt_exp]; exact hM0
      rw [map_inv₀, Valuation.map_add_eq_of_lt_right _ (by rwa [Valuation.map_one]), hw',
        exp_neg]
  choose e he₁ he₂ using he
  refine ⟨∑ w' ∈ S, a w' * e w', fun w hw => ?_⟩
  have hy : (∑ w' ∈ S, a w' * e w') - a w =
      ∑ w' ∈ S, a w' * (e w' - if w' = w then 1 else 0) := by
    simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      if_pos hw]
  have hMM : exp M * exp (-M) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  rw [hy]
  refine Valuation.map_sum_le _ fun w' hw' => ?_
  rw [Valuation.map_mul, ← hMM]
  by_cases hww : w' = w
  · subst hww
    rw [if_pos rfl]
    exact mul_le_mul' (ha _ hw _ hw) (he₁ _)
  · rw [if_neg hww, sub_zero]
    exact mul_le_mul' (ha _ hw _ hw') (he₂ w' w hw (Ne.symm hww))

theorem mem_repartitionsOf_zero_iff {α : ↥(repartitions K F)} :
    α ∈ repartitionsOf (0 : Divisor K F) ↔
      ∀ v : Place K F, v.adicValuation ((α : Place K F → F) v) ≤ 1 := by
  change (∀ v : Place K F, v.adicValuation ((α : Place K F → F) v) ≤ exp ((0 : Divisor K F) v)) ↔ _
  simp only [Finsupp.coe_zero, Pi.zero_apply, exp_zero]

structure GoodBasis (K K' F F' : Type*) [Field K] [Field K'] [Field F] [Field F']
    [Algebra K' F'] [Algebra K F] [Algebra F F'] [Algebra K F'] [IsScalarTower K F F']
    [Algebra.IsIntegral F F'] (ι : Type*) where
  basis : Module.Basis ι F F'
  elt : ι → K'
  basis_eq : ∀ i, basis i = algebraMap K' F' (elt i)
  repr_mem : ∀ (v : Place K F) (x : F'),
    (∀ w : Place K F', w.restrict F = v → x ∈ w.toValuationSubring) →
      ∀ i, basis.repr x i ∈ v.toValuationSubring

section Compare

variable {K' F' : Type*} [Field K'] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']
    {ι : Type*} [Fintype ι]

theorem mem_restrictConstants_iff (w : Place K' F') (f : F) :
    f ∈ (Place.restrictConstants F (K := K) w).toValuationSubring ↔
      algebraMap F F' f ∈ w.toValuationSubring :=
  Iff.rfl

theorem restrictConstants_extendConstants [Algebra.IsIntegral K K'] (w : Place K F') :
    Place.restrictConstants F (K := K) (Place.extendConstants K' w) = w.restrict F := by
  have : Place.forgetConstants (K := K) (Place.extendConstants K' w) = w := Place.ext rfl
  rw [Place.restrictConstants, this]

namespace GoodBasis

variable (B : GoodBasis K K' F F' ι)

noncomputable def psi (α : ι → Place K F → F) (w : Place K' F') : F' :=
  ∑ i, algebraMap F F' (α i (Place.restrictConstants F (K := K) w)) * B.basis i

theorem psi_mem (α : ι → Place K F → F) (w : Place K' F')
    (h : ∀ i, α i (Place.restrictConstants F (K := K) w) ∈
      (Place.restrictConstants F (K := K) w).toValuationSubring) :
    B.psi α w ∈ w.toValuationSubring :=
  sum_mem fun i _ => mul_mem ((mem_restrictConstants_iff w _).mp (h i))
    (by rw [B.basis_eq]; exact w.algebraMap_mem' _)

theorem adicValuation_psi_le_one (α : ι → Place K F → F) (w : Place K' F')
    (h : ∀ i, (Place.restrictConstants F (K := K) w).adicValuation
      (α i (Place.restrictConstants F (K := K) w)) ≤ 1) :
    w.adicValuation (B.psi α w) ≤ 1 := by
  rw [← Place.mem_iff_adicValuation_le_one]
  exact B.psi_mem α w fun i => (Place.mem_iff_adicValuation_le_one _).mpr (h i)

theorem sub_repr_mem [Algebra.IsIntegral K K'] (α : ι → Place K F → F) (β : Place K' F' → F')
    (y : F') (hβ : ∀ w : Place K' F', w.adicValuation (β w) ≤ 1)
    (h : ∀ w, B.psi α w = β w + y) (i : ι) (v : Place K F) :
    α i v - B.basis.repr y i ∈ v.toValuationSubring := by
  have hz : B.basis.repr (∑ j, (α j v - B.basis.repr y j) • B.basis j) i =
      α i v - B.basis.repr y i :=
    congrFun (B.basis.repr_sum_self _) i
  rw [← hz]
  refine B.repr_mem v _ (fun w hw => ?_) i
  set w' := Place.extendConstants K' w with hw'
  have hrc : Place.restrictConstants F (K := K) w' = v := by
    rw [hw', restrictConstants_extendConstants, hw]
  have h1 : ∑ j, (α j v) • B.basis j = β w' + y := by
    have := h w'
    simp only [psi, hrc] at this
    simpa only [Algebra.smul_def] using this
  have h2 : ∑ j, (B.basis.repr y j) • B.basis j = y := B.basis.sum_repr y
  have hsum : ∑ j, (α j v - B.basis.repr y j) • B.basis j = β w' := by
    simp only [sub_smul, Finset.sum_sub_distrib, h1, h2, add_sub_cancel_right]
  rw [hsum]
  exact (Place.mem_iff_adicValuation_le_one w').mpr (hβ w')

variable [HasPrincipalDivisors K F] [HasPrincipalDivisors K' F']

omit [HasPrincipalDivisors K F] in
theorem psi_mem_repartitions (α : ι → Place K F → F)
    (hα : ∀ i, {v : Place K F | ¬ v.adicValuation (α i v) ≤ 1}.Finite) :
    B.psi α ∈ repartitions K' F' := by
  apply mem_repartitions_of_finite
  have hfin : (⋃ i, Place.restrictConstants (K := K) (K' := K') (F' := F') F ⁻¹'
      {v : Place K F | ¬ v.adicValuation (α i v) ≤ 1}).Finite :=
    Set.finite_iUnion fun i => (hα i).preimage' fun v _ =>
      Place.restrictConstants_fiber_finite K' v
  refine hfin.subset fun w hw => ?_
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage] at hw ⊢
  by_contra h
  push Not at h
  exact hw (B.adicValuation_psi_le_one α w h)

noncomputable def Psi : (ι → ↥(repartitions K F)) →ₗ[K] ↥(repartitions K' F') where
  toFun α := ⟨B.psi (fun i => (α i : Place K F → F)),
    B.psi_mem_repartitions _ fun i => finite_setOf_not_le_one (α i).2⟩
  map_add' α β := by
    ext w
    simp only [psi, Pi.add_apply, Subalgebra.coe_add, map_add, add_mul,
      Finset.sum_add_distrib]
  map_smul' c α := by
    ext w
    simp only [psi, Pi.smul_apply, Subalgebra.coe_smul, RingHom.id_apply]
    simp only [Algebra.smul_def, map_mul, Finset.mul_sum, ← IsScalarTower.algebraMap_apply K F F',
      mul_assoc]

@[scoped simp]
theorem coe_Psi (α : ι → ↥(repartitions K F)) :
    ((B.Psi α : ↥(repartitions K' F')) : Place K' F' → F') =
      B.psi fun i => (α i : Place K F → F) :=
  rfl

theorem Psi_mem_iff [Algebra.IsIntegral K K'] (α : ι → ↥(repartitions K F)) :
    B.Psi α ∈ repartitionsOf (0 : Divisor K' F') ⊔ principalRepartitions K' F' ↔
      ∀ i, α i ∈ repartitionsOf (0 : Divisor K F) ⊔ principalRepartitions K F := by
  constructor
  · intro h i
    obtain ⟨β, hβ, γ, hγ, hβγ⟩ := Submodule.mem_sup.mp h
    rw [mem_repartitionsOf_zero_iff] at hβ
    obtain ⟨y, hy⟩ := mem_principalRepartitions_iff.mp hγ
    have hpsi : ∀ w, B.psi (fun i => (α i : Place K F → F)) w = (β : Place K' F' → F') w + y := by
      intro w
      have := congrArg (fun δ : ↥(repartitions K' F') => (δ : Place K' F' → F') w) hβγ
      simp only [Subalgebra.coe_add, Pi.add_apply, hy, coe_Psi] at this
      exact this.symm
    refine Submodule.mem_sup.mpr ⟨α i - algebraMap F _ (B.basis.repr y i), ?_,
      algebraMap F _ (B.basis.repr y i), ?_, sub_add_cancel _ _⟩
    · rw [mem_repartitionsOf_zero_iff]
      intro v
      rw [← Place.mem_iff_adicValuation_le_one]
      simpa using B.sub_repr_mem _ _ y hβ hpsi i v
    · exact mem_principalRepartitions_iff.mpr ⟨B.basis.repr y i, rfl⟩
  · intro h
    choose β hβ γ hγ hβγ using fun i => Submodule.mem_sup.mp (h i)
    have hα : α = β + γ := funext fun i => (hβγ i).symm
    rw [hα, map_add]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [mem_repartitionsOf_zero_iff]
      intro w
      rw [coe_Psi]
      refine B.adicValuation_psi_le_one _ w fun i => ?_
      exact (mem_repartitionsOf_zero_iff.mp (hβ i)) _
    · choose f hf using fun i => mem_principalRepartitions_iff.mp (hγ i)
      rw [mem_principalRepartitions_iff]
      refine ⟨∑ i, algebraMap F F' (f i) * B.basis i, funext fun w => ?_⟩
      simp only [coe_Psi, psi, hf]

theorem exists_sub_Psi_mem (α' : ↥(repartitions K' F')) :
    ∃ α : ι → ↥(repartitions K F), α' - B.Psi α ∈ repartitionsOf (0 : Divisor K' F') := by
  classical
  set S' := (finite_setOf_not_le_one α'.2).toFinset with hS'
  set T : Finset (Place K F) :=
    S'.image (Place.restrictConstants (K := K) (K' := K') (F' := F') F) with hT
  choose Y₀ hY₀ using fun v : Place K F =>
    exists_sub_le_one (K := K') (Place.fiberConstants K' F' v) (α' : Place K' F' → F')
  let Y : Place K F → F' := fun v => if v ∈ T then Y₀ v else 0
  have hYmem : ∀ i, (fun v => B.basis.repr (Y v) i) ∈ repartitions K F := fun i => by
    apply mem_repartitions_of_finite
    refine T.finite_toSet.subset fun v hv => ?_
    by_contra hvT
    rw [Finset.mem_coe] at hvT
    apply hv
    simp [Y, hvT]
  refine ⟨fun i => ⟨_, hYmem i⟩, ?_⟩
  rw [mem_repartitionsOf_zero_iff]
  intro w
  have hsum : B.psi (fun i v => B.basis.repr (Y v) i) w =
      Y (Place.restrictConstants F (K := K) w) := by
    simp only [psi, ← Algebra.smul_def, B.basis.sum_repr]
  simp only [AddSubgroupClass.coe_sub, Pi.sub_apply, coe_Psi, hsum]
  by_cases hTw : Place.restrictConstants F (K := K) w ∈ T
  · have h1 := hY₀ (Place.restrictConstants F (K := K) w) w
      (by rw [Place.mem_fiberConstants])
    simp only [Y, if_pos hTw]
    rw [Valuation.map_sub_swap]
    exact h1
  · have hw : w ∉ S' := fun h => hTw (Finset.mem_image_of_mem _ h)
    simp only [Y, if_neg hTw, sub_zero]
    simp only [hS', Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
    exact hw

noncomputable def Phi : (ι → ↥(repartitions K F)) →ₗ[K] H1 (0 : Divisor K' F') :=
  ((repartitionsOf (0 : Divisor K' F') ⊔ principalRepartitions K' F').mkQ.restrictScalars K).comp
    B.Psi

theorem Phi_apply (α : ι → ↥(repartitions K F)) :
    B.Phi α = Submodule.Quotient.mk (B.Psi α) := rfl

theorem Phi_surjective : Function.Surjective B.Phi := by
  intro q
  obtain ⟨α', rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨α, hα⟩ := B.exists_sub_Psi_mem α'
  refine ⟨α, ?_⟩
  rw [Phi_apply, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.eq]
  exact Submodule.mem_sup_left hα

variable [Algebra.IsIntegral K K']

theorem ker_Phi : LinearMap.ker B.Phi = Submodule.pi Set.univ
    fun _ : ι => repartitionsOf (0 : Divisor K F) ⊔ principalRepartitions K F := by
  ext α
  rw [LinearMap.mem_ker, Submodule.mem_pi, Phi_apply, Submodule.Quotient.mk_eq_zero, Psi_mem_iff]
  simp

noncomputable def H1Equiv [DecidableEq ι] :
    H1 (0 : Divisor K' F') ≃ₗ[K] (ι → H1 (0 : Divisor K F)) :=
  (B.Phi.quotKerEquivOfSurjective B.Phi_surjective).symm ≪≫ₗ
    (Submodule.quotEquivOfEq _ _ B.ker_Phi) ≪≫ₗ Submodule.quotientPi _

include B in
theorem finrank_H1_eq [DecidableEq ι] :
    Module.finrank K (H1 (0 : Divisor K' F')) =
      Fintype.card ι * Module.finrank K (H1 (0 : Divisor K F)) := by
  haveI : Module.Free K (H1 (0 : Divisor K F)) := Module.Free.of_divisionRing K _
  rw [(B.H1Equiv).finrank_eq]
  simp only [Module.finrank, rank_fun_eq_lift_mul, Cardinal.toNat_mul, Cardinal.toNat_natCast,
    Cardinal.toNat_lift]

include B in

theorem genusFF_eq [FiniteDimensional K K'] [DecidableEq ι]
    (hcard : Fintype.card ι = Module.finrank K K') :
    genusFF K' F' = genusFF K F := by
  have h1 := Module.finrank_mul_finrank K K' (H1 (0 : Divisor K' F'))
  rw [B.finrank_H1_eq, hcard] at h1
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1

end GoodBasis
p2m_reactivate "P2MW.S_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finiteDimensional.GenusCFE.GoodBasis"

end Compare
p2m_reactivate "P2MW.S_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finiteDimensional.GenusCFE.GoodBasis"

end GenusCFE
p2m_reactivate "P2MW.S_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finiteDimensional.GenusCFE.GoodBasis P2MW.S_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finiteDimensional.GenusCFE"

open AlgebraicCurve in
theorem solution
    {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional K K'] [Algebra.IsSeparable K K'] [Algebra.IsIntegral F F']
    [AlgebraicCurve.IsCurveOver K F] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K' F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range) :
    AlgebraicCurve.genusFF K' F' = AlgebraicCurve.genusFF K F := by
  classical
  haveI : FiniteDimensional F F' := GenusCFE.finiteDimensional' (K := K) hgen
  haveI : Algebra.IsSeparable F F' := GenusCFE.isSeparable' hgen hconst
  let pb := Field.powerBasisOfFiniteOfSeparable K K'
  let B : GenusCFE.GoodBasis K K' F F' (Fin pb.dim) :=
    { basis := GenusCFE.bF hgen hconst pb
      elt := pb.basis
      basis_eq := GenusCFE.bF_apply hgen hconst pb
      repr_mem := fun v x hx i =>
        GenusCFE.repr_mem_valuationSubring (K := K) (GenusCFE.bF hgen hconst pb) pb.basis
          (GenusCFE.bF_apply hgen hconst pb)
          (fun j => (Algebra.traceForm K K').dualBasis (traceForm_nondegenerate K K') pb.basis j)
          (GenusCFE.dualBasis_bF_apply hgen hconst pb)
          (fun k j => RingHom.mem_range.mpr ⟨_, (GenusCFE.bF_repr_algebraMap hgen hconst pb k j).symm⟩)
          v x hx i }
  exact B.genusFF_eq (by rw [Fintype.card_fin, pb.finrank])

end S_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finiteDimensional
end P2MW
export P2MW.S_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finiteDimensional (solution)
