-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0140
-- name    : PNT_ZeroFree_433_0140
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:49:33.336741+00:00
-- url     : https://prove2.me/theorems/92771bec-a487-4fd5-b88a-216014d84c79
-- title:
--   Zero-free region foundations: Eisenstein.CompactProfiles [0140]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.CompactProfiles
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CompactProfiles.lean#L79-L687

import Definitions.Def_PNT_ZeroFree_433_0138
import Definitions.Def_PNT_ZeroFree_433_0140_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CompactProfiles.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal

lemma cosetHeight_continuous (r : CuspCosets) : Continuous (cosetHeight r) := by
  induction r using Quotient.inductionOn with
  | _ M =>
    have heq : cosetHeight (cosetOf M)=(fun w => hyperbolicHeight (complexMatrix M • w)) :=
      funext (cosetHeight_cosetOf M)
    change Continuous (cosetHeight (cosetOf M))
    rw [heq]
    exact hyperbolicHeight_continuous.comp (continuous_hyperbolic_action _)

lemma cuspCutoffCorrection_measurable (Y : ℝ) (F : ℝ → ℂ) (hF : Measurable F) :
    Measurable (cuspCutoffCorrection Y F) := by
  unfold cuspCutoffCorrection
  apply Measurable.tsum
  intro r
  apply Measurable.ite
  · exact (isOpen_lt continuous_const (cosetHeight_continuous r)).measurableSet
  · exact measurable_const.mul (hF.comp (cosetHeight_continuous r).measurable)
  · exact measurable_const


lemma smoothCuspSeedDefect_measurable (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Measurable (smoothCuspSeedDefect a b s) :=
  cuspCutoffCorrection_measurable 1 _ (cuspSeedDefectProfile_continuous a b s ha hab).measurable

lemma smoothCuspSeedDefect_bounded (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    ∃C : ℝ, 0≤C ∧ ∀w,‖smoothCuspSeedDefect a b s w‖≤C := by
  obtain ⟨C,hC⟩ := (cuspSeedDefectProfile_hasCompactSupport a b s hab).exists_bound_of_continuous
    (cuspSeedDefectProfile_continuous a b s ha hab)
  refine ⟨max C 0,le_max_right _ _,fun w => ?_⟩
  exact cuspCutoffCorrection_norm_le _ _ (le_max_right _ _) (fun v => (hC v).trans (le_max_left _ _)) w

lemma kernelQuotientDefect_measurable (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Measurable (kernelQuotientDefect a b s) :=
  measurable_from_quotient.mpr (smoothCuspSeedDefect_measurable a b s ha hab)

theorem kernelQuotientDefect_memLp (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    MemLp (kernelQuotientDefect a b s) 2 (integralQuotientVolume globalKubotaKernel) := by
  obtain ⟨C,hC,hbound⟩ := smoothCuspSeedDefect_bounded a b s ha hab
  apply MemLp.of_bound (kernelQuotientDefect_measurable a b s ha hab).aestronglyMeasurable C
  apply Filter.Eventually.of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ w => exact hbound w

def kernelL2Defect (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : KernelQuotientL2 :=
  (kernelQuotientDefect_memLp a b s ha hab).toLp (kernelQuotientDefect a b s)

lemma kernelL2Defect_ae_eq (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    kernelL2Defect a b ha hab s =ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientDefect a b s :=
  MemLp.coeFn_toLp _

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal


def kernelCompactProfile (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    IntegralOrbitQuotient globalKubotaKernel → ℂ :=
  Quotient.lift (cuspCutoffCorrection 1 (compactHeightProfile a b hab F)) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,ActualEisensteinCubic.O))).mp M.property
    have he := cuspCutoffCorrection_automorphy 1 le_rfl (compactHeightProfile a b hab F)
      (⟨(M:SL(2,ActualEisensteinCubic.O)),hM⟩ : CubicKubota.levelThree) w
    rw [hchar,one_mul] at he
    exact he.symm)

lemma kernelCompactProfile_measurable (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    Measurable (kernelCompactProfile a b hab F) :=
  measurable_from_quotient.mpr (cuspCutoffCorrection_measurable 1 _
    (compactHeightProfile_measurable a b hab F))

lemma kernelCompactProfile_norm_le (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ))
    (q : IntegralOrbitQuotient globalKubotaKernel) : ‖kernelCompactProfile a b hab F q‖≤‖F‖ := by
  induction q using Quotient.inductionOn with
  | _ w =>
    exact cuspCutoffCorrection_norm_le _ _ (norm_nonneg F)
      (compactHeightProfile_norm_le a b hab F) w

lemma kernelCompactProfile_memLp (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    MemLp (kernelCompactProfile a b hab F) 2 (integralQuotientVolume globalKubotaKernel) :=
  MemLp.of_bound (kernelCompactProfile_measurable a b hab F).aestronglyMeasurable ‖F‖
    (Filter.Eventually.of_forall (kernelCompactProfile_norm_le a b hab F))

lemma kernelCompactProfile_add (a b : ℝ) (hab : a≤b) (F G : C(Set.Icc a b,ℂ)) :
    kernelCompactProfile a b hab (F+G)=kernelCompactProfile a b hab F+kernelCompactProfile a b hab G := by
  funext q
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 _ w=_
    rw [compactHeightProfile_add,cuspCutoffCorrection_add]
    rfl

lemma kernelCompactProfile_smul (a b : ℝ) (hab : a≤b) (c : ℂ) (F : C(Set.Icc a b,ℂ)) :
    kernelCompactProfile a b hab (c • F)=c • kernelCompactProfile a b hab F := by
  funext q
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 _ w=_
    rw [compactHeightProfile_smul,cuspCutoffCorrection_smul]
    rfl

def compactProfileL2Linear (a b : ℝ) (hab : a≤b) : C(Set.Icc a b,ℂ) →ₗ[ℂ] KernelQuotientL2 where
  toFun F := (kernelCompactProfile_memLp a b hab F).toLp (kernelCompactProfile a b hab F)
  map_add' F G := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp,Lp.coeFn_add,MemLp.coeFn_toLp,MemLp.coeFn_toLp]
    rw [kernelCompactProfile_add]
  map_smul' c F := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp,Lp.coeFn_smul,MemLp.coeFn_toLp]
    rw [kernelCompactProfile_smul]
    exact Filter.Eventually.of_forall (fun _ => rfl)

lemma compactProfileL2Linear_bound (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    ‖compactProfileL2Linear a b hab F‖≤
      (measureUnivNNReal (integralQuotientVolume globalKubotaKernel) : ℝ)^((2:ℝ)⁻¹)*‖F‖ := by
  apply Lp.norm_le_of_ae_bound (norm_nonneg F)
  filter_upwards [MemLp.coeFn_toLp (kernelCompactProfile_memLp a b hab F)] with q hq
  change ‖((kernelCompactProfile_memLp a b hab F).toLp (kernelCompactProfile a b hab F)) q‖≤‖F‖
  rw [hq]
  exact kernelCompactProfile_norm_le a b hab F q

def compactProfileL2 (a b : ℝ) (hab : a≤b) : C(Set.Icc a b,ℂ) →L[ℂ] KernelQuotientL2 :=
  (compactProfileL2Linear a b hab).mkContinuous
    ((measureUnivNNReal (integralQuotientVolume globalKubotaKernel) : ℝ)^((2:ℝ)⁻¹))
    (compactProfileL2Linear_bound a b hab)

lemma compactProfileL2_ae_eq (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    compactProfileL2 a b hab F =ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelCompactProfile a b hab F :=
  MemLp.coeFn_toLp (kernelCompactProfile_memLp a b hab F)


def compactDefectSecond (a b : ℝ) : C(Set.Icc a b,ℂ) where
  toFun v := (v:ℂ)^2*((deriv (deriv (cuspTransition a b)) (v:ℝ):ℝ):ℂ)
  continuous_toFun := by
    have hd := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2
    have hdd := (contDiff_infty_iff_deriv.mp hd).2
    exact (Complex.continuous_ofReal.comp continuous_subtype_val).pow 2 |>.mul
      (Complex.continuous_ofReal.comp (hdd.continuous.comp continuous_subtype_val))

def compactDefectFirst (a b : ℝ) : C(Set.Icc a b,ℂ) where
  toFun v := (v:ℂ)*((deriv (cuspTransition a b) (v:ℝ):ℝ):ℂ)
  continuous_toFun := by
    have hd := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2
    exact (Complex.continuous_ofReal.comp continuous_subtype_val).mul
      (Complex.continuous_ofReal.comp (hd.continuous.comp continuous_subtype_val))

def compactDefectProfile (a b : ℝ) (ha : 0<a) (s : ℂ) : C(Set.Icc a b,ℂ) :=
  NormedSpace.exp (s • compactLogProfile a b ha)*
    (compactDefectSecond a b+(2*s-1) • compactDefectFirst a b)

lemma compactDefectProfile_apply (a b : ℝ) (ha : 0<a) (s : ℂ) (v : Set.Icc a b) :
    compactDefectProfile a b ha s v=cuspSeedDefectProfile a b s v := by
  have hexp := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ v)
    (continuous_eval_const v) (s • compactLogProfile a b ha)
  change (NormedSpace.exp (s • compactLogProfile a b ha)) v*
    (compactDefectSecond a b v+(2*s-1)*compactDefectFirst a b v)=_
  change (NormedSpace.exp (s • compactLogProfile a b ha)) v=
    NormedSpace.exp ((s • compactLogProfile a b ha) v) at hexp
  rw [hexp,←Complex.exp_eq_exp_ℂ]
  simp only [compactLogProfile,ContinuousMap.smul_apply,smul_eq_mul,
    compactDefectSecond,compactDefectFirst,cuspSeedDefectProfile,positiveHeightPower,
    logRatioPower,Real.log_one,sub_zero,ContinuousMap.coe_mk]
  ring

lemma compactDefectProfile_entire (a b : ℝ) (ha : 0<a) :
    Differentiable ℂ (compactDefectProfile a b ha) := by
  have he := differentiable_exp_smul_const ℂ (compactLogProfile a b ha)
  exact he.mul ((differentiable_const _).add
    (((differentiable_const (2:ℂ)).mul differentiable_id |>.sub (differentiable_const 1)).smul
      (differentiable_const (compactDefectFirst a b))))

lemma compactHeightProfile_actual_defect (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    compactHeightProfile a b hab.le (compactDefectProfile a b ha s)=cuspSeedDefectProfile a b s := by
  funext v
  by_cases hv : v∈Set.Icc a b
  · rw [compactHeightProfile,Set.indicator_of_mem hv,Set.projIcc_of_mem hab.le hv,
      compactDefectProfile_apply]
  · rw [compactHeightProfile,Set.indicator_of_notMem hv]
    have hout : v<a ∨ b<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using hv
    exact (cuspSeedDefectProfile_zero a b s v hab hout).symm

lemma compactProfileL2_actual_defect (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    compactProfileL2 a b hab.le (compactDefectProfile a b ha s)=kernelL2Defect a b ha hab s := by
  apply Lp.ext
  grw [compactProfileL2_ae_eq,kernelL2Defect_ae_eq]
  apply Filter.Eventually.of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 (compactHeightProfile a b hab.le (compactDefectProfile a b ha s)) w=
      cuspCutoffCorrection 1 (cuspSeedDefectProfile a b s) w
    rw [compactHeightProfile_actual_defect a b ha hab s]

theorem kernelL2Defect_entire (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Differentiable ℂ (kernelL2Defect a b ha hab) := by
  have heq : kernelL2Defect a b ha hab=
      fun s => compactProfileL2 a b hab.le (compactDefectProfile a b ha s) :=
    funext (fun s => (compactProfileL2_actual_defect a b ha hab s).symm)
  rw [heq]
  exact (compactProfileL2 a b hab.le).differentiable.comp (compactDefectProfile_entire a b ha)

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap ContDiff


namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label)
open JointLogSeparation (halfNormalizationCLM)
open SecondPassFiber (newRow)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondLiteralTerm (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (ell Y : ℝ) (side : Bool) (x : GlobalSecondData ι) : ℂ :=
  let X := globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon
  let m' := m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  let c := secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  (primeProductNorm p x.firstCommon : ℂ)⁻¹ *
    secondExpansionSource p hp hcop hg (globalSecondRawPool F x) Ψ m' c d ray {x.source}
      (fun A => normalizedColumn p (fun S => g₁ (columnLog p X S)) A)
      (fun A => normalizedColumn p (fun S => g₂ (columnLog p X S)) A) W Y

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] hp in
theorem globalResidualScale_eq (ell : ℝ) (side : Bool) (x : GlobalSecondData ι) :
    secondExpansionScale p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor))
      (expansionSupportData x.common x.firstDivisor x.source) = globalActualResidualScale p ell side x := by
  simp only [secondExpansionScale,expansionSupportData,primeSubsetGenerator_norm_eq_productNorm,globalActualResidualScale]
  ring

end

theorem globalSecondLiteralTerm_fixed_profiles
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU₁ : ∀ t,g₁ t ≠ 0 → U t=1) (hU₂ : ∀ t,g₂ t ≠ 0 → U t=1)
    (hg₁ : ∀ t,g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t,g₂ t ≠ 0 → |t| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ,ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t| ≤ A+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
        [∀ i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i,lambda ∉ Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hpr : ∀ i,lambda^2 ∣ p i-1)
        (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
        (ell Y : ℝ) (side : Bool) (x : GlobalSecondData ι),
        0 < ell → x.source.divisor ⊆ x.source.sourceCommon → x.source.frequency ≠ 0 →
        let j := globalScaleIndex p side x
        globalSecondLiteralTerm p hp hcop hg F Ψ m ray g₁ g₂ W ell Y side x =
          globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x *
          postCommonSmoothPair p hp hcop hg (globalSecondRawPool F x)
            (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) (globalSecondRawMask p m x)
            (globalSecondLabel p x) (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x))
            A₁ A₂ W windows (globalBinZ p ell side j x) (globalBinUd p j x)
            (globalBinUe p j x) (globalBinUv p j x) (globalBinKap p j x)
            (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j) := by
  have h1 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₁ A hg₁
  have h2 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := SecondPassIntegration.full_uniform_normalized_child_tests
    (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂) W A 6 hA (by norm_num) h1 h2
  refine ⟨A₁,A₂,windows,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hpr F Ψ m ray ell Y side x hell hE hk
  dsimp only
  let j := globalScaleIndex p side x
  let X := globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)
  let c := secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.source.divisor
  let m' := m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  have hX : 0 < X := div_pos (globalFirstColumnScale_pos p hp ell hell x side)
    (FirstPassCubeLabels.primeProductNorm_pos p hp _)
  have hr : Ideal.span {secondMaskQuotient p x.source.divisor x.source.sourceCommon hE}=Ideal.span {r} := by
    rw [secondMaskQuotient_span]
    exact (ConcretePrimeRowBridge.span_idealGenerator _).symm
  have hnorm := weighted_secondRayChild_normalized p hp hcop hg hinj hpr
    x.source.sourceCommon x.source.divisor hE (globalSecondRawPool F x) x.source.overlap Ψ Ψ
    m' c d x.source.frequency r ray hr X Y hX U hUc hUs g₁ g₂ W hU₁ hU₂
  have hscale : X/(‖ConcreteTraceCRT.eisEmbedding e‖^2*‖ConcreteTraceCRT.eisEmbedding r‖^2)=
      globalActualResidualScale p ell side x := globalResidualScale_eq p ell side x
  dsimp only at hnorm
  rw [hscale] at hnorm
  have hcoords := globalPooled_log_coordinates p hp ell hell side x hk
  have hid' := hid p hp hcop hg (globalLogRep j 5) (globalLogRep j 6) (globalLogRep j 7)
    (globalActualResidualScale p ell side x) (globalPooledColumnScale ell j) (globalLogRep j 8) Y
    (globalLogRep_pos j 5) (globalLogRep_pos j 6) (globalLogRep_pos j 7)
    (globalActualResidualScale_pos p hp ell hell side x) (globalPooledColumnScale_pos ell hell j) (globalLogRep_pos j 8)
    (globalSecondRawPool F x) x.source.overlap (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    m' r c d e x.source.frequency (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _) hk
    hcoords.1 hcoords.2.1 hcoords.2.2.1 hcoords.2.2.2.1 hcoords.2.2.2.2
  rw [hid'] at hnorm
  have hgoal := congrArg (fun z : ℂ => (primeProductNorm p x.firstCommon : ℂ)⁻¹ *
    ((Y : ℂ)*secondSourceCommonCoefficient p hg Ψ m' c d x.source.sourceCommon x.source.divisor) * z) hnorm
  have hrow : newRow (globalSecondTuple p x) = d*e*x.source.frequency := rfl
  have hlabel : globalSecondLabel p x = c*e*∏ i ∈ x.source.overlap,p i := rfl
  have hmask : globalSecondRawMask p m x = m'*r := rfl
  have hz : globalBinZ p ell side j x =
      Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j /
        globalActualResidualScale p ell side x) := rfl
  have hud : globalBinUd p j x = Real.log (SecondPassIntegration.elementNorm d/globalLogRep j 5) := rfl
  have hue : globalBinUe p j x = Real.log (SecondPassIntegration.elementNorm e/globalLogRep j 6) := rfl
  have huv : globalBinUv p j x = Real.log (primeProductNorm p x.source.overlap/globalLogRep j 7) := rfl
  have hkap : globalBinKap p j x = Real.log (SecondPassIntegration.elementNorm (d*e*x.source.frequency)/globalLogRep j 8) := rfl
  change globalSecondLiteralTerm p hp hcop hg F Ψ m ray g₁ g₂ W ell Y side x = _
  rw [hrow,hlabel,hmask,hz,hud,hue,huv,hkap]
  have hq := secondExpansionQuotient_of_subset p x.source hE
  simp only [globalSecondLiteralTerm,secondExpansionSource,Finset.sum_singleton,hq,
    globalSecondOuterWeight,secondNormalizedExpansionWeight,
    globalResidualScale_eq p ell side x,globalBinRadial,m',c,d,e,r,X,j,mul_neg,mul_assoc] at hgoal ⊢
  exact hgoal

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label)
open JointLogSeparation (halfNormalizationCLM frequencyTwist frequencyTwist_apply halfNormalization_twist)
open SecondPassFiber (newRow)

theorem globalSecondLiteralTerm_twisted_profiles
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU₁ : ∀ t,g₁ t ≠ 0 → U t=1) (hU₂ : ∀ t,g₂ t ≠ 0 → U t=1)
    (hg₁ : ∀ t,g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t,g₂ t ≠ 0 → |t| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ,ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t| ≤ A+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
        [∀ i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i,lambda ∉ Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hpr : ∀ i,lambda^2 ∣ p i-1)
        (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
        (θ₁ θ₂ ell Y : ℝ) (side : Bool) (x : GlobalSecondData ι),
        0 < ell → x.source.divisor ⊆ x.source.sourceCommon → x.source.frequency ≠ 0 →
        let j := globalScaleIndex p side x
        globalSecondLiteralTerm p hp hcop hg F Ψ m ray (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell Y side x =
          globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x *
          postCommonSmoothPair p hp hcop hg (globalSecondRawPool F x)
            (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) (globalSecondRawMask p m x)
            (globalSecondLabel p x) (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x))
            (frequencyTwist A₁ (-θ₁)) (frequencyTwist A₂ θ₂) W windows (globalBinZ p ell side j x) (globalBinUd p j x)
            (globalBinUe p j x) (globalBinUv p j x) (globalBinKap p j x)
            (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j) := by
  have h1 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₁ A hg₁
  have h2 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := SecondPassIntegration.full_uniform_twisted_normalized_child_tests
    (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂) W A 6 hA (by norm_num) h1 h2
  refine ⟨A₁,A₂,windows,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hpr F Ψ m ray θ₁ θ₂ ell Y side x hell hE hk
  dsimp only
  let j := globalScaleIndex p side x
  let X := globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)
  let c := secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.source.divisor
  let m' := m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  have hX : 0 < X := div_pos (globalFirstColumnScale_pos p hp ell hell x side)
    (FirstPassCubeLabels.primeProductNorm_pos p hp _)
  have hr : Ideal.span {secondMaskQuotient p x.source.divisor x.source.sourceCommon hE}=Ideal.span {r} := by
    rw [secondMaskQuotient_span]
    exact (ConcretePrimeRowBridge.span_idealGenerator _).symm
  have htw₁ : ∀ t, frequencyTwist g₁ θ₁ t ≠ 0 → U t = 1 := by
    intro t ht
    apply hU₁ t
    intro hz
    exact ht (by simp [frequencyTwist_apply,hz])
  have htw₂ : ∀ t, frequencyTwist g₂ θ₂ t ≠ 0 → U t = 1 := by
    intro t ht
    apply hU₂ t
    intro hz
    exact ht (by simp [frequencyTwist_apply,hz])
  have hnorm := weighted_secondRayChild_normalized p hp hcop hg hinj hpr
    x.source.sourceCommon x.source.divisor hE (globalSecondRawPool F x) x.source.overlap Ψ Ψ
    m' c d x.source.frequency r ray hr X Y hX U hUc hUs (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W htw₁ htw₂
  have hscale : X/(‖ConcreteTraceCRT.eisEmbedding e‖^2*‖ConcreteTraceCRT.eisEmbedding r‖^2)=
      globalActualResidualScale p ell side x := globalResidualScale_eq p ell side x
  dsimp only at hnorm
  rw [hscale,halfNormalization_twist U hUc hUs,halfNormalization_twist U hUc hUs] at hnorm
  have hcoords := globalPooled_log_coordinates p hp ell hell side x hk
  have hid' := hid p hp hcop hg θ₁ θ₂ (globalLogRep j 5) (globalLogRep j 6) (globalLogRep j 7)
    (globalActualResidualScale p ell side x) (globalPooledColumnScale ell j) (globalLogRep j 8) Y
    (globalLogRep_pos j 5) (globalLogRep_pos j 6) (globalLogRep_pos j 7)
    (globalActualResidualScale_pos p hp ell hell side x) (globalPooledColumnScale_pos ell hell j) (globalLogRep_pos j 8)
    (globalSecondRawPool F x) x.source.overlap (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    m' r c d e x.source.frequency (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _) hk
    hcoords.1 hcoords.2.1 hcoords.2.2.1 hcoords.2.2.2.1 hcoords.2.2.2.2
  rw [hid'] at hnorm
  have hgoal := congrArg (fun z : ℂ => (primeProductNorm p x.firstCommon : ℂ)⁻¹ *
    ((Y : ℂ)*secondSourceCommonCoefficient p hg Ψ m' c d x.source.sourceCommon x.source.divisor) * z) hnorm
  have hrow : newRow (globalSecondTuple p x) = d*e*x.source.frequency := rfl
  have hlabel : globalSecondLabel p x = c*e*∏ i ∈ x.source.overlap,p i := rfl
  have hmask : globalSecondRawMask p m x = m'*r := rfl
  have hz : globalBinZ p ell side j x =
      Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j /
        globalActualResidualScale p ell side x) := rfl
  have hud : globalBinUd p j x = Real.log (SecondPassIntegration.elementNorm d/globalLogRep j 5) := rfl
  have hue : globalBinUe p j x = Real.log (SecondPassIntegration.elementNorm e/globalLogRep j 6) := rfl
  have huv : globalBinUv p j x = Real.log (primeProductNorm p x.source.overlap/globalLogRep j 7) := rfl
  have hkap : globalBinKap p j x = Real.log (SecondPassIntegration.elementNorm (d*e*x.source.frequency)/globalLogRep j 8) := rfl
  change globalSecondLiteralTerm p hp hcop hg F Ψ m ray (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell Y side x = _
  rw [hrow,hlabel,hmask,hz,hud,hue,huv,hkap]
  have hq := secondExpansionQuotient_of_subset p x.source hE
  simp only [globalSecondLiteralTerm,secondExpansionSource,Finset.sum_singleton,hq,
    globalSecondOuterWeight,secondNormalizedExpansionWeight,
    globalResidualScale_eq p ell side x,globalBinRadial,m',c,d,e,r,X,j,mul_neg,mul_assoc] at hgoal ⊢
  exact hgoal

end SecondPassArithmetic

end

end OAI

end


