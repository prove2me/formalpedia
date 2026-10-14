-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0141
-- name    : PNT_ZeroFree_433_0141
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:53:00.560695+00:00
-- url     : https://prove2.me/theorems/5f5cf356-2cc6-462b-ba81-a78df9fa283e
-- title:
--   Zero-free region foundations: CubicSieve.LiteralSources [0141]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.LiteralSources
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/LiteralSources.lean#L85-L649

import Definitions.Def_PNT_ZeroFree_433_0140
import Definitions.Def_PNT_ZeroFree_433_0141_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/LiteralSources.lean
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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassArithmetic
open ActualEisensteinCubic
open JointLogSeparation (frequencyTwist)
open SecondPassIntegration (densityChildEnergy)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondLiteralBinSource (γ : GlobalSecondData ι → ℂ)
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (g₁ g₂ W : 𝓢(ℝ,ℂ)) (ell Y : ℝ) : ℂ :=
  ∑ ray : SecondRayIndex,∑ x∈globalLogSector p s side j,
    γ x * globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g₁ g₂ W ell Y side x

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem sum_globalArithmeticBin {M : Type*} [AddCommMonoid M]
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (f : GlobalSecondData ι → M) :
    ∑ x∈globalLogSector p s side j,f x =
    ∑ q∈globalBinTriples p s side j,∑ x∈globalArithmeticBin p s side q j,f x := by
  have h := sum_globalSecondFixedTriple p (globalLogSector p s side j) f
  simpa only [globalBinTriples,globalLogSector,globalArithmeticBin,Finset.filter_filter,and_comm] using h
end

theorem globalSecondLiteralBinSource_transfer
    (ε : ℝ) (hε : 0 < ε) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (M : ℝ) (hM : 0 ≤ M)
    (hg₁ : ∀ t,g₁ t ≠ 0 → |t| ≤ M) (hg₂ : ∀ t,g₂ t ≠ 0 → |t| ≤ M)
    (A J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C : ℝ),0 ≤ C ∧
      (∀ i,HasCompactSupport (windows i)) ∧
      (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t| ≤ M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (θ₁ θ₂ K ell B F : ℝ) (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
      (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (γ : GlobalSecondData ι → ℂ) (Γ : ℝ),
      0 < K → 0 < ell → 0 < B → 0 < F → 0 ≤ Γ → (∀ x∈s,‖γ x‖ ≤ Γ) → (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,x.source.frequency ≠ 0) →
      globalBinFirstCoefficient K ell B F j *
      ‖globalSecondLiteralBinSource p hp hcop hg γ s side j pool Ψ m
        (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell (globalPooledRowScale K ell B F j)‖ ≤
      ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalDescentWeight (Γ*C) ε θ₁ θ₂ K ell B F A J j ray q *
        (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (fixedTripleMask m q) (globalArithmeticTargets p s side q j) (windows 5) (windows 6)
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J /
          (globalPooledColumnScale ell j*globalPooledLabelScale j)) := by
  obtain ⟨U,hUc,hUs,hUone,hUsupp,hUzero⟩ := FourierBridge.exists_complex_smooth_cutoff M hM
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := globalSecondLiteralTerm_twisted_profiles U hUc hUs
    g₁ g₂ W M hM (fun t ht => hUone t (hg₁ t ht)) (fun t ht => hUone t (hg₂ t ht)) hg₁ hg₂
  obtain ⟨C,hC,htrans⟩ := weightedGlobalPositiveBin_transfer ε hε A₁ A₂ W windows
    (fun _ => M+6+1) (fun _ => by linarith) hwb hwc (fun i => (hws i).continuous) A J
  refine ⟨windows,C,hC,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr θ₁ θ₂ K ell B F s side j pool Ψ m γ Γ hK hell hB hF hΓ hγ hΨ hs hk
  have heq : globalSecondLiteralBinSource p hp hcop hg γ s side j pool Ψ m
      (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell (globalPooledRowScale K ell B F j) =
      ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        weightedGlobalArithmeticBinSource p hp hcop hg γ s side q j pool Ψ m ray
          (frequencyTwist A₁ (-θ₁)) (frequencyTwist A₂ θ₂) W windows ell (globalPooledRowScale K ell B F j) := by
    unfold globalSecondLiteralBinSource
    apply Finset.sum_congr rfl
    intro ray hray
    rw [sum_globalArithmeticBin p s side j]
    apply Finset.sum_congr rfl
    intro q hq
    unfold weightedGlobalArithmeticBinSource globalSecondRawSource
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨hxs,hxq,hxj⟩ := Finset.mem_filter.mp hx
    have h := hid p hp hcop hg hinj hpr pool Ψ m ray θ₁ θ₂ ell
      (globalPooledRowScale K ell B F j) side x hell (hs x hxs).2.1 (hk x hxs)
    dsimp only at h
    rw [hxj] at h
    rw [h,mul_assoc]
  rw [heq]
  simpa only [globalDescentWeight,norm_neg] using
    htrans p hp hcop hg hinj hc (-θ₁) θ₂ K ell B F s side j pool Ψ m γ Γ
      hK hell hB hF hΓ hγ hΨ hs hk

end SecondPassArithmetic

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise

local notation "O" => ActualEisensteinCubic.O


instance integralSubgroupContinuousAction (H : Subgroup (SL(2,O))) :
    ContinuousConstSMul H HyperbolicSpace :=
  ⟨fun M => continuous_hyperbolic_action (integralComplexMatrix (M:SL(2,O)))⟩

instance integralSubgroupProperlyDiscontinuous (H : Subgroup (SL(2,O))) :
    ProperlyDiscontinuousSMul H HyperbolicSpace where
  finite_disjoint_inter_image := by
    intro source target hsource htarget
    obtain ⟨C,hC⟩ := hsource.exists_bound_of_continuousOn hyperbolicFrobenius_continuous.continuousOn
    obtain ⟨D,hD⟩ := htarget.exists_bound_of_continuousOn hyperbolicFrobenius_continuous.continuousOn
    have hfin : Set.Finite {M : H | matrixFrobenius (integralComplexMatrix (M:SL(2,O)))≤
        max D 0*max C 0} := by
      have hf := Set.Finite.preimage (f := fun M : H => (M:SL(2,O))) Subtype.val_injective.injOn
        (integral_frobenius_sublevel_finite 1 (max D 0*max C 0))
      simpa only [mul_one,Set.preimage_ofPred_eq] using hf
    apply hfin.subset
    rintro M ⟨u,⟨w,hw,rfl⟩,hu⟩
    have hb := matrixFrobenius_le_displacement (integralComplexMatrix (M:SL(2,O))) w
    apply hb.trans
    apply mul_le_mul
    · exact ((le_abs_self _).trans (hD _ hu)).trans (le_max_left _ _)
    · exact ((le_abs_self _).trans (hC _ hw)).trans (le_max_left _ _)
    · exact hyperbolicFrobenius_nonneg _
    · exact le_max_right _ _

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise

namespace CubicEisenstein

section
local notation "O" => ActualEisensteinCubic.O


instance hyperbolicLocallyCompact : LocallyCompactSpace HyperbolicSpace :=
  upperCoordinatesHomeomorph.symm.isOpenEmbedding.locallyCompactSpace
instance hyperbolicSecondCountable : SecondCountableTopology HyperbolicSpace :=
  upperCoordinatesHomeomorph.symm.secondCountableTopology


instance hyperbolicPolish : PolishSpace HyperbolicSpace :=
  upperCoordinatesHomeomorph.symm.isClosedEmbedding.polishSpace

lemma integralOrbitRel_eq (H : Subgroup (SL(2,O))) :
    integralOrbitRel H=MulAction.orbitRel H HyperbolicSpace := by
  ext u v
  change (∃M:H,M • u=v) ↔ ∃M:H,M • v=u
  constructor
  · rintro ⟨M,hM⟩
    exact ⟨M⁻¹,by rw [←hM,inv_smul_smul]⟩
  · rintro ⟨M,hM⟩
    exact ⟨M⁻¹,by rw [←hM,inv_smul_smul]⟩

instance integralOrbitQuotientT2 (H : Subgroup (SL(2,O))) : T2Space (IntegralOrbitQuotient H) := by
  change T2Space (Quotient (integralOrbitRel H))
  rw [integralOrbitRel_eq]
  infer_instance

lemma integralSubgroupFree (H : Subgroup (SL(2,O))) (hH : H≤CubicKubota.levelThree) :
    IsCancelSMul H HyperbolicSpace :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr (subgroup_action_free H hH)

lemma integralOrbitProjection_eq_iff (H : Subgroup (SL(2,O))) (u v : HyperbolicSpace) :
    integralOrbitProjection H u=integralOrbitProjection H v ↔ u∈MulAction.orbit H v := by
  constructor
  · intro he
    obtain ⟨M,hM⟩ := Quotient.exact he.symm
    exact ⟨M,hM⟩
  · rintro ⟨M,hM⟩
    apply Eq.symm
    apply Quotient.sound
    exact ⟨M,hM⟩

theorem integralOrbitProjection_quotientCovering (H : Subgroup (SL(2,O)))
    (hH : H≤CubicKubota.levelThree) : IsQuotientCoveringMap (integralOrbitProjection H) H := by
  let : IsCancelSMul H HyperbolicSpace := integralSubgroupFree H hH
  have hq : Topology.IsQuotientMap (integralOrbitProjection H) := isQuotientMap_quotient_mk'
  exact hq.isQuotientCoveringMap_of_properlyDiscontinuousSMul (integralOrbitProjection_eq_iff H _ _)

lemma integralOrbitProjection_covering (H : Subgroup (SL(2,O))) (hH : H≤CubicKubota.levelThree) :
    IsCoveringMap (integralOrbitProjection H) :=
  (integralOrbitProjection_quotientCovering H hH).isCoveringMap

lemma integralOrbitProjection_openQuotient (H : Subgroup (SL(2,O))) (hH : H≤CubicKubota.levelThree) :
    IsOpenQuotientMap (integralOrbitProjection H) :=
  ⟨Quotient.mk_surjective,continuous_integralOrbitProjection H,
    (integralOrbitProjection_covering H hH).isOpenMap⟩

instance kernelQuotientLocallyCompact : LocallyCompactSpace (IntegralOrbitQuotient globalKubotaKernel) :=
  (integralOrbitProjection_openQuotient globalKubotaKernel globalKubotaKernel_le_levelThree).locallyCompactSpace
instance kernelQuotientSecondCountable : SecondCountableTopology (IntegralOrbitQuotient globalKubotaKernel) :=
  (integralOrbitProjection_openQuotient globalKubotaKernel globalKubotaKernel_le_levelThree).isQuotientMap.secondCountableTopology
    (integralOrbitProjection_openQuotient globalKubotaKernel globalKubotaKernel_le_levelThree).isOpenMap

instance kernelQuotientBorel : BorelSpace (IntegralOrbitQuotient globalKubotaKernel) :=
  Quotient.borelSpace

lemma kernelQuotient_localHomeomorph : IsLocalHomeomorph (integralOrbitProjection globalKubotaKernel) :=
  (integralOrbitProjection_covering globalKubotaKernel globalKubotaKernel_le_levelThree).isLocalHomeomorph

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal

lemma integralOrbitProjection_preimage_image (H : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (S : Set HyperbolicSpace) :
    integralOrbitProjection H ⁻¹' (integralOrbitProjection H '' S)=⋃M:H,M • S := by
  ext w
  constructor
  · rintro ⟨u,hu,he⟩
    obtain ⟨M,hM⟩ := (integralOrbitProjection_eq_iff H w u).mp he.symm
    exact Set.mem_iUnion.mpr ⟨M,⟨u,hu,hM⟩⟩
  · intro hw
    obtain ⟨M,u,hu,rfl⟩ := Set.mem_iUnion.mp hw
    exact ⟨u,hu,(integralOrbitProjection_eq H M u).symm⟩

lemma kernelProjection_translates_disjoint (S : Set HyperbolicSpace)
    (hS : Set.InjOn (integralOrbitProjection globalKubotaKernel) S) :
    Pairwise (fun M N : globalKubotaKernel => Disjoint (M • S) (N • S)) := by
  let : IsCancelSMul globalKubotaKernel HyperbolicSpace :=
    integralSubgroupFree globalKubotaKernel globalKubotaKernel_le_levelThree
  intro M N hMN
  apply Set.disjoint_left.mpr
  rintro _ ⟨w,hw,rfl⟩ ⟨u,hu,he⟩
  have hwu : w=u := hS hw hu (by
    calc
      integralOrbitProjection globalKubotaKernel w=
          integralOrbitProjection globalKubotaKernel (M • w) := (integralOrbitProjection_eq _ M w).symm
      _=integralOrbitProjection globalKubotaKernel (N • u) := congrArg _ he.symm
      _=integralOrbitProjection globalKubotaKernel u := integralOrbitProjection_eq _ N u)
  subst u
  exact hMN (IsCancelSMul.right_cancel M N w he.symm)

theorem kernelProjection_measure_image (S : Set HyperbolicSpace) (hS : MeasurableSet S)
    (hinj : Set.InjOn (integralOrbitProjection globalKubotaKernel) S) :
    integralQuotientVolume globalKubotaKernel (integralOrbitProjection globalKubotaKernel '' S)=
      hyperbolicVolume S := by
  have himg := hS.image_of_continuousOn_injOn
    (continuous_integralOrbitProjection globalKubotaKernel).continuousOn hinj
  rw [integralQuotientVolume,Measure.map_apply (measurable_integralOrbitProjection _) himg,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) himg),
    integralOrbitProjection_preimage_image,Set.iUnion_inter]
  rw [measure_iUnion]
  · exact (globalKubotaKernel_isFundamentalDomain.measure_eq_tsum S).symm
  · intro M N hMN
    exact (kernelProjection_translates_disjoint S hinj hMN).mono Set.inter_subset_left Set.inter_subset_left
  · intro M
    exact (hS.const_smul M).inter (hyperbolicFundamentalSet_measurable _)

theorem kernelProjection_measurePreserving_on (U : Set HyperbolicSpace) (hU : MeasurableSet U)
    (hinj : Set.InjOn (integralOrbitProjection globalKubotaKernel) U) :
    MeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict U)
      ((integralQuotientVolume globalKubotaKernel).restrict (integralOrbitProjection globalKubotaKernel '' U)) := by
  refine ⟨measurable_integralOrbitProjection _,?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_integralOrbitProjection _) hB,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) hB),Measure.restrict_apply hB]
  have hset : B∩(integralOrbitProjection globalKubotaKernel '' U)=
      integralOrbitProjection globalKubotaKernel '' (integralOrbitProjection globalKubotaKernel ⁻¹' B∩U) := by
    ext q
    constructor
    · rintro ⟨hq,w,hw,rfl⟩
      exact ⟨w,⟨hq,hw⟩,rfl⟩
    · rintro ⟨w,⟨hw,hu⟩,rfl⟩
      exact ⟨hw,⟨w,hu,rfl⟩⟩
  rw [hset,kernelProjection_measure_image _ (((measurable_integralOrbitProjection _) hB).inter hU)
    (hinj.mono Set.inter_subset_right)]

theorem kernelL2_continuous_compact_approx (f : KernelQuotientL2) (ε : ℝ≥0∞) (hε : ε≠0) :
    ∃g : IntegralOrbitQuotient globalKubotaKernel → ℂ,
      HasCompactSupport g ∧ eLpNorm ((f : _ → ℂ)-g) 2 (integralQuotientVolume globalKubotaKernel)≤ε ∧
      Continuous g ∧ MemLp g 2 (integralQuotientVolume globalKubotaKernel) := by
  exact (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hε

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label)


variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})


theorem globalFirstTruncatedSource_eq_literal
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    globalFirstTruncatedSource p hp hg hinj pool s w cutoff Ψ m g W ell side Y =
      ∑ ray : SecondRayIndex,∑ x∈globalFirstExpansionPool pool s cutoff,
        w x.first*globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell (Y x.first) side x := by
  unfold globalFirstTruncatedSource
  simp_rw [truncatedSecondSource_eq_expansionPool p hp hcop hg hinj hc hpr]
  rw [Finset.sum_comm]
  simp_rw [sum_globalFirstExpansionPool]
  apply Finset.sum_congr rfl
  intro b hb
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ray hray
  unfold secondExpansionSource
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [globalSecondLiteralTerm,GlobalFirstData.append,GlobalSecondData.first,
    globalSecondRawPool,globalFirstRawPool,globalFirstBlockBadLabel,globalFirstBlockLabel,
    globalFirstBlockTest,globalFirstBlockColumnScale,globalFirstColumnScale,
    secondExpansionSource,Finset.sum_singleton,mul_assoc]

end


end SecondPassArithmetic

end

end OAI

end


