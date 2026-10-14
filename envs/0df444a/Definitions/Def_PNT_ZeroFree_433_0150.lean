-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0150
-- name    : PNT_ZeroFree_433_0150
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:19:22.111931+00:00
-- url     : https://prove2.me/theorems/5cbde062-dbfd-40b5-8ee5-2da567afe3b2
-- title:
--   Zero-free region foundations: CubicSieve.RowCaps [0150]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.RowCaps
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/RowCaps.lean#L82-L692

import Definitions.Def_PNT_ZeroFree_433_0147
import Definitions.Def_PNT_ZeroFree_433_0149
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/RowCaps.lean
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

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)


variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalFirstPooledRow_le_cap (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (b : GlobalCubeBlock ι) (hadm : GlobalCubeAdmissible b)
    (hb₁ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) :
    globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤globalFirstRowCap K ell B F := by
  let x := (b.withCommon ∅).append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p true x
  have hbds := globalScaleIndex_bounds p hp true x (by exact one_ne_zero)
  have hd := (hbds 5).1
  have hc := (hbds 1).2
  change globalLogRep j 5≤primeProductNorm p b.firstDivisor at hd
  change primeProductNorm p b.common≤globalLogRep j 1*Real.exp 1 at hc
  have hrad := globalCube_radical_bound p hp B hB.le x hb₁ hb₂
  have h1p := globalLogRep_pos j 1
  have hd' : globalLogRep j 5≤globalLogRep j 1*Real.exp 1*B^2 := by
    calc
      _ ≤ primeProductNorm p b.firstDivisor := hd
      _ ≤ primeProductNorm p (b.common∪b.cube.support) := primeProductNorm_mono p hp hadm.2.2
      _ = primeProductNorm p b.common*primeProductNorm p b.cube.support :=
        FirstPassCubeLabels.primeProductNorm_union p _ _ hadm.2.1
      _ ≤ (globalLogRep j 1*Real.exp 1)*B^2 :=
        mul_le_mul hc hrad (FirstPassCubeLabels.primeProductNorm_pos p hp _).le (by positivity)
  have h1 := globalLogRep_ge_one j 1
  have h4 := globalLogRep_ge_one j 4
  have h4p := globalLogRep_pos j 4
  have hm : globalLogRep j 1≤(globalLogRep j 1)^2*globalLogRep j 4 := by
    calc
      globalLogRep j 1 = globalLogRep j 1*1*1 := by ring
      _ ≤ globalLogRep j 1*globalLogRep j 1*globalLogRep j 4 := by gcongr
      _ = _ := by ring
  have hr : globalLogRep j 5/((globalLogRep j 1)^2*globalLogRep j 4)≤Real.exp 1*B^2 := by
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos h1p) h4p)).mpr
    calc
      _ ≤ globalLogRep j 1*Real.exp 1*B^2 := hd'
      _ ≤ ((globalLogRep j 1)^2*globalLogRep j 4)*Real.exp 1*B^2 := by gcongr
      _ = _ := by ring
  change Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)≤_
  calc
    _ = (Real.exp 1*ell^2*B^4*F^2/K)*(globalLogRep j 5/((globalLogRep j 1)^2*globalLogRep j 4)) := by ring
    _ ≤ (Real.exp 1*ell^2*B^4*F^2/K)*(Real.exp 1*B^2) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = globalFirstRowCap K ell B F := by unfold globalFirstRowCap; ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem globalTwoPassage_original_ranges
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Ct₁ C₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Ct₂ ∧
      (∀ i,HasCompactSupport (windows₁ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀ i t,windows₁ i t≠0 → |t|≤M₁+6+1) ∧
      (∀ i,HasCompactSupport (windows₂ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀ i t,windows₂ i t≠0 → |t|≤M₂+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ K ell B F H : ℝ),
      0≤Γ → 0<K → 0<ell → 0<B → 0<F → 0≤H →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,(Ideal.absNorm x.1 : ℝ)≤F) →
      (∀ b∈blocks,∀ x∈s b,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,globalCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstFamilyBudget p hp hcop hg pool blocks w Ψ₁ m₁ g₁ V₁ windows₁ C₁ Ct₁ Γ ε K ell B F M₁ H A J N true) *
        Real.sqrt (globalFirstFamilyBudget p hp hcop hg pool blocks w Ψ₂ m₂ g₂ V₂ windows₂ C₂ Ct₂ Γ ε K ell B F M₂ H A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Ct₁,C₂,Ct₂,hCfirst,hC₁,hCt₁,hC₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,htransfer⟩ :=
    globalTwoPassage_transfer W g₁ g₂ V₁ V₂ M₁ M₂ N₁ N₂ hM₁ hM₂ hN₁ hN₂ hg₁ hg₂ hV₁ hV₂ ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Ct₁,C₂,Ct₂,hCfirst,hC₁,hCt₁,hC₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H
    hΓ hK hell hB hF hH hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hsf hs0 hf hh
  exact htransfer p hp hinj hcop hg hc hpr pool blocks s a w
    (fun b => globalCubeFirstTargets p b (s b)) Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H (globalFirstRowCap K ell B F)
    hΓ hK hell hB hF hH (globalFirstRowCap_pos K ell B F hK hell hB hF).le hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂
    (fun b hb => globalFirstPooledRow_le_cap p hp K ell B F hK hell hB hF b (hadm b hb) (hb₁ b hb) (hb₂ b hb))
    hsf hs0
    (fun b _ x hx => globalCubeFirstTargets_mem p b (s b) x hx)
    (fun b hb z hz => globalCubeFirstTargets_ne_zero p hp b (s b) (hsf b hb) (hs0 b hb) z hz)
    (fun b hb z hz => globalCubeFirstTargets_norm_bound p hp b (s b) K ell B F hK hell hB hF
      (hb₁ b hb) (hb₂ b hb) (hf b hb) (hh b hb) z hz)

end SecondPassArithmetic

open scoped BigOperators Classical


namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss

theorem product_quadratic_norm_scaled (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀K U B lengthScale : ℝ,1≤K → 1≤U → 1≤B → 0≤lengthScale →
    ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : Ideal O→Ideal O→ℂ,(∀n∈S,∀b∈T,‖β n b‖≤lengthScale) →
      (∑k : idealRange K,‖∑n∈S,∑b∈T,
        quadraticRow k.val (primaryGenerator (n*b))*β n b‖^2)≤
      C*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2 := by
  obtain ⟨C,hC,hbound⟩ := product_quadratic_norm_all ε hε
  refine ⟨C,hC,?_⟩
  intro K U B lengthScale hK hU hB hL S T hS hT β hβ
  by_cases hL0 : lengthScale=0
  · have hz n hn b hb : β n b=0 := norm_eq_zero.mp (le_antisymm (by simpa [hL0] using hβ n hn b hb) (norm_nonneg _))
    simp only [hL0,pow_two,mul_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro k _
    have hh : (∑n∈S,∑b∈T,quadraticRow k.val (primaryGenerator (n*b))*β n b)=0 := by
      apply Finset.sum_eq_zero
      intro n hn
      apply Finset.sum_eq_zero
      intro b hb
      rw [hz n hn b hb,mul_zero]
    rw [hh,norm_zero,zero_mul]
  have hLp : 0<lengthScale := lt_of_le_of_ne hL (Ne.symm hL0)
  have hLc : (lengthScale:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hL0
  let γ : Ideal O→Ideal O→ℂ := fun n b => β n b/(lengthScale:ℂ)
  have hγ (n : Ideal O) (hn : n∈S) (b : Ideal O) (hb : b∈T) : ‖γ n b‖≤1 := by
    dsimp [γ]
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hL]
    exact (div_le_one hLp).mpr (hβ n hn b hb)
  have hb := hbound K U B hK hU hB S T hS hT γ hγ
  have he (k : idealRange K) :
      (∑n∈S,∑b∈T,quadraticRow k.val (primaryGenerator (n*b))*β n b)=
      (lengthScale:ℂ)*(∑n∈S,∑b∈T,quadraticRow k.val (primaryGenerator (n*b))*γ n b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    dsimp [γ]
    field_simp
  simp_rw [he,norm_mul,Complex.norm_real,Real.norm_of_nonneg hL,mul_pow]
  rw [←Finset.mul_sum]
  calc
    _ ≤ lengthScale^2*(C*(K*(U*B))^ε*(K+U*B)*(U*B)) := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by ring

theorem completed_quadratic_dyad (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀K U B r S₀ E : ℝ,
      1≤K → 1≤U → 1≤B → 0<r → 0<S₀ → 0<E →
    ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : Ideal O→Ideal O→ℂ,
      (∀n∈S,∀b∈T,‖β n b‖≤1/(Real.sqrt U*B*r*Real.sqrt (S₀*E))) →
      (∑k : idealRange K,‖∑n∈S,∑b∈T,
        quadraticRow k.val (primaryGenerator (n*b))*β n b‖^2)≤
      C*(K*(U*B))^ε*(K+U*B)/(B*r^2*S₀*E) := by
  obtain ⟨C,hC,hbound⟩ := product_quadratic_norm_scaled ε hε
  refine ⟨C,hC,?_⟩
  intro K U B r S₀ E hK hU hB hr hS₀ hE S T hS hT β hβ
  apply (hbound K U B _ hK hU hB (by positivity) S T hS hT β hβ).trans
  apply le_of_eq
  have hU0 : U≠0 := by linarith
  have hB0 : B≠0 := by linarith
  have hr0 := ne_of_gt hr
  have hS0 := ne_of_gt hS₀
  have hE0 := ne_of_gt hE
  simp only [one_div,inv_pow,mul_pow,Real.sq_sqrt (show 0≤U by linarith),
    Real.sq_sqrt (show 0≤S₀*E by positivity)]
  field_simp

end CanonicalQuadraticSieve

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff

namespace CubicEisenstein


lemma mobiusSpatial_coordinates (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2) :
    hyperbolicSpatialCoordinates (g • upperPoint (spatialHorizontal p) (p 2) hp)=mobiusSpatial g p := by
  rw [mobius_upperPoint]
  simp only [hyperbolicSpatialCoordinates,hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint,
    mobiusSpatial,mobiusSpatialHorizontal,mobiusSpatialDenominator,Complex.normSq_eq_norm_sq]


def positiveSpatialHomeomorph : PositiveSpatial ≃ₜ HyperbolicSpace :=
  positiveSpatialUpperHomeomorph.trans upperCoordinatesHomeomorph

lemma hyperbolicSpatial_isOpenEmbedding : Topology.IsOpenEmbedding hyperbolicSpatialCoordinates := by
  have ho : IsOpen {p : SpatialCoordinates | 0<p 2} := isOpen_lt continuous_const (by fun_prop)
  have he := ho.isOpenEmbedding_subtypeVal.comp positiveSpatialHomeomorph.symm.isOpenEmbedding
  exact he

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff Manifold

namespace CubicEisenstein

abbrev KernelQuotient := IntegralOrbitQuotient globalKubotaKernel

def hyperbolicSpatialChart : OpenPartialHomeomorph HyperbolicSpace SpatialCoordinates :=
  hyperbolicSpatial_isOpenEmbedding.toOpenPartialHomeomorph hyperbolicSpatialCoordinates

@[simp] lemma hyperbolicSpatialChart_apply (w : HyperbolicSpace) :
    hyperbolicSpatialChart w=hyperbolicSpatialCoordinates w := rfl

@[simp] lemma hyperbolicSpatialChart_source : hyperbolicSpatialChart.source=Set.univ := rfl

lemma hyperbolicSpatialChart_target_positive {p : SpatialCoordinates}
    (hp : p∈hyperbolicSpatialChart.target) : 0<p 2 := by
  have he := hyperbolicSpatialChart.right_inv hp
  have hh := hyperbolicSpatialCoordinates_positive (hyperbolicSpatialChart.symm p)
  rwa [← hyperbolicSpatialChart_apply,he] at hh

def kernelLocalLift (w : HyperbolicSpace) : OpenPartialHomeomorph KernelQuotient HyperbolicSpace :=
  kernelQuotient_localHomeomorph.localInverseAt w

@[simp] lemma kernelLocalLift_symm (w : HyperbolicSpace) :
    (kernelLocalLift w).symm=integralOrbitProjection globalKubotaKernel :=
  kernelQuotient_localHomeomorph.localInverseAt_symm w

lemma kernelLocalLift_project {w : HyperbolicSpace} {q : KernelQuotient}
    (hq : q∈(kernelLocalLift w).source) :
    integralOrbitProjection globalKubotaKernel (kernelLocalLift w q)=q :=
  kernelQuotient_localHomeomorph.apply_localInverseAt_of_mem hq

lemma kernel_lifts_eventually_eq {X : Type*} [TopologicalSpace X]
    {f g : X→HyperbolicSpace} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hfg : f x=g x)
    (hproj : (fun y => integralOrbitProjection globalKubotaKernel (f y))=ᶠ[𝓝 x]
      (fun y => integralOrbitProjection globalKubotaKernel (g y))) : f=ᶠ[𝓝 x]g := by
  obtain ⟨U,hU,hx,hUinj⟩ := kernelQuotient_localHomeomorph.isLocallyInjective (f x)
  have hfn : ∀ᶠ y in 𝓝 x,f y∈U := hf (hU.mem_nhds hx)
  have hgn : ∀ᶠ y in 𝓝 x,g y∈U := hg (hU.mem_nhds (hfg ▸ hx))
  filter_upwards [hfn,hgn,hproj] with y hyf hyg hye
  exact hUinj hyf hyg hye

lemma kernel_lifts_eventually_deck {X : Type*} [TopologicalSpace X]
    {f g : X→HyperbolicSpace} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hproj : (fun y => integralOrbitProjection globalKubotaKernel (f y))=ᶠ[𝓝 x]
      (fun y => integralOrbitProjection globalKubotaKernel (g y))) :
    ∃M : globalKubotaKernel, f=ᶠ[𝓝 x](fun y => integralComplexMatrix M • g y) := by
  have he := (integralOrbitProjection_eq_iff globalKubotaKernel (f x) (g x)).mp
    hproj.self_of_nhds
  obtain ⟨M,hM⟩ := MulAction.mem_orbit_iff.mp he
  refine ⟨M,kernel_lifts_eventually_eq hf
    ((continuous_hyperbolic_action (integralComplexMatrix M)).continuousAt.comp hg) hM.symm ?_⟩
  filter_upwards [hproj] with y hy
  simpa only [integralOrbitProjection_eq] using hy

lemma mobiusSpatial_coordinates_global (g : SL(2,ℂ)) (w : HyperbolicSpace) :
    hyperbolicSpatialCoordinates (g•w)=mobiusSpatial g (hyperbolicSpatialCoordinates w) := by
  have hp := hyperbolicSpatialCoordinates_positive w
  have hr := hyperbolicSpatialCoordinates_reconstruct w
  nth_rw 1 [← hr]
  exact mobiusSpatial_coordinates g (hyperbolicSpatialCoordinates w) hp

def kernelCoordinateTransition (w : HyperbolicSpace) (p : SpatialCoordinates) : SpatialCoordinates :=
  hyperbolicSpatialCoordinates (kernelLocalLift w
    (integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)))

lemma kernelCoordinateTransition_eventually (w : HyperbolicSpace) (p : SpatialCoordinates)
    (hp : p∈hyperbolicSpatialChart.target)
    (hq : integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)∈
      (kernelLocalLift w).source) :
    ∃M : globalKubotaKernel,kernelCoordinateTransition w=ᶠ[𝓝 p]
      mobiusSpatial (integralComplexMatrix M) := by
  have hc : ContinuousAt hyperbolicSpatialChart.symm p :=
    hyperbolicSpatialChart.symm.continuousAt hp
  have hπ : ContinuousAt (fun y => integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm y)) p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp hc
  have hl : ContinuousAt (fun y => kernelLocalLift w (integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm y))) p :=
    ((kernelLocalLift w).continuousAt hq).comp
      (f := fun y : SpatialCoordinates => integralOrbitProjection globalKubotaKernel
        (hyperbolicSpatialChart.symm y)) hπ
  have hqn : ∀ᶠ y in 𝓝 p,integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm y)∈(kernelLocalLift w).source :=
    hπ ((kernelLocalLift w).open_source.mem_nhds hq)
  have hproj : (fun y => integralOrbitProjection globalKubotaKernel (kernelLocalLift w
      (integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm y))))=ᶠ[𝓝 p]
      (fun y => integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm y)) := by
    filter_upwards [hqn] with y hy
    exact kernelLocalLift_project hy
  obtain ⟨M,hM⟩ := kernel_lifts_eventually_deck hl hc hproj
  refine ⟨M,?_⟩
  filter_upwards [hM,hyperbolicSpatialChart.open_target.mem_nhds hp] with y hy hyt
  change hyperbolicSpatialCoordinates _=mobiusSpatial _ y
  rw [hy,mobiusSpatial_coordinates_global]
  exact congrArg _ (hyperbolicSpatialChart.right_inv hyt)

lemma kernelCoordinateTransition_contDiffAt (w : HyperbolicSpace) (p : SpatialCoordinates)
    (hp : p∈hyperbolicSpatialChart.target)
    (hq : integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)∈
      (kernelLocalLift w).source) : ContDiffAt ℝ ∞ (kernelCoordinateTransition w) p := by
  obtain ⟨M,hM⟩ := kernelCoordinateTransition_eventually w p hp hq
  exact (mobiusSpatial_contDiffAt _ p (hyperbolicSpatialChart_target_positive hp)).congr_of_eventuallyEq hM

def kernelQuotientChart (q : KernelQuotient) : OpenPartialHomeomorph KernelQuotient SpatialCoordinates :=
  (kernelLocalLift q.out).trans hyperbolicSpatialChart

@[simp] lemma kernelQuotientChart_symm (q : KernelQuotient) (p : SpatialCoordinates) :
    (kernelQuotientChart q).symm p=
      integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p) := by
  change (kernelLocalLift q.out).symm (hyperbolicSpatialChart.symm p)=_
  rw [kernelLocalLift_symm]

lemma kernelQuotientChart_contDiffOn (q r : KernelQuotient) :
    ContDiffOn ℝ ∞ ((kernelQuotientChart q).symm.trans (kernelQuotientChart r))
      ((kernelQuotientChart q).symm.trans (kernelQuotientChart r)).source := by
  intro p hp
  have hp' : p∈hyperbolicSpatialChart.target := hp.1.1
  have hq' : integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)∈
      (kernelLocalLift r.out).source := by
    rw [← kernelQuotientChart_symm q p]
    exact hp.2.1
  have he : (fun p => ((kernelQuotientChart q).symm.trans (kernelQuotientChart r)) p)=
      kernelCoordinateTransition r.out := by
    funext y
    change hyperbolicSpatialChart (kernelLocalLift r.out ((kernelQuotientChart q).symm y))=_
    rw [kernelQuotientChart_symm]
    rfl
  change ((kernelQuotientChart q).symm.trans (kernelQuotientChart r) : SpatialCoordinates→SpatialCoordinates)=_ at he
  rw [he]
  exact (kernelCoordinateTransition_contDiffAt r.out p hp' hq').contDiffWithinAt

end CubicEisenstein

end

end OAI

end


