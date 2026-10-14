-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0147
-- name    : PNT_ZeroFree_433_0147
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:12:53.342638+00:00
-- url     : https://prove2.me/theorems/654dd287-e7aa-416b-9c78-34b650ae7223
-- title:
--   Zero-free region foundations: GaussSum.PowerfulParts [0147]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.PowerfulParts
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/PowerfulParts.lean#L80-L630

import Definitions.Def_PNT_ZeroFree_433_0116
import Definitions.Def_PNT_ZeroFree_433_0146
import Definitions.Def_PNT_ZeroFree_433_0147_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/PowerfulParts.lean
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

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff gCoeff)


section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def GlobalCubeAdmissible (b : GlobalCubeBlock ι) : Prop :=
  b.cube.Admissible ∧ Disjoint b.common b.cube.support ∧ b.firstDivisor⊆b.common∪b.cube.support

theorem globalFirstFamilyWeight_bounds (blocks : Finset (GlobalCubeBlock ι))
    (w : GlobalCubeBlock ι → ℝ) (Γ : ℝ) (hw : ∀ b∈blocks,0≤w b ∧ w b≤Γ)
    (Ψ : O →* ℂ) (hΨ : ∀ a,‖Ψ a‖≤1) (m : O) (side : Bool) (r : FirstCoreIndex)
    (pool : Finset ι) (d : GlobalFirstData ι) (hd : d∈globalFirstFamilySet pool blocks) :
    0≤globalFirstFamilyWeight p hg w Ψ m side r d ∧
      globalFirstFamilyWeight p hg w Ψ m side r d≤Γ*firstCoreUniformWeight r := by
  have hw' := hw d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1
  constructor
  · exact mul_nonneg hw'.1 (norm_nonneg _)
  · have h1 := firstCoreOuter_norm_le p hg d.cube.support
      (fun i => d.cube.leftExponent i+d.cube.rightExponent i) d.cube.leftBit d.cube.rightBit
      side Ψ m d.firstCommon r
    have h2 := FirstPassCubeLabels.coreRayCoefficient_norm_le p
      (FirstPassCubeLabels.cubeOddSupport d.cube.support
        (fun i => d.cube.leftExponent i+d.cube.rightExponent i) d.cube.leftBit d.cube.rightBit)
      side r.1 r.2.1 r.2.2
    have hnorm : ‖firstCoreOuter p hg d.cube.support
        (fun i => d.cube.leftExponent i+d.cube.rightExponent i) d.cube.leftBit d.cube.rightBit
        side Ψ m d.firstCommon r‖≤firstCoreUniformWeight r :=
      (h1.trans (mul_le_of_le_one_right (norm_nonneg _) (hΨ _))).trans h2
    exact mul_le_mul hw'.2 hnorm (norm_nonneg _) (hw'.1.trans hw'.2)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstPooledRow_block (K ell B F : ℝ) (side : Bool) (d : GlobalFirstData ι) :
    globalFirstPooledRow p K ell B F side d=
      globalFirstPooledRow p K ell B F side (d.block.withCommon ∅) := by
  simp [globalFirstPooledRow,globalPooledRowScale,globalFirstIndex,globalLogRep,globalScaleIndex,
    globalScaleVector,GlobalFirstData.append,GlobalFirstData.block,GlobalCubeBlock.withCommon,globalCubeJNorm]

end


section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalFirstFamilyBudget (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
    (w : GlobalCubeBlock ι → ℝ) (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ,ℂ))
    (windows : Fin 7 → ℝ → ℂ) (C Ct Γ ε K ell B F M H : ℝ) (A J N : ℕ) (side : Bool) : ℝ :=
  let family := globalFirstFamilySet pool blocks
  let source := globalFirstSupportedPool p pool family
    (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
  ∑ a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖*∑ r : FirstCoreIndex,
    let Ψmode := firstCoreTwist side (if side then a.1 else a.2) Ψ r
    let weight := fun d => globalFirstFamilyWeight p hg w Ψ m side r d*globalFirstCoefficient p K ell B F side d
    (∫ t : ℝ,firstLogDensity 0 t)*
      (globalFirstDiagonalCost p hg pool family (fun d => weight d) Ψmode m
          (firstCoreBaseProfile g V side) rowMajorant ell side (globalFirstPooledRow p K ell B F side) +
        globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*firstCoreUniformWeight r*C) ε 0 0 K ell B F M H A J side +
        Ct*globalFirstTailCost p family (fun d => weight d) K ell B F M H N side)

end

theorem globalCubeInputFamilyEnergy_transfer
    (ε : ℝ) (hε : 0<ε) (g V : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool) (A J N : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Ct : ℝ),0≤C ∧ 0<Ct ∧
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t|≤M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (w : GlobalCubeBlock ι → ℝ) (Γ K ell B F H : ℝ)
      (Ψ : O →* ℂ) (m : O) (T : GlobalCubeBlock ι → Finset O),
      0≤Γ → (∀ b∈blocks,0≤w b ∧ w b≤Γ) → 0<K → 0<ell → 0<B → 0<F → 0≤H →
      (∀ b∈blocks,GlobalCubeAdmissible b) → (∀ a,‖Ψ a‖≤1) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F side (b.withCommon ∅)) →
      (∀ b∈blocks,∀ z∈T b,z≠0) →
      (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F side b*
        globalCubeInputFamilyEnergy p hg pool b Ψ m g V ell side (2*(J+2)) (T b)) ≤
      globalFirstFamilyBudget p hp hcop hg pool blocks w Ψ m g V windows C Ct Γ ε K ell B F M H A J N side := by
  obtain ⟨windows,C,Ct,hC,hCt,hwc,hws,hwb,hrow⟩ := globalFirstCoreRows_integrated_transfer ε hε g V M hM hgM side A J N
  refine ⟨windows,C,Ct,hC,hCt,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr pool blocks w Γ K ell B F H Ψ m T hΓ hw hK hell hB hF hH hs hΨ hb₁ hb₂ hT hT0
  rw [globalCubeInputFamilyEnergy_eq_integrated_rows]
  unfold globalFirstFamilyBudget
  dsimp only
  apply Finset.sum_le_sum
  intro a ha
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro r hr
  have hΓr : 0≤Γ*firstCoreUniformWeight r := mul_nonneg hΓ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  apply hrow p hp hcop hg hinj hc hpr pool (globalFirstFamilySet pool blocks)
    (globalFirstFamilyWeight p hg w Ψ m side r) (Γ*firstCoreUniformWeight r) K ell B F H Ψ m
    (if side then a.1 else a.2) r (fun d => T d.block) hΓr
    (fun d hd => globalFirstFamilyWeight_bounds p hg blocks w Γ hw Ψ hΨ m side r pool d hd)
    hK hell hB hF hH
  · intro d hd
    exact hs d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1
  · exact hΨ
  · intro d hd; exact hb₁ d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1
  · intro d hd; exact hb₂ d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1
  · intro d hd z hz
    rw [globalFirstPooledRow_block]
    exact hT d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1 z hz
  · intro d hd z hz
    exact hT0 d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1 z hz

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel columnLog)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCubeColumnScale_pos (ell : ℝ) (hell : 0<ell) (side : Bool) (b : GlobalCubeBlock ι) :
    0<globalCubeColumnScale p ell side b :=
  div_pos hell (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp _) (FirstPassCubeLabels.primeProductNorm_pos p hp _))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCubeCoefficient_side (K ell B F : ℝ) (b : GlobalCubeBlock ι) (side : Bool) :
    globalCubeCoefficient p K ell B F side b=globalCubeCoefficient p K ell B F true b := by
  simp [globalCubeCoefficient,globalFirstCoefficient,globalBinFirstCoefficient,globalFirstIndex,
    globalScaleIndex,globalScaleVector,globalLogRep,GlobalFirstData.append,GlobalCubeBlock.withCommon,globalCubeActiveRoot]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstPooledRow_side (K ell B F : ℝ) (b : GlobalCubeBlock ι) (side : Bool) :
    globalFirstPooledRow p K ell B F side (b.withCommon ∅)=globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  simp [globalFirstPooledRow,globalPooledRowScale,globalFirstIndex,globalScaleIndex,globalScaleVector,
    globalLogRep,GlobalFirstData.append,GlobalCubeBlock.withCommon,globalCubeJNorm]

include hp in
theorem globalCube_first_scalar_bound (K ell B F : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (b : GlobalCubeBlock ι) :
    (ell*B^2*F)⁻¹*((K/primeProductNorm p b.firstDivisor)/
      ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
        (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖) ≤
      globalCubeCoefficient p K ell B F true b := by
  have h := globalBin_first_coefficient_bound p hp K ell B F hK.le hell hB hF true
    ((b.withCommon ∅).append ⟨∅,∅,∅,1⟩) (by exact one_ne_zero)
  change K/(primeProductNorm p b.firstDivisor*ell*B^2*F*
    ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖) ≤ _ at h
  change _ ≤ globalCubeCoefficient p K ell B F true b at h
  convert! h using 1 ; ring

def globalCubeFirstBlock (pool : Finset ι) (b : GlobalCubeBlock ι)
    (s : Finset (Ideal O × O)) (a : Ideal O × O → ℂ)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ W V₁ V₂ : 𝓢(ℝ,ℂ)) (K ell : ℝ) : ℂ :=
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) b.common
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor
  let X₁ := globalCubeColumnScale p ell true b
  let X₂ := globalCubeColumnScale p ell false b
  ∑ x∈s,a x*actualFirstKernel p hp hcop hg (globalCubePool pool b) b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    (originalLabelColumn p hg b.cube.support b.cube.leftBit b.cube.rightBit true
      (multiplicativeCoreColumn p Ψ₁ m₁ (fun S => g₁ (columnLog p X₁ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    (originalLabelColumn p hg b.cube.support b.cube.leftBit b.cube.rightBit false
      (multiplicativeCoreColumn p Ψ₂ m₂ (fun S => g₂ (columnLog p X₂ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    W V₁ V₂ X₁ X₂ (K/primeProductNorm p b.firstDivisor) d x.2

end

theorem globalCubeFirstBlock_input_transfer
    (W V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ : ℝ) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤M₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0<deltaLoss) :
    ∃ C : ℝ,0≤C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ) (T : GlobalCubeBlock ι → Finset O)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ : 𝓢(ℝ,ℂ)) (K ell B F Ymax : ℝ),
      0<K → 0<ell → 0<B → 0<F →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤Ymax) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
          b.cube.leftBit b.cube.rightBit) x∈T b) →
      (∀ b∈blocks,∀ z∈T b,z≠0) →
      (∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤
        globalFirstPooledRow p K ell B F true (b.withCommon ∅)) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,globalCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      C*Ymax^deltaLoss*
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F true b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)) *
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F false b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)) := by
  obtain ⟨C,hC,hfirst⟩ := first_passage_full_uniform_input_family W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J deltaLoss hδ
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ K ell B F Ymax hK hell hB hF hΨ₁ hΨ₂ hw ha hYmax hsf hs0 hmap hT0 hT
  by_cases hempty : blocks=∅
  · subst blocks
    simp only [Finset.sum_empty,mul_zero,norm_zero,Real.sqrt_zero,le_refl]
  have hne : blocks.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let E₁ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)
  let E₂ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)
  let v := fun b => w b*globalCubeCoefficient p K ell B F true b
  have hv (b) (hb : b∈blocks) : 0≤v b := mul_nonneg (hw b hb)
    (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
  have hE₁ (b) : 0≤E₁ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hE₂ (b) : 0≤E₂ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hden : 0<ell*B^2*F := by positivity
  have hYmax0 : 0≤Ymax := by
    obtain ⟨b,hb⟩ := hne
    exact (globalPooledRowScale_pos K ell B F hK hell hB hF _).le.trans (hYmax b hb)
  have hpref : 0≤C*Ymax^deltaLoss := mul_nonneg hC (Real.rpow_nonneg hYmax0 deltaLoss)
  have hpoint (b) (hb : b∈blocks) : (ell*B^2*F)⁻¹*
      ‖globalCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      (C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
    have hFB : Disjoint (globalCubePool pool b) b.cube.support := by
      apply Finset.disjoint_left.mpr
      intro i hi hiB
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hiB)
    have hX₁ := globalCubeColumnScale_pos p hp ell hell true b
    have hX₂ := globalCubeColumnScale_pos p hp ell hell false b
    have hL := div_pos hK (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor)
    have hY := globalPooledRowScale_pos K ell B F hK hell hB hF (globalFirstIndex p true (b.withCommon ∅))
    have hh := hfirst p hp hinj hcop hg hc hpr (globalCubePool pool b) b.cube.support hFB
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit b.cube.support_pos
      Ψ₁ Ψ₂ m₁ m₂ (fun A => g₁ (columnLog p (globalCubeColumnScale p ell true b) A))
      (fun A => g₂ (columnLog p (globalCubeColumnScale p ell false b) A))
      (fun A hA => hΨ₁ _) (fun A hA => hΨ₂ _)
      _ _ hX₁ hX₂ _ hL (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) (primeSubsetGenerator_ne_zero _ _)
      (s b) (T b) (a b) (w b) (globalFirstPooledRow p K ell B F true (b.withCommon ∅))
      (hw b hb) hY.le (hsf b hb) (hs0 b hb) (hmap b hb) (hT0 b hb) (hT b hb) (ha b hb)
    have hscl := globalCube_first_scalar_bound p hp K ell B F hK hell hB hF b
    have hpow := Real.rpow_le_rpow hY.le (hYmax b hb) hδ.le
    have hmul := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hden.le)
    change _ ≤ _ at hmul
    apply hmul.trans
    calc
      _ = ((ell*B^2*F)⁻¹*((K/primeProductNorm p b.firstDivisor)/
          ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
            (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖))*
          (w b*C*(globalFirstPooledRow p K ell B F true (b.withCommon ∅))^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by dsimp [E₁,E₂,globalCubeInputFamilyEnergy];ring
      _ ≤ globalCubeCoefficient p K ell B F true b*(w b*C*Ymax^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        apply mul_le_mul hscl
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg (hw b hb) hC))
          (mul_nonneg (mul_nonneg (hw b hb) hC) (Real.rpow_nonneg hY.le _))
          (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
      _ = _ := by dsimp [v];ring
  rw [norm_mul, norm_inv]
  have hn : ‖(ell*B^2*F : ℂ)‖=ell*B^2*F := by
    norm_cast
    exact abs_of_pos hden
  rw [hn]
  calc
    _ ≤ (ell*B^2*F)⁻¹*∑ b∈blocks,‖globalCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hden.le)
    _ ≤ ∑ b∈blocks,(C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpoint
    _ = (C*Ymax^deltaLoss)*∑ b∈blocks,Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Real.sqrt_mul (hv b hb),Real.sqrt_mul (hv b hb)]
      have hs := Real.sq_sqrt (hv b hb)
      calc
        _ = (C*Ymax^deltaLoss)*(Real.sqrt (v b))^2*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by rw [hs]
        _ = _ := by ring
    _ ≤ (C*Ymax^deltaLoss)*(Real.sqrt (∑ b∈blocks,v b*E₁ b)*Real.sqrt (∑ b∈blocks,v b*E₂ b)) :=
      mul_le_mul_of_nonneg_left (by
        have hcauchy := Real.sum_sqrt_mul_sqrt_le blocks.attach
          (fun b => mul_nonneg (hv b.val b.property) (hE₁ b.val))
          (fun b => mul_nonneg (hv b.val b.property) (hE₂ b.val))
        simpa only [Finset.sum_attach (f := fun b => Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b)),
          Finset.sum_attach (f := fun b => v b*E₁ b),Finset.sum_attach (f := fun b => v b*E₂ b)] using hcauchy) hpref
    _ = _ := by simp only [v,E₁,E₂,globalCubeCoefficient_side,mul_assoc]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem globalTwoPassage_transfer
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
      (w : GlobalCubeBlock ι → ℝ) (T : GlobalCubeBlock ι → Finset O)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ K ell B F H Ymax : ℝ),
      0≤Γ → 0<K → 0<ell → 0<B → 0<F → 0≤H → 0≤Ymax →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤Ymax) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
          b.cube.leftBit b.cube.rightBit) x∈T b) →
      (∀ b∈blocks,∀ z∈T b,z≠0) →
      (∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤
        globalFirstPooledRow p K ell B F true (b.withCommon ∅)) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,globalCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      Cfirst*Ymax^deltaLoss*
        Real.sqrt (globalFirstFamilyBudget p hp hcop hg pool blocks w Ψ₁ m₁ g₁ V₁ windows₁ C₁ Ct₁ Γ ε K ell B F M₁ H A J N true) *
        Real.sqrt (globalFirstFamilyBudget p hp hcop hg pool blocks w Ψ₂ m₂ g₂ V₂ windows₂ C₂ Ct₂ Γ ε K ell B F M₂ H A J N false) := by
  obtain ⟨Cfirst,hCfirst,hfirst⟩ := globalCubeFirstBlock_input_transfer W V₁ V₂ N₁ N₂ hN₁ hN₂ hV₁ hV₂ (2*(J+2)) deltaLoss hδ
  obtain ⟨windows₁,C₁,Ct₁,hC₁,hCt₁,hwc₁,hws₁,hwb₁,hleft⟩ := globalCubeInputFamilyEnergy_transfer ε hε g₁ V₁ M₁ hM₁ hg₁ true A J N
  obtain ⟨windows₂,C₂,Ct₂,hC₂,hCt₂,hwc₂,hws₂,hwb₂,hright⟩ := globalCubeInputFamilyEnergy_transfer ε hε g₂ V₂ M₂ hM₂ hg₂ false A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Ct₁,C₂,Ct₂,hCfirst,hC₁,hCt₁,hC₂,hCt₂,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H Ymax
    hΓ hK hell hB hF hH hYmax0 hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hYmax hsf hs0 hmap hT0 hT
  have hf := hfirst p hp hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ K ell B F Ymax
    hK hell hB hF hΨ₁ hΨ₂ (fun b hb => (hw b hb).1) ha hYmax hsf hs0 hmap hT0 hT
  have hl := hleft p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H Ψ₁ m₁ T hΓ hw hK hell hB hF hH hadm hΨ₁ hb₁ hb₂ hT hT0
  have hT' : ∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤
      globalFirstPooledRow p K ell B F false (b.withCommon ∅) := by
    intro b hb z hz
    rw [globalFirstPooledRow_side]
    exact hT b hb z hz
  have hr := hright p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H Ψ₂ m₂ T hΓ hw hK hell hB hF hH hadm hΨ₂ hb₁ hb₂ hT' hT0
  have hprefix : 0≤Cfirst*Ymax^deltaLoss := mul_nonneg hCfirst (Real.rpow_nonneg hYmax0 _)
  apply hf.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) hprefix)
    (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _) (mul_nonneg hprefix (Real.sqrt_nonneg _))

end SecondPassArithmetic

end

end OAI

end


