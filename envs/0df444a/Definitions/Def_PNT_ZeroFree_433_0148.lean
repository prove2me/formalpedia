-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0148
-- name    : PNT_ZeroFree_433_0148
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:22:33.354205+00:00
-- url     : https://prove2.me/theorems/a66e5404-db68-44b6-ab98-952975f9f216
-- title:
--   Zero-free region foundations: MeanSquare.SourceTransfer [0148]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.MeanSquare.SourceTransfer
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/SourceTransfer.lean#L89-L647

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0073
import Definitions.Def_PNT_ZeroFree_433_0078
import Definitions.Def_PNT_ZeroFree_433_0079
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0081
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0088
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0093
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0133_parallel1
import Definitions.Def_PNT_ZeroFree_433_0140_parallel1
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0145_parallel2
import Definitions.Def_PNT_ZeroFree_433_0148_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148_parallel2
import Definitions.Def_PNT_ZeroFree_433_0213_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/SourceTransfer.lean
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
namespace InitialMeanSquare

section
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open JointLogSeparation (halfNormalizationCLM)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (elementNorm)


theorem initial_source_fixed_profiles
    (U : ℝ→ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hU₁ : ∀t,g₁ t≠0→U t=1) (hU₂ : ∀t,g₂ t≠0→U t=1)
    (hg₁ : ∀t,g₁ t≠0→|t|≤A) (hg₂ : ∀t,g₂ t≠0→|t|≤A) :
    ∃ (A₁ A₂ : 𝓢(ℝ,ℂ)) (windows : Fin 7→ℝ→ℂ),
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      (∀i t,windows i t≠0→|t|≤A+B+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hpr : ∀i,lambda^2∣p i-1)
        (F : Finset ι) (Ψ : O→*ℂ) (m : O) (ray : SecondRayIndex)
        (x : SecondExpansionData ι) (Z H E V₀ X₀ K : ℝ),
        x.divisor⊆x.sourceCommon → x.frequency≠0 →
        0<Z → 0<E → 0<V₀ → 0<X₀ → 0<K →
        let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor
        let r := secondExpansionQuotient p x
        let X := residualScale p Z x
        let z := Real.log (primeProductNorm p x.overlap*X₀/X)
        let ue := Real.log (elementNorm e/E)
        let uv := Real.log (primeProductNorm p x.overlap/V₀)
        let kap := Real.log (elementNorm (e*x.frequency)/K)
        |z|≤B → |ue|≤B → |uv|≤B → |kap|≤B →
        secondExpansionSource p hp hcop hg F Ψ m 1 1 ray {x}
          (fun S => normalizedColumn p (fun T => g₁ (columnLog p Z T)) S)
          (fun S => normalizedColumn p (fun T => g₂ (columnLog p Z T)) S) W H =
        sourceWeight p hp hcop hg Ψ m ray Z H x *
          postCommonSmoothPair p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
            (m*r) (e*∏i∈x.overlap,p i) (e*x.frequency) (-(e*x.frequency))
            A₁ A₂ W windows z 0 ue uv kap X₀ X₀ (H*K/(E^2*V₀^2*X₀^2)) := by
  have h1 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₁ A hg₁
  have h2 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := SecondPassIntegration.full_uniform_normalized_child_tests
    (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂) W A B hA hB h1 h2
  refine ⟨A₁,A₂,windows,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hpr F Ψ m ray x Z H E V₀ X₀ K hE hk hZ hEs hV hX₀ hK
  dsimp only
  intro hz hue huv hkap
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor
  let r := secondExpansionQuotient p x
  have he : e≠0 := primeSubsetGenerator_ne_zero _ _
  have hq : secondMaskQuotient p x.divisor x.sourceCommon hE=r :=
    (secondExpansionQuotient_of_subset p x hE).symm
  have hr : r≠0 := by
    rw [←hq]
    intro hr0
    have hs := secondMaskQuotient_spec p x.divisor x.sourceCommon hE
    rw [hr0,mul_zero] at hs
    exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) hs
  have hX : 0<residualScale p Z x := div_pos hZ
    (mul_pos (SecondPassIntegration.elementNorm_pos e he) (SecondPassIntegration.elementNorm_pos r hr))
  have hnorm := weighted_secondRayChild_normalized p hp hcop hg hinj hpr
    x.sourceCommon x.divisor hE F x.overlap Ψ Ψ m 1 1 x.frequency r ray
      (congrArg (fun a:O => Ideal.span {a}) hq) Z H hZ U hUc hUs g₁ g₂ W hU₁ hU₂
  dsimp only at hnorm
  have hnormone : elementNorm (1:O)=1 := by simp [elementNorm]
  have hid' := hid p hp hcop hg 1 E V₀ (residualScale p Z x) X₀ K H
    (by norm_num) hEs hV hX hX₀ hK F x.overlap (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      m r 1 1 e x.frequency one_ne_zero he hk hz
      (by simpa only [hnormone,div_one,Real.log_one,abs_zero] using hB) hue huv
      (by simpa only [one_mul] using hkap)
  simp only [one_mul,mul_neg,hnormone,div_one,Real.log_one] at hid'
  have hscale : Z/(‖eisEmbedding e‖^2*‖eisEmbedding r‖^2)=residualScale p Z x := rfl
  rw [hscale,hid'] at hnorm
  rw [hq] at hnorm
  have hgoal := congrArg (fun t:ℂ => ((H:ℂ)*secondSourceCommonCoefficient p hg Ψ m 1 1 x.sourceCommon x.divisor)*t) hnorm
  simp only [secondExpansionSource,Finset.sum_singleton,sourceWeight,
    secondNormalizedExpansionWeight,e,r,mul_assoc] at hgoal ⊢
  exact hgoal

end

open ActualEisensteinCubic SecondPassArithmetic IdealMobiusDivisorSum
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)


end InitialMeanSquare


open scoped BigOperators Classical


open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation


private theorem weighted_conjugate_pair_swap {α : Type*} (s : Finset α)
    (w P Q : α → ℂ) (B X Y : ℝ)
    (h : ‖∑ x ∈ s, w x * P x * star (Q x)‖ ≤ B * X * Y) :
    ‖∑ x ∈ s, w x * star (Q x) * P x‖ ≤ B * (Y * X) := by
  have he : (∑ x ∈ s, w x * star (Q x) * P x) =
      ∑ x ∈ s, w x * P x * star (Q x) := by
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [he]
  exact h.trans_eq (by ring)

theorem integrated_source_transfer (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (r : O) (s : Finset (SecondExpansionData ι)) (T : Finset (O×O))
      (w : Frequency→SecondExpansionData ι→ℂ) (A K : ℝ)
      (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O) (V₁ V₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
      (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)),
      0≤A → 0≤K → (∀x∈s,InSecondQuotientSector p r x) →
      (∀x∈s,sourceObservation p x∈T) → (∀y∈T,y.1≠0) →
      (∀y∈T,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
      (∀q,∀x∈s,‖w q x‖≤A) → (∀x∈s,Continuous (fun q => w q x)) →
      ‖integratedSourceMode p hp hcop hg b₁ b₂ b₃ s w F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂‖≤
        A*C*K^ε*(∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖*
          sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨C,hC,hpointwise⟩ := source_weighted_cauchy ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hcop hg hinj r s T w A K F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂ b₁ b₂ b₃ hA hK hs hmap hT hnorm hw hwc
  let f := sourceFixedMode p hp hcop hg s w F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂
  let G := sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂
  have hc₁ := sourceChildEnergy_continuous p hp hcop hg F Ψ₁ m T V₁ X₁ true false
    (fun q:Frequency => q.1) (fun q:Frequency => q.2.2) continuous_fst continuous_snd.snd
  have hc₂ := sourceChildEnergy_continuous p hp hcop hg F Ψ₂ m T V₂ X₂ false true
    (fun q:Frequency => q.2.1) (fun q:Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
  have hG : Continuous G := (Real.continuous_sqrt.comp hc₁).mul (Real.continuous_sqrt.comp hc₂)
  have hG0 : ∀q,0≤G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let M := Real.sqrt (sourceEnergyMagnitude p hp hcop hg F Ψ₁ m T V₁ X₁ true false)*
    Real.sqrt (sourceEnergyMagnitude p hp hcop hg F Ψ₂ m T V₂ X₂ false true)
  have hM : ∀q,G q≤M := by
    intro q
    dsimp [G,sourceGeometricMean,M]
    gcongr
    · exact sourceChildEnergy_le p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2
    · exact sourceChildEnergy_le p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2
  have hf : Continuous f := by
    unfold f sourceFixedMode
    apply continuous_finsetSum
    intro x hx
    have h₁ := fixedRow_continuous p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 V₁ X₁ true
      (fun q:Frequency => q.1) (fun q:Frequency => q.2.2) continuous_fst continuous_snd.snd
    have h₂ := fixedRow_continuous p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) V₂ X₂ false
      (fun q:Frequency => q.2.1) (fun q:Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
    exact ((hwc x hx).mul h₁.star).mul h₂
  have hpoint : ∀q,‖f q‖≤(A*C*K^ε)*G q := by
    intro q
    let P : O × O → ℂ := fun u => fixedChildRow p hp hcop hg F Ψ₂ m
      (fixedSecondTest p V₂ X₂ q.2.1 q.2.2 false) u.2 (-u.1)
    let Q : O × O → ℂ := fun u => fixedChildRow p hp hcop hg F Ψ₁ m
      (fixedSecondTest p V₁ X₁ q.1 q.2.2 true) u.2 u.1
    have hh := hpointwise p hinj r s T (w q) P Q
      A K hA hK hs hmap hT hnorm (hw q)
    have hh' := weighted_conjugate_pair_swap s (w q)
      (fun x => P (sourceObservation p x)) (fun x => Q (sourceObservation p x))
      (A*C*K^ε) _ _ hh
    simpa only [f,G,sourceFixedMode,sourceGeometricMean,sourceChildEnergy,P,Q,
      Bool.false_eq_true,ite_false,ite_true] using hh'
  exact triple_integral_bound b₁ b₂ b₃ f G hf hG hG0 (A*C*K^ε) M (by positivity) hM hpoint

end InitialMeanSquare

end

end OAI

end


