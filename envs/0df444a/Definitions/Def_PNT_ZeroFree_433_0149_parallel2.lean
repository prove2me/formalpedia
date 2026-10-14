-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0149_parallel2
-- name    : PNT_ZeroFree_433_0149_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:46:37.327765+00:00
-- url     : https://prove2.me/theorems/1dff2ded-f0b2-4f56-80ad-669d173e5b1e
-- title:
--   Zero-free region foundations: MeanSquare.LogarithmicBins [0149_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.MeanSquare.LogarithmicBins
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/LogarithmicBins.lean#L180-L503

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0059
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0066
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0077
import Definitions.Def_PNT_ZeroFree_433_0078
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0093
import Definitions.Def_PNT_ZeroFree_433_0102
import Definitions.Def_PNT_ZeroFree_433_0107
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0113
import Definitions.Def_PNT_ZeroFree_433_0118_parallel1
import Definitions.Def_PNT_ZeroFree_433_0122_parallel1
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0127_parallel2
import Definitions.Def_PNT_ZeroFree_433_0128_parallel1
import Definitions.Def_PNT_ZeroFree_433_0129_parallel1
import Definitions.Def_PNT_ZeroFree_433_0132_parallel1
import Definitions.Def_PNT_ZeroFree_433_0135_parallel1
import Definitions.Def_PNT_ZeroFree_433_0137_parallel2
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148
import Definitions.Def_PNT_ZeroFree_433_0148_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148_parallel2
import Definitions.Def_PNT_ZeroFree_433_0149_parallel1
import Definitions.Def_PNT_ZeroFree_433_0181_parallel1
import Definitions.Def_PNT_ZeroFree_433_0208_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/LogarithmicBins.lean
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

namespace InitialMeanSquare

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform


open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation

theorem initial_source_uniform_transfer (ε : ℝ) (hε : 0<ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7→ℝ→ℂ) (M : Fin 7→ℝ)
    (hM : ∀j,0≤M j) (hV : ∀j x,V j x≠0→|x|≤M j) (N J : ℕ) :
    ∃ Cₐ : ℝ,0<Cₐ ∧ ∃ Cₛ : ℝ,0≤Cₛ ∧ ∀R:ℝ,0<R→∃b:𝓢(ℝ,ℂ),
      (∀t₁ t₂ t₃:ℝ,(1+R)^N*‖(𝓕 A₁) t₁*(𝓕 A₂) t₂*b t₃‖≤
        Cₛ*FirstPassCubeLabels.firstLogDensity J t₁*FirstPassCubeLabels.firstLogDensity J t₂*
          FirstPassCubeLabels.firstLogDensity J t₃) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (r : O) (s : Finset (SecondExpansionData ι)) (T : Finset (O×O))
        (w : SecondExpansionData ι→ℂ) (A K : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O)
        (z ud ue uv kap : SecondExpansionData ι→ℝ) (X₁ X₂ : ℝ),
        0≤A → 0≤K → (∀x∈s,InSecondQuotientSector p r x) →
        (∀x∈s,sourceObservation p x∈T) → (∀y∈T,y.1≠0) →
        (∀y∈T,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
        (∀x∈s,‖w x‖*‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖≤A) →
        ‖initialSourceSum p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R‖≤
          A*Cₐ*K^ε*(∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖*
            sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨Cₐ,hCₐ,htrans⟩ := integrated_source_transfer ε hε
  obtain ⟨Cₛ,hCₛ,hsep⟩ := full_uniform_postCommonSmoothPair_fixed_tests A₁ A₂ W V M hM hV N J
  refine ⟨Cₐ,hCₐ,Cₛ,hCₛ,?_⟩
  intro R hR
  obtain ⟨b,hpoint,hid⟩ := hsep R hR
  refine ⟨b,hpoint,?_⟩
  intro ι _ p hp _ hcop hg hinj r s T w A K F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hA hK hs hmap hT hnorm hw
  have hsource := initialSource_eq_integrated p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W b
    V z ud ue uv kap X₁ X₂ R (fun x hx => hid p hp hcop hg F Ψ₁ Ψ₂ m
      (sourceObservation p x).2 (sourceObservation p x).1 (-(sourceObservation p x).1)
      (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂)
  rw [hsource]
  apply htrans p hp hcop hg hinj r s T (initialOuterWeight V w z ud ue uv kap) A K
    F Ψ₁ Ψ₂ m (V 5) (V 6) X₁ X₂ (𝓕 A₁) (𝓕 A₂) b hA hK hs hmap hT hnorm
  · intro q x hx
    rw [initialOuterWeight_norm]
    exact hw x hx
  · intro x hx
    exact initialOuterWeight_continuous V w z ud ue uv kap x

end

section
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm)
open SecondPassIntegration (elementNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

def initialLogIndex (x : SecondExpansionData ι) : SecondLogIndex :=
  (normLogBin (primeProductNorm p x.divisor),normLogBin (primeProductNorm p x.overlap),
    normLogBin (elementNorm (sourceObservation p x).1))

def initialLogColumn (Z B : ℝ) (j : SecondLogIndex) : ℝ :=
  Z/(secondLogE j*secondLogV j*B)

def initialLogLabel (j : SecondLogIndex) : ℝ := secondLogE j*secondLogV j*Real.exp 2


omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceLabel_norm (x : SecondExpansionData ι) :
    elementNorm (sourceObservation p x).2=primeProductNorm p x.divisor*primeProductNorm p x.overlap := by
  simp only [elementNorm,sourceObservation,map_mul,norm_mul,mul_pow,
    primeSubsetGenerator_norm_eq_productNorm,primeProductNorm]


include hp in

theorem initial_log_coordinates (Z : ℝ) (hZ : 0<Z) (x : SecondExpansionData ι)
    (hE : x.divisor⊆x.sourceCommon) (hk : x.frequency≠0) :
    let j := initialLogIndex p x
    let B := elementNorm (secondExpansionQuotient p x)
    let X₀ := initialLogColumn Z B j
    |Real.log (primeProductNorm p x.overlap*X₀/residualScale p Z x)|≤2 ∧
    |Real.log (primeProductNorm p x.divisor/secondLogE j)|≤2 ∧
    |Real.log (primeProductNorm p x.overlap/secondLogV j)|≤2 ∧
    |Real.log (elementNorm (sourceObservation p x).1/secondLogK j)|≤2 := by
  dsimp only
  have he := normLogBin_error (primeProductNorm p x.divisor) (primeProductNorm_ge_one p hp _)
  have hv := normLogBin_error (primeProductNorm p x.overlap) (primeProductNorm_ge_one p hp _)
  have hn : 1≤elementNorm (sourceObservation p x).1 := element_norm_ge_one _ (sourceRow_nonzero p x hk)
  have hrow := normLogBin_error (elementNorm (sourceObservation p x).1) hn
  have hE0 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.divisor).ne'
  have hV0 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.overlap).ne'
  have hB0 := (SecondPassIntegration.elementNorm_pos _ (sourceQuotient_nonzero p hp x hE)).ne'
  have hE1 := (normLogScale_pos (normLogBin (primeProductNorm p x.divisor))).ne'
  have hV1 := (normLogScale_pos (normLogBin (primeProductNorm p x.overlap))).ne'
  have hratio : primeProductNorm p x.overlap*initialLogColumn Z
      (elementNorm (secondExpansionQuotient p x)) (initialLogIndex p x)/residualScale p Z x=
      (primeProductNorm p x.divisor/normLogScale (normLogBin (primeProductNorm p x.divisor)))*
      (primeProductNorm p x.overlap/normLogScale (normLogBin (primeProductNorm p x.overlap))) := by
    simp only [initialLogColumn,residualScale,initialLogIndex,secondLogE,secondLogV,
      elementNorm,primeSubsetGenerator_norm_eq_productNorm]
    have hZ0 := hZ.ne'
    dsimp [elementNorm] at hB0
    have hBn : ‖eisEmbedding (secondExpansionQuotient p x)‖≠0 := by
      intro hz
      apply hB0
      rw [hz]
      norm_num
    field_simp [hBn]

  refine ⟨?_,?_,?_,?_⟩
  · rw [hratio,Real.log_mul (div_ne_zero hE0 hE1) (div_ne_zero hV0 hV1),
      abs_of_nonneg (add_nonneg he.1 hv.1)]
    linarith [he.2,hv.2]
  · change |Real.log (_/normLogScale (normLogBin _))|≤2
    rw [abs_of_nonneg he.1]
    linarith [he.2]
  · change |Real.log (_/normLogScale (normLogBin _))|≤2
    rw [abs_of_nonneg hv.1]
    linarith [hv.2]
  · change |Real.log (_/normLogScale (normLogBin _))|≤2
    rw [abs_of_nonneg hrow.1]
    linarith [hrow.2]

include hp in

omit [DecidableEq ι] in
theorem initial_log_target_bounds (x : SecondExpansionData ι) (hk : x.frequency≠0) :
    elementNorm (sourceObservation p x).2 ≤ initialLogLabel (initialLogIndex p x) ∧
    elementNorm (sourceObservation p x).1≤secondLogK (initialLogIndex p x)*Real.exp 1 := by
  have he := (normLogBin_scale_bounds _ (primeProductNorm_ge_one p hp x.divisor)).2
  have hv := (normLogBin_scale_bounds _ (primeProductNorm_ge_one p hp x.overlap)).2
  have hk' := (normLogBin_scale_bounds _ (element_norm_ge_one _ (sourceRow_nonzero p x hk))).2
  refine ⟨?_,hk'⟩
  rw [sourceLabel_norm]
  have hh := mul_le_mul he hv (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
    (mul_nonneg (normLogScale_pos _).le (Real.exp_pos _).le)
  simpa only [initialLogLabel,initialLogIndex,secondLogE,secondLogV,
    show (2:ℝ)=1+1 by norm_num,Real.exp_add,mul_assoc,mul_left_comm,mul_comm] using hh

theorem initial_log_mass (Z B : ℝ) (hB : B≠0) (j : SecondLogIndex) :
    initialLogColumn Z B j*initialLogLabel j=Z/B*Real.exp 2 := by
  have he := (normLogScale_pos j.1).ne'
  have hv := (normLogScale_pos j.2.1).ne'
  unfold initialLogColumn initialLogLabel secondLogE secondLogV
  field_simp

theorem initial_log_radial (Z H B : ℝ) (hZ : Z≠0) (hB : B≠0) (j : SecondLogIndex) :
    H*secondLogK j/(secondLogE j^2*secondLogV j^2*initialLogColumn Z B j^2)=
      H*secondLogK j*B^2/Z^2 := by
  have he := (normLogScale_pos j.1).ne'
  have hv := (normLogScale_pos j.2.1).ne'
  unfold initialLogColumn secondLogE secondLogV
  field_simp

end

open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm)
open SecondPassIntegration (elementNorm)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))

include hcop in
theorem sourceLabel_squarefree (x : SecondExpansionData ι)
    (hE : x.divisor⊆x.sourceCommon) (hV : Disjoint x.sourceCommon x.overlap) :
    Squarefree (Ideal.span {(sourceObservation p x).2}) := by
  have hd : Disjoint x.divisor x.overlap := hV.mono_left hE
  rw [sourceLabel_span,←Finset.prod_union hd]
  exact primeSpanProduct_squarefree p hcop _


include hp in
theorem initialLogIndex_mem_box (Z M K : ℝ) (x : SecondExpansionData ι)
    (hs : SecondSourceSupport p Z M x) (hE : x.divisor⊆x.sourceCommon)
    (hk : x.frequency≠0) (hK : elementNorm (sourceObservation p x).1≤K) :
    initialLogIndex p x∈secondLogBinBox (Z*Real.exp M) K := by
  obtain ⟨hG,hE',hV⟩ := secondSourceSupport_bounds p hp Z M x hs hE
  simp only [initialLogIndex,secondLogBinBox,Finset.mem_product,Finset.mem_range,Nat.lt_succ_iff]
  exact ⟨normLogBin_mono (FirstPassCubeLabels.primeProductNorm_pos p hp _) hE',
    normLogBin_mono (FirstPassCubeLabels.primeProductNorm_pos p hp _) hV,
    normLogBin_mono (SecondPassIntegration.elementNorm_pos _ (sourceRow_nonzero p x hk)) hK⟩

end


end InitialMeanSquare

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (bit conductorExponent dilationExponent retained parity evenDouble
  primeProduct primeProductNorm aLabel dilationLabel jLabel j2Label squarefreeLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)


variable {ι : Type*} [DecidableEq ι] (p : ι → O)


variable [∀ i,(Ideal.span {p i}).IsMaximal]


variable (hp : ∀ i,p i≠0)
include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem first_conductor_norm_bound (S : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i) (B : ℝ) (hB : 0≤B)
    (hb₁ : ‖eisEmbedding (primeProduct p S v₁)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p S v₂)‖^2≤B) :
    ‖eisEmbedding (∏ i∈cubeActiveSupport S (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖^2*
      ‖eisEmbedding (dilationLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2*
      ‖eisEmbedding (jLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2 ≤
    ‖eisEmbedding (aLabel p S ε₁)‖^2*‖eisEmbedding (aLabel p S ε₂)‖^2*B^4 := by
  have hn : aLabel p S ε₁*aLabel p S ε₂*(primeProduct p S v₁*primeProduct p S v₂)^2≠0 := by
    apply mul_ne_zero (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _))
    exact pow_ne_zero _ (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _))
  have h := element_norm_le_of_dvd hn (first_conductor_product_dvd p S v₁ v₂ ε₁ ε₂ hv)
  simp only [map_mul,map_pow,norm_mul,norm_pow,mul_pow] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hm := mul_le_mul hb₁ hb₂ (sq_nonneg _) hB
  have hs := pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hm 2
  convert! hs using 1 <;> ring

end


end SecondPassArithmetic

end

end OAI

end


