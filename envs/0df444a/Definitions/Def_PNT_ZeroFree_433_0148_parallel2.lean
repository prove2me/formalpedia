-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0148_parallel2
-- name    : PNT_ZeroFree_433_0148_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:39:35.332519+00:00
-- url     : https://prove2.me/theorems/7c2274f5-d2c5-49e4-a60b-bf26e3397099
-- title:
--   Zero-free region foundations: MeanSquare.SourceTransfer [0148_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.MeanSquare.SourceTransfer
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/SourceTransfer.lean#L89-L573

import Definitions.Def_PNT_ZeroFree_433_0005
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0025
import Definitions.Def_PNT_ZeroFree_433_0026
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0050
import Definitions.Def_PNT_ZeroFree_433_0053
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0073
import Definitions.Def_PNT_ZeroFree_433_0078
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0087
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0093
import Definitions.Def_PNT_ZeroFree_433_0097
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0143_parallel1
import Definitions.Def_PNT_ZeroFree_433_0145_parallel1
import Definitions.Def_PNT_ZeroFree_433_0146_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148_parallel1
import Definitions.Def_PNT_ZeroFree_433_0227_parallel1
import Definitions.Def_PNT_ZeroFree_433_0231_parallel2
import Definitions.Def_PNT_ZeroFree_433_0234_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel1_1

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

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def residualScale (Z : ℝ) (x : SecondExpansionData ι) : ℝ :=
  Z/(elementNorm (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)*
    elementNorm (secondExpansionQuotient p x))

def sourceWeight (Ψ : O→*ℂ) (m : O) (ray : SecondRayIndex)
    (Z H : ℝ) (x : SecondExpansionData ι) : ℂ :=
  secondNormalizedExpansionWeight p hp hcop hg Ψ m 1 1 ray Z H x *
    (residualScale p Z x : ℂ)⁻¹

theorem sourceWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (Ψ : O→*ℂ) (m : O) (ray : SecondRayIndex) (Z H : ℝ) (x : SecondExpansionData ι)
    (hZ : 0<Z) (hH : 0≤H)
    (hΨG : ‖Ψ (∏i∈x.sourceCommon,p i)‖≤1) (hΨV : ‖Ψ (∏i∈x.overlap,p i)‖≤1) :
    ‖sourceWeight p hp hcop hg Ψ m ray Z H x‖≤
      H*elementNorm (secondExpansionQuotient p x)/Z^2*‖secondRayCoefficient ray‖ := by
  simpa only [sourceWeight,residualScale,elementNorm,secondExpansionScale,expansionSupportData] using
    secondNormalizedExpansionWeight_norm_le p hp hcop hg hinj hc ∅ ∅ Ψ m 1 1
      (secondExpansionQuotient p x) ray Z H hZ hH x hΨG hΨV

end


end

open ActualEisensteinCubic SecondPassArithmetic IdealMobiusDivisorSum
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def sourceElementData (x : SecondExpansionData ι) : ElementDatum where
  divisor := ∏i∈x.divisor,Ideal.span {p i}
  shared := ∏i∈x.overlap,p i
  frequency := x.frequency

def sourceObservation (x : SecondExpansionData ι) : O×O :=
  (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor*x.frequency,
   primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor*∏i∈x.overlap,p i)

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceObservation_eq (x : SecondExpansionData ι) :
    sourceObservation p x=elementObservation idealGenerator (sourceElementData p x) := rfl

include hinj in

theorem sourceElementData_injective (r : O) :
    Set.InjOn (sourceElementData p) {x | InSecondQuotientSector p r x} := by
  intro x hx y hy heq
  have hE := congrArg ElementDatum.divisor heq
  have hV := congrArg ElementDatum.shared heq
  have hk := congrArg ElementDatum.frequency heq
  have he : x.divisor=y.divisor := FirstCauchyArithmetic.family_product_injective _ hinj hE
  have hv : x.overlap=y.overlap := by
    apply FirstCauchyArithmetic.family_product_injective _ hinj
    have hh := congrArg (fun a:O => Ideal.span {a}) hV
    simpa only [sourceElementData,FiniteGaussPhase.span_finset_prod] using hh
  apply expansionSupportData_injOn p hinj ∅ ∅ r hx hy
  exact SecondSupportData.ext rfl rfl he hv hk

include hinj in

theorem source_fiber_card_le (r : O) (s : Finset (SecondExpansionData ι))
    (hs : ∀x∈s,InSecondQuotientSector p r x) (y f : O) (hy : y≠0) :
    (s.filter (fun x => sourceObservation p x=(y,f))).card≤
      (idealDivisors (Ideal.span {y})).card := by
  have hmap : (s.filter (fun x => sourceObservation p x=(y,f))).card≤
      ((s.image (sourceElementData p)).filter (fun x => elementObservation idealGenerator x=(y,f))).card := by
    apply Finset.card_le_card_of_injOn (sourceElementData p)
    · intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,(Finset.mem_filter.mp hx).1,rfl⟩,?_⟩
      exact (Finset.mem_filter.mp hx).2
    · intro x hx y hy he
      exact sourceElementData_injective p hinj r (hs x (Finset.mem_filter.mp hx).1)
        (hs y (Finset.mem_filter.mp hy).1) he
  exact hmap.trans (element_fiber_card_le idealGenerator span_idealGenerator _ y f hy)

end

theorem source_weighted_energy_pushforward (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (r : O) (s : Finset (SecondExpansionData ι)) (t : Finset (O×O))
      (w : SecondExpansionData ι→ℂ) (P : O×O→ℂ) (A K : ℝ),
      0≤A → 0≤K → (∀x∈s,InSecondQuotientSector p r x) →
      (∀x∈s,sourceObservation p x∈t) → (∀y∈t,y.1≠0) →
      (∀y∈t,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
      (∀x∈s,‖w x‖≤A) →
      (∑x∈s,‖w x‖*‖P (sourceObservation p x)‖^2)≤A*C*K^ε*∑y∈t,‖P y‖^2 := by
  obtain ⟨C,hC,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p _ hinj r s t w P A K hA hK hs hmap ht hnorm hw
  apply (DescentWeightedCauchy.bounded_energy_pushforward s t (sourceObservation p) w P A hmap hw).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  have hyI : (Ideal.span {y.1}:Ideal O)≠0 := by intro hz; exact ht y hy (Ideal.span_singleton_eq_bot.mp hz)
  have hcard : ((s.filter (fun x => sourceObservation p x=y)).card:ℝ)≤C*K^ε := by
    calc
      _ ≤ ((idealDivisors (Ideal.span {y.1})).card:ℝ) := by
        exact_mod_cast source_fiber_card_le p hinj r s hs y.1 y.2 (ht y hy)
      _ ≤ C*(Ideal.absNorm (Ideal.span {y.1}):ℝ)^ε := hdiv _ hyI
      _ ≤ C*K^ε := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm y hy) hε.le) hC.le
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hA) (sq_nonneg ‖P y‖)
  simpa only [mul_assoc] using hh

theorem source_weighted_cauchy (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (r : O) (s : Finset (SecondExpansionData ι)) (t : Finset (O×O))
      (w : SecondExpansionData ι→ℂ) (P Q : O×O→ℂ) (A K : ℝ),
      0≤A → 0≤K → (∀x∈s,InSecondQuotientSector p r x) →
      (∀x∈s,sourceObservation p x∈t) → (∀y∈t,y.1≠0) →
      (∀y∈t,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
      (∀x∈s,‖w x‖≤A) →
      ‖∑x∈s,w x*P (sourceObservation p x)*star (Q (sourceObservation p x))‖≤
        A*C*K^ε*Real.sqrt (∑y∈t,‖P y‖^2)*Real.sqrt (∑y∈t,‖Q y‖^2) := by
  obtain ⟨C,hC,hpool⟩ := source_weighted_energy_pushforward ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p _ hinj r s t w P Q A K hA hK hs hmap ht hnorm hw
  have hP := hpool p hinj r s t w P A K hA hK hs hmap ht hnorm hw
  have hQ := hpool p hinj r s t w Q A K hA hK hs hmap ht hnorm hw
  have hD : 0≤A*C*K^ε := by positivity
  apply (DescentWeightedCauchy.weighted_cauchy s w (fun x => P (sourceObservation p x))
    (fun x => Q (sourceObservation p x))).trans
  calc
    _ ≤ Real.sqrt (A*C*K^ε*∑y∈t,‖P y‖^2)*Real.sqrt (A*C*K^ε*∑y∈t,‖Q y‖^2) := by gcongr
    _ = _ := by
      rw [Real.sqrt_mul hD,Real.sqrt_mul hD]
      calc
        _ = (Real.sqrt (A*C*K^ε))^2*Real.sqrt (∑y∈t,‖P y‖^2)*Real.sqrt (∑y∈t,‖Q y‖^2) := by ring
        _ = _ := by rw [Real.sq_sqrt hD]

end InitialMeanSquare


open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CompletedGauss FirstCauchyArithmetic ShortDraftHeckeBridge


theorem idealRowSum_eq_mobiusRow (F : Finset (Ideal O)) (hF : ∀I∈F,Admissible I)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ) (z : O) :
    let hFpos := fun I hI => (hF I hI).1
    let hFgood := fun I hI P hP => ((hF I hI).2.2 P hP).1
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    idealRowSum F hFpos hFgood χ W z=
      mobiusRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ (normCharacter χ) 1
        (selectedIdealTest F W) z := by
  dsimp only
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hP : (fun i:primePool F => Ideal.span {poolPrimary F i})=(fun i:primePool F => i.val) :=
    funext (poolPrimary_span F hF)
  unfold idealRowSum
  rw [sum_selected_ideals F (fun I hI => (hF I hI).2.1)]
  unfold mobiusRow
  apply Finset.sum_congr rfl
  intro S hS
  have ht := normCharacter_prod (poolPrimary F) S χ
  simp only [hP] at ht
  by_cases hs : (∏i∈S,i.val)∈F
  · rw [if_pos hs]
    simp only [inputColumn,selectedIdealTest,if_pos hs,mul_one,ht]
    have hm : rowCoprimeMask (fun i => Ideal.span {poolPrimary F i}) S 1=1 := by
      simp [rowCoprimeMask,Ideal.IsPrime.one_notMem]
    rw [hm,mul_one]
    simp only [supportMobius,hP,baseChangeWeight,idealSexticRow,pool_support_product]
    ring
  · rw [if_neg hs]
    simp only [inputColumn,selectedIdealTest,if_neg hs,mul_zero,zero_mul]

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})


def sourceFixedMode (s : Finset (SecondExpansionData ι)) (w : Frequency→SecondExpansionData ι→ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O) (V₁ V₂ : ℝ→ℂ) (X₁ X₂ : ℝ) (q : Frequency) : ℂ :=
  ∑x∈s,w q x*
    star (fixedChildRow p hp hcop hg F Ψ₁ m (fixedSecondTest p V₁ X₁ q.1 q.2.2 true)
      (sourceObservation p x).2 (sourceObservation p x).1)*
    fixedChildRow p hp hcop hg F Ψ₂ m (fixedSecondTest p V₂ X₂ q.2.1 q.2.2 false)
      (sourceObservation p x).2 (-(sourceObservation p x).1)

def integratedSourceMode (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (s : Finset (SecondExpansionData ι)) (w : Frequency→SecondExpansionData ι→ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O) (V₁ V₂ : ℝ→ℂ) (X₁ X₂ : ℝ) : ℂ :=
  ∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)*
    sourceFixedMode p hp hcop hg s w F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂ (t₁,t₂,t₃)

end


end InitialMeanSquare

end

end OAI

end


