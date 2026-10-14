-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0208_parallel1
-- name    : PNT_ZeroFree_433_0208_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:41:01.796119+00:00
-- url     : https://prove2.me/theorems/869f78d3-4148-4a7e-8081-28c9c932f5e3
-- title:
--   Zero-free region foundations: MeanSquare.ThetaDensity [0208_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.MeanSquare.ThetaDensity
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/ThetaDensity.lean#L324-L642

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0026
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0038_1
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0043
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0053
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0069_1
import Definitions.Def_PNT_ZeroFree_433_0117_1
import Definitions.Def_PNT_ZeroFree_433_0127_parallel1
import Definitions.Def_PNT_ZeroFree_433_0168_parallel1
import Definitions.Def_PNT_ZeroFree_433_0195_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/ThetaDensity.lean
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical


namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups


lemma cuspBarrierProfile_log_derivative_bound :
    ∃D : ℝ,0≤D ∧ ∀v : ℝ,1<v→
      |v*deriv (cuspBarrierProfile 2 3) v|≤D*(1+cuspBarrierProfile 2 3 v) := by
  have hd := (contDiff_infty_iff_deriv.mp (cuspBarrierProfile_smooth 2 3)).2.continuous
  obtain ⟨C,hC⟩ := ((isCompact_Icc : IsCompact (Set.Icc (1:ℝ) 3)).image hd.abs).bddAbove
  let D := max 1 (3*max C 0)
  have hD : 0≤D := le_trans (by norm_num) (le_max_left _ _)
  refine ⟨D,hD,fun v hv => ?_⟩
  by_cases hhigh : 3<v
  · have he : cuspBarrierProfile 2 3 =ᶠ[𝓝 v] (fun x => x-1) := by
      filter_upwards [Ioi_mem_nhds hhigh] with x hx
      rw [cuspBarrierProfile,cuspTransition_one 2 3 x (by norm_num) hx.le,one_mul]
    have hder : deriv (cuspBarrierProfile 2 3) v=1 := by rw [he.deriv_eq]; simp
    rw [hder,mul_one,abs_of_pos (by linarith),he.self_of_nhds]
    have h := mul_le_mul_of_nonneg_right (le_max_left 1 (3*max C 0)) (show 0≤v by linarith)
    dsimp only [D]
    nlinarith
  · have hCv : |deriv (cuspBarrierProfile 2 3) v|≤max C 0 :=
      (hC (Set.mem_image_of_mem _ (show v∈Set.Icc (1:ℝ) 3 from ⟨hv.le,not_lt.mp hhigh⟩))).trans (le_max_left _ _)
    have h1 : |v*deriv (cuspBarrierProfile 2 3) v|≤3*max C 0 := by
      rw [abs_mul,abs_of_pos (by linarith)]
      exact mul_le_mul (not_lt.mp hhigh) hCv (abs_nonneg _) (by positivity)
    have hphi := cuspBarrierProfile_nonneg 2 3 (by norm_num) (by norm_num) v
    exact (h1.trans (le_max_right _ _)).trans (by nlinarith)


end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace SixthPowerAverage
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open EisensteinSchwartzPoisson hiding O
open IdealMobiusDivisorSum hiding O
open ConcreteTraceCRT ShortDraftHeckeBridge
open QuadraticInitialBound hiding O

def totientDensity (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  ∏ P ∈ primeSupport I, (1-(1:ℂ)/(Ideal.absNorm P:ℂ))

theorem idealSupport_card (F : Finset (Ideal ActualEisensteinCubic.O)) {I : Ideal ActualEisensteinCubic.O} (hI : I∈F) :
    (idealSupport F I).card=(primeSupport I).card := by
  rw [primeSupport,←idealSupport_image_eq_factors F hI]
  exact (Finset.card_image_iff.mpr (fun _ _ _ _ h => Subtype.val_injective h)).symm

theorem idealSupport_density (F : Finset (Ideal ActualEisensteinCubic.O)) {I : Ideal ActualEisensteinCubic.O} (hI : I∈F) :
    (∏ i ∈ idealSupport F I, (1-(1:ℂ)/(Ideal.absNorm i.val:ℂ)))=totientDensity I := by
  rw [totientDensity, primeSupport, ←idealSupport_image_eq_factors F hI,
    Finset.prod_image]
  exact fun _ _ _ _ h => Subtype.val_injective h

theorem idealSexticRow_sixth_mask
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (I : Ideal ActualEisensteinCubic.O) (b : ActualEisensteinCubic.O) :
    idealSexticRow F hF hg I (b^6)=
      rowCoprimeMask (fun i : primePool F => i.val) (idealSupport F I) b := by
  let : ∀i : primePool F,(i.val).IsMaximal := primePool_maximal F hF
  exact finiteSquarefreeRow_sixth_power _ _ _ _

theorem idealSexticRow_sixth_radial_summable
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (I : Ideal ActualEisensteinCubic.O) (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    Summable (fun b : ActualEisensteinCubic.O => idealSexticRow F hF hg I (b^6)*V (‖eisEmbedding b‖^2/Y)) := by
  have hs : Summable (fun b : ActualEisensteinCubic.O => V (‖eisEmbedding b‖^2/Y)) := by
    simpa only [scaledRadialTest_apply] using
      (actual_eisenstein_summable_norm (scaledRadialTest V Y hY)).of_norm
  simp_rw [idealSexticRow_sixth_mask]
  convert! hs.indicator {b : ActualEisensteinCubic.O | ¬∃i∈idealSupport F I,b∈i.val} using 1
  funext b
  by_cases hb : ∃i∈idealSupport F I,b∈i.val
  · rw [Set.indicator_of_notMem (show b∉{b : ActualEisensteinCubic.O | ¬∃i∈idealSupport F I,b∈i.val} from fun hn=>hn hb)]
    simp only [rowCoprimeMask,if_pos hb,zero_mul]
  · rw [Set.indicator_of_mem hb]
    simp only [rowCoprimeMask,if_neg hb,one_mul]

theorem idealSexticRow_sixth_average
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    {I : Ideal ActualEisensteinCubic.O} (hI : I∈F) (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    (∑'b : ActualEisensteinCubic.O,idealSexticRow F hF hg I (b^6)*V (‖eisEmbedding b‖^2/Y))=
      (Y:ℂ)*paperRadialFourier V 0*totientDensity I+
      maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y := by
  let : ∀i : primePool F,(i.val).IsMaximal := primePool_maximal F hF
  simp_rw [idealSexticRow_sixth_mask]
  rw [masked_principal_radial_poisson_zero_split _ Subtype.val_injective _ V Y hY,
    idealSupport_density F hI]

theorem idealRowSum_sixth_average {q : ℕ}
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ)
    (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    (∑'b : ActualEisensteinCubic.O, V (‖eisEmbedding b‖^2/Y)*idealRowSum F hF hg χ W (b^6))=
      (Y:ℂ)*paperRadialFourier V 0*
        (∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*totientDensity I)+
      ∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y := by
  have he (b : ActualEisensteinCubic.O) : V (‖eisEmbedding b‖^2/Y)*idealRowSum F hF hg χ W (b^6)=
      ∑I∈F,(baseChangeWeight χ I*W (Ideal.absNorm I))*
        (idealSexticRow F hF hg I (b^6)*V (‖eisEmbedding b‖^2/Y)) := by
    rw [idealRowSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I hI
    ring
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun I _ =>
    (idealSexticRow_sixth_radial_summable F hF hg I V Y hY).mul_left _)]
  simp_rw [tsum_mul_left]
  rw [show (∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
      ∑'b : ActualEisensteinCubic.O,idealSexticRow F hF hg I (b^6)*V (‖eisEmbedding b‖^2/Y))=
      ∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        ((Y:ℂ)*paperRadialFourier V 0*totientDensity I+
          maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y) by
    apply Finset.sum_congr rfl
    intro I hI
    rw [idealSexticRow_sixth_average F hF hg hI V Y hY]]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  ring

theorem sixth_average_remainder_bound {q : ℕ}
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ)
    (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    ‖∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y‖≤
      ∑I∈F,‖W (Ideal.absNorm I)‖*(2:ℝ)^(primeSupport I).card*pvControl V := by
  let : ∀i : primePool F,(i.val).IsMaximal := primePool_maximal F hF
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  have hr := maskedPrincipalRemainder_uniform (fun i : primePool F=>i.val)
    (idealSupport F I) V Y hY
  rw [idealSupport_card F hI] at hr
  rw [norm_mul,norm_mul]
  calc
    _≤(1*‖W (Ideal.absNorm I)‖)*((2:ℝ)^(primeSupport I).card*pvControl V) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (baseChangeWeight_norm_le_one χ I) (norm_nonneg _))
        hr (norm_nonneg _) (by positivity)
    _=_ := by ring

theorem sixth_power_fiber_card (s : Finset ActualEisensteinCubic.O) (z : ActualEisensteinCubic.O) :
    (s.filter (fun b=>b^6=z)).card≤6 := by
  calc
    _≤(Polynomial.nthRoots 6 z).toFinset.card := by
      apply Finset.card_le_card
      intro b hb
      exact Multiset.mem_toFinset.mpr
        ((Polynomial.mem_nthRoots (by norm_num : 0<6)).mpr (Finset.mem_filter.mp hb).2)
    _≤(Polynomial.nthRoots 6 z).card := Multiset.toFinset_card_le _
    _≤6 := Polynomial.card_nthRoots 6 z

theorem sixth_power_average_cauchy (s : Finset ActualEisensteinCubic.O) (V A : ActualEisensteinCubic.O→ℂ)
    (hV : ∀b∈s,‖V b‖≤1) :
    ‖∑b∈s,V b*A (b^6)‖^2≤
      6*s.card*∑z∈s.image (fun b=>b^6),‖A z‖^2 := by
  have hc := DescentWeightedCauchy.weighted_cauchy_sq s V (fun b=>A (b^6)) (fun _=>1)
  simp only [star_one,mul_one,norm_one,one_pow,mul_one] at hc
  have hp := DescentWeightedCauchy.weighted_energy_pushforward s (s.image (fun b=>b^6))
    (fun b=>b^6) V A (fun _=>6) (fun b hb=>Finset.mem_image.mpr ⟨b,hb,rfl⟩) (by
      intro z hz
      calc
        _≤∑b∈s with b^6=z,(1:ℝ) := Finset.sum_le_sum (fun b hb=>hV b (Finset.mem_filter.mp hb).1)
        _=(s.filter (fun b=>b^6=z)).card := by simp
        _≤6 := by exact_mod_cast sixth_power_fiber_card s z)
  have hv : (∑b∈s,‖V b‖)≤s.card := by
    simpa using Finset.sum_le_sum (fun b hb=>hV b hb)
  apply hc.trans
  calc
    _≤(∑z∈s.image (fun b=>b^6),6*‖A z‖^2)*(s.card:ℝ) :=
      mul_le_mul hp hv (Finset.sum_nonneg (fun _ _=>norm_nonneg _))
        (Finset.sum_nonneg (fun _ _=>by positivity))
    _=_ := by rw [←Finset.mul_sum]; ring

end SixthPowerAverage

end

end OAI

end


