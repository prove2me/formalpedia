-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0209_parallel1
-- name    : PNT_ZeroFree_433_0209_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:48:15.541582+00:00
-- url     : https://prove2.me/theorems/e3522da8-5c2c-4ea4-bb44-23c8c8606867
-- title:
--   Zero-free region foundations: Mellin.SixthPowerAverage [0209_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Mellin.SixthPowerAverage
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/SixthPowerAverage.lean#L84-L680

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0026
import Definitions.Def_PNT_ZeroFree_433_0029
import Definitions.Def_PNT_ZeroFree_433_0030
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0033
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0043
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0058
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0109_1
import Definitions.Def_PNT_ZeroFree_433_0118_parallel1
import Definitions.Def_PNT_ZeroFree_433_0122_parallel1
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0127_parallel2
import Definitions.Def_PNT_ZeroFree_433_0128_parallel1
import Definitions.Def_PNT_ZeroFree_433_0129_parallel1
import Definitions.Def_PNT_ZeroFree_433_0135_parallel1
import Definitions.Def_PNT_ZeroFree_433_0137_parallel2
import Definitions.Def_PNT_ZeroFree_433_0181_parallel1
import Definitions.Def_PNT_ZeroFree_433_0208_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/SixthPowerAverage.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace SixthPowerAverage

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

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Metric
open EisensteinSchwartzPoisson

theorem exists_averaging_test :
    ∃V : 𝓢(ℝ,ℂ),
      (∀x,‖V x‖≤1) ∧
      (Function.support (V:ℝ→ℂ)⊆Set.Icc ((1:ℝ)/2) 1) ∧
      V 0=0 ∧ paperRadialFourier V 0≠0 := by
  let f : ContDiffBump ((3:ℝ)/4) := ⟨1/8,1/4,by norm_num,by norm_num⟩
  let g : ℝ→ℂ := fun x=>(f x:ℂ)
  have hgs : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp f.contDiff
  have hsupport : Function.support g⊆Set.Icc ((1:ℝ)/2) 1 := by
    intro x hx
    have hf : f x≠0 := by simpa only [g,Function.mem_support,ne_eq,Complex.ofReal_eq_zero] using hx
    have hh : |x-(3:ℝ)/4|<1/4 := by
      have hi : x∈Function.support (f:ℝ→ℝ) := hf
      rw [f.support_eq] at hi
      simpa only [Metric.mem_ball,Real.dist_eq,f] using hi
    exact ⟨by linarith [(abs_lt.mp hh).1],by linarith [(abs_lt.mp hh).2]⟩
  have hgc : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupport
  let V : 𝓢(ℝ,ℂ) := hgc.toSchwartzMap hgs
  have hz : V 0=0 := by
    by_contra h
    have hh := (hsupport h).1
    norm_num at hh
  refine ⟨V,?_,hsupport,hz,?_⟩
  · intro x
    change ‖(f x:ℂ)‖≤1
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg f.nonneg]
    exact f.le_one
  · rw [paperRadialFourier_zero_eq_halfline]
    have he : (∫x : ℝ in Set.Ioi 0,(V x))=∫x : ℝ,(f x:ℂ) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      by_contra hn
      have hp := (hsupport hn).1
      simp only [Set.mem_Ioi,not_lt] at hx
      linarith
    rw [he,integral_complex_ofReal]
    apply mul_ne_zero
    · apply div_ne_zero
      · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
      · exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<3))
    · have hfint : Integrable (f:ℝ→ℝ) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
      have hfpos : 0 < ∫x : ℝ,f x := by
        apply (integral_pos_iff_support_of_nonneg f.nonneg' hfint).mpr
        rw [f.support_eq]
        exact measure_ball_pos volume _ f.rOut_pos
      exact_mod_cast hfpos.ne'

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge

lemma prime_coprime_span_iff (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (b : ActualEisensteinCubic.O) : IsCoprime P (Ideal.span {b}) ↔ b∉P := by
  rw [Ideal.isCoprime_iff_codisjoint,
    ←(Ideal.isMaximal_def.mp (inferInstance : P.IsMaximal)).not_le_iff_codisjoint,
    Ideal.span_singleton_le_iff_mem]

lemma squarefree_sixth_row_coprime
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    {I : Ideal ActualEisensteinCubic.O} (hI : I∈F) (hsq : Squarefree I)
    (b : ActualEisensteinCubic.O) :
    idealSexticRow F hF hg I (b^6)=if IsCoprime I (Ideal.span {b}) then 1 else 0 := by
  let : ∀i : primePool F,(i.val).IsMaximal:=primePool_maximal F hF
  have hc : IsCoprime I (Ideal.span {b}) ↔ ¬∃i∈idealSupport F I,b∈i.val := by
    conv_lhs => rw [←idealSupport_product_eq F hI hsq]
    rw [IsCoprime.prod_left_iff]
    simp only [prime_coprime_span_iff,not_exists,not_and]
  rw [idealSexticRow_sixth_mask,hc]
  by_cases hn : ∃i∈idealSupport F I,b∈i.val <;> simp [rowCoprimeMask,hn]

theorem idealRowSum_sixth_eq_coprime_sum {q : ℕ}
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ) (b : ActualEisensteinCubic.O) :
    idealRowSum F hF hg χ W (b^6)=
      ∑I∈F with IsCoprime I (Ideal.span {b}),baseChangeWeight χ I*W (Ideal.absNorm I) := by
  rw [idealRowSum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hsq : Squarefree I
  · rw [squarefree_sixth_row_coprime F hF hg hI hsq b]
    split_ifs <;> simp
  · rw [ConcretePrimeRowBridge.baseChangeWeight_zero_of_not_squarefree χ I hsq]
    simp

end

section

open scoped BigOperators Classical SchwartzMap ContDiff

section
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open EisensteinSchwartzPoisson hiding O
open IdealMobiusDivisorSum hiding O
open ConcreteTraceCRT ShortDraftHeckeBridge
open QuadraticInitialBound hiding O

def averagingRows (Y : ℝ) : Finset ActualEisensteinCubic.O := rowNormDisk ⌊Y⌋₊

theorem mem_averagingRows {Y : ℝ} {b : ActualEisensteinCubic.O} (hY : 0≤Y) :
    b∈averagingRows Y ↔ b≠0 ∧ ‖eisEmbedding b‖^2≤Y := by
  rw [averagingRows,mem_rowNormDisk]
  have hz : 0<Ideal.absNorm (Ideal.span {b}:Ideal ActualEisensteinCubic.O) ↔ b≠0 := by
    rw [Nat.pos_iff_ne_zero,ne_eq,Ideal.absNorm_eq_zero_iff,Ideal.span_singleton_eq_bot]
  rw [hz,Nat.le_floor_iff hY,←eisEmbedding_norm_sq_eq_absNorm_span]

theorem averagingRows_card (Y : ℝ) (hY : 1≤Y) :
    ((averagingRows Y).card:ℝ)≤128*Y :=
  DescentFiberCost.finite_element_count_real _ Y hY
    (fun b hb=>(mem_averagingRows (by linarith)).mp hb |>.2)

theorem averagingRows_power_norm (Y : ℝ) (hY : 1≤Y)
    {z : ActualEisensteinCubic.O} (hz : z∈(averagingRows Y).image (fun b=>b^6)) :
    z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤Y^6 := by
  obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hz
  have hh:=(mem_averagingRows (by linarith : (0:ℝ)≤Y)).mp hb
  refine ⟨pow_ne_zero _ hh.1,?_⟩
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,map_pow,norm_pow,
    ←pow_mul,show (6:ℕ)*2=2*6 by omega,pow_mul]
  exact pow_le_pow_left₀ (sq_nonneg _) hh.2 _

theorem average_tsum_eq_finite (V : 𝓢(ℝ,ℂ))
    (hV : Function.support (V:ℝ→ℂ)⊆Set.Icc ((1:ℝ)/2) 1)
    (hV0 : V 0=0) (Y : ℝ) (hY : 0<Y) (A : ActualEisensteinCubic.O→ℂ) :
    (∑'b : ActualEisensteinCubic.O,V (‖eisEmbedding b‖^2/Y)*A (b^6))=
      ∑b∈averagingRows Y,V (‖eisEmbedding b‖^2/Y)*A (b^6) := by
  apply tsum_eq_sum
  intro b hb
  have hz : V (‖eisEmbedding b‖^2/Y)=0 := by
    by_contra hv
    apply hb
    apply (mem_averagingRows hY.le).mpr
    refine ⟨?_,?_⟩
    · intro he
      simp only [he,map_zero,norm_zero,zero_pow (by decide : (2:ℕ)≠0),zero_div,hV0] at hv
      exact hv trivial
    · exact (div_le_one hY).mp (hV hv).2
  rw [hz,zero_mul]

theorem average_tsum_cauchy (V : 𝓢(ℝ,ℂ))
    (hV : ∀x,‖V x‖≤1)
    (hs : Function.support (V:ℝ→ℂ)⊆Set.Icc ((1:ℝ)/2) 1)
    (hV0 : V 0=0) (Y : ℝ) (hY : 1≤Y) (A : ActualEisensteinCubic.O→ℂ) :
    ‖∑'b : ActualEisensteinCubic.O,V (‖eisEmbedding b‖^2/Y)*A (b^6)‖^2≤
      768*Y*∑z∈(averagingRows Y).image (fun b=>b^6),‖A z‖^2 := by
  rw [average_tsum_eq_finite V hs hV0 Y (by linarith) A]
  apply (sixth_power_average_cauchy _ _ _ (fun b hb=>hV _)).trans
  have hc:=averagingRows_card Y hY
  nlinarith [Finset.sum_nonneg (s:=(averagingRows Y).image (fun b=>b^6))
    (fun z _=>sq_nonneg ‖A z‖)]

theorem average_remainder_small_power (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ {q : ℕ}
      (F : Finset (Ideal ActualEisensteinCubic.O)) (_hF : ∀I∈F,I≠⊥)
      (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ)
      (V : 𝓢(ℝ,ℂ)) (Y lengthScale G : ℝ),0<Y → 1≤lengthScale → 0≤G →
      (∀n,‖W n‖≤G) → (∀I∈F,W (Ideal.absNorm I)≠0→(Ideal.absNorm I:ℝ)≤lengthScale) →
      ‖∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F=>i.val) (idealSupport F I) V Y‖≤
      C*G*pvControl V*lengthScale^(1+ε) := by
  obtain ⟨C,hC,hp⟩:=SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨128*C,by positivity,?_⟩
  intro q F hF χ W V Y lengthScale G hY hL hG hW hnorm
  apply (sixth_average_remainder_bound F hF χ W V Y hY).trans
  let T:=F.filter (fun I=>W (Ideal.absNorm I)≠0)
  have he : (∑I∈F,‖W (Ideal.absNorm I)‖*(2:ℝ)^(primeSupport I).card*pvControl V)=
      ∑I∈T,‖W (Ideal.absNorm I)‖*(2:ℝ)^(primeSupport I).card*pvControl V := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro I hI hn
    have hz : W (Ideal.absNorm I)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hI,hh⟩)
    simp only [hz,norm_zero,zero_mul]
  have hc : (T.card:ℝ)≤128*lengthScale :=
    DescentFiberCost.finite_ideal_count_real T lengthScale hL
      (fun I hI=>hF I (Finset.mem_filter.mp hI).1)
      (fun I hI=>hnorm I (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hI).2)
  rw [he]
  calc
    _≤∑I∈T,G*(C*lengthScale^ε)*pvControl V := by
      apply Finset.sum_le_sum
      intro I hI
      have hh:=Finset.mem_filter.mp hI
      have hb:=(hp I (hF I hh.1)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm I hh.1 hh.2) hε.le) hC.le)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hW _) hb (by positivity) hG) (pvControl_nonneg V)
    _=(T.card:ℝ)*(G*(C*lengthScale^ε)*pvControl V) := by simp
    _≤128*lengthScale*(G*(C*lengthScale^ε)*pvControl V) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg (by positivity) (pvControl_nonneg V))
    _=(128*C)*G*pvControl V*lengthScale^(1+ε) := by
      rw [Real.rpow_add (by linarith : (0:ℝ)<lengthScale),Real.rpow_one]
      ring

theorem totient_sum_normalized_bound {q : ℕ}
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ)
    (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    Y*‖paperRadialFourier V 0‖*
      ‖∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*totientDensity I‖≤
      ‖∑'b : ActualEisensteinCubic.O,V (‖eisEmbedding b‖^2/Y)*idealRowSum F hF hg χ W (b^6)‖+
      ‖∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F=>i.val) (idealSupport F I) V Y‖ := by
  have he:=idealRowSum_sixth_average F hF hg χ W V Y hY
  have hh:=norm_sub_le (∑'b : ActualEisensteinCubic.O,V (‖eisEmbedding b‖^2/Y)*idealRowSum F hF hg χ W (b^6))
    (∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
      maskedPrincipalRemainder (fun i : primePool F=>i.val) (idealSupport F I) V Y)
  rw [he,add_sub_cancel_right,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY] at hh
  rwa [←he] at hh

end

open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open EisensteinSchwartzPoisson hiding O
open ConcreteTraceCRT ShortDraftHeckeBridge
open QuadraticInitialBound hiding O
open InitialMeanSquare
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion


end

section

open scoped BigOperators Classical SchwartzMap ContDiff Topology
open Filter Asymptotics MeasureTheory
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge
open IdealMobiusDivisorSum hiding O
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion
open InitialMeanSquare

def weightedMoebius {q : ℕ} (χ : DirichletCharacter ℂ q) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  baseChangeWeight χ I*totientDensity I

def outsideWeight {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) : Ideal ActualEisensteinCubic.O→ℂ :=
  FiniteSFactor.outsideWeight S (weightedMoebius χ)

def weightedCoeff {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) : ℕ→ℂ :=
  FiniteSFactor.outsideCoeff S (weightedMoebius χ)

theorem totientDensity_norm_le_one (I : Ideal ActualEisensteinCubic.O) : ‖totientDensity I‖≤1 := by
  rw [totientDensity,norm_prod]
  apply Finset.prod_le_one
  · intro P hP
    exact norm_nonneg _
  · intro P hP
    have hN : (2:ℝ)≤Ideal.absNorm P:=by exact_mod_cast IdealDivisorBound.support_norm_two_le hP
    have hNp : (0:ℝ)<Ideal.absNorm P:=by linarith
    have he : (1-(1:ℂ)/(Ideal.absNorm P:ℂ))=((1-1/(Ideal.absNorm P:ℝ):ℝ):ℂ) := by push_cast;rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    · exact sub_le_self _ (by positivity)
    · have hi : (1:ℝ)/(Ideal.absNorm P:ℝ)≤1 := (div_le_one hNp).mpr (by linarith)
      linarith

theorem weightedMoebius_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    (I : Ideal ActualEisensteinCubic.O) : ‖weightedMoebius χ I‖≤1 := by
  rw [weightedMoebius,norm_mul]
  exact (mul_le_mul (ConcretePrimeRowBridge.baseChangeWeight_norm_le_one χ I)
    (totientDensity_norm_le_one I) (norm_nonneg _) zero_le_one).trans_eq (mul_one _)

@[simp] theorem weightedMoebius_zero {q : ℕ} (χ : DirichletCharacter ℂ q) :
    weightedMoebius χ (0:Ideal ActualEisensteinCubic.O)=0 := by
  change ((UniqueFactorizationMonoid.moebius (0:Ideal ActualEisensteinCubic.O):ℂ)*
    χ (Ideal.absNorm (0:Ideal ActualEisensteinCubic.O)))*totientDensity 0=0
  rw [UniqueFactorizationMonoid.moebius_zero,Int.cast_zero,zero_mul,zero_mul]

theorem outsideWeight_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (I : Ideal ActualEisensteinCubic.O) :
    ‖outsideWeight χ S I‖≤1 := by
  unfold outsideWeight FiniteSFactor.outsideWeight
  split_ifs
  · exact weightedMoebius_norm_le_one χ I
  · simp

@[simp] theorem outsideWeight_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) :
    outsideWeight χ S (0:Ideal ActualEisensteinCubic.O)=0 := by
  unfold outsideWeight FiniteSFactor.outsideWeight
  split_ifs
  · exact weightedMoebius_zero χ
  · rfl

@[simp] theorem weightedCoeff_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) : weightedCoeff χ S 0=0 := by
  unfold weightedCoeff FiniteSFactor.outsideCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hz:=Ideal.absNorm_eq_zero_iff.mp (FiniteSFactor.mem_fiber.mp hI)
  change outsideWeight χ S I=0
  rw [hz]
  exact outsideWeight_zero χ S

theorem weightedCoeff_norm_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (n : ℕ) : ‖weightedCoeff χ S n‖≤128*n := by
  by_cases hn : n=0
  · subst n
    simp
  have hn1 : (1:ℝ)≤n:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hc:=DescentFiberCost.finite_ideal_count_real (FiniteSFactor.fiber n) n hn1 (by
      intro I hI hz
      have hh:=FiniteSFactor.mem_fiber.mp hI
      rw [hz] at hh
      simp only [Ideal.absNorm_bot] at hh
      exact hn hh.symm) (by
      intro I hI
      exact_mod_cast (FiniteSFactor.mem_fiber.mp hI).le)
  calc
    _≤∑I∈FiniteSFactor.fiber n,‖outsideWeight χ S I‖:=norm_sum_le _ _
    _≤∑I∈FiniteSFactor.fiber n,(1:ℝ):=Finset.sum_le_sum (fun I hI=>outsideWeight_norm_le_one χ S I)
    _=(FiniteSFactor.fiber n).card:=by simp
    _≤128*n:=hc

theorem weightedCoeff_LSeriesSummable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (s : ℂ) (hs : 2<s.re) :
    LSeriesSummable (weightedCoeff χ S) s := by
  apply LSeriesSummable_of_isBigO_rpow hs
  apply Asymptotics.IsBigO.of_bound 128
  filter_upwards [] with n
  simpa only [show (2:ℝ)-1=1 by norm_num,Real.rpow_one,Real.norm_natCast]
    using weightedCoeff_norm_bound χ S n

theorem weightedCoeff_hasSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (b Z : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0→x≤b) (D : ℕ) (hD : b*Z≤D) :
    HasSum (fun n : ℕ=>weightedCoeff χ S n*W ((n:ℝ)/Z))
      (∑I∈outsideIdealsUpTo S D,baseChangeWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I) := by
  have ht (n : ℕ) (hn : n∉Finset.Icc 1 D) : weightedCoeff χ S n*W ((n:ℝ)/Z)=0 := by
    by_cases hn0 : n=0
    · subst n
      simp
    · have hnD : D<n := by simp only [Finset.mem_Icc] at hn;omega
      have hz : W ((n:ℝ)/Z)=0 := by
        by_contra hw
        have hh:=(div_le_iff₀ hZ).mp (hW _ hw)
        have hl : (D:ℝ)<n:=by exact_mod_cast hnD
        linarith
      rw [hz,mul_zero]
  have hh : HasSum (fun n : ℕ=>weightedCoeff χ S n*W ((n:ℝ)/Z))
      (∑n∈Finset.Icc 1 D,weightedCoeff χ S n*W ((n:ℝ)/Z)) :=
    hasSum_sum_of_ne_finset_zero ht
  have he:=outsideIdealSum_eq_outsideCoeff_sum S D (weightedMoebius χ)
    (fun n=>W ((n:ℝ)/Z))
  change _=(∑n∈Finset.Icc 1 D,weightedCoeff χ S n*W ((n:ℝ)/Z)) at he
  rw [←he] at hh
  convert! hh using 1
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only [weightedMoebius]
  ring

theorem ideal_weighted_hasSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (b Z : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0→x≤b) (D : ℕ) (hD : b*Z≤D) :
    HasSum (fun I : Ideal ActualEisensteinCubic.O=>outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z))
      (∑I∈outsideIdealsUpTo S D,baseChangeWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I) := by
  have ht (I : Ideal ActualEisensteinCubic.O) (hI : I∉outsideIdealsUpTo S D) :
      outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z)=0 := by
    by_cases hI0 : I=0
    · rw [hI0,outsideWeight_zero,zero_mul]
    by_cases hg : ∀P∈S,¬P∣I
    · have hz : W ((Ideal.absNorm I:ℝ)/Z)=0 := by
        by_contra hn
        apply hI
        refine mem_outsideIdealsUpTo.mpr ⟨?_,?_,hg⟩
        · exact Nat.one_le_iff_ne_zero.mpr (fun hh=>hI0 (Ideal.absNorm_eq_zero_iff.mp hh))
        · exact_mod_cast ((div_le_iff₀ hZ).mp (hW _ hn)).trans hD
      rw [hz,mul_zero]
    · simp [outsideWeight,FiniteSFactor.outsideWeight,hg]
  have hh : HasSum (fun I : Ideal ActualEisensteinCubic.O=>outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z))
      (∑I∈outsideIdealsUpTo S D,outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z)) :=
    hasSum_sum_of_ne_finset_zero ht
  convert! hh using 1
  apply Finset.sum_congr rfl
  intro I hI
  simp only [outsideWeight,FiniteSFactor.outsideWeight,if_pos (mem_outsideIdealsUpTo.mp hI).2.2,weightedMoebius]
  ring

end

open scoped BigOperators Classical SchwartzMap ContDiff Topology
open Filter Asymptotics MeasureTheory
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion
open InitialMeanSquare CompactMellinBridge

def weightedCompactSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (t : ℝ) : ℂ :=
  ∑'n : ℕ,weightedCoeff χ S n*W ((n:ℝ)*t)

theorem weightedCompactSum_hasSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ)
    (hW : ∀x,2≤x→W x=0) (t : ℝ) (ht : 0<t) :
    HasSum (fun n : ℕ=>weightedCoeff χ S n*W ((n:ℝ)*t)) (weightedCompactSum χ S W t) := by
  obtain ⟨N,hN⟩:=exists_nat_gt (2/t)
  have hz (n : ℕ) (hn : n∉Finset.range N) : weightedCoeff χ S n*W ((n:ℝ)*t)=0 := by
    have hNn : N≤n:=by simpa only [Finset.mem_range,not_lt] using hn
    have htwo : 2≤(n:ℝ)*t := by
      have hh:=(div_lt_iff₀ ht).mp hN
      exact hh.le.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hNn) ht.le)
    rw [hW _ htwo,mul_zero]
  exact (summable_of_ne_finset_zero hz).hasSum

theorem weightedCompactSum_inv_eq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (Z b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0→x≤b) (D : ℕ) (hD : b*Z≤D) :
    weightedCompactSum χ S W Z⁻¹=
      ∑I∈outsideIdealsUpTo S D,baseChangeWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I := by
  simpa only [weightedCompactSum,div_eq_mul_inv] using
    (weightedCoeff_hasSum χ S W b Z hZ hW D hD).tsum_eq

theorem weightedCompactSum_eq_ideal_tsum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (Z b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0→x≤b) :
    weightedCompactSum χ S W Z⁻¹=
      ∑'I : Ideal ActualEisensteinCubic.O,outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z) := by
  have hD : b*Z≤(⌈b*Z⌉₊:ℝ):=Nat.le_ceil _
  rw [weightedCompactSum_inv_eq χ S W Z b hZ hW _ hD,
    (ideal_weighted_hasSum χ S W b Z hZ hW _ hD).tsum_eq]


theorem weightedCompactMellin_eq_series {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀) (S : Finset (Ideal ActualEisensteinCubic.O))
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : ∀x,x≤1 ∨ 2≤x→W x=0)
    (s : ℂ) (hRe : 2<s.re) :
    mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s)=
      mellin W s*LSeries (weightedCoeff χ S) s := by
  have hls:=weightedCoeff_LSeriesSummable χ S s hRe
  exact mellin_weighted_sum (weightedCoeff χ S) W (weightedCompactSum χ S W) s
    (weightedCoeff_zero χ S) (weightedCompactSum_hasSum χ S W (fun x hx=>hs x (Or.inr hx)))
    (weighted_term_integrable _ (weightedCoeff_zero χ S) W s (compact_weight_mellin_convergent W hW hs s))
    (weighted_terms_fubini _ (weightedCoeff_zero χ S) W s hls) hls


end SixthPowerAverage

end

end OAI

end


