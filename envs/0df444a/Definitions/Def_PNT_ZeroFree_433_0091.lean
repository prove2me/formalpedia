-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0091
-- name    : PNT_ZeroFree_433_0091
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:59:54.086536+00:00
-- url     : https://prove2.me/theorems/5b03e646-04c7-40f3-8e59-454d2b802a96
-- title:
--   Zero-free region foundations: CubicSieve.ResidualSectors [0091]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.ResidualSectors
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ResidualSectors.lean#L79-L610

import Definitions.Def_PNT_ZeroFree_433_0090

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ResidualSectors.lean#L79-L610
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.ResidualSectors
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

theorem second_common_support_reconstruct {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (E G G' : Finset ι) (hEG : E ⊆ G) (hEG' : E ⊆ G')
    (hr : Ideal.span {secondMaskQuotient p E G hEG} =
      Ideal.span {secondMaskQuotient p E G' hEG'}) : G = G' := by
  apply FirstCauchyArithmetic.family_product_injective (fun i => Ideal.span {p i}) hinj
  have hprod (A : Finset ι) (hEA : E ⊆ A) :
      (∏ i ∈ A, (Ideal.span {p i} : Ideal O)) =
        (∏ i ∈ E, Ideal.span {p i}) * Ideal.span {secondMaskQuotient p E A hEA} := by
    rw [secondMaskQuotient_span]
    simpa only [mul_comm] using (Finset.prod_sdiff (f := fun i => (Ideal.span {p i} : Ideal O)) hEA).symm
  change (∏ i ∈ G, (Ideal.span {p i} : Ideal O)) = ∏ i ∈ G', Ideal.span {p i}
  rw [hprod G hEG, hprod G' hEG', hr]

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def secondSourcePairKernel (e k : O) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (S T : Finset ι) : ℂ :=
  (star (H₁ S) * H₂ T /
    ((‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ) * (‖eisEmbedding (∏ i ∈ T, p i)‖ : ℂ))) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * (primeProductNorm p S * primeProductNorm p T)))

theorem secondFrequencyKernel_eq_kernelPair (F : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k H₁ H₂ W Y =
      (Y : ℂ) * secondKernelPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
        (secondSourcePairKernel p e k H₁ H₂ W Y) := by
  unfold secondFrequencyKernel secondKernelPair
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [if_pos hd, secondSourcePairKernel]
    rw [secondGaussTerm_test_factors, Finset.prod_union hd, map_mul, norm_mul,
      Complex.ofReal_mul, FirstPassCubeLabels.primeProductNorm_union p S T hd]
    ring
  · simp [hd]

theorem secondFrequencyKernel_eq_child_sectors
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k H₁ H₂ W Y =
      (Y : ℂ) * ∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
          secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
            m r c d e k (-k) (secondSourcePairKernel p e k H₁ H₂ W Y) := by
  rw [secondFrequencyKernel_eq_kernelPair,
    secondKernelPair_eq_children p hp hcop hg hinj hc hpr]

def secondSourceCommonCoefficient (Ψ : O →* ℂ) (m c d : O) (G E : Finset ι) : ℂ :=
  (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
      (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ))

def truncatedSecondSource (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) : ℂ :=
  ∑ G ∈ F.powerset, ∑ E : G.powerset, ∑ k ∈ K G E.val,
    secondSourceCommonCoefficient p hg Ψ m c d G E.val *
      secondFrequencyKernel p hp hg hinj F Ψ Ψ m
        (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
        (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y

def secondSourceTail (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) : ℂ :=
  ∑ G ∈ F.powerset, ∑ E : G.powerset,
    secondSourceCommonCoefficient p hg Ψ m c d G E.val *
      ∑' k : {k : O // k ∉ K G E.val},
        secondFrequencyKernel p hp hg hinj F Ψ Ψ m
          (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k.val
          (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y

theorem inputConjugateRow_eq_truncated_add_tail
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) (K : Finset ι → Finset ι → Finset O) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ)) =
      truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K +
        secondSourceTail p hp hg hinj F Ψ m c d H W Y K := by
  rw [inputConjugateRow_smoothed_frequency_blocks p hp hg hinj hc F Ψ m c d H W Y hY]
  unfold truncatedSecondSource secondSourceTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro G hG
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  have hs : Summable (fun k : O => secondFrequencyKernel p hp hg hinj F Ψ Ψ m
      (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
      (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y) := by
    simp_rw [← residualSecondMode_eq_frequencyKernel p hp hg hinj F G E.val
      (Finset.mem_powerset.mp E.property) Ψ Ψ m c d (fun U => H (G ∪ U)) (fun U => H (G ∪ U))]
    exact residualSecondMode_summable p hp hg hinj F G Ψ Ψ m c d
      (fun U => H (G ∪ U)) (fun U => H (G ∪ U))
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)
      (primeSubsetGenerator_ne_zero _ _) W Y hY
  rw [← hs.sum_add_tsum_subtype_compl (K G E.val)]
  simp only [secondSourceCommonCoefficient, mul_add, Finset.mul_sum]
  ring_nf

theorem truncatedSecondSource_eq_child_sectors
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) :
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      ∑ G ∈ F.powerset, ∑ E : G.powerset,
        ∑ z : SecondRayIndex, ∑ V ∈ F.powerset, ∑ k ∈ K G E.val,
          ((Y : ℂ) * secondSourceCommonCoefficient p hg Ψ m c d G E.val *
            secondTotalWeight p hp hcop hg Ψ Ψ m
              (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
              (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k (z,V)) *
          secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ z) (secondRayPlus Ψ z)
            m (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
            (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k (-k)
            (secondSourcePairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
              (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y) := by
  unfold truncatedSecondSource
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro E hE
  simp_rw [secondFrequencyKernel_eq_child_sectors p hp hg hinj hcop hc hpr]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro V hV
  apply Finset.sum_congr rfl
  intro k hk
  ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

@[ext] structure SecondExpansionData (ι : Type*) where
  sourceCommon : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  frequency : O
  deriving DecidableEq

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

def InSecondQuotientSector (r : O) (x : SecondExpansionData ι) : Prop :=
  ∃ h : x.divisor ⊆ x.sourceCommon,
    Ideal.span {secondMaskQuotient p x.divisor x.sourceCommon h} = Ideal.span {r}

def expansionSupportData (C D : Finset ι) (x : SecondExpansionData ι) : SecondSupportData ι where
  common := C
  firstDivisor := D
  secondDivisor := x.divisor
  overlap := x.overlap
  frequency := x.frequency

theorem expansionSupportData_injOn
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (C D : Finset ι) (r : O) :
    Set.InjOn (expansionSupportData (ι := ι) C D) {x | InSecondQuotientSector p r x} := by
  intro x hx y hy h
  obtain ⟨hxE, hxr⟩ := hx
  obtain ⟨hyE, hyr⟩ := hy
  have he := congrArg SecondSupportData.secondDivisor h
  have hv := congrArg SecondSupportData.overlap h
  have hk := congrArg SecondSupportData.frequency h
  change x.divisor = y.divisor at he
  change x.overlap = y.overlap at hv
  change x.frequency = y.frequency at hk
  have hg : x.sourceCommon = y.sourceCommon := by
    cases x with
    | mk G E V k =>
      cases y with
      | mk G' E' V' k' =>
        dsimp only at he hxE hyE hxr hyr ⊢
        subst E'
        exact second_common_support_reconstruct p hinj E G G' hxE hyE (hxr.trans hyr.symm)
  exact SecondExpansionData.ext hg he hv hk

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_quotient_sector (E G : Finset ι) (hEG : E ⊆ G) (r : O)
    (hr : Ideal.span {secondMaskQuotient p E G hEG} = Ideal.span {r}) :
    primeProductNorm p G =
      ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
        ‖eisEmbedding r‖ ^ 2 := by
  unfold primeProductNorm
  rw [secondMaskQuotient_spec p E G hEG, map_mul, norm_mul, mul_pow]
  congr 1
  rw [eisEmbedding_norm_sq_eq_absNorm_span, eisEmbedding_norm_sq_eq_absNorm_span, hr]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem residual_scale_quotient_sector (X : ℝ) (E G : Finset ι) (hEG : E ⊆ G) (r : O)
    (hr : Ideal.span {secondMaskQuotient p E G hEG} = Ideal.span {r}) :
    X / primeProductNorm p G = X /
      (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
        ‖eisEmbedding r‖ ^ 2) := by
  rw [primeProductNorm_quotient_sector p E G hEG r hr]

end

theorem rowCoprimeMask_eq_of_span_eq {ι : Type*} (P : ι → Ideal O)
    (S : Finset ι) {a b : O} (hab : Ideal.span {a} = Ideal.span {b}) :
    rowCoprimeMask P S a = rowCoprimeMask P S b := by
  have hm (i : ι) : a ∈ P i ↔ b ∈ P i := by
    rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.span_singleton_le_iff_mem, hab]
  simp only [rowCoprimeMask, hm]

theorem rowCoprimeMask_mul_eq_of_span_eq {ι : Type*} (P : ι → Ideal O)
    (S : Finset ι) (m : O) {a b : O} (hab : Ideal.span {a} = Ideal.span {b}) :
    rowCoprimeMask P S (m*a) = rowCoprimeMask P S (m*b) := by
  apply rowCoprimeMask_eq_of_span_eq P S
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton, hab]

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace SecondPassIntegration
open ActualEisensteinCubic FirstPassCubeLabels
open SecondPassArithmetic (SecondSupportData secondSectorZ)

def residualColumnScale (X : ℝ) (e r : O) : ℝ :=
  X / (elementNorm e * elementNorm r)

theorem residualColumnScale_pos (X : ℝ) (hX : 0 < X) (e r : O)
    (he : e ≠ 0) (hr : r ≠ 0) : 0 < residualColumnScale X e r :=
  div_pos hX (mul_pos (elementNorm_pos e he) (elementNorm_pos r hr))

theorem secondSectorZ_residualColumnScale {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (X X₀ : ℝ) (hX : 0 < X) (e r : O) (he : e ≠ 0) (hr : r ≠ 0)
    (x : SecondSupportData ι) :
    secondSectorZ p (residualColumnScale X e r) X₀ x =
      Real.log (elementNorm e * elementNorm r * primeProductNorm p x.overlap * X₀ / X) := by
  have hNe := elementNorm_pos e he
  have hNr := elementNorm_pos r hr
  unfold secondSectorZ residualColumnScale
  congr 1
  field_simp

theorem second_divisor_residual_normalization (X : ℝ) (hX : 0 < X)
    (e r : O) (he : e ≠ 0) (hr : r ≠ 0) (a : ℂ) :
    (a / (elementNorm e : ℂ)) * (residualColumnScale X e r : ℂ)⁻¹ =
      a * (elementNorm r : ℂ) / (X : ℂ) := by
  have hNe : (elementNorm e : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (elementNorm_pos e he)
  have hNr : (elementNorm r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (elementNorm_pos r hr)
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hX
  simp only [residualColumnScale, Complex.ofReal_div, Complex.ofReal_mul]
  field_simp

end SecondPassIntegration

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel)
open SecondPassIntegration (exists_fixed_normalized_child_tests elementNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def actualSecondRawVariableSector
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r : O)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (X : SecondSupportData ι → ℝ) (Y : ℝ) : ℂ :=
  ∑ x ∈ s, w x *
    secondChildKernelPair p hp hcop hg F x.overlap Ψ₁ Ψ₂ m r
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.common *
        jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor)
      x.frequency (-x.frequency)
      (radialPairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor)
        x.frequency W g₁ g₂ (X x) (X x) Y)

theorem actualSecondRawVariableSector_fixed_profiles
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j t, windows j t ≠ 0 → |t| ≤ A+H+1) ∧
      ∀ (D E V₀ X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X₀ → 0 < K →
      ∀ (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r : O) (X : SecondSupportData ι → ℝ),
        (∀ x ∈ s, 0 < X x) →
        (∀ x ∈ s, x.frequency ≠ 0) →
        (∀ x ∈ s, |secondSectorZ p (X x) X₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorUd p D x| ≤ H) →
        (∀ x ∈ s, |secondSectorUe p E x| ≤ H) →
        (∀ x ∈ s, |secondSectorUv p V₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorKap p K x| ≤ H) →
        actualSecondRawVariableSector p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r g₁ g₂ W X Y =
          actualSecondVariableSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s
            (fun x => w x * (X x : ℂ)⁻¹) F Ψ₁ Ψ₂ (m*r)
            A₁ A₂ W windows D E V₀ X X₀ K Y := by
  obtain ⟨A₁, A₂, windows, hwc, hws, hwb, hid⟩ :=
    exists_fixed_normalized_child_tests p hp hcop hg g₁ g₂ W A H hA hH hg₁ hg₂
  refine ⟨A₁, A₂, windows, hwc, hws, hwb, ?_⟩
  intro D E V₀ X₀ K Y hD hE hV₀ hX₀ hK B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r X hX hk hz hud hue huv hkap
  simp only [actualSecondRawVariableSector, actualSecondVariableSectorSource]
  apply Finset.sum_congr rfl
  intro x hx
  have heq := hid D E V₀ (X x) X₀ K Y hD hE hV₀ (hX x hx) hX₀ hK F x.overlap Ψ₁ Ψ₂ m r
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.common *
      jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor) x.frequency
    (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _) (hk x hx)
    (hz x hx) (hud x hx) (hue x hx) (huv x hx) (hkap x hx)
  rw [heq]
  simp only [secondSupportLabel, secondSupportRow, actualSecondRow,
    secondSectorZ, secondSectorUd, secondSectorUe, secondSectorUv, secondSectorKap,
    elementNorm, mul_neg]
  ring

end
section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label firstLogDensity)
open SecondPassIntegration (childGeometricMean)
open JointLogSeparation

theorem outerWindow_global_bound (windows : Fin 7 → ℝ → ℂ)
    (hc : ∀ j, HasCompactSupport (windows j)) (hs : ∀ j, Continuous (windows j)) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ z ud ue uv kap : ℝ,
      ‖outerWindow windows z ud ue uv kap‖ ≤ Cw := by
  have hb (j : Fin 7) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, ‖windows j x‖ ≤ B := by
    obtain ⟨B,hB⟩ := ((hc j).isCompact_range (hs j)).bddAbove_image continuous_norm.continuousOn
    have he (x : ℝ) : ‖windows j x‖ ≤ B := hB ⟨windows j x, ⟨x,rfl⟩,rfl⟩
    exact ⟨B,(norm_nonneg _).trans (he 0),he⟩
  choose B hB hbound using hb
  have h0 := hB 0
  have h1 := hB 1
  have h2 := hB 2
  have h3 := hB 3
  have h4 := hB 4
  refine ⟨B 0 * B 1 * B 2 * B 3 * B 4, by positivity, ?_⟩
  intro z ud ue uv kap
  simp only [outerWindow, norm_mul]
  gcongr
  all_goals first | positivity | apply hbound

theorem actual_raw_variable_sector_transfer {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      (∀ z ud ue uv kap : ℝ, ‖outerWindow windows z ud ue uv kap‖ ≤ Cw) ∧
      ∀ D E V₀ X₀ K Y : ℝ, 0 < D → 0 < E → 0 < V₀ → 0 < X₀ → 0 < K → 0 < Y →
      ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ,
        (1+Y*K/(D*E^2*V₀^2*X₀^2))^decayOrder * ‖(𝓕 A₁) t₁*(𝓕 A₂) t₂*b t₃‖ ≤
          Cₛ*firstLogDensity J t₁*firstLogDensity J t₂*firstLogDensity J t₃) ∧
      ∀ (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (s : Finset (SecondSupportData ι)) (T : Finset (Ideal O × O))
        (w : SecondSupportData ι → ℂ) (Bnd lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r : O) (X : SecondSupportData ι → ℝ),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) →
        (∀ x ∈ s, Disjoint x.common B) →
        (∀ x ∈ s, x.firstDivisor ⊆ x.common ∪ B) →
        (∀ x ∈ s, 0 < X x) → (∀ x ∈ s, x.frequency ≠ 0) →
        (∀ x ∈ s, |secondSectorZ p (X x) X₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorUd p D x| ≤ H) →
        (∀ x ∈ s, |secondSectorUe p E x| ≤ H) →
        (∀ x ∈ s, |secondSectorUv p V₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorKap p K x| ≤ H) →
        0 ≤ Bnd → 0 ≤ lengthScale →
        (∀ x ∈ s, (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ x, secondSupportRow p x) ∈ T) →
        (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
        (∀ x ∈ s, ‖w x * (X x : ℂ)⁻¹‖ * ‖outerWindow windows
          (secondSectorZ p (X x) X₀ x) (secondSectorUd p D x) (secondSectorUe p E x)
          (secondSectorUv p V₀ x) (secondSectorKap p K x)‖ ≤ Bnd) →
        ‖actualSecondRawVariableSector p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r g₁ g₂ W X Y‖ ≤
          (Bnd*Cₐ*(lengthScale*Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
          (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
            ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖ *
              childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ (m*r) T (windows 5) (windows 6)
                X₀ X₀ (t₁,t₂,t₃)) := by
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ :=
    actualSecondRawVariableSector_fixed_profiles p hp hcop hg g₁ g₂ W A H hA hH hg₁ hg₂
  obtain ⟨Cw,hCw,hwglobal⟩ := outerWindow_global_bound windows hwc (fun j => (hws j).continuous)
  have hM : ∀ j : Fin 7, 0 ≤ (fun _ : Fin 7 => A+H+1) j := by intro j; dsimp; linarith
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ :=
    actual_second_variable_sector_uniform_transfer p hp hcop hg hinj ε hε A₁ A₂ W windows
      (fun _ => A+H+1) hM hwb decayOrder J
  refine ⟨A₁,A₂,windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,hwglobal,?_⟩
  intro D E V₀ X₀ K Y hD hE hV₀ hX₀ hK hY
  obtain ⟨b,hb,hbound⟩ := htrans D E V₀ X₀ K Y hD hE hV₀ hX₀ hK hY
  refine ⟨b,hb,?_⟩
  intro B v₁ v₂ ε₁ ε₂ s T w Bnd lengthScale F Ψ₁ Ψ₂ m r X hv hCB hdiv hX hk hz hud hue huv hkap
    hBnd hL hmap hT hnorm hw
  rw [hid D E V₀ X₀ K Y hD hE hV₀ hX₀ hK B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r X
    hX hk hz hud hue huv hkap]
  exact hbound B v₁ v₂ ε₁ ε₂ s T (fun x => w x*(X x : ℂ)⁻¹) Bnd lengthScale F Ψ₁ Ψ₂ (m*r) X
    hv hCB hdiv hBnd hL hmap hT hnorm hw

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open JointLogSeparation (halfNormalizationCLM)
open SecondPassIntegration (normalizedColumn_pair_extract_fixed_profiles conjugateProfile)

theorem secondSourcePairKernel_normalized_shift {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (G S T : Finset ι)
    (hGS : Disjoint G S) (hGT : Disjoint G T)
    (e k : O) (X Y : ℝ) (hX : 0 < X)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) :
    secondSourcePairKernel p e k
      (fun A => normalizedColumn p (fun B => g₁ (columnLog p X B)) (G∪A))
      (fun A => normalizedColumn p (fun B => g₂ (columnLog p X B)) (G∪A)) W Y S T =
      (X : ℂ)⁻¹ * radialPairKernel p e k W
        (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂)
        (X / primeProductNorm p G) (X / primeProductNorm p G) Y S T := by
  unfold secondSourcePairKernel
  rw [normalizedColumn_pair_extract_fixed_profiles p hp G S T hGS hGT X hX U hUc hUs
    g₁ g₂ hU₁ hU₂]
  simp only [radialPairKernel, normalizedColumn, SecondPassIntegration.conjugateProfile_apply,
     Complex.star_def, Complex.conj_ofReal, div_eq_mul_inv,
     mul_inv_rev, map_inv₀, map_mul]
  ring_nf

end SecondPassArithmetic

open scoped BigOperators Classical
namespace UnrestrictedIdealReindex
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open PrimaryIdealUnitReindex CanonicalQuadraticSieve

abbrev NonzeroIdeal := {I : Ideal O // I ≠ 0}
abbrev NonzeroElement := {z : O // z ≠ 0}

theorem span_unit_generator (u : Oˣ) (I : NonzeroIdeal) :
    Ideal.span {u.val * idealGenerator I.val} = I.val := by
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, span_idealGenerator]

def unitIdealToElement (p : Oˣ × NonzeroIdeal) : NonzeroElement :=
  ⟨p.1.val * idealGenerator p.2.val, mul_ne_zero p.1.ne_zero (idealGenerator_ne_zero p.2.val p.2.property)⟩

theorem unitIdealToElement_bijective : Function.Bijective unitIdealToElement := by
  constructor
  · intro p q hpq
    have he : p.1.val * idealGenerator p.2.val = q.1.val * idealGenerator q.2.val := congrArg Subtype.val hpq
    have hi : p.2 = q.2 := by
      apply Subtype.ext
      simpa only [span_unit_generator] using congrArg (fun z : O => Ideal.span {z}) he
    have hu : p.1 = q.1 := by
      apply Units.ext
      rw [hi] at he
      exact mul_right_cancel₀ (idealGenerator_ne_zero q.2.val q.2.property) he
    exact Prod.ext hu hi
  · intro z
    let I : NonzeroIdeal := ⟨Ideal.span {z.val}, Ideal.span_singleton_eq_bot.not.mpr z.property⟩
    have ha : Associated (idealGenerator I.val) z.val :=
      Ideal.span_singleton_eq_span_singleton.mp (span_idealGenerator I.val)
    obtain ⟨u, hu⟩ := ha
    refine ⟨(u, I), Subtype.ext ?_⟩
    change u.val * idealGenerator I.val = z.val
    simpa only [mul_comm] using hu

def unitIdealEquiv : Oˣ × NonzeroIdeal ≃ NonzeroElement :=
  Equiv.ofBijective unitIdealToElement unitIdealToElement_bijective

theorem tsum_nonzero_unit_invariant (f : O → ℂ) (hf : Summable f)
    (hu : ∀ (u : Oˣ) (z : O), f (u.val * z) = f z) :
    (∑' z : NonzeroElement, f z.val) = (6 : ℂ) * ∑' I : NonzeroIdeal, f (idealGenerator I.val) := by
  let : Finite Oˣ := finite_units
  let : Fintype Oˣ := Fintype.ofFinite _
  have he : (∑' z : NonzeroElement, f z.val) =
      ∑' p : Oˣ × NonzeroIdeal, f (p.1.val * idealGenerator p.2.val) :=
    (unitIdealEquiv.tsum_eq (fun z : NonzeroElement => f z.val)).symm
  have hs : Summable (fun p : Oˣ × NonzeroIdeal => f (p.1.val * idealGenerator p.2.val)) :=
    unitIdealEquiv.summable_iff.mpr (hf.subtype _)
  rw [he, hs.tsum_prod]
  simp only [hu, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : Fintype.card Oˣ = 6 := by simpa only [Nat.card_eq_fintype_card] using card_units_eq_six
  rw [hc]
  norm_num

theorem tsum_unit_invariant_of_zero (f : O → ℂ) (hf : Summable f) (h0 : f 0 = 0)
    (hu : ∀ (u : Oˣ) (z : O), f (u.val * z) = f z) :
    (∑' z : O, f z) = (6 : ℂ) * ∑' I : NonzeroIdeal, f (idealGenerator I.val) := by
  have he : (∑' z : NonzeroElement, f z.val) = ∑' z : O, f z := by
    apply tsum_subtype_eq_of_support_subset
    intro z hz
    exact fun hz0 => hz (hz0 ▸ h0)
  rw [← he]
  exact tsum_nonzero_unit_invariant f hf hu

end UnrestrictedIdealReindex

end

end OAI

end


