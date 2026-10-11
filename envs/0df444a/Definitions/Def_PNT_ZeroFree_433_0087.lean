-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0087
-- name    : PNT_ZeroFree_433_0087
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:51:01.638976+00:00
-- url     : https://prove2.me/theorems/129bed47-03af-4f61-a21b-c2f7e16ad99a
-- title:
--   Zero-free region foundations: CubicSieve.FrequencyBlocks [0087]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.FrequencyBlocks
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/FrequencyBlocks.lean#L89-L702

import Definitions.Def_PNT_ZeroFree_433_0086

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/FrequencyBlocks.lean#L89-L702
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.FrequencyBlocks
section
namespace OAI

noncomputable section

namespace SecondPassArithmetic

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

section

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem inputConjugateRow_smoothed_frequency_blocks
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ)) =
    ∑ G ∈ F.powerset,
      (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
      ∑ E : G.powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E.val, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖ ^ 2 : ℝ)) *
        ∑' k : O,
          secondFrequencyKernel p hp hg hinj F Ψ Ψ m
            (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
            (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
            (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y := by
  rw [inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ m c d H W Y hY]
  apply Finset.sum_congr rfl
  intro G hG
  change secondOverlapBlock p hp hg hinj F G Ψ m c d H W Y = _
  rw [secondOverlapBlock_eq_modes p hp hg hinj F G Ψ m c d H W Y hY]
  congr 1
  rw [← Finset.sum_coe_sort (s := G.powerset)]
  apply Finset.sum_congr rfl
  intro E hE
  congr 1
  apply tsum_congr
  intro k
  exact residualSecondMode_eq_frequencyKernel p hp hg hinj F G E.val
    (Finset.mem_powerset.mp E.property) Ψ Ψ m c d
    (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) k W Y

theorem firstCoreInputRow_finite_le_frequency_blocks
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (T : Finset O) (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) :
    let Ψ' := firstCoreTwist negative χ Ψ r
    let m' := m * FirstPassCubeLabels.b0Label p B v ε₁ ε₂
    let c' := c * FirstPassCubeLabels.jLabel p B v ε₁ ε₂
    let H' := firstCoreTest H V y negative t D
    (∑ z ∈ T, ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) ≤
      (∑ G ∈ (F \ D).powerset,
        (↑(‖secondInputCoefficient p hg Ψ' m' c' d (fun _ => 1) G‖ ^ 2) : ℂ) *
        ∑ E : G.powerset,
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E.val, Ideal.span {p i}) : ℂ) /
            (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖ ^ 2 : ℝ)) *
          ∑' k : O,
            secondFrequencyKernel p hp hg hinj (F \ D) Ψ' Ψ' m'
              (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c' d
              (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
              (fun U => H' (G ∪ U)) (fun U => H' (G ∪ U)) rowMajorant Y).re := by
  dsimp only
  have h := finite_row_energy_le_rowMajorant
    (firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t) T Y hY hT
  rw [firstCoreInputRow_smoothed_sign p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t rowMajorant Y,
    inputConjugateRow_smoothed_frequency_blocks p hp hg hinj hc] at h
  · exact h
  · exact hY

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportConjugateSum supportMobius)
open RayFourExpansion (RayCharacter)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
lemma finiteSquarefreeRow_zero_of_nonempty (S : Finset ι) (hS : S.Nonempty) :
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S 0 = 0 := by
  obtain ⟨i, hi⟩ := hS
  apply FirstPassCubeLabels.row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg S 0
  have h : ∃ j ∈ S, (0 : O) ∈ Ideal.span {p j} := ⟨i, hi, Ideal.zero_mem _⟩
  simp only [rowCoprimeMask, if_pos h]

theorem inputConjugateRow_zero (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) : inputConjugateRow p hg F Ψ m c d H 0 = H ∅ := by
  unfold inputConjugateRow supportConjugateSum
  rw [Finset.sum_eq_single ∅]
  · have hm : supportMobius (fun i => Ideal.span {p i}) ∅ = 1 := by
      simp only [supportMobius, Finset.prod_empty, UniqueFactorizationMonoid.moebius_one, Int.cast_one]
    rw [hm]
    simp [secondInputCoefficient, rowCoprimeMask, finiteSquarefreeRow]
  · intro S hS hne
    rw [finiteSquarefreeRow_zero_of_nonempty p hg S (Finset.nonempty_iff_ne_empty.mpr hne),
      star_zero, mul_zero]
  · simp

theorem firstCoreInputRow_zero
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t 0 =
      firstCoreTest H V y negative t D ∅ := by
  unfold firstCoreInputRow
  simp only [neg_zero, ite_self, inputConjugateRow_zero]

end

def nonzeroRowMajorantSum (P : O → ℂ) (Y : ℝ) : ℂ :=
  ∑' z : O, if z = 0 then 0 else
    rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)

lemma nonzeroRowMajorant_summable (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun z : O => if z = 0 then 0 else
      rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rowMajorantBall Y) ?_).summable
  intro z hz
  rw [rowMajorant_zero_outside Y hY z hz]
  simp

theorem nonzeroRowMajorantSum_eq_sub (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    nonzeroRowMajorantSum P Y =
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) -
        (↑(‖P 0‖ ^ 2) : ℂ) := by
  have h := (rowMajorant_summable P Y hY).tsum_eq_add_tsum_ite 0
  have h0 : rowMajorant (0 : ℝ) = 1 := rowMajorant_one 0 (by norm_num)
  simp only [map_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, h0, one_mul] at h
  change _ = _ + nonzeroRowMajorantSum P Y at h
  rw [h]
  ring

theorem finite_nonzero_row_energy_le_majorant (P : O → ℂ) (T : Finset O)
    (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0) :
    (∑ z ∈ T, ‖P z‖ ^ 2) ≤ (nonzeroRowMajorantSum P Y).re := by
  have hs := nonzeroRowMajorant_summable P Y hY
  unfold nonzeroRowMajorantSum
  rw [Complex.re_tsum hs]
  calc
    _ = ∑ z ∈ T, (if z = 0 then (0 : ℂ) else
        rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)).re := by
      apply Finset.sum_congr rfl
      intro z hz
      have hratio : |‖eisEmbedding z‖ ^ 2 / Y| ≤ 1 := by
        rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hY.le)]
        apply (div_le_one hY).2
        rw [eisEmbedding_norm_sq_eq_absNorm_span]
        exact hT z hz
      rw [if_neg (hT0 z hz), rowMajorant_one _ hratio, one_mul, Complex.ofReal_re]
    _ ≤ _ := by
      apply (Complex.hasSum_re hs.hasSum).summable.sum_le_tsum
      intro z hz
      split_ifs
      · norm_num
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        exact mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem inputConjugateRow_nonzero_correction (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (Y : ℝ) (hY : 0 < Y) :
    nonzeroRowMajorantSum (inputConjugateRow p hg F Ψ m c d H) Y =
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ)) - (↑(‖H ∅‖ ^ 2) : ℂ) := by
  rw [nonzeroRowMajorantSum_eq_sub _ Y hY, inputConjugateRow_zero]

theorem firstCoreInputRow_nonzero_correction
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (Y : ℝ) (hY : 0 < Y) :
    nonzeroRowMajorantSum (firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t) Y =
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)) -
          (↑(‖firstCoreTest H V y negative t D ∅‖ ^ 2) : ℂ) := by
  rw [nonzeroRowMajorantSum_eq_sub _ Y hY, firstCoreInputRow_zero]

theorem firstCoreInputRow_finite_le_corrected_source
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (T : Finset O) (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0) :
    (∑ z ∈ T, ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) ≤
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)).re -
          ‖firstCoreTest H V y negative t D ∅‖ ^ 2 := by
  have h := finite_nonzero_row_energy_le_majorant
    (firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t) T Y hY hT hT0
  rw [firstCoreInputRow_nonzero_correction p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t Y hY,
    Complex.sub_re, Complex.ofReal_re] at h
  exact h

end

section

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

lemma firstCoreTest_empty_mass {ι : Type*} [DecidableEq ι]
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (negative : Bool) (t : ℝ) (D : Finset ι) :
    ‖firstCoreTest H V y negative t D ∅‖ ^ 2 = ‖H D‖ ^ 2 * ‖V (y D)‖ ^ 2 := by
  cases negative <;> simp only [firstCoreTest, Finset.union_empty, Bool.false_eq_true,
    ite_false, ite_true, norm_mul, norm_star, FourierBridge.logPhase_norm, mul_one, mul_pow]

theorem firstCoreInputRow_integrated_le_corrected_source
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (T : Finset O) (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0)
    {k : ℝ → ℝ} (hk : Integrable k volume) (hk0 : ∀ t, 0 ≤ k t) :
    (∫ t : ℝ, k t * ∑ z ∈ T,
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) ≤
    (∫ t : ℝ, k t *
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)).re) -
      (‖H D‖ ^ 2 * ‖V (y D)‖ ^ 2) * ∫ t : ℝ, k t := by
  let mass := ‖H D‖ ^ 2 * ‖V (y D)‖ ^ 2
  let source := fun t : ℝ =>
    (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)).re
  have isource : Integrable (fun t : ℝ => k t * source t) volume :=
    firstCoreInputRow_majorant_integrable p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r Y hY hk
  have icorr : Integrable (fun t : ℝ => k t * (source t - mass)) volume := by
    simp only [mul_sub]
    exact isource.sub (hk.mul_const mass)
  have hpoint (t : ℝ) : k t * (∑ z ∈ T,
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) ≤
      k t * (source t - mass) := by
    have h := firstCoreInputRow_finite_le_corrected_source p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t T Y hY hT hT0
    rw [firstCoreTest_empty_mass] at h
    exact mul_le_mul_of_nonneg_left h (hk0 t)
  calc
    _ ≤ ∫ t : ℝ, k t * (source t - mass) := by
      apply integral_mono _ icorr hpoint
      simp only [Finset.mul_sum]
      exact integrable_finsetSum _ (fun z hz =>
        firstCoreInputRow_integrable p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r z hk)
    _ = _ := by
      simp only [mul_sub]
      rw [integral_sub isource (hk.mul_const mass), integral_mul_const]
      dsimp only [source, mass]
      ring

end

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct cubeRadical aLabel jLabel j2Label squarefreeLabel b0Label
  bit retained parity b0Exponent)

lemma span_dvd_of_element_dvd {a b : O} (h : a ∣ b) :
    (Ideal.span {a} : Ideal O) ∣ Ideal.span {b} := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨Ideal.span {c}, (Ideal.span_singleton_mul_span_singleton a c).symm⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma primeProduct_add (B : Finset ι) (u v : ι → ℕ) :
    primeProduct p B (fun i => u i + v i) = primeProduct p B u * primeProduct p B v := by
  simp only [primeProduct, pow_add, Finset.prod_mul_distrib]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma aLabel_dvd_primeProduct (B : Finset ι) (v : ι → ℕ) (ε : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) : aLabel p B ε ∣ primeProduct p B v := by
  unfold aLabel primeProduct
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  apply pow_dvd_pow
  cases h : ε i <;> simp only [bit, h, Bool.false_eq_true, ite_false, ite_true]
  · exact Nat.zero_le _
  · exact hv i hi

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeRadical_dvd_jLabel_b0 (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) : cubeRadical p B ∣ jLabel p B v ε₁ ε₂ * b0Label p B v ε₁ ε₂ := by
  have hle (i : ι) (hi : i ∈ B) :
      1 ≤ bit (retained (parity (v i)) (ε₁ i) (ε₂ i)) + b0Exponent (v i) (ε₁ i) (ε₂ i) := by
    cases h : retained (parity (v i)) (ε₁ i) (ε₂ i)
    · have hp := FirstPassCubeLabels.b0Exponent_pos_of_not_retained (v i) (ε₁ i) (ε₂ i) (hv i hi) h
      simp only [bit,  Bool.false_eq_true, ite_false, zero_add]
      omega
    · simp only [bit,  ite_true]
      omega
  have hd := Finset.prod_dvd_prod_of_dvd (s := B) (fun i => p i ^ 1)
    (fun i => p i ^ (bit (retained (parity (v i)) (ε₁ i) (ε₂ i)) + b0Exponent (v i) (ε₁ i) (ε₂ i)))
    (fun i hi => pow_dvd_pow (p i) (hle i hi))
  simpa only [cubeRadical, jLabel, b0Label, primeProduct, pow_one, pow_add,
    Finset.prod_mul_distrib] using hd

def actualSecondTuple (B C D E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (k : O) : SecondPassFiber.OldTuple where
  core := ![Ideal.span {jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂},
    ∏ i ∈ C, Ideal.span {p i}, ∏ i ∈ E, Ideal.span {p i},
    Ideal.span {squarefreeLabel p B (fun i => v₁ i + v₂ i)},
    Ideal.span {primeProduct p B v₁}, Ideal.span {aLabel p B ε₁},
    Ideal.span {aLabel p B ε₂}, ∏ i ∈ D, Ideal.span {p i}]
  v := ∏ i ∈ V, Ideal.span {p i}
  j2 := Ideal.span {j2Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂}
  b2 := Ideal.span {primeProduct p B v₂}
  row := k

def actualSecondLabel (B C E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Ideal O :=
  Ideal.span {jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂} *
    (∏ i ∈ C, Ideal.span {p i}) * (∏ i ∈ E, Ideal.span {p i}) * (∏ i ∈ V, Ideal.span {p i})

def actualSecondRow (D E : Finset ι) (k : O) : O :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) D *
    primeSubsetGenerator (fun i => Ideal.span {p i}) E * k

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem actualSecondTuple_valid
    (B C D E V : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C ∪ B)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i + v₂ i) (k : O) :
    SecondPassFiber.Valid (actualSecondTuple p B C D E V v₁ v₂ ε₁ ε₂ k)
      (actualSecondLabel p B C E V v₁ v₂ ε₁ ε₂)
      (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂})
      (actualSecondRow p D E k) := by
  have hJ := congrArg (fun a : O => (Ideal.span {a} : Ideal O))
    (FirstPassCubeLabels.jLabel_eq_squarefree_mul_j2 p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
  have hb := congrArg (fun a : O => (Ideal.span {a} : Ideal O))
    (FirstPassCubeLabels.cube_product_decomposition p B (fun i => v₁ i + v₂ i) ε₁ ε₂ hv)
  rw [primeProduct_add] at hb
  have hA₁ := span_dvd_of_element_dvd (aLabel_dvd_primeProduct p B (fun i => v₁ i + v₂ i) ε₁ hv)
  have hA₂ := span_dvd_of_element_dvd (aLabel_dvd_primeProduct p B (fun i => v₁ i + v₂ i) ε₂ hv)
  rw [primeProduct_add, ← Ideal.span_singleton_mul_span_singleton] at hA₁ hA₂
  have hrad := span_dvd_of_element_dvd (cubeRadical_dvd_jLabel_b0 p B (fun i => v₁ i + v₂ i) ε₁ ε₂ hv)
  rw [← Ideal.span_singleton_mul_span_singleton] at hrad
  have hD' : (∏ i ∈ D, Ideal.span {p i}) ∣
      (∏ i ∈ C, Ideal.span {p i}) * Ideal.span {cubeRadical p B} := by
    have hh := Finset.prod_dvd_prod_of_subset D (C ∪ B) (fun i => (Ideal.span {p i} : Ideal O)) hD
    rw [Finset.prod_union hCB] at hh
    simpa only [cubeRadical, FiniteGaussPhase.span_finset_prod] using hh
  have hD'' := hD'.trans (mul_dvd_mul_left (∏ i ∈ C, (Ideal.span {p i} : Ideal O)) hrad)
  constructor
  · rfl
  · change Ideal.span {squarefreeLabel p B (fun i => v₁ i + v₂ i)} *
        Ideal.span {j2Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂} =
          Ideal.span {jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂}
    simpa only [← Ideal.span_singleton_mul_span_singleton] using hJ.symm
  · change Ideal.span {primeProduct p B v₁} * Ideal.span {primeProduct p B v₂} =
        Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂} ^ 2 *
        Ideal.span {j2Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂} ^ 2 *
        Ideal.span {squarefreeLabel p B (fun i => v₁ i + v₂ i)}
    simpa only [pow_two, ← Ideal.span_singleton_mul_span_singleton] using hb
  · exact hA₁
  · exact hA₂
  · apply hD''.trans
    refine ⟨(∏ i ∈ E, Ideal.span {p i}) * (∏ i ∈ V, Ideal.span {p i}), ?_⟩
    simp only [actualSecondLabel]
    ring
  · rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem actualSecondTuple_newLabel
    (B C D E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (k : O) :
    SecondPassFiber.newLabel (actualSecondTuple p B C D E V v₁ v₂ ε₁ ε₂ k) =
      actualSecondLabel p B C E V v₁ v₂ ε₁ ε₂ := rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem actualSecondTuple_newRow
    (B C D E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (k : O) :
    SecondPassFiber.newRow (actualSecondTuple p B C D E V v₁ v₂ ε₁ ε₂ k) =
      actualSecondRow p D E k := rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem actualSecondLabel_span
    (B C E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) C *
      jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂ *
      primeSubsetGenerator (fun i => Ideal.span {p i}) E * (∏ i ∈ V, p i)} =
      actualSecondLabel p B C E V v₁ v₂ ε₁ ε₂ := by
  simp only [actualSecondLabel, ← Ideal.span_singleton_mul_span_singleton,
    primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator,
    FiniteGaussPhase.span_finset_prod]
  ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel b0Label primeProductNorm)

@[ext] structure SecondSupportData (ι : Type*) where
  common : Finset ι
  firstDivisor : Finset ι
  secondDivisor : Finset ι
  overlap : Finset ι
  frequency : O
  deriving DecidableEq

instance {ι : Type*} : Inhabited (SecondSupportData ι) := ⟨⟨∅, ∅, ∅, ∅, 0⟩⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondSupportTuple (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondSupportData ι) : SecondPassFiber.OldTuple :=
  actualSecondTuple p B x.common x.firstDivisor x.secondDivisor x.overlap v₁ v₂ ε₁ ε₂ x.frequency

def secondSupportLabel (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondSupportData ι) : O :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) x.common *
    jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂ *
    primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor * (∏ i ∈ x.overlap, p i)

def secondSupportNewLabel (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondSupportData ι) : Ideal O :=
  actualSecondLabel p B x.common x.secondDivisor x.overlap v₁ v₂ ε₁ ε₂

def secondSupportRow (x : SecondSupportData ι) : O :=
  actualSecondRow p x.firstDivisor x.secondDivisor x.frequency

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
@[simp] theorem secondSupportTuple_newLabel
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (x : SecondSupportData ι) :
    SecondPassFiber.newLabel (secondSupportTuple p B v₁ v₂ ε₁ ε₂ x) =
      secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ x := rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
@[simp] theorem secondSupportTuple_newRow
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (x : SecondSupportData ι) :
    SecondPassFiber.newRow (secondSupportTuple p B v₁ v₂ ε₁ ε₂ x) = secondSupportRow p x := rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondSupportLabel_span
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (x : SecondSupportData ι) :
    Ideal.span {secondSupportLabel p B v₁ v₂ ε₁ ε₂ x} = secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ x :=
  actualSecondLabel_span p B x.common x.secondDivisor x.overlap v₁ v₂ ε₁ ε₂

theorem secondSupportTuple_injective
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    Function.Injective (secondSupportTuple p B v₁ v₂ ε₁ ε₂) := by
  intro x y h
  have hC := congrArg (fun z : SecondPassFiber.OldTuple => z.core 1) h
  have hD := congrArg (fun z : SecondPassFiber.OldTuple => z.core 7) h
  have hE := congrArg (fun z : SecondPassFiber.OldTuple => z.core 2) h
  have hV := congrArg SecondPassFiber.OldTuple.v h
  have hk := congrArg SecondPassFiber.OldTuple.row h
  apply SecondSupportData.ext
  · exact FirstCauchyArithmetic.family_product_injective _ hinj hC
  · exact FirstCauchyArithmetic.family_product_injective _ hinj hD
  · exact FirstCauchyArithmetic.family_product_injective _ hinj hE
  · exact FirstCauchyArithmetic.family_product_injective _ hinj hV
  · exact hk

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondSupportTuple_valid
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i + v₂ i) (x : SecondSupportData ι)
    (hCB : Disjoint x.common B) (hD : x.firstDivisor ⊆ x.common ∪ B) :
    SecondPassFiber.Valid (secondSupportTuple p B v₁ v₂ ε₁ ε₂ x)
      (SecondPassFiber.newLabel (secondSupportTuple p B v₁ v₂ ε₁ ε₂ x))
      (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂})
      (SecondPassFiber.newRow (secondSupportTuple p B v₁ v₂ ε₁ ε₂ x)) :=
  actualSecondTuple_valid p B x.common x.firstDivisor x.secondDivisor x.overlap hCB hD
    v₁ v₂ ε₁ ε₂ hv x.frequency

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem sector_b0_ne_bot (hp : ∀ i, p i ≠ 0)
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂} : Ideal O) ≠ ⊥ := by
  apply Ideal.span_singleton_eq_bot.not.mpr
  exact Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (hp i))

def secondSectorZ (X X₀ : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (primeProductNorm p x.overlap * X₀ / X)

def secondSectorUd (D : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (‖ConcreteTraceCRT.eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)‖ ^ 2 / D)

def secondSectorUe (E : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (‖ConcreteTraceCRT.eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor)‖ ^ 2 / E)

def secondSectorUv (V₀ : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (primeProductNorm p x.overlap / V₀)

def secondSectorKap (K : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (‖ConcreteTraceCRT.eisEmbedding (secondSupportRow p x)‖ ^ 2 / K)

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open SecondPassIntegration (tupleSourceSum tupleSource_uniform_transfer childGeometricMean)
open JointLogSeparation
open FirstPassCubeLabels (b0Label)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def actualSecondSectorSource
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ)
    (D₀ E₀ V₀ X X₀ K Y : ℝ) : ℂ :=
  ∑ x ∈ s, w x * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m
    (secondSupportLabel p B v₁ v₂ ε₁ ε₂ x) (secondSupportRow p x) (-secondSupportRow p x)
    A₁ A₂ W windows (secondSectorZ p X X₀ x) (secondSectorUd p D₀ x)
    (secondSectorUe p E₀ x) (secondSectorUv p V₀ x) (secondSectorKap p K x)
    X₀ X₀ (Y*K/(D₀*E₀^2*V₀^2*X₀^2))

theorem actual_second_sector_uniform_transfer
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (ε : ℝ) (hε : 0 < ε) (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (windows : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hwindows : ∀ j x, windows j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∃ Cₛ : ℝ, 0 ≤ Cₛ ∧
      ∀ D₀ E₀ V₀ X X₀ K Y : ℝ,
      0 < D₀ → 0 < E₀ → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K → 0 < Y →
      ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ,
        (1 + Y*K/(D₀*E₀^2*V₀^2*X₀^2))^A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
          Cₛ * FirstPassCubeLabels.firstLogDensity J t₁ *
            FirstPassCubeLabels.firstLogDensity J t₂ * FirstPassCubeLabels.firstLogDensity J t₃) ∧
      ∀ (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (s : Finset (SecondSupportData ι)) (T : Finset (Ideal O × O))
        (w : SecondSupportData ι → ℂ) (Bnd lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) →
        (∀ x ∈ s, Disjoint x.common B) →
        (∀ x ∈ s, x.firstDivisor ⊆ x.common ∪ B) →
        0 ≤ Bnd → 0 ≤ lengthScale →
        (∀ x ∈ s, (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ x, secondSupportRow p x) ∈ T) →
        (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
        (∀ x ∈ s, ‖w x‖ * ‖outerWindow windows
          (secondSectorZ p X X₀ x) (secondSectorUd p D₀ x) (secondSectorUe p E₀ x)
          (secondSectorUv p V₀ x) (secondSectorKap p K x)‖ ≤ Bnd) →
        ‖actualSecondSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m
          A₁ A₂ W windows D₀ E₀ V₀ X X₀ K Y‖ ≤
        (Bnd * Cₐ * (lengthScale * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂}))^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖ *
            childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T (windows 5) (windows 6) X₀ X₀ (t₁,t₂,t₃)) := by
  obtain ⟨Cₐ, hCₐ, Cₛ, hCₛ, htrans⟩ :=
    tupleSource_uniform_transfer p hp hcop hg ε hε A₁ A₂ W windows M hM hwindows A J
  refine ⟨Cₐ, hCₐ, Cₛ, hCₛ, ?_⟩
  intro D₀ E₀ V₀ X X₀ K Y hD₀ hE₀ hV₀ hX hX₀ hK hY
  have hR : 0 < Y*K/(D₀*E₀^2*V₀^2*X₀^2) := by positivity
  obtain ⟨b, hb, hbound⟩ := htrans _ hR
  refine ⟨b, hb, ?_⟩
  intro B v₁ v₂ ε₁ ε₂ s T w Bnd lengthScale F Ψ₁ Ψ₂ m hv hCB hD hBnd hL hmap hT0 hnorm hw
  let encode := secondSupportTuple p B v₁ v₂ ε₁ ε₂
  have hi : Function.Injective encode := secondSupportTuple_injective p hinj B v₁ v₂ ε₁ ε₂
  let decode := Function.invFun encode
  have hdec (x : SecondSupportData ι) : decode (encode x) = x := Function.leftInverse_invFun hi x
  let s' := s.image encode
  let w' := fun x => w (decode x)
  let label' := fun x => secondSupportLabel p B v₁ v₂ ε₁ ε₂ (decode x)
  let z' := fun x => secondSectorZ p X X₀ (decode x)
  let ud' := fun x => secondSectorUd p D₀ (decode x)
  let ue' := fun x => secondSectorUe p E₀ (decode x)
  let uv' := fun x => secondSectorUv p V₀ (decode x)
  let kap' := fun x => secondSectorKap p K (decode x)
  have hsvalid : ∀ x ∈ s', SecondPassFiber.Valid x (SecondPassFiber.newLabel x)
      (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂}) (SecondPassFiber.newRow x) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact secondSupportTuple_valid p B v₁ v₂ ε₁ ε₂ hv a (hCB a ha) (hD a ha)
  have hsmap : ∀ x ∈ s', (SecondPassFiber.newLabel x, SecondPassFiber.newRow x) ∈ T := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact hmap a ha
  have hsw : ∀ x ∈ s', ‖w' x‖ * ‖outerWindow windows (z' x) (ud' x) (ue' x) (uv' x) (kap' x)‖ ≤ Bnd := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    dsimp only [w', z', ud', ue', uv', kap']
    rw [hdec]
    exact hw a ha
  have hslabel : ∀ x ∈ s', Ideal.span {label' x} = SecondPassFiber.newLabel x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    dsimp only [label']
    rw [hdec]
    exact secondSupportLabel_span p B v₁ v₂ ε₁ ε₂ a
  have hout := hbound s' T (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂})
    w' Bnd lengthScale label' F Ψ₁ Ψ₂ m z' ud' ue' uv' kap' X₀ X₀
    (sector_b0_ne_bot p hp B v₁ v₂ ε₁ ε₂) hBnd hL hsvalid hsmap hT0 hnorm hsw hslabel
  have hsource : tupleSourceSum p hp hcop hg s' w' label' F Ψ₁ Ψ₂ m
      A₁ A₂ W windows z' ud' ue' uv' kap' X₀ X₀ (Y*K/(D₀*E₀^2*V₀^2*X₀^2)) =
      actualSecondSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m
        A₁ A₂ W windows D₀ E₀ V₀ X X₀ K Y := by
    unfold tupleSourceSum actualSecondSectorSource
    rw [Finset.sum_image (fun a ha c hc h => hi h)]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp only [w', label', z', ud', ue', uv', kap']
    rw [hdec]
    rfl
  rw [hsource] at hout
  exact hout

end SecondPassArithmetic

end

end OAI

end


