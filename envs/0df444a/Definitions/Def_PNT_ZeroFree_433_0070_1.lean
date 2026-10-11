-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0070_1
-- name    : PNT_ZeroFree_433_0070_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T21:15:11.276981+00:00
-- url     : https://prove2.me/theorems/4dc49c07-30d5-4f0d-b9ca-f0a7c23ba2bd
-- title:
--   Zero-free region foundations: CubicSieve.FirstPassage [0070_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.FirstPassage
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/FirstPassage.lean#L182-L365

import Definitions.Def_PNT_ZeroFree_433_0070_1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/FirstPassage.lean
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

namespace FirstPassCubeLabels

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)


open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)
open ConcreteTraceCRT (eisEmbedding)


theorem first_passage_transfer {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (C₁ C₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale → ∀ c d : O, d ≠ 0 →
      ∀ (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) → (∀ x ∈ s, x.2 ≠ 0) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      ‖∑ x ∈ s, w x * actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (originalLabelColumn p hg B ε₁ ε₂ true C₁ c (ConcretePrimeRowBridge.idealGenerator x.1))
        (originalLabelColumn p hg B ε₁ ε₂ false C₂ c (ConcretePrimeRowBridge.idealGenerator x.1))
        W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt (firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ c d J T) *
        Real.sqrt (firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ c d J T) := by
  obtain ⟨H, hH, hsep⟩ := actual_first_kernel_uniform_energy_envelope p hp hinj hcop hg hc hpr F B hFB
    v ε₁ ε₂ W V₁ V₂ X₁ X₂ hX₁ hX₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ 0 J
  obtain ⟨K, hK, hpush⟩ := first_column_energy_integral deltaLoss hδ
  refine ⟨H * K, mul_nonneg hH hK.le, ?_⟩
  intro lengthScale hL c d hd s T w M Y hM hY hs hnonzero hmap hT hnorm hw
  let A₁ := fun x : Ideal O × O => originalLabelColumn p hg B ε₁ ε₂ true C₁ c (ConcretePrimeRowBridge.idealGenerator x.1)
  let A₂ := fun x : Ideal O × O => originalLabelColumn p hg B ε₁ ε₂ false C₂ c (ConcretePrimeRowBridge.idealGenerator x.1)
  let q := lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖
  have hq : 0 ≤ q := div_nonneg hL.le (norm_nonneg _)
  have hfam : ∀ x : Ideal O × O, ∃ b : 𝓢(ℝ, ℂ), x ∈ s →
      (∀ t : ℝ, ‖b t‖ ≤ H * firstLogDensity J t) ∧
      ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ (A₁ x) (A₂ x) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
        q * Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true (A₁ x) V₁ X₁ d x.2 b) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false (A₂ x) V₂ X₂ d x.2 b) := by
    intro x
    by_cases hx : x ∈ s
    · obtain ⟨b, hb, hk⟩ := hsep lengthScale hL d x.2 hd (hnonzero x hx)
      refine ⟨b, fun _ => ⟨?_, hk (A₁ x) (A₂ x)⟩⟩
      simpa only [pow_zero, one_mul] using hb
    · exact ⟨0, fun hx' => (hx hx').elim⟩
  choose b hb using hfam
  let E₁ := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true (A₁ x) V₁ X₁ d x.2 (b x)
  let E₂ := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false (A₂ x) V₂ X₂ d x.2 (b x)
  let O₁ := firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ c d J T
  let O₂ := firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ c d J T
  let P := M * H * K * Y ^ deltaLoss
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg (mul_nonneg hM hH) hK.le) (Real.rpow_nonneg hY deltaLoss)
  have hE₁ (x) : 0 ≤ E₁ x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ true _ _ _ _ _ _
  have hE₂ (x) : 0 ≤ E₂ x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ false _ _ _ _ _ _
  have hdom : ∀ x ∈ s, ∀ t : ℝ, ‖b x t‖ ≤ H * firstLogDensity J t := fun x hx => (hb x hx).1
  have hsum₁ : (∑ x ∈ s, ‖w x‖ * E₁ x) ≤ P * O₁ :=
    hpush p hp hinj hcop hg hc F B v ε₁ ε₂ hv true C₁ V₁ X₁ c d s T w b J M H Y
      hM hH hY hs hmap hT hnorm hw hdom
  have hsum₂ : (∑ x ∈ s, ‖w x‖ * E₂ x) ≤ P * O₂ :=
    hpush p hp hinj hcop hg hc F B v ε₁ ε₂ hv false C₂ V₂ X₂ c d s T w b J M H Y
      hM hH hY hs hmap hT hnorm hw hdom
  have hterm (x) : ‖w x‖ * (Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) =
      Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x) := by
    rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_mul (norm_nonneg _)]
    calc
      _ = (Real.sqrt ‖w x‖) ^ 2 * (Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) := by
        rw [Real.sq_sqrt (norm_nonneg _)]
      _ = _ := by ring
  calc
    _ ≤ ∑ x ∈ s, ‖w x * actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (A₁ x) (A₂ x) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ s, q * (Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x)) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul, ← hterm]
      calc
        _ ≤ ‖w x‖ * (q * Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) :=
          mul_le_mul_of_nonneg_left (hb x hx).2 (norm_nonneg _)
        _ = _ := by ring
    _ = q * (∑ x ∈ s, Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ q * (Real.sqrt (∑ x ∈ s, ‖w x‖ * E₁ x) * Real.sqrt (∑ x ∈ s, ‖w x‖ * E₂ x)) :=
      mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le s
        (fun x => mul_nonneg (norm_nonneg _) (hE₁ x))
        (fun x => mul_nonneg (norm_nonneg _) (hE₂ x))) hq
    _ ≤ q * (Real.sqrt (P * O₁) * Real.sqrt (P * O₂)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.sqrt_le_sqrt hsum₁) (Real.sqrt_le_sqrt hsum₂)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hq
    _ = _ := by
      rw [Real.sqrt_mul hP, Real.sqrt_mul hP]
      calc
        _ = q * (Real.sqrt P)^2 * Real.sqrt O₁ * Real.sqrt O₂ := by ring
        _ = _ := by rw [Real.sq_sqrt hP]; dsimp only [P]; ring

end

open ActualEisensteinCubic
open ConcretePrimeRowBridge (conjugateIdealRowSum mobiusIdealColumn idealPairPoissonKernel
  primePool mem_primePool_iff conjugateIdealRowSum_smoothed_summable
  conjugateIdealRowSum_smoothed_poisson)
open FirstCauchyArithmetic (supportIdealFamily supportIdealFamily_pos supportIdealFamily_good
  recoveredSupport supportRay)
open RayFourExpansion (RayCharacter)
open ConcreteTraceCRT (eisEmbedding)

def dilatedIdealCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool) (χ : RayCharacter)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ) (I : Ideal O) : ℂ :=
  let U := recoveredSupport (fun i => Ideal.span {p i}) (F \ D) I
  (if negative then star (supportRay p χ U) else supportRay p χ U) *
    cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t (D ∪ U) *
    afterDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ c d U

theorem dilatedCoreRow_eq_ideal {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool) (χ : RayCharacter)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ) (z : O) :
    dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t z =
    conjugateIdealRowSum (supportIdealFamily (fun i => Ideal.span {p i}) (F \ D))
      (supportIdealFamily_pos (fun i => Ideal.span {p i}) (F \ D))
      (supportIdealFamily_good (fun i => Ideal.span {p i}) hg (F \ D))
      (dilatedIdealCoefficient p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t) z :=
  FirstCauchyArithmetic.supportConjugateSum_eq_conjugateIdealRowSum
    (fun i => Ideal.span {p i}) hinj hg (F \ D) _ z

theorem supportFamily_primePool_char {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S : Finset ι) :
    ∀ Q : primePool (supportIdealFamily (fun i => Ideal.span {p i}) S),
      ringChar (O ⧸ Q.val) ≠ 2 := by
  intro Q
  obtain ⟨I, hI, hQ⟩ := mem_primePool_iff.mp Q.property
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hI
  have hp' (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hU0 : (∏ i ∈ U, Ideal.span {p i}) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => (hp' i).ne_zero)
  obtain ⟨hprime, hdiv⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hU0).mp hQ
  obtain ⟨i, hi, hdi⟩ := (hprime.dvd_finsetProd_iff (fun i => Ideal.span {p i})).mp hdiv
  have he : Q.val = Ideal.span {p i} := associated_iff_eq.mp (hprime.associated_of_dvd (hp' i) hdi)
  change ringChar (O ⧸ Q.val) ≠ 2
  rw [he]
  exact hc i

theorem dilatedCoreRow_smoothed_summable {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool) (χ : RayCharacter)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ)
    (W : 𝓢(ℝ, ℂ)) (lengthScale : ℝ) (hL : 0 < lengthScale) :
    Summable (fun z : O => W (‖eisEmbedding z‖ ^ 2 / lengthScale) *
      (↑(‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t z‖ ^ 2) : ℂ)) := by
  simp_rw [dilatedCoreRow_eq_ideal p hp hinj hcop hg F D B v ε₁ ε₂ negative χ C V y c d t]
  exact conjugateIdealRowSum_smoothed_summable _ _ _ _ W lengthScale hL

theorem dilatedCoreRow_second_poisson {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool) (χ : RayCharacter)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ)
    (W : 𝓢(ℝ, ℂ)) (lengthScale : ℝ) (hL : 0 < lengthScale) :
    let H := supportIdealFamily (fun i => Ideal.span {p i}) (F \ D)
    let A := dilatedIdealCoefficient p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / lengthScale) *
      (↑(‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t z‖ ^ 2) : ℂ)) =
    ∑ I ∈ H, ∑ J ∈ H, (star (mobiusIdealColumn A I) * mobiusIdealColumn A J) *
      idealPairPoissonKernel H (supportIdealFamily_pos (fun i => Ideal.span {p i}) (F \ D))
        (supportIdealFamily_good (fun i => Ideal.span {p i}) hg (F \ D)) J I W lengthScale := by
  dsimp only
  simp_rw [dilatedCoreRow_eq_ideal p hp hinj hcop hg F D B v ε₁ ε₂ negative χ C V y c d t]
  exact conjugateIdealRowSum_smoothed_poisson _ _ _ (supportFamily_primePool_char p hc (F \ D)) _ W lengthScale hL

end FirstPassCubeLabels


end

end OAI

end


