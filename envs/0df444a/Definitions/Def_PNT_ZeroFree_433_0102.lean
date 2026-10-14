-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0102
-- name    : PNT_ZeroFree_433_0102
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:46:38.852893+00:00
-- url     : https://prove2.me/theorems/84780e59-deb7-4b6d-bf70-1bd5861f736a
-- title:
--   Zero-free region foundations: QuadraticSieve.PrincipalDifference [0102]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalDifference
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PrincipalDifference.lean#L81-L666

import Definitions.Def_PNT_ZeroFree_433_0100
import Definitions.Def_PNT_ZeroFree_433_0101

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PrincipalDifference.lean#L81-L666
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalDifference
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
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open IdealMobiusDivisorSum QuadraticMainBoundary QuadraticMainOperatorBound IdealCoprimeSieveOperator

theorem normalizedPair_boundary_term
    (I J H D E : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (hH : Supported H) (K : ℝ) (a b : ℂ) :
    (star a * b) * ((UniqueFactorizationMonoid.moebius E : ℂ) *
      normalizedIdealPair I J (H * D * E) * (cutoffDifference K H D : ℂ)) =
    (UniqueFactorizationMonoid.moebius E : ℂ) * mainWeight K H D E *
      (star (quadraticRow I (primaryGenerator H) *
        (a * quadraticRow I (idealGenerator D * idealGenerator E))) *
       (quadraticRow J (primaryGenerator H) *
        (b * quadraticRow J (idealGenerator D * idealGenerator E)))) := by
  have hspan : Ideal.span {idealGenerator D * idealGenerator E} = D * E := by
    rw [← Ideal.span_singleton_mul_span_singleton, span_idealGenerator, span_idealGenerator]
  have hde := unrestrictedPairCharacter_span I J hI hJ hray (idealGenerator D * idealGenerator E)
  rw [hspan] at hde
  have hp : unrestrictedPairCharacter I J (H * D * E) =
      (quadraticRow I (primaryGenerator H) * quadraticRow J (primaryGenerator H)) *
      (quadraticRow I (idealGenerator D * idealGenerator E) *
        quadraticRow J (idealGenerator D * idealGenerator E)) := by
    rw [mul_assoc, unrestrictedPairCharacter_mul I J hI hJ hray,
      unrestrictedPairCharacter_eq_primary I J hI hJ hray H hH, hde]
  rw [normalizedIdealPair, hp]
  simp only [mainWeight, div_eq_mul_inv, star_mul,
    canonical_quadraticRow_star I hI]
  ring

def actualPrincipalDifference {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (G : Ideal O) (K : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j) * a k *
      (normalizedPairPartial (cols j) (cols k) K * normalizedPairDivisors (cols j) (cols k) G -
       normalizedPairCoprimePartial (cols j) (cols k) G K * normalizedPairDensity (cols j) (cols k) G)
    else 0

theorem actualPrincipalDifference_bound
    {n : Type*} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (N : ℝ) (hN : 0 ≤ N) (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (hray : ∀ j k, columnRay (cols j) = columnRay (cols k)) (a : n → ℂ)
    (G : Ideal O) (hG : Squarefree G) (hbad : ∀ P ∈ fixedBadPrimes, P ∣ G)
    (K : ℝ) (hK : 0 < K) (ε : ℝ) (hε : 0 < ε) :
    ‖actualPrincipalDifference cols a G K‖ ≤
      ((idealDivisors G).card : ℝ) ^ 2 *
        ((1 / Real.sqrt K) * sieveNorm K N * (supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) := by
  let S := coprimeSquarefreeRange G K
  have hS : S ⊆ idealRange K := coprimeSquarefreeRange_subset_idealRange G hbad K
  let A : Matrix S n ℂ := fun H j => quadraticRow (cols j) (primaryGenerator H.val)
  let r : Ideal O → Ideal O → n → ℂ := fun D E j =>
    quadraticRow (cols j) (idealGenerator D * idealGenerator E)
  have hpoint (j k : n) :
      (if IsCoprime (cols j) (cols k) then star (a j) * a k *
        (normalizedPairPartial (cols j) (cols k) K * normalizedPairDivisors (cols j) (cols k) G -
         normalizedPairCoprimePartial (cols j) (cols k) G K * normalizedPairDensity (cols j) (cols k) G) else 0) =
      ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G, ∑ H : S,
        (UniqueFactorizationMonoid.moebius E : ℂ) * mainWeight K H.val D E *
          (if IsCoprime (cols j) (cols k) then
            star (A H j * (a j * r D E j)) * (A H k * (a k * r D E k)) else 0) := by
    dsimp only [A, r]
    by_cases hc : IsCoprime (cols j) (cols k)
    · rw [if_pos hc, normalizedPair_main_difference (cols j) (cols k) (hcols j).1 (hcols k).1 (hray j k) G hG K]
      simp only [Finset.mul_sum]
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (coprimeSquarefreeRange G K))) (t := idealDivisors G)]
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro E hE
      apply Finset.sum_congr rfl
      intro H _
      rw [if_pos hc]
      exact normalizedPair_boundary_term (cols j) (cols k) H.val D E (hcols j).1 (hcols k).1
        (hray j k) (admissible_supported (mem_idealRange.mp (hS H.property)).1) K (a j) (a k)
    · simp only [hc, ite_false, mul_zero, Finset.sum_const_zero]
  have heq : actualPrincipalDifference cols a G K =
      ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          (∑ H : S, mainWeight K H.val D E *
            (∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
              star (A H j * (a j * r D E j)) * (A H k * (a k * r D E k)) else 0)) := by
    dsimp only [A, r]
    unfold actualPrincipalDifference
    simp_rw [hpoint]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset n)) (t := idealDivisors G),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset S))]
    simp only [Finset.mul_sum, mul_assoc, A, r]
  rw [heq]
  have hb := main_difference_operator_bound ε hε K hK G hG.ne_zero (fun H : S => H.val)
    cols (fun j => (hcols j).1.1) N hN (fun j => (hcols j).2) A a r
    (fun D E j => quadraticRow_norm_le_one (cols j) _)
  have hA : ‖FiniteSieveOperator.operator A‖ ^ 2 ≤ sieveNorm K N :=
    family_squared_norm_le (fun H : S => H.val) cols Subtype.val_injective hinj K N
      (fun H => mem_idealRange.mp (hS H.property)) hcols
  apply hb.trans
  have hs : 0 ≤ supportConstant ε hε := (supportConstant_pos ε hε).le
  gcongr

end

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def middleRatio (B b D₁ d D₂ e : ℝ) : ℝ := Real.sqrt (B / b) * (D₁ / d) * (D₂ / e)

theorem middleRatio_bounds (B b D₁ d D₂ e : ℝ)
    (hB : 0 < B) (hb : B / 2 ≤ b ∧ b ≤ B)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d ∧ d ≤ 2 * D₁)
    (hD₂ : 0 < D₂) (he : D₂ ≤ e ∧ e ≤ 2 * D₂) :
    1 / 4 ≤ middleRatio B b D₁ d D₂ e ∧ middleRatio B b D₁ d D₂ e ≤ 2 := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd.1
  have he0 : 0 < e := hD₂.trans_le he.1
  have hu1 : 1 ≤ Real.sqrt (B / b) := by
    have hq : 1 ≤ B / b := (le_div_iff₀ hb0).mpr (by simpa using hb.2)
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hq
  have hu2 : Real.sqrt (B / b) ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ hb0).mpr
    nlinarith
  have hv : (1 / 2 : ℝ) ≤ D₁ / d ∧ D₁ / d ≤ 1 :=
    ⟨(le_div_iff₀ hd0).mpr (by linarith), (div_le_one hd0).mpr hd.1⟩
  have hw : (1 / 2 : ℝ) ≤ D₂ / e ∧ D₂ / e ≤ 1 :=
    ⟨(le_div_iff₀ he0).mpr (by linarith), (div_le_one he0).mpr he.1⟩
  have hv0 : 0 ≤ D₁ / d := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hv.1
  have hw0 : 0 ≤ D₂ / e := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hw.1
  have hvw1 : (1 / 4 : ℝ) ≤ (D₁ / d) * (D₂ / e) := by
    nlinarith [mul_le_mul hv.1 hw.1 (by norm_num : (0 : ℝ) ≤ 1 / 2) hv0]
  have hvw2 : (D₁ / d) * (D₂ / e) ≤ 1 := by
    nlinarith [mul_le_mul hv.2 hw.2 hw0 (by norm_num : (0 : ℝ) ≤ 1)]
  unfold middleRatio
  constructor
  · nlinarith [mul_le_mul hu1 hvw1 (by norm_num : (0 : ℝ) ≤ 1 / 4) (Real.sqrt_nonneg (B / b))]
  · nlinarith [mul_le_mul hu2 hvw2 (mul_nonneg hv0 hw0) (by norm_num : (0 : ℝ) ≤ 2)]

theorem middleRatio_log_bound (r : ℝ) (hr : (1 / 4 : ℝ) ≤ r ∧ r ≤ 2) : |Real.log r| ≤ 4 := by
  have hr0 : 0 < r := by linarith
  have hi : r⁻¹ ≤ 4 := by
    have h : (1 : ℝ) / r ≤ 4 := (div_le_iff₀ hr0).mpr (by linarith)
    simpa only [one_div] using h
  have h₁ := Real.log_le_sub_one_of_pos hr0
  have h₂ := Real.log_le_sub_one_of_pos (inv_pos.mpr hr0)
  rw [Real.log_inv] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem middleRatio_argument (M B b D₁ d D₂ e q : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b ∧ b ≤ B)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d ∧ d ≤ 2 * D₁)
    (hD₂ : 0 < D₂) (he : D₂ ≤ e ∧ e ≤ 2 * D₂) :
    (Real.sqrt (M / B) * q / (D₁ * D₂)) * Real.exp (Real.log (middleRatio B b D₁ d D₂ e)) =
      Real.sqrt (M / b) * q / (d * e) := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd.1
  have he0 : 0 < e := hD₂.trans_le he.1
  have hr : 0 < middleRatio B b D₁ d D₂ e := by
    have hh := middleRatio_bounds B b D₁ d D₂ e hB hb hD₁ hd hD₂ he
    linarith
  rw [Real.exp_log hr]
  have hs : Real.sqrt (M / B) * Real.sqrt (B / b) = Real.sqrt (M / b) := by
    rw [← Real.sqrt_mul (div_nonneg hM.le hB.le)]
    congr 1
    field_simp
  unfold middleRatio
  calc
    _ = (Real.sqrt (M / B) * Real.sqrt (B / b)) * q / (d * e) := by
      field_simp

    _ = _ := by rw [hs]

theorem actual_middle_radial_block_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
        [DecidableEq m] [DecidableEq n] [DecidableEq p]
        (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
        (D₁ D₂ B N M : ℝ) (_hD₁ : 1 ≤ D₁) (_hD₂ : 1 ≤ D₂) (_hB : 1 ≤ B) (_hN : 1 ≤ N) (_hM : 0 < M)
        (_hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
        (_hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
        (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
        (_hr : Function.Injective rows) (_hl : Function.Injective left) (_hri : Function.Injective right)
        (_hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
        (_hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
        (_hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
        (a : n → ℂ) (b : p → ℂ) (h : O), h ≠ 0 →
        (1 + Real.sqrt (M / B) * ‖eisEmbedding h‖ ^ 2 / (D₁ * D₂)) ^ A *
          (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k,
            originalTerm rows left right a b D.val E.val i j k *
              paperRadialFourier W
                (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
                  ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖) ≤
          C * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  obtain ⟨C, hC, hb⟩ := canonical_original_radial_divisor_block_bound W 4 0 0 (by norm_num) (by norm_num) (by norm_num) A
  refine ⟨C, hC, ?_⟩
  intro m n p _ _ _ _ _ _ ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT rows left right hr hl hri hrows hleft hright a b h hh
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hB0 : 0 < B := by linarith
  let R := Real.sqrt (M / B) * ‖eisEmbedding h‖ ^ 2 / (D₁ * D₂)
  have hR : 0 < R := div_pos (mul_pos (Real.sqrt_pos.mpr (div_pos hM hB0))
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)))) (mul_pos hD₁0 hD₂0)
  let x : S → T → m → ℝ := fun D E i => Real.log
    (middleRatio B (Ideal.absNorm (rows i)) D₁ (Ideal.absNorm D.val) D₂ (Ideal.absNorm E.val))
  have hx (D : S) (E : T) (i : m) : |x D E i| ≤ 4 :=
    middleRatio_log_bound _ (middleRatio_bounds _ _ _ _ _ _ hB0 (hrows i).2 hD₁0
      (hS D.val D.property) hD₂0 (hT E.val E.property))
  have he := hb R hR ε hε S T D₁ D₂ B N hD₁ hD₂ hN hS hT rows left right hr hl hri
    (fun i => ⟨(hrows i).1, (hrows i).2.2⟩) hleft hright a b x (fun _ => 0) (fun _ => 0) hx
    (fun _ => by simp) (fun _ => by simp)
  have harg (D : S) (E : T) (i : m) : R * Real.exp (x D E i + (0 + 0)) =
      Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)) := by
    simp only [add_zero]
    exact middleRatio_argument _ _ _ _ _ _ _ _ hM hB0 (hrows i).2 hD₁0
      (hS D.val D.property) hD₂0 (hT E.val E.property)
  simpa only [harg, R] using he

end CanonicalQuadraticSieve

namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hp

theorem firstCoreInputRow_smoothed_mode
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (g V W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (Y : ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
        (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t z‖ ^ 2 : ℝ)) =
      ((primeProductNorm p D)⁻¹ : ℝ) *
      ∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
        (‖inputConjugateRow p hg (F\D) (firstCoreTwist negative χ Ψ r)
          (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
          (normalizedColumn p (fun A => firstCoreModeProfile g V negative t
            (columnLog p (X / primeProductNorm p D) A))) z‖ ^ 2 : ℝ) := by
  let P := inputConjugateRow p hg (F\D) (firstCoreTwist negative χ Ψ r)
    (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
    (normalizedColumn p (fun A => firstCoreModeProfile g V negative t
      (columnLog p (X / primeProductNorm p D) A)))
  have he (z : O) : W (‖eisEmbedding z‖ ^ 2 / Y) *
      (‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
        (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t z‖ ^ 2 : ℝ) =
      (((primeProductNorm p D)⁻¹ : ℝ) : ℂ) *
        (W (‖eisEmbedding z‖ ^ 2 / Y) * (‖P (if negative then -z else z)‖ ^ 2 : ℝ)) := by
    rw [firstCoreInputRow_mode_norm_sq p hp hg F D B v ε₁ ε₂ negative χ Ψ m g V X hX c d r t z]
    push_cast
    ring
  simp_rw [he]
  rw [tsum_mul_left]
  have hsign : (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (‖P (if negative then -z else z)‖ ^ 2 : ℝ)) =
      ∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) * (‖P z‖ ^ 2 : ℝ) := by
    cases negative
    · rfl
    · simpa only [Bool.true_eq, ite_true, Equiv.neg_apply, map_neg, norm_neg] using
        (Equiv.neg O).tsum_eq (fun z : O => W (‖eisEmbedding z‖ ^ 2 / Y) * (‖P z‖ ^ 2 : ℝ))
  rw [hsign]

theorem firstCoreInputRow_smoothed_truncated
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (g V W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (Y : ℝ) (hY : 0 < Y) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (K : Finset ι → Finset ι → Finset O) :
    let Hmode := normalizedColumn p (fun A => firstCoreModeProfile g V negative t
      (columnLog p (X / primeProductNorm p D) A))
    let Ψmode := firstCoreTwist negative χ Ψ r
    let m' := m * b0Label p B v ε₁ ε₂
    let c' := c * jLabel p B v ε₁ ε₂
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
        (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t z‖ ^ 2 : ℝ)) =
      ((primeProductNorm p D)⁻¹ : ℝ) *
        (truncatedSecondSource p hp hg hinj (F\D) Ψmode m' c' d Hmode W Y K +
          secondSourceTail p hp hg hinj (F\D) Ψmode m' c' d Hmode W Y K) := by
  dsimp only
  rw [firstCoreInputRow_smoothed_mode p hp hg F D B v ε₁ ε₂ negative χ Ψ m g V W X hX Y c d r t,
    inputConjugateRow_eq_truncated_add_tail p hp hg hinj hc]
  exact hY

theorem firstCoreInputRow_finite_le_truncated_tail
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (Y : ℝ) (hY : 0 < Y) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (T : Finset O)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0) (K : Finset ι → Finset ι → Finset O) :
    let Hmode := normalizedColumn p (fun A => firstCoreModeProfile g V negative t
      (columnLog p (X / primeProductNorm p D) A))
    let Ψmode := firstCoreTwist negative χ Ψ r
    let m' := m * b0Label p B v ε₁ ε₂
    let c' := c * jLabel p B v ε₁ ε₂
    (∑ z ∈ T, ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
      (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t z‖ ^ 2) +
      ‖firstCoreTest (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X)
        negative t D ∅‖ ^ 2 ≤
      (primeProductNorm p D)⁻¹ *
        (‖truncatedSecondSource p hp hg hinj (F\D) Ψmode m' c' d Hmode rowMajorant Y K‖ +
          ‖secondSourceTail p hp hg hinj (F\D) Ψmode m' c' d Hmode rowMajorant Y K‖) := by
  dsimp only
  have h := firstCoreInputRow_finite_le_corrected_source p hg F D B v ε₁ ε₂ negative χ Ψ m
    (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t T Y hY hT hT0
  have he := firstCoreInputRow_smoothed_truncated p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m
    g V rowMajorant X hX Y hY c d r t K
  rw [he] at h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.add_re] at h
  apply (le_sub_iff_add_le.mp h).trans
  apply mul_le_mul_of_nonneg_left
  · exact add_le_add (Complex.re_le_norm _) (Complex.re_le_norm _)
  · exact inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp D).le

end SecondPassArithmetic

namespace SecondPassIntegration

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

lemma childEnergy_eq_difference (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V : ℝ → ℂ) (X a b : ℝ)
    (testNegative rowNegative : Bool) :
    childEnergy p hp hcop hg F Ψ m T V X testNegative rowNegative a b =
      childEnergy p hp hcop hg F Ψ m T V X testNegative rowNegative (a-b) 0 := by
  have he : fixedSecondTest p V X a b testNegative =
      fixedSecondTest p V X (a-b) 0 testNegative := by
    funext N
    simp only [fixedSecondTest, sub_zero]
  simp only [childEnergy, he]

theorem densityChildEnergy_polynomial_bound (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (J : ℕ) (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (h₁ : ∀ a : ℝ, childEnergy p hp hcop hg F Ψ₁ m T V₁ X₁ true false a 0 ≤
      B₁ * (1+‖a‖)^(2*J))
    (h₂ : ∀ a : ℝ, childEnergy p hp hcop hg F Ψ₂ m T V₂ X₂ false true a 0 ≤
      B₂ * (1+‖a‖)^(2*J)) :
    densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (2*J) ≤
      (Real.sqrt B₁ * Real.sqrt B₂) *
        (∫ t : ℝ, FirstPassCubeLabels.firstLogDensity 0 t)^3 := by
  let G := childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂
  have hc₁ := childEnergy_continuous p hp hcop hg F Ψ₁ m T V₁ X₁ true false
    (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
  have hc₂ := childEnergy_continuous p hp hcop hg F Ψ₂ m T V₂ X₂ false true
    (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
  have hG : Continuous G := (Real.continuous_sqrt.comp hc₁).mul (Real.continuous_sqrt.comp hc₂)
  have hG0 : ∀ q, 0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let M := Real.sqrt (energyMagnitude p hp hcop hg F Ψ₁ m T V₁ X₁ true false) *
    Real.sqrt (energyMagnitude p hp hcop hg F Ψ₂ m T V₂ X₂ false true)
  have hM : ∀ q, G q ≤ M := by
    intro q
    dsimp [G, childGeometricMean, M]
    gcongr
    · exact childEnergy_le p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2
    · exact childEnergy_le p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2
  have hsqrt (B a e : ℝ) (hB : 0 ≤ B) (he : e ≤ B*(1+‖a‖)^(2*J)) :
      Real.sqrt e ≤ Real.sqrt B * (1+‖a‖)^J := by
    calc
      _ ≤ Real.sqrt (B*(1+‖a‖)^(2*J)) := Real.sqrt_le_sqrt he
      _ = _ := by
        rw [Real.sqrt_mul hB, mul_comm 2 J, pow_mul, Real.sqrt_sq (by positivity)]
  have hbound (q : Frequency) : G q ≤
      (Real.sqrt B₁ * Real.sqrt B₂) *
        (1+‖q.1‖)^(2*J)*(1+‖q.2.1‖)^(2*J)*(1+‖q.2.2‖)^(2*J) := by
    have hleft := h₁ (q.1-q.2.2)
    have hright := h₂ (q.2.1-q.2.2)
    rw [← childEnergy_eq_difference p hp hcop hg F Ψ₁ m T V₁ X₁ q.1 q.2.2 true false] at hleft
    rw [← childEnergy_eq_difference p hp hcop hg F Ψ₂ m T V₂ X₂ q.2.1 q.2.2 false true] at hright
    calc
      _ ≤ (Real.sqrt B₁ * (1+‖q.1-q.2.2‖)^J) *
          (Real.sqrt B₂ * (1+‖q.2.1-q.2.2‖)^J) :=
        mul_le_mul (hsqrt B₁ _ _ hB₁ hleft) (hsqrt B₂ _ _ hB₂ hright)
          (Real.sqrt_nonneg _) (by positivity)
      _ = (Real.sqrt B₁ * Real.sqrt B₂) *
          ((1+‖q.1-q.2.2‖)^J * (1+‖q.2.1-q.2.2‖)^J) := by ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (difference_height_weight_le q.1 q.2.1 q.2.2 J)
          (mul_nonneg (Real.sqrt_nonneg B₁) (Real.sqrt_nonneg B₂))
        simpa only [mul_assoc] using hh
  exact triple_density_polynomial_bound G hG hG0 M hM (2*J)
    (Real.sqrt B₁ * Real.sqrt B₂) hbound

end SecondPassIntegration

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def residualPairWeight (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (S T : Finset ι) : ℂ :=
  star (supportMobius (fun i => Ideal.span {p i}) S * secondInputCoefficient p hg Ψ₁ m c d H₁ S) *
    (supportMobius (fun i => Ideal.span {p i}) T * secondInputCoefficient p hg Ψ₂ m c d H₂ T)

theorem residualSecondMode_tail_eq (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m c d : O) (H₁ H₂ : Finset ι → ℂ) (e : O) (he : e ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) (K : Finset O) :
    (∑' k : {k : O // k ∉ K}, residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e k.val W Y) =
    ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset, if Disjoint S T then
      residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T *
        ∑' k : {k : O // k ∉ K}, secondPairRadialMode p hp hg hinj S T e k.val W Y else 0 := by
  have hs (S T : Finset ι) : Summable (fun k : {k : O // k ∉ K} =>
      if Disjoint S T then residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T *
        secondPairRadialMode p hp hg hinj S T e k.val W Y else 0) := by
    by_cases hd : Disjoint S T
    · simp only [if_pos hd]
      exact ((secondPairRadialMode_summable p hp hg hinj S T e he W Y hY).subtype _).mul_left _
    · simp only [if_neg hd]
      exact summable_zero
  change (∑' k : {k : O // k ∉ K}, ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset,
    if Disjoint S T then residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T *
      secondPairRadialMode p hp hg hinj S T e k.val W Y else 0) = _
  rw [Summable.tsum_finsetSum (fun S _ => summable_sum (fun T _ => hs S T))]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Summable.tsum_finsetSum (fun T _ => hs S T)]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [if_pos hd, tsum_mul_left]
  · simp [hd]

def residualTailCost (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m c d : O) (H₁ H₂ : Finset ι → ℂ) (e : O) (Y H : ℝ) (A : ℕ) (P : ℝ) : ℝ :=
  ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset, if Disjoint S T then
    let n := ∏ i : activeSupport T S, p i.val
    let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
    ‖residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T‖ *
      ((Y/‖eisEmbedding n‖) * (P / ((min 1 scale)^2 * (1+H)^A)))
    else 0

theorem residualSecondMode_tail_bound
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O) (H₁ H₂ : Finset ι → ℂ)
      (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ), 0 < Y → 0 ≤ H → ∀ K : Finset O,
      (∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T ≠ 0 →
        ∀ k : O, k ∉ K →
          H ≤ (Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) *
            ‖eisEmbedding k‖^2) →
      ‖∑' k : {k : O // k ∉ K}, residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e k.val W Y‖ ≤
      residualTailCost p hg F G Ψ₁ Ψ₂ m c d H₁ H₂ e Y H A (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s,C,hC,hb⟩ := secondPairRadialMode_remainder p hp hg hinj hc A
  refine ⟨s,C,hC,?_⟩
  intro F G Ψ₁ Ψ₂ m c d H₁ H₂ e he W Y H hY hH K hK
  rw [residualSecondMode_tail_eq p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e he W Y hY K]
  unfold residualTailCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro S hS
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [if_pos hd, norm_mul]
    by_cases hw : residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T = 0
    · simp only [hw, norm_zero, zero_mul, le_refl]
    · exact mul_le_mul_of_nonneg_left (hb S T e he W Y H hY hH K (hK S hS T hT hd hw)) (norm_nonneg _)
  · simp [hd]

theorem secondSourceTail_bound
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (Hcol : Finset ι → ℂ)
      (W : 𝓢(ℝ, ℂ)) (Y H : ℝ), 0 < Y → 0 ≤ H →
      ∀ K : Finset ι → Finset ι → Finset O,
      (∀ G ∈ F.powerset, ∀ E : G.powerset,
        ∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U)) S T ≠ 0 →
        ∀ k : O, k ∉ K G E.val →
          H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖^2 *
            ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
      ∑ G ∈ F.powerset, ∑ E : G.powerset, ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
        residualTailCost p hg F G Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s,C,hC,hb⟩ := residualSecondMode_tail_bound p hp hg hinj hc A
  refine ⟨s,C,hC,?_⟩
  intro F Ψ m c d Hcol W Y H hY hH K hK
  unfold secondSourceTail
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro G hG
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro E hE
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simp_rw [← residualSecondMode_eq_frequencyKernel p hp hg hinj F G E.val
    (Finset.mem_powerset.mp E.property) Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))]
  exact hb F G Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))
    (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) (primeSubsetGenerator_ne_zero _ _)
    W Y H hY hH (K G E.val) (hK G hG E)

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_eq_ideal_norm (S : Finset ι) :
    primeProductNorm p S = (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) := by
  rw [primeProductNorm, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    FiniteGaussPhase.span_finset_prod]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_ge_one (S : Finset ι) : 1 ≤ primeProductNorm p S :=
  by
    rw [primeProductNorm, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {∏ i ∈ S, p i}) ≠ 0 by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_mono {S T : Finset ι} (hST : S ⊆ T) :
    primeProductNorm p S ≤ primeProductNorm p T := by
  have hd : Disjoint S (T\S) := Finset.disjoint_sdiff
  have hu : S ∪ (T\S) = T := Finset.union_sdiff_of_subset hST
  rw [← hu, FirstPassCubeLabels.primeProductNorm_union p S (T\S) hd]
  exact le_mul_of_one_le_right (FirstPassCubeLabels.primeProductNorm_pos p hp S).le
    (primeProductNorm_ge_one p hp _)

def boundedPrimeSupports (F : Finset ι) (X : ℝ) : Finset (Finset ι) :=
  F.powerset.filter (fun S => primeProductNorm p S ≤ X)

include hinj in
theorem boundedPrimeSupports_card (F : Finset ι) (X : ℝ) (hX : 1 ≤ X) :
    ((boundedPrimeSupports p F X).card : ℝ) ≤ 128*X := by
  let q : Finset ι → Ideal O := fun S => ∏ i ∈ S, Ideal.span {p i}
  have hq : Function.Injective q := FirstCauchyArithmetic.family_product_injective _ hinj
  let I := (boundedPrimeSupports p F X).image q
  have hcard : I.card = (boundedPrimeSupports p F X).card := Finset.card_image_of_injective _ hq
  rw [← hcard]
  apply DescentFiberCost.finite_ideal_count_real I X hX
  · intro J hJ
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hJ
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => NeZero.ne (Ideal.span {p i}))
  · intro J hJ
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hJ
    rw [← primeProductNorm_eq_ideal_norm p S]
    exact (Finset.mem_filter.mp hS).2

include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem normalizedColumn_subset_norm_bound (g : 𝓢(ℝ, ℂ)) (A X : ℝ)
    (hX : 0 < X) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A) (G S U : Finset ι)
    (hU : U ⊆ G∪S)
    (hn : FirstPassCubeLabels.normalizedColumn p
      (fun R => g (FirstPassCubeLabels.columnLog p X R)) (G∪S) ≠ 0) :
    primeProductNorm p U ≤ X*Real.exp A := by
  have hval : g (FirstPassCubeLabels.columnLog p X (G∪S)) ≠ 0 := by
    intro h
    apply hn
    simp only [FirstPassCubeLabels.normalizedColumn,h,zero_div]
  exact (primeProductNorm_mono p hp hU).trans
    (columnLog_norm_upper p hp X A hX (G∪S) ((le_abs_self _).trans (hgA _ hval)))

end SecondPassArithmetic

end

end OAI

end


