-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0114
-- name    : PNT_ZeroFree_433_0114
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:26:52.966241+00:00
-- url     : https://prove2.me/theorems/d71855b5-8e6e-45e1-9899-59b288f9fb44
-- title:
--   Zero-free region foundations: QuadraticSieve.MaskedPrincipalBounds [0114]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.MaskedPrincipalBounds
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/MaskedPrincipalBounds.lean#L80-L635

import Definitions.Def_PNT_ZeroFree_433_0112

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/MaskedPrincipalBounds.lean#L80-L635
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.QuadraticSieve.MaskedPrincipalBounds
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem middleTruncation_coprime_common_mask
    (G C : Ideal O) (hG : Squarefree G) (hC : Squarefree C) (hGC : IsCoprime G C)
    (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) :
    middleTruncation (fun P : primePool {G * C} => P.val) Finset.univ W X Y Z lengthScale =
      ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q : ℂ) *
        middleTruncation (fun P : primePool {C} => P.val) Finset.univ W
          (X / (Ideal.absNorm q : ℝ)) (Y / (Ideal.absNorm q : ℝ)) (Z / (Ideal.absNorm q : ℝ)) lengthScale := by
  classical
  have hprod : Squarefree (G * C) := squarefree_mul_iff.mpr ⟨hGC.isRelPrime, hG, hC⟩
  rw [middleTruncation_eq_ideal_frequencies _ hprod]
  simp_rw [middleTruncation_eq_ideal_frequencies C hC]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := idealDivisors G) (t := rowNormDisk ⌊lengthScale⌋₊)]
  apply Finset.sum_congr rfl
  intro h hh
  rw [QuadraticDivisorSplit.sum_divisors_coprime_product G C hG.ne_zero hC.ne_zero hGC]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro d hd
  have hqG := (mem_idealDivisors hG.ne_zero).mp hq
  have hdC := (mem_idealDivisors hC.ne_zero).mp hd
  have hq0 : q ≠ 0 := by intro he; rw [he, zero_dvd_iff] at hqG; exact hG.ne_zero hqG
  have hNq : 0 < (Ideal.absNorm q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
  have hqd := (hGC.mono hqG hdC).isRelPrime
  have hlow : Y < (Ideal.absNorm q : ℝ) * (Ideal.absNorm d : ℝ) ↔
      Y / (Ideal.absNorm q : ℝ) < (Ideal.absNorm d : ℝ) := by
    constructor
    · intro hy
      apply (div_lt_iff₀ hNq).mpr
      simpa only [mul_comm] using hy
    · intro hy
      simpa only [mul_comm] using (div_lt_iff₀ hNq).mp hy
  have hhigh : (Ideal.absNorm q : ℝ) * (Ideal.absNorm d : ℝ) ≤ Z ↔
      (Ideal.absNorm d : ℝ) ≤ Z / (Ideal.absNorm q : ℝ) := by
    constructor
    · intro hz
      apply (le_div_iff₀ hNq).mpr
      simpa only [mul_comm] using hz
    · intro hz
      simpa only [mul_comm] using (le_div_iff₀ hNq).mp hz
  simp only [map_mul, Nat.cast_mul, hlow, hhigh, hqd.moebius_mul, Int.cast_mul]
  by_cases hp : Y / (Ideal.absNorm q : ℝ) < (Ideal.absNorm d : ℝ) ∧
      (Ideal.absNorm d : ℝ) ≤ Z / (Ideal.absNorm q : ℝ)
  · simp only [hp, and_self, ite_true]
    have harg : X * ‖eisEmbedding h‖ ^ 2 / ((Ideal.absNorm q : ℝ) * (Ideal.absNorm d : ℝ)) =
        (X / (Ideal.absNorm q : ℝ)) * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ) := by ring
    rw [harg]
    push_cast
    ring
  · simp only [hp, ite_false, mul_zero]

theorem sqrt_norm_divisor_scale (M B q : ℝ) (hM : 0 ≤ M) (_hB : 0 ≤ B) (hq : 0 < q) :
    Real.sqrt (M / B) / q = Real.sqrt ((M / q ^ 2) / B) := by
  rw [Real.sqrt_div hM, Real.sqrt_div (by positivity : 0 ≤ M / q ^ 2), Real.sqrt_div hM, Real.sqrt_sq hq.le]
  ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalMaskedTruncatedMiddle (G : Ideal O) (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    middleTruncation (fun P : primePool {G * (left j * right k)} => P.val) Finset.univ W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (Y i) (Z i) lengthScale

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMaskedTruncatedMiddle_eq_divisors
    (G : Ideal O) (hG : Squarefree G) (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (hM : 0 ≤ M) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hGl : ∀ j, IsCoprime G (left j)) (hGr : ∀ k, IsCoprime G (right k)) :
    originalMaskedTruncatedMiddle G W rows left right a b M Y Z lengthScale =
      ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q : ℂ) *
        originalTruncatedMiddle W rows left right a b (M / (Ideal.absNorm q : ℝ) ^ 2)
          (fun i => Y i / (Ideal.absNorm q : ℝ)) (fun i => Z i / (Ideal.absNorm q : ℝ)) lengthScale := by
  classical
  have hp (i : m) (j : n) (k : p) :
      originalTerm rows left right a b 1 1 i j k *
        middleTruncation (fun P : primePool {G * (left j * right k)} => P.val) Finset.univ W
          (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (Y i) (Z i) lengthScale =
      ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q : ℂ) *
        (originalTerm rows left right a b 1 1 i j k *
          middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
            (Real.sqrt ((M / (Ideal.absNorm q : ℝ) ^ 2) / (Ideal.absNorm (rows i) : ℝ)))
            (Y i / (Ideal.absNorm q : ℝ)) (Z i / (Ideal.absNorm q : ℝ)) lengthScale) := by
    by_cases hc : IsCoprime (left j) (right k)
    · have hsq : Squarefree (left j * right k) :=
        squarefree_mul_iff.mpr ⟨hc.isRelPrime, (hleft j).2.1, (hright k).2.1⟩
      rw [middleTruncation_coprime_common_mask G _ hG hsq ((hGl j).mul_right (hGr k)), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      have hqG := (mem_idealDivisors hG.ne_zero).mp hq
      have hq0 : q ≠ 0 := by intro he; rw [he, zero_dvd_iff] at hqG; exact hG.ne_zero hqG
      have hNq : 0 < (Ideal.absNorm q : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
      rw [sqrt_norm_divisor_scale M _ _ hM (Nat.cast_nonneg _) hNq]
      ring
    · have hz : originalTerm rows left right a b 1 1 i j k = 0 := by simp only [originalTerm, hc, ite_false]
      simp only [hz, zero_mul, mul_zero, Finset.sum_const_zero]
  unfold originalMaskedTruncatedMiddle
  simp_rw [hp]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset p)) (t := idealDivisors G),
    Finset.sum_comm (s := (Finset.univ : Finset n)) (t := idealDivisors G),
    Finset.sum_comm (s := (Finset.univ : Finset m)) (t := idealDivisors G)]
  simp only [originalTruncatedMiddle, Finset.mul_sum]

theorem HasSieveExponent.original_masked_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (G : Ideal O) (hG : Squarefree G)
    (B N M U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hGl : ∀ j, IsCoprime G (left j)) (hGr : ∀ k, IsCoprime G (right k))
    (hZ : ∀ i, Z i ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) :
    ‖originalMaskedTruncatedMiddle G W rows left right a b M Y Z lengthScale‖ ≤
      (idealDivisors G).card * (((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2)))) := by
  let V := ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2)))
  have hqbound (q : Ideal O) (hq : q ∈ idealDivisors G) :
      ‖originalTruncatedMiddle W rows left right a b (M / (Ideal.absNorm q : ℝ) ^ 2)
        (fun i => Y i / (Ideal.absNorm q : ℝ)) (fun i => Z i / (Ideal.absNorm q : ℝ)) lengthScale‖ ≤ V := by
    have hqG := (mem_idealDivisors hG.ne_zero).mp hq
    have hq0 : q ≠ 0 := by intro he; rw [he, zero_dvd_iff] at hqG; exact hG.ne_zero hqG
    have hq1 : (1 : ℝ) ≤ Ideal.absNorm q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
    have hqpos : (0 : ℝ) < Ideal.absNorm q := by linarith
    have hZq (i : m) : Z i / (Ideal.absNorm q : ℝ) ≤
        U * Real.sqrt ((M / (Ideal.absNorm q : ℝ) ^ 2) / (Ideal.absNorm (rows i) : ℝ)) := by
      calc
        _ ≤ (U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) / (Ideal.absNorm q : ℝ) :=
          div_le_div_of_nonneg_right (hZ i) hqpos.le
        _ = U * (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) / (Ideal.absNorm q : ℝ)) := by ring
        _ = _ := by rw [sqrt_norm_divisor_scale M _ _ hM.le (Nat.cast_nonneg _) hqpos]
    have hb := hexp.original_truncated_middle deltaLoss hδ ε hε B N (M / (Ideal.absNorm q : ℝ) ^ 2) U
      hB hN (by positivity) hU rows left right hr hl hri hrows a b W
      (fun i => Y i / (Ideal.absNorm q : ℝ)) (fun i => Z i / (Ideal.absNorm q : ℝ)) lengthScale hleft hright hZq
    apply hb.trans
    dsimp only [V]
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := originalMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a b
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    gcongr
    exact div_le_self hM.le (one_le_pow₀ hq1)
  rw [originalMaskedTruncatedMiddle_eq_divisors G hG W rows left right a b M hM.le Y Z lengthScale
    (fun j => (hleft j).1) (fun k => (hright k).1) hGl hGr]
  calc
    _ ≤ ∑ q ∈ idealDivisors G,
        ‖(UniqueFactorizationMonoid.moebius q : ℂ) *
          originalTruncatedMiddle W rows left right a b (M / (Ideal.absNorm q : ℝ) ^ 2)
            (fun i => Y i / (Ideal.absNorm q : ℝ)) (fun i => Z i / (Ideal.absNorm q : ℝ)) lengthScale‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ idealDivisors G, V := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (QuadraticInitialBound.norm_ideal_moebius_le_one q)).trans (hqbound q hq)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, V]

end

open ActualEisensteinCubic IdealMobiusDivisorSum IdealCoprimeSieveOperator

theorem HasSieveExponent.actual_principal_difference {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : Type} [Fintype n] [DecidableEq n]
      (cols : n → Ideal O) (_hinj : Function.Injective cols)
      (M N K : ℝ), 1 ≤ M → 1 ≤ N → 1 ≤ K →
      (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
      (∀ j k, columnRay (cols j) = columnRay (cols k)) →
      ∀ (a : n → ℂ) (G : Ideal O), Squarefree G →
      (∀ P ∈ fixedBadPrimes, P ∣ G) → ∀ (ε : ℝ) (hε : 0 < ε),
      ‖(Real.sqrt M : ℂ) * actualPrincipalDifference cols a G K‖ ≤
        ((idealDivisors G).card : ℝ)^2 * (supportConstant ε hε * N^ε) *
          C * (K*N)^deltaLoss * (Real.sqrt (M/K)*N + Real.sqrt M*K^(α-1/2)) *
          ∑ j, ‖a j‖^2 := by
  obtain ⟨C,hC,hbound⟩ := hexp.reverse deltaLoss hδ
  refine ⟨C,hC,?_⟩
  intro n _ _ cols hinj M N K hM hN hK hcols hray a G hG hbad ε hε
  have hM0 : 0 ≤ M := by linarith
  have hK0 : 0 < K := by linarith
  have hs := actualPrincipalDifference_bound cols hinj N (by linarith) hcols hray a G hG hbad K hK0 ε hε
  have hsupp := (supportConstant_pos ε hε).le
  have hb := hbound K N hK hN
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg M)]
  calc
    _ ≤ Real.sqrt M * (((idealDivisors G).card : ℝ)^2 *
        ((1/Real.sqrt K)*sieveNorm K N*(supportConstant ε hε*N^ε)*∑ j, ‖a j‖^2)) :=
      mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt M * (((idealDivisors G).card : ℝ)^2 *
        ((1/Real.sqrt K)*(C*(K*N)^deltaLoss*(N+K^α))*(supportConstant ε hε*N^ε)*∑ j, ‖a j‖^2)) := by
      gcongr
    _ = ((idealDivisors G).card : ℝ)^2*(supportConstant ε hε*N^ε)*C*(K*N)^deltaLoss*
        (Real.sqrt (M/K)*(N+K^α))*∑ j, ‖a j‖^2 := by
      rw [Real.sqrt_div hM0]
      ring
    _ = _ := by
      rw [mul_add, sqrt_div_mul_rpow M K α hM0 hK0]

end CanonicalQuadraticSieve

namespace ShortDraftDescent
open MeasureTheory Filter

theorem integral_geometric_descent
    {Node Parameter : Type*} [MeasurableSpace Parameter]
    (rank : Node → ℕ) (energy mass terminal : Node → ℝ)
    (left right : Node → Parameter → Node)
    (measure : Node → Measure Parameter) (weight : Node → Parameter → ℝ)
    (hweight : ∀ x, ∀ᵐ t ∂measure x, 0 ≤ weight x t)
    (hintegrable : ∀ x, Integrable (fun t => weight x t *
      Real.sqrt (mass (left x t)) * Real.sqrt (mass (right x t))) (measure x))
    (hterminal : ∀ x, rank x = 0 → energy x ≤ mass x)
    (hchildren : ∀ x, rank x ≠ 0 → ∀ᵐ t ∂measure x,
      rank (left x t) < rank x ∧ rank (right x t) < rank x)
    (hstep : ∀ x, rank x ≠ 0 → energy x ≤ terminal x +
      ∫ t, weight x t * Real.sqrt (energy (left x t)) * Real.sqrt (energy (right x t)) ∂measure x)
    (hbudget : ∀ x, rank x ≠ 0 → terminal x +
      (∫ t, weight x t * Real.sqrt (mass (left x t)) * Real.sqrt (mass (right x t)) ∂measure x) ≤ mass x) :
    ∀ x, energy x ≤ mass x := by
  have h : ∀ n : ℕ, ∀ x, rank x = n → energy x ≤ mass x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      by_cases hn : n = 0
      · exact hterminal x (hx.trans hn)
      have hx0 : rank x ≠ 0 := by omega
      have hmono : (∫ t, weight x t * Real.sqrt (energy (left x t)) *
          Real.sqrt (energy (right x t)) ∂measure x) ≤
          ∫ t, weight x t * Real.sqrt (mass (left x t)) *
          Real.sqrt (mass (right x t)) ∂measure x := by
        refine integral_mono_of_nonneg ?_ (hintegrable x) ?_
        · filter_upwards [hweight x] with t ht
          exact mul_nonneg (mul_nonneg ht (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
        · filter_upwards [hweight x, hchildren x hx0] with t ht hr
          have hl := ih (rank (left x t)) (by omega) (left x t) rfl
          have hh := ih (rank (right x t)) (by omega) (right x t) rfl
          exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) ht)
            (Real.sqrt_le_sqrt hh) (Real.sqrt_nonneg _)
            (mul_nonneg ht (Real.sqrt_nonneg _))
      exact (hstep x hx0).trans ((add_le_add le_rfl hmono).trans (hbudget x hx0))
  intro x
  exact h (rank x) x rfl

end ShortDraftDescent

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic FourierBridge

def halfShellFactor (N q : ℝ) : ℝ := Real.sqrt (N/2) / Real.sqrt q

lemma halfShellFactor_nonneg (N q : ℝ) : 0 ≤ halfShellFactor N q := by
  unfold halfShellFactor
  positivity

lemma halfShellFactor_le_one (N q : ℝ) (hq : 0 < q) (h : N/2 ≤ q) :
    halfShellFactor N q ≤ 1 := by
  unfold halfShellFactor
  exact (div_le_one (Real.sqrt_pos.mpr hq)).mpr (Real.sqrt_le_sqrt h)

lemma halfShellFactor_pair (M F N i j : ℝ) (hN : 0 < N) (hi : 0 < i) (hj : 0 < j)
    (hF : 0 < F) :
    (2*M/(F*N))*halfShellFactor N i*halfShellFactor N j =
      M/(Real.sqrt (i*j)*F) := by
  unfold halfShellFactor
  rw [Real.sqrt_mul hi.le]
  have hs := Real.sq_sqrt (show 0 ≤ N/2 by positivity)
  have hsi := (Real.sqrt_pos.mpr hi).ne'
  have hsj := (Real.sqrt_pos.mpr hj).ne'
  field_simp
  rw [hs]
  ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def smallPrincipalCorrection (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) : ℝ :=
  ∑ D ∈ S, ∑ E ∈ T, ∑ i,
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k *
      ((M/(Real.sqrt ((Ideal.absNorm (left j) : ℝ)*(Ideal.absNorm (right k) : ℝ))*F) : ℝ) : ℂ)‖

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma originalTerm_real_scaling
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (u : n → ℝ) (v : p → ℝ)
    (D E : Ideal O) (i : m) (j : n) (k : p) :
    originalTerm rows left right (fun j => a j*(u j:ℂ)) (fun k => b k*(v k:ℂ)) D E i j k =
      originalTerm rows left right a b D E i j k * (u j:ℂ) * (v k:ℂ) := by
  unfold originalTerm
  by_cases hc : IsCoprime (left j) (right k) <;>
    by_cases hd : D ∣ left j <;> by_cases he : E ∣ right k <;>
    simp only [hc,hd,he,ite_true,ite_false,mul_zero,zero_mul,star_zero,star_mul,Complex.star_def,
      Complex.conj_ofReal] ; ring

theorem smallPrincipalCorrection_bound
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2*D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) :
    smallPrincipalCorrection S T rows left right a b M F ≤
      (2*M/(F*N))*Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  have hN0 : 0 < N := by linarith
  let u := fun j => halfShellFactor N (Ideal.absNorm (left j) : ℝ)
  let v := fun k => halfShellFactor N (Ideal.absNorm (right k) : ℝ)
  let a' := fun j => a j*(u j:ℂ)
  let b' := fun k => b k*(v k:ℂ)
  have hu (j) : 0 ≤ u j ∧ u j ≤ 1 :=
    ⟨halfShellFactor_nonneg _ _,halfShellFactor_le_one _ _ (by linarith [(hleft j).2.1]) (hleft j).2.1⟩
  have hv (k) : 0 ≤ v k ∧ v k ≤ 1 :=
    ⟨halfShellFactor_nonneg _ _,halfShellFactor_le_one _ _ (by linarith [(hright k).2.1]) (hright k).2.1⟩
  have ha (j) : ‖a' j‖ ≤ ‖a j‖ := by
    simp only [a',norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hu j).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hu j).2
  have hb (k) : ‖b' k‖ ≤ ‖b k‖ := by
    simp only [b',norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hv k).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hv k).2
  have ht (D E : Ideal O) (i j k) :
      originalTerm rows left right a b D E i j k *
        ((M/(Real.sqrt ((Ideal.absNorm (left j) : ℝ)*(Ideal.absNorm (right k) : ℝ))*F) : ℝ) : ℂ) =
      ((2*M/(F*N):ℝ):ℂ)*originalTerm rows left right a' b' D E i j k := by
    have hid := halfShellFactor_pair M F N (Ideal.absNorm (left j) : ℝ) (Ideal.absNorm (right k) : ℝ)
      hN0 (by linarith [(hleft j).2.1]) (by linarith [(hright k).2.1]) hF
    rw [←hid, show originalTerm rows left right a' b' D E i j k =
      originalTerm rows left right a b D E i j k*(u j:ℂ)*(v k:ℂ) from
      originalTerm_real_scaling rows left right a b u v D E i j k]
    push_cast
    dsimp only [u,v]
    ring
  have hblock := canonical_original_divisor_block_phase_bound ε hε S T D₁ D₂ B N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows (fun j => ⟨(hleft j).1,(hleft j).2.2⟩)
      (fun k => ⟨(hright k).1,(hright k).2.2⟩) a' b' (fun _ => 0) (fun _ => 0) 0
  simp only [zero_add,logPhase_zero,mul_one] at hblock
  have hcost := divisorBlockCost_mono_coefficients ε hε D₁ D₂ B N (by linarith) (by linarith) a' a b' b ha hb
  have heq : smallPrincipalCorrection S T rows left right a b M F =
      (2*M/(F*N))*(∑ D ∈ S, ∑ E ∈ T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a' b' D E i j k‖) := by
    unfold smallPrincipalCorrection
    simp_rw [ht,←Finset.mul_sum]
    simp only [norm_mul,Complex.norm_of_nonneg (show 0 ≤ 2*M/(F*N) by positivity)]
    simp_rw [←Finset.mul_sum]
  rw [heq]
  exact mul_le_mul_of_nonneg_left (hblock.trans (Real.sqrt_le_sqrt hcost)) (by positivity)

end

open ActualEisensteinCubic

theorem HasSieveExponent.small_principal_correction {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2*D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (hcut : D₁*D₂ ≤ U*(N*Real.sqrt (F/(M*B)))) :
    smallPrincipalCorrection S T rows left right a b M F ≤
      2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (M/F+U*Real.sqrt (M/F)*B^(α-1/2)) := by
  have hb := smallPrincipalCorrection_bound ε hε S T D₁ D₂ B N M F hD₁ hD₂ hN hM hF hS hT
    rows left right hr hl hri hrows hleft hright a b
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N a b
  have he := divisorEnergyFactor_nonneg ε hε N a b
  have hC := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ (2*M/(F*N))*(divisorEnergyFactor ε hε N a b*
        (divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss*(N+B^α*(D₁*D₂)))) :=
      hb.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    _ = (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss))*
        ((M/(F*N))*(N+B^α*(D₁*D₂))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dual_middle_scale_shape M F B N (D₁*D₂) U α hM hF (by linarith) (by linarith) hcut)
      (by positivity)

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

theorem truncationError_symmetric_bound (m : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X₀ X T : ℝ),
        0 < X₀ → X₀ / 2 ≤ X → X ≤ 2 * X₀ → 4 ≤ T →
        ‖truncationError P S W X (X₀ / T) (T * X₀) (T ^ 4)‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ m := by
  obtain ⟨s, C, hC, hb⟩ := truncationError_bound (m + 3)
  refine ⟨s, C * 2 ^ (m + 10), by positivity, ?_⟩
  intro ι _ P _ hinj S W X₀ X T hX₀ hlo hhi hT
  obtain ⟨hX, hY, hYX, hXZ, hL⟩ := symmetric_truncation_scales X₀ X T hX₀ hlo hhi hT
  have hp := hb P hinj S W X (X₀ / T) (T * X₀) (T ^ 4) hX hY hYX hXZ hL
  have hs := symmetric_truncation_scalar_bound m X₀ X T hX₀ hlo hhi hT
  calc
    _ ≤ (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
        (((X₀ / T) / X) ^ (m + 3) + 1 / (1 + (T * X₀) / X) ^ (m + 3) +
          (X / (X₀ / T)) / ((min 1 (X / (T * X₀))) ^ 2 * (1 + X * T ^ 4 / (T * X₀)) ^ (m + 3))) := hp
    _ ≤ (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * (2 ^ (m + 10) / T ^ m) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

theorem primePool_symmetric_error_bound (m : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (G : Ideal O) (_hG : G ≠ 0)
        (W : 𝓢(ℝ, ℂ)) (X₀ X T : ℝ),
        0 < X₀ → X₀ / 2 ≤ X → X ≤ 2 * X₀ → 4 ≤ T →
        ‖truncationError (fun P : primePool {G} => P.val) Finset.univ W
          X (X₀ / T) (T * X₀) (T ^ 4)‖ ≤
          (supportConstant ε hε * (Ideal.absNorm G : ℝ) ^ ε) *
            (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ m := by
  obtain ⟨s, C, hC, hb⟩ := truncationError_symmetric_bound m
  refine ⟨s, C, hC, ?_⟩
  intro ε hε G hG W X₀ X T hX₀ hlo hhi hT
  have hh := hb (fun P : primePool {G} => P.val) Subtype.val_injective Finset.univ W
    X₀ X T hX₀ hlo hhi hT
  simp only [Finset.card_univ, Fintype.card_coe, primePool_singleton_eq_primeSupport] at hh
  apply hh.trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (support_card_bound ε hε G hG) (by positivity)) (by positivity)

theorem lowPrincipal_symmetric_error_bound (m : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (I J : Ideal O) (_hI : Admissible I) (_hJ : Admissible J)
        (W : 𝓢(ℝ, ℂ)) (X₀ X T : ℝ),
        0 < X₀ → X₀ / 2 ≤ X → X ≤ 2 * X₀ → 4 ≤ T →
        ‖lowPrincipalError I J W X (X₀ / T) (T * X₀) (T ^ 4)‖ ≤
          (4 * supportConstant ε hε * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) ^ ε) *
            (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) / T ^ m := by
  obtain ⟨s, C, hC, hb⟩ := lowPrincipalError_bound (m + 3)
  refine ⟨s, C * 2 ^ (m + 10), by positivity, ?_⟩
  intro ε hε I J hI hJ W X₀ X T hX₀ hlo hhi hT
  obtain ⟨hX, hY, hYX, hXZ, hL⟩ := symmetric_truncation_scales X₀ X T hX₀ hlo hhi hT
  have hh := hb ε hε I J hI hJ W X (X₀ / T) (T * X₀) (T ^ 4) hX hY hYX hXZ hL
  have hs := symmetric_truncation_scalar_bound m X₀ X T hX₀ hlo hhi hT
  have hc := (supportConstant_pos ε hε).le
  calc
    _ ≤ (4 * supportConstant ε hε * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) ^ ε) *
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) *
        (((X₀ / T) / X) ^ (m + 3) + 1 / (1 + (T * X₀) / X) ^ (m + 3) +
          (X / (X₀ / T)) / ((min 1 (X / (T * X₀))) ^ 2 * (1 + X * T ^ 4 / (T * X₀)) ^ (m + 3))) := hh
    _ ≤ (4 * supportConstant ε hε * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) ^ ε) *
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) * (2 ^ (m + 10) / T ^ m) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

theorem originalTerm_one_norm_le {m n p : Type*}
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (i : m) (j : n) (k : p) :
    ‖originalTerm rows left right a b 1 1 i j k‖ ≤ ‖a j‖ * ‖b k‖ := by
  classical
  unfold originalTerm
  simp only [one_dvd, ite_true]
  split_ifs with hc
  · simp only [norm_mul, norm_star]
    calc
      _ ≤ (1 * ‖a j‖) * (1 * ‖b k‖) := mul_le_mul
        (mul_le_mul_of_nonneg_right (quadraticRow_norm_le_one _ _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (quadraticRow_norm_le_one _ _) (norm_nonneg _))
        (by positivity) (by positivity)
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

theorem actual_pair_error_energy {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ)
    (E : ℝ) (hE : 0 ≤ E) (error : m → n → n → ℂ)
    (herr : ∀ i j k, ‖error i j k‖ ≤ E) :
    ‖∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k * error i j k‖ ≤
      Fintype.card m * Fintype.card n * E * ∑ j, ‖a j‖ ^ 2 := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : n => ‖a j‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  have hs : (∑ j, ∑ k, ‖a j‖ * ‖a k‖ * E) = (∑ j, ‖a j‖) ^ 2 * E := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, ‖originalTerm rows cols cols a a 1 1 i j k * error i j k‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun j hj => norm_sum_le _ _)
    _ ≤ ∑ _i : m, ∑ j, ∑ k, ‖a j‖ * ‖a k‖ * E := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul (originalTerm_one_norm_le rows cols cols a a i j k) (herr i j k)
        (norm_nonneg _) (by positivity)
    _ = (Fintype.card m : ℝ) * ((∑ j, ‖a j‖) ^ 2 * E) := by
      simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Fintype.card m : ℝ) * (((∑ j, ‖a j‖ ^ 2) * Fintype.card n) * E) := by gcongr
    _ = _ := by ring

theorem finite_ideal_family_card_bound {m : Type*} [Fintype m]
    (I : m → Ideal O) (hI : Function.Injective I) (B : ℝ) (hB : 1 ≤ B)
    (hzero : ∀ i, I i ≠ 0) (hNorm : ∀ i, (Ideal.absNorm (I i) : ℝ) ≤ B) :
    (Fintype.card m : ℝ) ≤ 128 * B := by
  classical
  have hb := DescentFiberCost.finite_ideal_count_real (Finset.univ.image I) B hB
    (by intro J hJ; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hJ; exact hzero i)
    (by intro J hJ; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hJ; exact hNorm i)
  simpa only [Finset.card_image_of_injective _ hI, Finset.card_univ] using hb

theorem actual_pair_error_ideal_bound {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (hr : Function.Injective rows) (hc : Function.Injective cols)
    (B N : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (hcols : ∀ j, cols j ≠ 0 ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (a : n → ℂ) (E : ℝ) (hE : 0 ≤ E) (error : m → n → n → ℂ)
    (herr : ∀ i j k, ‖error i j k‖ ≤ E) :
    ‖∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k * error i j k‖ ≤
      16384 * B * N * E * ∑ j, ‖a j‖ ^ 2 := by
  have hrc := finite_ideal_family_card_bound rows hr B hB (fun i => (hrows i).1) (fun i => (hrows i).2)
  have hcc := finite_ideal_family_card_bound cols hc N hN (fun j => (hcols j).1) (fun j => (hcols j).2)
  apply (actual_pair_error_energy rows cols a E hE error herr).trans
  calc
    _ ≤ (128 * B) * (128 * N) * E * ∑ j, ‖a j‖ ^ 2 := by gcongr
    _ = _ := by ring

end CanonicalQuadraticSieve

end

end OAI

end


