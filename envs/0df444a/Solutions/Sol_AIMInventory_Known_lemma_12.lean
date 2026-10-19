-- Prove2me | solution 1 for AIMInventory.Known.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:55:51.387293+00:00
-- url     : https://prove2.me/submissions/020a34a5-74d2-4d43-928b-c323c6992533

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace SolL12

section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integrable_pow_of_memLp {f : Ω → ℝ} {p : ℕ} (hf : MemLp f p μ) {j : ℕ} (hj : j ≤ p) :
    Integrable (fun ω => f ω ^ j) μ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · have h2 : MemLp f (j : ENNReal) μ := hf.mono_exponent (by exact_mod_cast hj)
    refine h2.integrable_norm_pow'.mono' (h2.aestronglyMeasurable.pow j)
      (Filter.Eventually.of_forall fun ω => ?_)
    simp

lemma integral_add_pow {Y Z : Ω → ℝ} (h : IndepFun Y Z μ) (k : ℕ)
    (hY : ∀ j ≤ k, Integrable (fun ω => Y ω ^ j) μ)
    (hZ : ∀ j ≤ k, Integrable (fun ω => Z ω ^ j) μ) :
    ∫ ω, (Y ω + Z ω) ^ k ∂μ = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
      ((∫ ω, Y ω ^ j ∂μ) * ∫ ω, Z ω ^ (k - j) ∂μ) := by
  have hexp : ∀ ω, (Y ω + Z ω) ^ k =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (Y ω ^ j * Z ω ^ (k - j)) := by
    intro ω
    rw [add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hind : ∀ j, IndepFun (fun ω => Y ω ^ j) (fun ω => Z ω ^ (k - j)) μ := fun j =>
    h.comp (measurable_id.pow_const j) (measurable_id.pow_const (k - j))
  have hint : ∀ j ∈ Finset.range (k + 1), Integrable
      (fun ω => (k.choose j : ℝ) * (Y ω ^ j * Z ω ^ (k - j))) μ := by
    intro j hj
    have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using hj
    have := (hind j).integrable_mul (hY j hjk) (hZ (k - j) (Nat.sub_le _ _))
    exact this.const_mul _
  simp_rw [hexp]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using hj
  rw [integral_const_mul, (hind j).integral_fun_mul_eq_mul_integral
    (hY j hjk).aestronglyMeasurable (hZ (k - j) (Nat.sub_le _ _)).aestronglyMeasurable]

variable {X : ℕ → Ω → ℝ}

lemma step_moment (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {p : ℕ} (hmem : MemLp (X 0) p μ) (m k : ℕ) (hk : k ≤ p) :
    ∫ ω, (∑ i ∈ Finset.range (m + 1), X i ω) ^ k ∂μ =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        ((∫ ω, (∑ i ∈ Finset.range m, X i ω) ^ j ∂μ) * ∫ ω, X 0 ω ^ (k - j) ∂μ) := by
  have hmemi : ∀ i, MemLp (X i) p μ := fun i => (hident i).memLp_iff.2 hmem
  have e : (fun ω => ∑ i ∈ Finset.range m, X i ω) = ∑ i ∈ Finset.range m, X i := by
    ext ω; simp [Finset.sum_apply]
  have hSm : MemLp (fun ω => ∑ i ∈ Finset.range m, X i ω) p μ := by
    rw [e]; exact memLp_finsetSum' (Finset.range m) (fun i _ => hmemi i)
  have hind : IndepFun (fun ω => ∑ i ∈ Finset.range m, X i ω) (X m) μ := by
    rw [e]
    exact hindep.indepFun_finsetSum_of_notMem₀ (fun i => (hmemi i).aemeasurable)
      (Finset.notMem_range_self : m ∉ Finset.range m)
  have h := integral_add_pow hind k (fun j hj => integrable_pow_of_memLp hSm (hj.trans hk))
    (fun j hj => integrable_pow_of_memLp (hmemi m) (hj.trans hk))
  have hZ : ∀ l, ∫ ω, X m ω ^ l ∂μ = ∫ ω, X 0 ω ^ l ∂μ := fun l =>
    ((hident m).comp (measurable_id.pow_const l)).integral_eq
  simp_rw [Finset.sum_range_succ _ m]
  rw [h]
  simp_rw [hZ]


lemma moments_four (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hmem : MemLp (X 0) 4 μ) (hmean : ∫ ω, X 0 ω ∂μ = 0) (m : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range m, X i ω) ∂μ = 0) ∧
    (∫ ω, (∑ i ∈ Finset.range m, X i ω) ^ 2 ∂μ = m * ∫ ω, X 0 ω ^ 2 ∂μ) ∧
    (∫ ω, (∑ i ∈ Finset.range m, X i ω) ^ 3 ∂μ = m * ∫ ω, X 0 ω ^ 3 ∂μ) ∧
    (∫ ω, (∑ i ∈ Finset.range m, X i ω) ^ 4 ∂μ =
      m * ∫ ω, X 0 ω ^ 4 ∂μ + 3 * m * (m - 1) * (∫ ω, X 0 ω ^ 2 ∂μ) ^ 2) := by
  have hmem' : MemLp (X 0) ((4 : ℕ) : ENNReal) μ := by exact_mod_cast hmem
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    have e1 := step_moment hindep hident hmem' m 1 (by norm_num)
    have e2 := step_moment hindep hident hmem' m 2 (by norm_num)
    have e3 := step_moment hindep hident hmem' m 3 (by norm_num)
    have e4 := step_moment hindep hident hmem' m 4 (by norm_num)
    simp [Finset.sum_range_succ, Nat.choose, hmean] at e1 e2 e3 e4
    simp only [Finset.sum_range_succ _ m]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e1, h1]
    · rw [e2, h2]; push_cast; ring
    · rw [e3, h1, h3]; push_cast; ring
    · rw [e4, h1, h2, h4]; push_cast; ring

lemma moment_cs {f : Ω → ℝ} {p : ℕ} (hf : MemLp f p μ) (r s : ℕ) (hr : 2 * r ≤ p) (hs : 2 * s ≤ p) :
    (∫ ω, f ω ^ (r + s) ∂μ) ^ 2 ≤ (∫ ω, f ω ^ (2 * r) ∂μ) * ∫ ω, f ω ^ (2 * s) ∂μ := by
  have key : ∀ t : ℝ, 0 ≤ (∫ ω, f ω ^ (2 * s) ∂μ) * (t * t) + (2 * ∫ ω, f ω ^ (r + s) ∂μ) * t
      + ∫ ω, f ω ^ (2 * r) ∂μ := by
    intro t
    have hnn : 0 ≤ ∫ ω, (f ω ^ r + t * f ω ^ s) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    have i1 := integrable_pow_of_memLp hf (j := 2 * r) hr
    have i2 := integrable_pow_of_memLp hf (j := r + s) (by omega)
    have i3 := integrable_pow_of_memLp hf (j := 2 * s) hs
    have hpt : ∀ ω, (f ω ^ r + t * f ω ^ s) ^ 2 =
        f ω ^ (2 * r) + (2 * t) * f ω ^ (r + s) + t ^ 2 * f ω ^ (2 * s) := by
      intro ω; ring
    simp_rw [hpt] at hnn
    have j3 : Integrable (fun ω => 2 * t * f ω ^ (r + s)) μ := i2.const_mul _
    have j1 : Integrable (fun ω => f ω ^ (2 * r) + 2 * t * f ω ^ (r + s)) μ := i1.add j3
    have j2 : Integrable (fun ω => t ^ 2 * f ω ^ (2 * s)) μ := i3.const_mul _
    rw [integral_add j1 j2, integral_add i1 j3, integral_const_mul, integral_const_mul] at hnn
    nlinarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

lemma c2_sq_le_c4 {f : Ω → ℝ} {p : ℕ} (hf : MemLp f p μ) (hp : 4 ≤ p) :
    (∫ ω, f ω ^ 2 ∂μ) ^ 2 ≤ ∫ ω, f ω ^ 4 ∂μ := by
  have := moment_cs hf 2 0 (by omega) (by omega)
  simpa using this

lemma real_ineqs (c2 c4 c6 : ℝ) (n2 : 0 ≤ c2) (n4 : 0 ≤ c4) (n6 : 0 ≤ c6)
    (hA : c2 ^ 2 ≤ c4) (hB : c4 ^ 2 ≤ c2 * c6) : c2 ^ 3 ≤ c6 ∧ c2 * c4 ≤ c6 := by
  have hD : c2 ^ 3 ≤ c6 := by
    rcases n2.eq_or_lt with h | h
    · rw [← h]; simpa using n6
    · have : c2 * c2 ^ 3 ≤ c2 * c6 := by nlinarith [sq_nonneg c2]
      exact le_of_mul_le_mul_left this h
  refine ⟨hD, ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have h1 : (c2 * c4) ^ 2 ≤ c2 ^ 3 * c6 := by
    have : (c2 * c4) ^ 2 = c2 ^ 2 * c4 ^ 2 := by ring
    rw [this]
    calc c2 ^ 2 * c4 ^ 2 ≤ c2 ^ 2 * (c2 * c6) := by gcongr
      _ = c2 ^ 3 * c6 := by ring
  have h2 : c2 ^ 3 * c6 ≤ c6 * c6 := by nlinarith
  nlinarith [mul_nonneg n2 n4]

lemma sixth_bound (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hmem : MemLp (X 0) 6 μ) (hmean : ∫ ω, X 0 ω ∂μ = 0) (m : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range m, X i ω) ^ 6 ∂μ ≤ 15 * (m : ℝ) ^ 3 * ∫ ω, X 0 ω ^ 6 ∂μ := by
  have hmem' : MemLp (X 0) ((6 : ℕ) : ENNReal) μ := by exact_mod_cast hmem
  have hmem4 : MemLp (X 0) 4 μ := hmem.mono_exponent (by norm_num)
  have hA : (∫ ω, X 0 ω ^ 2 ∂μ) ^ 2 ≤ ∫ ω, X 0 ω ^ 4 ∂μ := c2_sq_le_c4 hmem' (by norm_num)
  have hB : (∫ ω, X 0 ω ^ 4 ∂μ) ^ 2 ≤ (∫ ω, X 0 ω ^ 2 ∂μ) * ∫ ω, X 0 ω ^ 6 ∂μ := by
    have := moment_cs hmem' 1 3 (by norm_num) (by norm_num)
    simpa using this
  have hC : (∫ ω, X 0 ω ^ 3 ∂μ) ^ 2 ≤ ∫ ω, X 0 ω ^ 6 ∂μ := by
    have := moment_cs hmem' 3 0 (by norm_num) (by norm_num)
    simpa using this
  have n2 : 0 ≤ ∫ ω, X 0 ω ^ 2 ∂μ := integral_nonneg fun ω => by positivity
  have n4 : 0 ≤ ∫ ω, X 0 ω ^ 4 ∂μ := integral_nonneg fun ω => by positivity
  have n6 : 0 ≤ ∫ ω, X 0 ω ^ 6 ∂μ := integral_nonneg fun ω => by positivity
  obtain ⟨hD, hE⟩ := real_ineqs _ _ _ n2 n4 n6 hA hB
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨h1, h2, h3, h4⟩ := moments_four hindep hident hmem4 hmean m
    have e6 := step_moment hindep hident hmem' m 6 le_rfl
    simp [Finset.sum_range_succ, Nat.choose, hmean] at e6
    simp only [Finset.sum_range_succ _ m]
    rw [e6, h1, h2, h3, h4]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hm1 : (0 : ℝ) ≤ m * (m - 1) := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · simp
      · have : (1 : ℝ) ≤ m := by exact_mod_cast hpos
        nlinarith
    have P1 := mul_le_mul_of_nonneg_left hE hm
    have P2 := mul_le_mul_of_nonneg_left hC hm
    have P3 := mul_le_mul_of_nonneg_left hD hm1
    have P4 := mul_nonneg hm n6
    push_cast
    nlinarith

end

end SolL12

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0) (n : ℕ) (hn : 1 ≤ n) :
    (MemLp (X 0) 4 μ →
      ∫ ω, (∑ i ∈ Finset.range n, X i ω) ^ 4 ∂μ ≤ 3 * (n : ℝ) ^ 2 * ∫ ω, X 0 ω ^ 4 ∂μ) ∧
    (MemLp (X 0) 6 μ →
      ∫ ω, (∑ i ∈ Finset.range n, X i ω) ^ 6 ∂μ ≤ 21 * (n : ℝ) ^ 3 * ∫ ω, X 0 ω ^ 6 ∂μ) := by
  constructor
  · intro h4
    obtain ⟨-, -, -, h⟩ := SolL12.moments_four hindep hident h4 hmean n
    have h4' : MemLp (X 0) ((4 : ℕ) : ENNReal) μ := by exact_mod_cast h4
    have hA := SolL12.c2_sq_le_c4 h4' le_rfl
    have n4 : 0 ≤ ∫ ω, X 0 ω ^ 4 ∂μ := integral_nonneg fun ω => by positivity
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [h]
    have := mul_le_mul_of_nonneg_left hA (by nlinarith : (0 : ℝ) ≤ 3 * n * (n - 1))
    nlinarith [mul_nonneg hn0 n4]
  · intro h6
    have := SolL12.sixth_bound hindep hident h6 hmean n
    have n6 : 0 ≤ ∫ ω, X 0 ω ^ 6 ∂μ := integral_nonneg fun ω => by positivity
    have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
    nlinarith [mul_nonneg hn0 n6]
