-- Prove2me | solution 1 for APrioriTSP.Sampling.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-28T09:11:24.884469+00:00
-- url     : https://prove2.me/submissions/592ad3c6-aa2f-4dfe-be75-2809f7bdc20d

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP

namespace Queelius.APrioriTSP

theorem geometric_tail (n : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => if n + 1 ≤ k then (k : ℝ) * q ^ (k - 1) else 0)
      (q ^ n / (1 - q) ^ 2 * (1 + n - q * n)) := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq0] using hq1
  have hne : 1 - q ≠ 0 := by linarith
  have hs := (((hasSum_geometric_of_norm_lt_one hnorm).mul_left ((n : ℝ) + 1)).add
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm)).mul_left (q ^ n)
  have hf : (fun j : ℕ => ((j : ℝ) + n + 1) * q ^ (j + n)) =
      (fun j : ℕ => q ^ n * (((n : ℝ) + 1) * q ^ j + (j : ℝ) * q ^ j)) := by
    funext j
    rw [pow_add]
    ring
  have hv : q ^ n / (1 - q) ^ 2 * (1 + n - q * n) =
      q ^ n * (((n : ℝ) + 1) * (1 - q)⁻¹ + q / (1 - q) ^ 2) := by
    field_simp
    <;> ring
  have hs' : HasSum (fun j : ℕ => ((j : ℝ) + n + 1) * q ^ (j + n))
      (q ^ n / (1 - q) ^ 2 * (1 + n - q * n)) := by
    rw [hf, hv]
    exact hs
  let f : ℕ → ℝ := fun k => if n + 1 ≤ k then (k : ℝ) * q ^ (k - 1) else 0
  have ht : HasSum (fun j : ℕ => f (j + (n + 1)))
      (q ^ n / (1 - q) ^ 2 * (1 + n - q * n)) := by
    convert hs' using 1
    ext j
    dsimp [f]
    rw [if_pos (by omega)]
    have he : j + (n + 1) - 1 = j + n := by omega
    try rw [he]
    push_cast
    ring
  have hz : ∑ i ∈ Finset.range (n + 1), f i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    dsimp [f]
    rw [if_neg (by have := Finset.mem_range.mp hi; omega)]
  have hall := (hasSum_nat_add_iff (n + 1)).mp ht
  simpa only [hz, add_zero] using hall

end Queelius.APrioriTSP

open APrioriTSP.Sampling

/-- Lemma 18 (p. 14): `Σ_{k=n+1}^∞ k q^{k−1} = q^n / (1 − q)² · (1 + n − q n)` for `n ∈ ℕ`,
`q ∈ (0, 1)`. -/
theorem prior_geometric_solution (n : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => if n + 1 ≤ k then (k : ℝ) * q ^ (k - 1) else 0)
      (q ^ n / (1 - q) ^ 2 * (1 + n - q * n)) := by
  exact Queelius.APrioriTSP.geometric_tail n q hq0 hq1


namespace Queelius.APrioriTSPTail

theorem linear_growth (B : ℕ → ℝ)
    (hB : ∀ i j, 1 ≤ i → 1 ≤ j → B (i+j) ≤ B i + B j)
    (k : ℕ) : B (k+1) ≤ (k+1 : ℕ) * B 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := hB (k+1) 1 (by omega) (by omega)
    push_cast
    push_cast at ih
    nlinarith

theorem linear_growth_pos (B : ℕ → ℝ)
    (hB : ∀ i j, 1 ≤ i → 1 ≤ j → B (i+j) ≤ B i + B j)
    (k : ℕ) (hk : 1 ≤ k) : B k ≤ (k : ℝ) * B 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact linear_growth B hB j

theorem geometric_tail_summable (B : ℕ → ℝ) (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ i j, 1 ≤ i → 1 ≤ j → B (i+j) ≤ B i + B j)
    (N : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    Summable (fun k : ℕ => if N < k then q^(k-1) * B k else 0) := by
  have hs := (Queelius.APrioriTSP.geometric_tail N q hq0 hq1).summable.mul_right (B 1)
  apply Summable.of_nonneg_of_le (f := fun k : ℕ =>
    (if N+1 ≤ k then (k : ℝ) * q^(k-1) else 0) * B 1) ?_ ?_ hs
  · intro k
    have hb := hB0 k
    split_ifs <;> positivity
  · intro k
    by_cases hk : N < k
    · simp only [if_pos hk, if_pos (by omega : N+1 ≤ k)]
      have h := mul_le_mul_of_nonneg_left (linear_growth_pos B hB k (by omega))
        (pow_nonneg hq0.le (k-1))
      nlinarith [h]
    · simp [hk, show ¬ N+1 ≤ k by omega]

theorem geometric_tail_bound (B : ℕ → ℝ) (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ i j, 1 ≤ i → 1 ≤ j → B (i+j) ≤ B i + B j)
    (N : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (∑' k : ℕ, if N < k then q^(k-1) * B k else 0) ≤
      (q^N / (1-q)^2 * (1+N-q*N)) * B 1 := by
  have hs := (Queelius.APrioriTSP.geometric_tail N q hq0 hq1).mul_right (B 1)
  rw [← hs.tsum_eq]
  apply Summable.tsum_le_tsum _ (geometric_tail_summable B hB0 hB N q hq0 hq1) hs.summable
  intro k
  by_cases hk : N < k
  · simp only [if_pos hk, if_pos (by omega : N+1 ≤ k)]
    have h := mul_le_mul_of_nonneg_left (linear_growth_pos B hB k (by omega))
      (pow_nonneg hq0.le (k-1))
    nlinarith [h]
  · simp [hk, show ¬ N+1 ≤ k by omega]

theorem exp_weight (t : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    Real.exp (-((k : ℝ)-1)*t) = Real.exp (-t)^(k-1) := by
  rw [← Real.exp_nat_mul]
  congr 1
  rw [Nat.cast_sub hk]
  push_cast
  ring

theorem exponential_tail_bound (B : ℕ → ℝ) (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ i j, 1 ≤ i → 1 ≤ j → B (i+j) ≤ B i + B j)
    (N : ℕ) (t : ℝ) (ht : 0 < t) :
    Summable (fun k : ℕ => if N < k then Real.exp (-((k : ℝ)-1)*t) * B k else 0) ∧
    (∑' k : ℕ, if N < k then Real.exp (-((k : ℝ)-1)*t) * B k else 0) ≤
      ((Real.exp (-t))^N / (1-Real.exp (-t))^2 *
        (1+N-Real.exp (-t)*N)) * B 1 := by
  have hq0 := Real.exp_pos (-t)
  have hq1 : Real.exp (-t) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have he : (fun k : ℕ => if N < k then Real.exp (-((k : ℝ)-1)*t) * B k else 0) =
      (fun k : ℕ => if N < k then Real.exp (-t)^(k-1) * B k else 0) := by
    funext k
    split_ifs with hk
    · rw [exp_weight t k (by omega)]
    · rfl
  rw [he]
  exact ⟨geometric_tail_summable B hB0 hB N _ hq0 hq1,
    geometric_tail_bound B hB0 hB N _ hq0 hq1⟩

theorem additive_tail_control :
    (∑' k : ℕ, if 1 < k then (1/2 : ℝ)^(k-1) * (k : ℝ) else 0) = 3 := by
  have h := (Queelius.APrioriTSP.geometric_tail 1 (1/2) (by norm_num) (by norm_num)).tsum_eq
  convert h using 1
  · congr 1
    funext k
    split_ifs <;> try omega
    all_goals ring
  · norm_num

theorem origin_unrestricted_control :
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j →
      (if i+j=0 then (100 : ℝ) else 0) ≤
        (if i=0 then (100 : ℝ) else 0) + (if j=0 then (100 : ℝ) else 0)) ∧
    ¬ ((if (0 : ℕ)=0 then (100 : ℝ) else 0) ≤ (0 : ℝ)*0) := by
  constructor
  · intro i j hi hj
    simp [show i+j≠0 by omega, show i≠0 by omega, show j≠0 by omega]
  · norm_num

theorem delta2_tail_bound (α σ β : ℝ) (hα : 0 ≤ α) (hσ : 0 < σ) (hβ : 0 < β)
    (B : ℕ → ℝ) (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ i j, 1 ≤ i → 1 ≤ j → B (i+j) ≤ B i + B j) (N : ℕ) :
    (α + 2*β / (Real.exp (N*σ*β) * (Real.exp (σ*β)-1))) *
      (∑' k : ℕ, if N < k then Real.exp (-((k : ℝ)-1)*σ*β) * B k else 0) ≤
        APrioriTSP.Sampling.delta2 α β σ N * B 1 := by
  have ht := mul_pos hσ hβ
  have he : 0 < Real.exp (σ*β)-1 := by
    have : 1 < Real.exp (σ*β) := by rw [Real.one_lt_exp_iff]; exact ht
    linarith
  have hc : 0 ≤ α + 2*β / (Real.exp (N*σ*β) * (Real.exp (σ*β)-1)) := by positivity
  have h := mul_le_mul_of_nonneg_left (exponential_tail_bound B hB0 hB N (σ*β) ht).2 hc
  have hp : Real.exp (-(σ*β))^N = Real.exp (-(N*σ*β)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simpa only [APrioriTSP.Sampling.delta2, hp, mul_assoc] using h

end Queelius.APrioriTSPTail

namespace Queelius.APrioriTSPDouble

lemma cut_summable (W : ℕ → ℝ) (hW : ∀ i, 0 ≤ W i) (hs : Summable W)
    (p : ℕ → Prop) [DecidablePred p] : Summable (fun i => if p i then W i else 0) := by
  apply Summable.of_nonneg_of_le (f := W) ?_ ?_ hs
  · intro i; split_ifs; exact hW i; rfl
  · intro i; split_ifs; rfl; exact hW i

lemma partition_bound (F : ℕ → ℕ → ℝ) (W V : ℕ → ℝ)
    (hF : ∀ i j, F i j ≤ W i * V j) (hSym : ∀ i j, F i j = F j i)
    (N i j : ℕ) :
    (if N < max i j then F i j else 0) ≤
      (if i ≤ N then W i else 0) * (if N < j then V j else 0) +
      (if j ≤ N then W j else 0) * (if N < i then V i else 0) +
      (if N < i then W i else 0) * (if N < j then V j else 0) := by
  by_cases hi : i ≤ N <;> by_cases hj : j ≤ N
  · simp [hi,hj,show ¬ N < i by omega,show ¬ N < j by omega,show ¬ N < max i j by omega]
  · simpa [hi,hj,show ¬ N < i by omega,show N < j by omega,show N < max i j by omega] using hF i j
  · simpa [hi,hj,show N < i by omega,show ¬ N < j by omega,show N < max i j by omega,hSym i j] using hF j i
  · simpa [hi,hj,show N < i by omega,show N < j by omega,show N < max i j by omega] using hF i j

/-- A symmetric nonnegative kernel dominated by a summable product admits a three-region tail bound. -/
theorem symmetric_double_tail (F : ℕ → ℕ → ℝ) (W V : ℕ → ℝ)
    (hW : ∀ i, 0 ≤ W i) (hV : ∀ i, 0 ≤ V i) (hsW : Summable W) (hsV : Summable V)
    (hF0 : ∀ i j, 0 ≤ F i j) (hF : ∀ i j, F i j ≤ W i * V j)
    (hSym : ∀ i j, F i j = F j i) (N : ℕ) :
    Summable (fun q : ℕ × ℕ => if N < max q.1 q.2 then F q.1 q.2 else 0) ∧
    (∑' q : ℕ × ℕ, if N < max q.1 q.2 then F q.1 q.2 else 0) ≤
      2 * (∑' i : ℕ, if i ≤ N then W i else 0) * (∑' j : ℕ, if N < j then V j else 0) +
      (∑' i : ℕ, if N < i then W i else 0) * (∑' j : ℕ, if N < j then V j else 0) := by
  let L := fun i => if i ≤ N then W i else 0
  let U := fun i => if N < i then W i else 0
  let R := fun i => if N < i then V i else 0
  have hL : Summable L := cut_summable W hW hsW _
  have hU : Summable U := cut_summable W hW hsW _
  have hR : Summable R := cut_summable V hV hsV _
  have hnL : ∀ i, 0 ≤ L i := by intro i; dsimp [L]; split_ifs; exact hW i; rfl
  have hnU : ∀ i, 0 ≤ U i := by intro i; dsimp [U]; split_ifs; exact hW i; rfl
  have hnR : ∀ i, 0 ≤ R i := by intro i; dsimp [R]; split_ifs; exact hV i; rfl
  have hA := hL.mul_of_nonneg hR hnL hnR
  have hB : Summable (fun q : ℕ × ℕ => L q.2 * R q.1) := hA.prod_symm
  have hC := hU.mul_of_nonneg hR hnU hnR
  have hD := (hA.add hB).add hC
  have hbound : ∀ q : ℕ × ℕ, (if N < max q.1 q.2 then F q.1 q.2 else 0) ≤
      (L q.1 * R q.2 + L q.2 * R q.1) + U q.1 * R q.2 := by
    intro q
    exact partition_bound F W V hF hSym N q.1 q.2
  have hs : Summable (fun q : ℕ × ℕ => if N < max q.1 q.2 then F q.1 q.2 else 0) := by
    apply Summable.of_nonneg_of_le (f := fun q : ℕ × ℕ =>
      (L q.1 * R q.2 + L q.2 * R q.1) + U q.1 * R q.2) ?_ hbound hD
    intro q; split_ifs; exact hF0 _ _; rfl
  refine ⟨hs, ?_⟩
  have hi := hs.tsum_le_tsum hbound hD
  rw [(hA.add hB).tsum_add hC,hA.tsum_add hB] at hi
  have hswap : (∑' q : ℕ × ℕ, L q.2 * R q.1) = ∑' q : ℕ × ℕ, L q.1 * R q.2 :=
    (Equiv.prodComm ℕ ℕ).tsum_eq (fun q : ℕ × ℕ => L q.1 * R q.2)
  rw [hswap,← hL.tsum_mul_tsum hR hA,← hU.tsum_mul_tsum hR hC] at hi
  dsimp [L,U,R] at hi
  nlinarith [hi]

lemma geometric_tail_value (N : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => if N < k then q^k else 0) (q^(N+1)*(1-q)⁻¹) := by
  have hn : ‖q‖ < 1 := by simpa [Real.norm_eq_abs,abs_of_pos hq0] using hq1
  have h := (hasSum_geometric_of_norm_lt_one hn).mul_left (q^(N+1))
  let f := fun k : ℕ => if N < k then q^k else 0
  have ht : HasSum (fun k : ℕ => f (k+(N+1))) (q^(N+1)*(1-q)⁻¹) := by
    have heq : (fun k : ℕ => f (k+(N+1))) = (fun k : ℕ => q^(N+1)*q^k) := by
      funext k
      simp only [f,if_pos (by omega : N < k+(N+1)),pow_add]
      ring
    rw [heq]
    exact h
  have hz : ∑ k ∈ Finset.range (N+1), f k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_range.mp hk
    simp [f,show ¬ N < k by omega]
  simpa only [hz,add_zero] using (hasSum_nat_add_iff (N+1)).mp ht

lemma exp_geometric (t : ℝ) (k : ℕ) : Real.exp (-(k : ℝ)*t) = Real.exp (-t)^k := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

lemma exp_tail_value (N : ℕ) (t : ℝ) (ht : 0 < t) :
    HasSum (fun k : ℕ => if N < k then Real.exp (-(k : ℝ)*t) else 0)
      (1 / (Real.exp (N*t)*(Real.exp t-1))) := by
  have hq0 := Real.exp_pos (-t)
  have hq1 : Real.exp (-t) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have h := geometric_tail_value N (Real.exp (-t)) hq0 hq1
  have hp : Real.exp (-t)^N = (Real.exp (N*t))⁻¹ := by
    rw [← Real.exp_nat_mul,← Real.exp_neg]
    congr 1
    ring
  have he : Real.exp t-1 ≠ 0 := by
    have : 1 < Real.exp t := by rw [Real.one_lt_exp_iff]; exact ht
    linarith
  have hv : Real.exp (-t)^(N+1)*(1-Real.exp (-t))⁻¹ =
      1 / (Real.exp (N*t)*(Real.exp t-1)) := by
    rw [pow_succ,hp,Real.exp_neg]
    field_simp
    <;> ring
  rw [hv] at h
  convert h using 1
  funext k
  split_ifs <;> first | rw [exp_geometric] | rfl

lemma full_weight_summable (B : ℕ → ℝ) (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ i j, 1 ≤ i → 1 ≤ j → B (i+j) ≤ B i+B j) (t : ℝ) (ht : 0 < t) :
    Summable (fun k : ℕ => Real.exp (-((k : ℝ)-1)*t)*B k) := by
  have hs := (Queelius.APrioriTSPTail.exponential_tail_bound B hB0 hB 0 t ht).1
  have hz := (hasSum_ite_eq (0 : ℕ) (Real.exp t * B 0)).summable
  convert hs.add hz using 1
  funext k
  by_cases hk : k=0
  · simp [hk]
  · simp [hk,show 0<k by omega]

lemma low_sum (W : ℕ → ℝ) (N : ℕ) :
    (∑' k : ℕ, if k ≤ N then W k else 0) = ∑ k ∈ Finset.range (N+1), W k := by
  calc
    _ = ∑ k ∈ Finset.range (N+1), (if k ≤ N then W k else 0) := by
      apply tsum_eq_sum
      intro k hk
      have : ¬ k < N+1 := by simpa using hk
      simp [show ¬ k ≤ N by omega]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_range] at hk
      simp [show k ≤ N by omega]

theorem weighted_double_tail (B : ℕ → ℝ) (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ i j, 1 ≤ i → 1 ≤ j → B (i+j) ≤ B i+B j) (N : ℕ) (t : ℝ) (ht : 0 < t) :
    (∑' z : ℕ × ℕ, if N < max z.1 z.2 then
      Real.exp (-(((z.1 : ℝ)+z.2-1)*t))*min (B z.1) (B z.2) else 0) ≤
      2*(∑ k ∈ Finset.range (N+1), Real.exp (-((k : ℝ)-1)*t)*B k)*
        (1/(Real.exp (N*t)*(Real.exp t-1))) +
      (∑' k : ℕ, if N < k then Real.exp (-((k : ℝ)-1)*t)*B k else 0)*
        (1/(Real.exp (N*t)*(Real.exp t-1))) := by
  let F := fun i j : ℕ => Real.exp (-(((i : ℝ)+j-1)*t))*min (B i) (B j)
  let W := fun i : ℕ => Real.exp (-((i : ℝ)-1)*t)*B i
  let V := fun i : ℕ => Real.exp (-(i : ℝ)*t)
  have hsW : Summable W := full_weight_summable B hB0 hB t ht
  have hq0 := Real.exp_pos (-t)
  have hq1 : Real.exp (-t) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hn : ‖Real.exp (-t)‖ < 1 := by simpa [Real.norm_eq_abs,abs_of_pos hq0] using hq1
  have hsV : Summable V := (hasSum_geometric_of_norm_lt_one hn).summable.congr
    (fun k => (exp_geometric t k).symm)
  have hF0 : ∀ i j, 0 ≤ F i j := by
    intro i j
    exact mul_nonneg (Real.exp_pos _).le (le_min (hB0 i) (hB0 j))
  have hdom : ∀ i j, F i j ≤ W i * V j := by
    intro i j
    have he : Real.exp (-(((i : ℝ)+j-1)*t)) =
        Real.exp (-((i : ℝ)-1)*t)*Real.exp (-(j : ℝ)*t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      F i j ≤ Real.exp (-(((i : ℝ)+j-1)*t))*B i :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.exp_pos _).le
      _ = W i * V j := by dsimp [W,V]; rw [he]; ring
  have hsym : ∀ i j, F i j = F j i := by
    intro i j
    dsimp [F]
    rw [add_comm (i : ℝ) (j : ℝ),min_comm]
  have hh := (symmetric_double_tail F W V
    (fun i => mul_nonneg (Real.exp_pos _).le (hB0 i)) (fun i => (Real.exp_pos _).le)
    hsW hsV hF0 hdom hsym N).2
  rw [low_sum W N] at hh
  dsimp only [F,W,V] at hh
  rw [(exp_tail_value N t ht).tsum_eq] at hh
  exact hh

end Queelius.APrioriTSPDouble


/-- Lemma 14 (p. 12): the error term beyond bucket `N` is bounded by
`δ₁ Σ_{k=0}^N e^{−(k−1)σβ} B_k + δ₂ B_1`. -/
theorem solution (α σ β : ℝ) (hα : 0 ≤ α) (hσ : 0 < σ) (hβ : 0 < β) (N : ℕ)
    (B : ℕ → ℝ) (hB0 : ∀ i, 0 ≤ B i)
    (hB : ∀ i j, 1 ≤ i → 1 ≤ j → B (i + j) ≤ B i + B j) :
    α * ∑' k : ℕ, (if N < k then Real.exp (-(((k : ℝ) - 1) * σ * β)) * B k else 0) +
        2 * β * ∑' q : ℕ × ℕ, (if N < max q.1 q.2 then
          Real.exp (-(((q.1 : ℝ) + q.2 - 1) * σ * β)) * min (B q.1) (B q.2) else 0) ≤
      delta1 β σ N * ∑ k ∈ Finset.range (N + 1), Real.exp (-(((k : ℝ) - 1) * σ * β)) * B k +
        delta2 α β σ N * B 1 := by
  let L : ℝ := ∑ k ∈ Finset.range (N+1), Real.exp (-(((k : ℝ)-1)*σ*β))*B k
  let U : ℝ := ∑' k : ℕ, if N < k then Real.exp (-(((k : ℝ)-1)*σ*β))*B k else 0
  let D : ℝ := ∑' z : ℕ × ℕ, if N < max z.1 z.2 then
    Real.exp (-(((z.1 : ℝ)+z.2-1)*σ*β))*min (B z.1) (B z.2) else 0
  let R : ℝ := 1 / (Real.exp (N*σ*β)*(Real.exp (σ*β)-1))
  have hd : D ≤ 2*L*R + U*R := by
    simpa only [D,L,U,R,mul_assoc,neg_mul] using
      Queelius.APrioriTSPDouble.weighted_double_tail B hB0 hB N (σ*β) (mul_pos hσ hβ)
  have hb : (α+2*β*R)*U ≤ delta2 α β σ N * B 1 := by
    simpa only [U,R,div_eq_mul_inv,one_mul,mul_assoc,neg_mul] using
      Queelius.APrioriTSPTail.delta2_tail_bound α σ β hα hσ hβ B hB0 hB N
  have he : delta1 β σ N = 4*β*R := by
    dsimp [delta1,R]
    ring
  change α*U + 2*β*D ≤ delta1 β σ N * L + delta2 α β σ N * B 1
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2*β)
  nlinarith [hm,hb]



namespace Queelius.APrioriTSPDouble
/-- The origin uses real subtraction: its weight is exp(t), not the natural-power value1. -/
theorem zero_index_weight (t : ℝ) : Real.exp (-(((0 : ℝ)-1)*t)) = Real.exp t := by
  congr 1
  ring
end Queelius.APrioriTSPDouble
