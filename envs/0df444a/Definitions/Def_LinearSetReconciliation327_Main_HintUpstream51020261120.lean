-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintUpstream51020261120
-- name    : LinearSetReconciliation327_Main_HintUpstream51020261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T08:42:48.718669+00:00
-- url     : https://prove2.me/theorems/3cd264c0-7684-4dbe-837f-e364c3a5c1f9
-- title:
--   LinearSetReconciliation327 — HintUpstream510 (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintUpstream51020261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch

set_option autoImplicit false

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main.HintUpstream510

set_option maxHeartbeats 2000000

/-!
## Lemma 5.10: size and depth of the recursion

We prove the termination of the `HintSketch` recursion together with the stated bounds.

The proof follows the paper: at a recursive node the total density `∑_s Y_s / Y` of the children is
at most `ρ/4`, where `ρ = Y/N`, and every recursive node has density `ρ > 1/(2 log¹³ n)`.  Hence the
density contracts by `4` per level (so the depth is `O(log log n)`) and the total density mass, hence
the number of recursive nodes, is `O(log¹³ n)`.  Finally every node has at most
`ℓ = O(A log¹⁴ n)` children, which yields `O(A log²⁷ n)` nodes.

The only probabilistic input is the first moment of the profile `Q_s`, which we re-derive here
(the same computation as in the proof of Lemma 5.8).
-/

/-! ### Elementary analytic toolkit -/

/-- All unmarked logarithms are to base two. -/
lemma lg_eq_log_div (x : ℝ) : lg x = Real.log x / Real.log 2 := rfl

lemma lg_two : lg 2 = 1 := by
  rw [lg_eq_log_div, div_self (ne_of_gt (by linarith [Real.log_two_gt_d9] : (0 : ℝ) < Real.log 2))]

lemma lg_exp_one : lg (Real.exp 1) = 1 / Real.log 2 := by
  rw [lg_eq_log_div, Real.log_exp]

lemma one_le_lg_exp : (1 : ℝ) ≤ lg (Real.exp 1) := by
  rw [lg_exp_one]
  have h0 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  rw [le_div_iff₀ h0]
  linarith

lemma lg_exp_one_le_two : lg (Real.exp 1) ≤ 2 := by
  rw [lg_exp_one]
  have h0 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [div_le_iff₀ h0]
  linarith [Real.log_two_gt_d9]

/-- `log x / x ≤ log e` for `x ≥ 1`. -/
lemma lg_div_self_le {x : ℝ} (hx : 1 ≤ x) : lg x / x ≤ lg (Real.exp 1) := by
  have hx0 : 0 < x := by linarith
  have h0 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogx : Real.log x ≤ x := by
    have := Real.log_le_sub_one_of_pos hx0
    linarith
  have h1 : lg x / x = (Real.log x / x) / Real.log 2 := by
    rw [lg_eq_log_div]
    field_simp
  rw [h1, lg_exp_one, div_le_div_iff_of_pos_right h0, div_le_one hx0]
  exact hlogx

lemma G_nonneg (a : ℕ) (z : ℝ) : 0 ≤ G a z := by
  unfold G
  exact le_min zero_le_one (Real.rpow_nonneg (by norm_num) _)

lemma G_le_one (a : ℕ) (z : ℝ) : G a z ≤ 1 := min_le_left _ _

lemma G_le_rpow (a : ℕ) (z : ℝ) : G a z ≤ (2 : ℝ) ^ (z - (a : ℝ)) := min_le_right _ _

/-- `2^{-r} = (1/2)^r` for natural `r`. -/
lemma two_rpow_neg_nat (r : ℕ) : (2 : ℝ) ^ (-(r : ℝ)) = (1 / 2 : ℝ) ^ r := by
  have h1 : (2 : ℝ) ^ (-(r : ℝ)) = ((2 : ℝ) ^ (-1 : ℝ)) ^ (r : ℝ) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [h1, Real.rpow_neg_one, Real.rpow_natCast]
  norm_num

lemma two_rpow_neg_le_one (s : ℕ) : (2 : ℝ) ^ (-(s : ℝ)) ≤ 1 := by
  rw [two_rpow_neg_nat]
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- Tail estimate: if `z < k + 1` and `a ≥ k + 1` then `G a z ≤ (1/2)^{a-k-1}`. -/
lemma G_tail_le {z : ℝ} {k a : ℕ} (hz : z < (k : ℝ) + 1) (ha : k + 1 ≤ a) :
    G a z ≤ (1 / 2 : ℝ) ^ (a - (k + 1)) := by
  have hcast : ((a - (k + 1) : ℕ) : ℝ) = (a : ℝ) - ((k : ℝ) + 1) := by
    have h := Nat.sub_add_cancel ha
    have h' := congrArg (fun x : ℕ => (x : ℝ)) h
    push_cast at h'
    linarith
  have h2 : z - (a : ℝ) ≤ -(((a - (k + 1) : ℕ)) : ℝ) := by
    linarith
  calc G a z ≤ (2 : ℝ) ^ (z - (a : ℝ)) := G_le_rpow a z
    _ ≤ (2 : ℝ) ^ (-(((a - (k + 1) : ℕ)) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
    _ = (1 / 2 : ℝ) ^ (a - (k + 1)) := two_rpow_neg_nat _

lemma tsum_half_pow : ∑' r : ℕ, (1 / 2 : ℝ) ^ r = 2 := by
  rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
  norm_num

lemma summable_half_pow : Summable fun r : ℕ => (1 / 2 : ℝ) ^ r :=
  summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)

/-- Shifting a summable nonnegative sequence down by `k` only decreases its finite sums. -/
lemma sum_shift_le_tsum {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) (hsum : Summable f)
    {s : Finset ℕ} {k : ℕ} (hk : ∀ a ∈ s, k ≤ a) :
    ∑ a ∈ s, f (a - k) ≤ ∑' i, f i := by
  have hinj : Set.InjOn (fun a : ℕ => a - k) (s : Set ℕ) := by
    intro a ha b hb hab
    have h1 := hk a ha
    have h2 := hk b hb
    have hab' : a - k = b - k := hab
    omega
  rw [← Finset.sum_image hinj]
  exact hsum.sum_le_tsum _ (fun i _ => hf i)

lemma head_card_le (n k : ℕ) :
    ((range n).filter (fun a => a ≤ k)).card ≤ k + 1 := by
  have h : (range n).filter (fun a => a ≤ k) ⊆ range (k + 1) := by
    intro a ha
    simp only [mem_filter, mem_range] at ha
    simp only [mem_range]
    omega
  calc ((range n).filter (fun a => a ≤ k)).card ≤ (range (k + 1)).card := card_le_card h
    _ = k + 1 := by simp

/-- Head of the first sum: the first `k+1` terms contribute at most `k+1`. -/
lemma sum_G_head_le (z : ℝ) (k n : ℕ) :
    ∑ a ∈ (range n).filter (fun a => a ≤ k), G a z ≤ (k : ℝ) + 1 := by
  classical
  have h1 : ∑ a ∈ (range n).filter (fun a => a ≤ k), G a z
      ≤ ∑ a ∈ (range n).filter (fun a => a ≤ k), (1 : ℝ) :=
    sum_le_sum (fun a _ => G_le_one a z)
  rw [sum_const, nsmul_eq_mul, mul_one] at h1
  have h2 : ((((range n).filter (fun a => a ≤ k)).card : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by
    have hc : (((range n).filter (fun a => a ≤ k)).card : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast head_card_le n k
    push_cast at hc
    linarith
  linarith

/-- Tail of the first sum: geometric decay contributes at most `2`. -/
lemma sum_G_tail_le (z : ℝ) (k n : ℕ) (hkz' : z < (k : ℝ) + 1) :
    ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), G a z ≤ 2 := by
  classical
  have h1 : ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), G a z
      ≤ ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), (1 / 2 : ℝ) ^ (a - (k + 1)) := by
    refine sum_le_sum (fun a ha => ?_)
    simp only [mem_filter, mem_range] at ha
    exact G_tail_le hkz' (by omega)
  have h2 : ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), (1 / 2 : ℝ) ^ (a - (k + 1)) ≤ 2 := by
    have h := sum_shift_le_tsum (f := fun r : ℕ => (1 / 2 : ℝ) ^ r) (fun i => by positivity)
      summable_half_pow (s := (range n).filter (fun a => ¬ a ≤ k)) (k := k + 1) (fun a ha => by
        simp only [mem_filter, mem_range] at ha
        omega)
    rw [tsum_half_pow] at h
    exact h
  linarith

/-- `∑_{a<n} G_a(z) ≤ z + 32`. -/
lemma sum_G_le (z : ℝ) (hz : 0 ≤ z) (n : ℕ) :
    ∑ a ∈ range n, G a z ≤ z + 32 := by
  classical
  set k := Nat.floor z with hk
  have hkz : (k : ℝ) ≤ z := Nat.floor_le hz
  have hkz' : z < (k : ℝ) + 1 := Nat.lt_floor_add_one z
  have hsplit : ∑ a ∈ range n, G a z
      = ∑ a ∈ (range n).filter (fun a => a ≤ k), G a z
        + ∑ a ∈ (range n).filter (fun a => ¬ a ≤ k), G a z :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit]
  have hhead := sum_G_head_le z k n
  have htail := sum_G_tail_le z k n hkz'
  linarith

/-! ### Expectation over the uniform law -/

lemma expU_mono {α : Type} [Fintype α] (hα : 0 < Fintype.card α) {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : expU f ≤ expU g := by
  unfold expU
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

lemma expU_nonneg {α : Type} [Fintype α] (hα : 0 < Fintype.card α) {f : α → ℝ}
    (h : ∀ a, 0 ≤ f a) : 0 ≤ expU f := by
  unfold expU
  exact div_nonneg (Finset.sum_nonneg (fun a _ => h a)) (by positivity)

lemma expU_const {α : Type} [Fintype α] (hα : 0 < Fintype.card α) (r : ℝ) :
    expU (fun _ : α => r) = r := by
  unfold expU
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card α : ℝ) ≠ 0 := by positivity
  field_simp

lemma expU_finset_sum {α ι : Type} [Fintype α] (hα : 0 < Fintype.card α)
    (s : Finset ι) (f : α → ι → ℝ) :
    expU (fun a => ∑ i ∈ s, f a i) = ∑ i ∈ s, expU (fun a => f a i) := by
  unfold expU
  simp only [Finset.sum_div]
  rw [Finset.sum_comm]

lemma expU_mul_const {α : Type} [Fintype α] (_hα : 0 < Fintype.card α) (f : α → ℝ) (r : ℝ) :
    expU (fun a => r * f a) = r * expU f := by
  unfold expU
  rw [← Finset.mul_sum]
  field_simp

/-! ### Counting lemmas for rows -/

/-- The size of row `j` is bounded by `⌈N/m⌉`. -/
lemma rowLen_le_ceil {N m j : ℕ} (hm : 0 < m) : rowLen N m j ≤ ⌈(N : ℝ) / (m : ℝ)⌉₊ := by
  rw [rowLen]
  have hmaps : Set.MapsTo (fun p : ℕ => p / m)
      ↑((range N).filter (fun p => p % m = j)) ↑(range ⌈(N : ℝ) / (m : ℝ)⌉₊) := by
    intro p hp
    simp only [mem_coe, mem_filter, mem_range] at hp ⊢
    obtain ⟨hpN, -⟩ := hp
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hdiv : ((p / m : ℕ) : ℝ) ≤ (p : ℝ) / (m : ℝ) := Nat.cast_div_le
    have hlt : (p : ℝ) / (m : ℝ) < (N : ℝ) / (m : ℝ) := by
      rw [div_lt_div_iff_of_pos_right hmR]
      exact_mod_cast hpN
    have h2 : ((p / m : ℕ) : ℝ) < (N : ℝ) / (m : ℝ) := lt_of_le_of_lt hdiv hlt
    have h3 : ¬ (⌈(N : ℝ) / (m : ℝ)⌉₊ ≤ p / m) := by
      rw [Nat.ceil_le]
      push_cast
      linarith
    omega
  have hinj : Set.InjOn (fun p : ℕ => p / m) ↑((range N).filter (fun p => p % m = j)) := by
    intro p hp q hq hpq
    simp only [mem_coe, mem_filter, mem_range] at hp hq
    change p / m = q / m at hpq
    have hp1 := Nat.div_add_mod p m
    have hq1 := Nat.div_add_mod q m
    rw [hpq] at hp1
    rw [hq.2] at hq1
    omega
  simpa using Finset.card_le_card_of_injOn _ hmaps hinj

/-- The size of row `j` is at most `2N/m`. -/
lemma rowLen_le_two {N m j : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (rowLen N m j : ℝ) ≤ 2 * (N : ℝ) / (m : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h1 : (rowLen N m j : ℝ) ≤ (⌈(N : ℝ) / (m : ℝ)⌉₊ : ℝ) := by
    exact_mod_cast rowLen_le_ceil (N := N) (m := m) (j := j) hm
  have hmN' : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
  have hx1 : (1 : ℝ) ≤ (N : ℝ) / (m : ℝ) := by
    rw [le_div_iff₀ hmR]
    linarith
  have h2 : (⌈(N : ℝ) / (m : ℝ)⌉₊ : ℝ) < (N : ℝ) / (m : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  calc (rowLen N m j : ℝ) ≤ (⌈(N : ℝ) / (m : ℝ)⌉₊ : ℝ) := h1
    _ ≤ (N : ℝ) / (m : ℝ) + 1 := le_of_lt h2
    _ ≤ 2 * (N : ℝ) / (m : ℝ) := by
        rw [show 2 * (N : ℝ) / (m : ℝ) = (N : ℝ) / (m : ℝ) + (N : ℝ) / (m : ℝ) by ring]
        linarith

/-- The card of the `π`-fiber over row `j` is the row length. -/
lemma card_fiber_eq_rowLen {N m j : ℕ} (π : Equiv.Perm (Fin N)) :
    ((univ.filter (fun p : Fin N => (π p).val % m = j)).card) = rowLen N m j := by
  rw [rowLen]
  refine Finset.card_bij (fun p (_ : p ∈ univ.filter (fun p : Fin N => (π p).val % m = j)) => (π p).val)
    ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_univ, true_and, mem_range] at hp ⊢
    exact ⟨(π p).isLt, hp⟩
  · intro p _ q _ h
    exact π.injective (Fin.ext h)
  · intro q hq
    simp only [mem_filter, mem_range] at hq
    exact ⟨π.symm ⟨q, hq.1⟩, by simp [hq.2], by simp⟩

/-- A row image has at most `rowLen` elements. -/
lemma rowImage_card_le_rowLen {N m j : ℕ} (π : Equiv.Perm (Fin N)) (S : Finset ℕ) :
    (rowImage N m π j S).card ≤ rowLen N m j := by
  classical
  unfold rowImage
  calc ((univ.filter (fun i : Fin N => i.val ∈ S ∧ (π i).val % m = j)).image
        (fun i => (π i).val / m)).card
      ≤ ((univ.filter (fun i : Fin N => i.val ∈ S ∧ (π i).val % m = j)).card) :=
        Finset.card_image_le
    _ ≤ ((univ.filter (fun i : Fin N => (π i).val % m = j)).card) :=
        Finset.card_le_card (by
          intro i
          simp only [mem_filter, mem_univ, true_and]
          tauto)
    _ = rowLen N m j := card_fiber_eq_rowLen π

/-- `sigma jCard Nj r ≤ Nj`. -/
lemma sigma_le {jCard Nj r : ℕ} (h : jCard ≤ Nj) : HintParams.sigma jCard Nj r ≤ Nj := by
  unfold HintParams.sigma
  rw [Nat.ceil_le]
  have hsum_le : (∑ h ∈ range (r + 1), (Nj - jCard).choose h) ≤ 2 ^ (Nj - jCard) := by
    by_cases hle : r + 1 ≤ Nj - jCard + 1
    · have hsub : range (r + 1) ⊆ range (Nj - jCard + 1) := by
        intro x hx
        simp only [mem_range] at hx ⊢
        omega
      have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (f := fun x => (Nj - jCard).choose x) (fun i _ _ => Nat.zero_le _)
      rwa [Nat.sum_range_choose] at h2
    · have hsub : range (Nj - jCard + 1) ⊆ range (r + 1) := by
        intro x hx
        simp only [mem_range] at hx ⊢
        omega
      have hzero : ∑ h ∈ range (r + 1), (Nj - jCard).choose h
          = ∑ h ∈ range (Nj - jCard + 1), (Nj - jCard).choose h := by
        refine (Finset.sum_subset hsub ?_).symm
        intro x hx1 hx2
        simp only [mem_range] at hx1 hx2
        exact Nat.choose_eq_zero_of_lt (by omega)
      rw [hzero, Nat.sum_range_choose]
  have hmain : (2 ^ jCard * ∑ h ∈ range (r + 1), (Nj - jCard).choose h : ℕ) ≤ 2 ^ Nj := by
    calc 2 ^ jCard * (∑ h ∈ range (r + 1), (Nj - jCard).choose h)
        ≤ 2 ^ jCard * 2 ^ (Nj - jCard) := Nat.mul_le_mul_left _ hsum_le
      _ = 2 ^ (jCard + (Nj - jCard)) := (Nat.pow_add _ _ _).symm
      _ = 2 ^ Nj := by rw [Nat.add_sub_cancel' h]
  have hpos : (0 : ℝ) < ((2 ^ jCard * ∑ h ∈ range (r + 1), (Nj - jCard).choose h : ℕ) : ℝ) := by
    have h2 : 0 < (2 ^ jCard * ∑ h ∈ range (r + 1), (Nj - jCard).choose h : ℕ) := by
      have h3 : 0 < ∑ h ∈ range (r + 1), (Nj - jCard).choose h := by
        apply Finset.sum_pos'
        · intro x _; exact Nat.zero_le _
        · refine ⟨0, by simp, ?_⟩
          simp
      exact Nat.mul_pos (Nat.pow_pos (by norm_num)) h3
    exact_mod_cast h2
  have hmainR : ((2 ^ jCard * ∑ h ∈ range (r + 1), (Nj - jCard).choose h : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ ((Nj : ℕ) : ℝ) := by
    calc ((2 ^ jCard * ∑ h ∈ range (r + 1), (Nj - jCard).choose h : ℕ) : ℝ)
        ≤ ((2 ^ Nj : ℕ) : ℝ) := by exact_mod_cast hmain
      _ = (2 : ℝ) ^ Nj := by rw [Nat.cast_pow]; norm_num
      _ = (2 : ℝ) ^ ((Nj : ℕ) : ℝ) := by rw [Real.rpow_natCast]
  have hlg : lg (((2 ^ jCard * ∑ h ∈ range (r + 1), (Nj - jCard).choose h : ℕ) : ℝ))
      ≤ (Nj : ℝ) := by
    calc lg (((2 ^ jCard * ∑ h ∈ range (r + 1), (Nj - jCard).choose h : ℕ) : ℝ))
        ≤ lg ((2 : ℝ) ^ ((Nj : ℕ) : ℝ)) := Real.logb_le_logb_of_le (by norm_num) hpos hmainR
      _ = (Nj : ℝ) := by
            simp only [lg]
            rw [Real.logb_rpow (by norm_num) (by norm_num : (2 : ℝ) ≠ 1)]
  simpa using hlg

/-- `sigmaStar` is at most the row length. -/
lemma sigmaStar_le_rowLen (P : HintParams) {N X Y j : ℕ} (π : Equiv.Perm (Fin N)) :
    (P.sigmaStar N X Y π j : ℝ) ≤ (rowLen N (P.rows X Y) j : ℝ) := by
  classical
  have h := sigma_le (jCard := (rowImage N (P.rows X Y) π j (HintParams.refHintLabels N X Y)).card)
    (Nj := rowLen N (P.rows X Y) j) (r := (rowImage N (P.rows X Y) π j (HintParams.refOutLabels N X Y)).card)
    (rowImage_card_le_rowLen π _)
  unfold HintParams.sigmaStar
  dsimp only
  exact_mod_cast h

/-! ### The profile `Q` and its first moment -/

/-- The pointwise profile whose expectation is `Q_s`. -/
def nodeProfile (P : HintParams) (N X Y : ℕ) (π : Equiv.Perm (Fin N)) (s : ℕ) : ℝ :=
  ∑ j ∈ range (P.rows X Y), G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))

lemma Q_eq_expU (P : HintParams) (N X Y s : ℕ) :
    P.Q N X Y s = expU (fun π => nodeProfile P N X Y π s) := rfl

/-- Splitting a summand into a term plus a constant. -/
lemma sum_add_const (Y : ℕ) (a : ℕ → ℝ) (c : ℝ) :
    ∑ j ∈ range Y, (a j + c) = (∑ j ∈ range Y, a j) + (Y : ℝ) * c := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma Q_nonneg (P : HintParams) {N X Y : ℕ} (hN : 1 ≤ N) (s : ℕ) : 0 ≤ P.Q N X Y s := by
  rw [Q_eq_expU]
  refine expU_nonneg ?_ (fun π => ?_)
  · rw [Fintype.card_perm, Fintype.card_fin]; exact Nat.factorial_pos N
  · exact Finset.sum_nonneg (fun j _ => G_nonneg _ _)

lemma Q_le_Y (P : HintParams) {N X Y : ℕ} (hN : 1 ≤ N) (hrows : P.rows X Y = Y) (s : ℕ) :
    P.Q N X Y s ≤ (Y : ℝ) := by
  rw [Q_eq_expU]
  have hcard : 0 < Fintype.card (Equiv.Perm (Fin N)) := by
    rw [Fintype.card_perm, Fintype.card_fin]; exact Nat.factorial_pos N
  calc expU (fun π => nodeProfile P N X Y π s)
      ≤ expU (fun _ : Equiv.Perm (Fin N) => (Y : ℝ)) := by
        refine expU_mono hcard (fun π => ?_)
        simp only [nodeProfile]
        rw [hrows]
        calc ∑ j ∈ range Y, G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))
            ≤ ∑ j ∈ range Y, (1 : ℝ) := Finset.sum_le_sum (fun j _ => G_le_one _ _)
          _ = (Y : ℝ) := by simp
    _ = (Y : ℝ) := expU_const hcard _

/-- First moment of the profile: `∑_s Q_s ≲ Y (N/Y + c)`. -/
lemma Q_sum_le (P : HintParams) {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    (hrows : P.rows X Y = Y) (hY : 1 ≤ Y) :
    ∑ s ∈ range (P.ell N X Y), P.Q N X Y s
      ≤ (Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32) := by
  classical
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs
  have hYposR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
  have hcard : 0 < Fintype.card (Equiv.Perm (Fin N)) := by
    rw [Fintype.card_perm, Fintype.card_fin]
    exact Nat.factorial_pos N
  have hσle : ∀ (π : Equiv.Perm (Fin N)) (j : ℕ),
      (P.sigmaStar N X Y π j : ℝ) ≤ 2 * (N : ℝ) / (Y : ℝ) := by
    intro π j
    have h1 := sigmaStar_le_rowLen (P := P) (N := N) (X := X) (Y := Y) (j := j) π
    have h2 : (rowLen N (P.rows X Y) j : ℝ) ≤ 2 * (N : ℝ) / (Y : ℝ) := by
      rw [hrows]
      exact rowLen_le_two (by omega) hYN
    linarith
  have hexp : ∑ s ∈ range (P.ell N X Y), P.Q N X Y s
      = expU (fun π : Equiv.Perm (Fin N) =>
          ∑ s ∈ range (P.ell N X Y), nodeProfile P N X Y π s) := by
    rw [expU_finset_sum hcard]
    exact Finset.sum_congr rfl (fun s _ => Q_eq_expU P N X Y s)
  rw [hexp]
  calc expU (fun π => ∑ s ∈ range (P.ell N X Y), nodeProfile P N X Y π s)
      ≤ expU (fun _ : Equiv.Perm (Fin N) =>
          (Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32)) := by
        refine expU_mono hcard (fun π => ?_)
        simp only [nodeProfile]
        rw [hrows]
        rw [Finset.sum_comm]
        have h1 : ∀ j ∈ range Y,
            ∑ s ∈ range (P.ell N X Y), G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))
            ≤ ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ)) + 32 :=
          fun j _ => sum_G_le _ (by positivity) _
        calc ∑ j ∈ range Y, ∑ s ∈ range (P.ell N X Y),
              G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))
            ≤ ∑ j ∈ range Y, (((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ)) + 32) :=
              Finset.sum_le_sum h1
          _ = (∑ j ∈ range Y, (P.sigmaStar N X Y π j : ℝ)) + (Y : ℝ) * ((P.c N X Y : ℝ) + 32) := by
              simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
                nsmul_eq_mul]
              ring
          _ ≤ (Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ)) + (Y : ℝ) * ((P.c N X Y : ℝ) + 32) := by
              have hσ : ∑ j ∈ range Y, (P.sigmaStar N X Y π j : ℝ)
                  ≤ (Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ)) := by
                calc ∑ j ∈ range Y, (P.sigmaStar N X Y π j : ℝ)
                    ≤ ∑ j ∈ range Y, (2 * (N : ℝ) / (Y : ℝ)) :=
                      Finset.sum_le_sum (fun j _ => hσle π j)
                  _ = (Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ)) := by simp
              linarith
          _ = (Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32) := by ring
    _ = (Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32) := expU_const hcard _


/-! ### The density of a node and the per-node estimates -/

/-- The density `ρ = Y/N` of a node. -/
def nodeDens (N Y : ℕ) : ℝ := (Y : ℝ) / (N : ℝ)

/-- The density floor `ε = 1/(2 log¹³ n)`; every recursive node has density `> ε`. -/
def densFloor (P : HintParams) : ℝ := (2 * P.lgn ^ 13)⁻¹

lemma nodeDens_nonneg (N Y : ℕ) : 0 ≤ nodeDens N Y := by
  unfold nodeDens; positivity

lemma nodeDens_le_one {N Y : ℕ} (hN : 1 ≤ N) (hYN : Y ≤ N) : nodeDens N Y ≤ 1 := by
  unfold nodeDens
  rw [div_le_one (by exact_mod_cast (by omega : 0 < N))]
  exact_mod_cast hYN

lemma nodeDens_pos {N Y : ℕ} (hN : 0 < N) (hY : 0 < Y) : 0 < nodeDens N Y := by
  unfold nodeDens; positivity

lemma one_le_lgn {P : HintParams} (hn : 2 ≤ P.n) : 1 ≤ P.lgn := by
  show (1 : ℝ) ≤ lg (P.n : ℝ)
  rw [← lg_two]
  exact Real.logb_le_logb_of_le (by norm_num) (by norm_num : (0 : ℝ) < 2)
    (by exact_mod_cast hn)

/-- The recursive rule forces `rows X Y = Y`, i.e. `X ≤ Y log³ n`. -/
lemma rows_eq_of_rule {P : HintParams} {N X Y : ℕ} (h : P.rule N X Y = .recursive) :
    P.rows X Y = Y := by
  unfold HintParams.rule at h
  split_ifs at h with h1 h2 h3 <;> simp_all

lemma X_le_of_rows {P : HintParams} {X Y : ℕ} (hlgn : 0 < P.lgn) (h : P.rows X Y = Y) :
    (X : ℝ) ≤ (Y : ℝ) * P.lgn ^ 3 := by
  unfold HintParams.rows at h
  have h3 : (0 : ℝ) < P.lgn ^ 3 := by positivity
  have hc : ⌈(X : ℝ) / P.lgn ^ 3⌉₊ ≤ Y := by
    have h1 : ⌈(X : ℝ) / P.lgn ^ 3⌉₊ ≤ max Y ⌈(X : ℝ) / P.lgn ^ 3⌉₊ := le_max_right _ _
    rwa [h] at h1
  have h2 : (X : ℝ) / P.lgn ^ 3 ≤ (Y : ℝ) := Nat.ceil_le.mp hc
  calc (X : ℝ) = (X : ℝ) / P.lgn ^ 3 * P.lgn ^ 3 := by field_simp
    _ ≤ (Y : ℝ) * P.lgn ^ 3 := by nlinarith

lemma D_le_N (N X Y : ℕ) : HintParams.D N X Y ≤ N := by
  unfold HintParams.D; omega

lemma D_le_sum (N X Y : ℕ) : HintParams.D N X Y ≤ X + Y := by
  unfold HintParams.D; omega

/-- The first (cheap) rule does not apply at a recursive node. -/
lemma N_lt_lgn_D {P : HintParams} {N X Y : ℕ} (hL : 1 ≤ P.lgn)
    (hrule : P.rule N X Y = .recursive) :
    (N : ℝ) < P.lgn ^ 10 * (HintParams.D N X Y : ℝ) := by
  have hnot : ¬ ((HintParams.D N X Y : ℝ) ≤ (N : ℝ) / P.lgn ^ 10) := by
    intro hc
    have hr : P.rule N X Y = .cheap := by
      unfold HintParams.rule
      rw [if_pos hc]
    rw [hrule] at hr
    exact absurd hr (by decide)
  have h10 : (0 : ℝ) < P.lgn ^ 10 := by positivity
  have hlt : (N : ℝ) / P.lgn ^ 10 < (HintParams.D N X Y : ℝ) := not_le.mp hnot
  calc (N : ℝ) = (N : ℝ) / P.lgn ^ 10 * P.lgn ^ 10 := by field_simp
    _ < (HintParams.D N X Y : ℝ) * P.lgn ^ 10 := by nlinarith
    _ = P.lgn ^ 10 * (HintParams.D N X Y : ℝ) := by ring

/-- The second (small) rule does not apply at a recursive node. -/
lemma Nthresh_lt {P : HintParams} {N X Y : ℕ} (hrule : P.rule N X Y = .recursive) :
    (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2 < (HintParams.D N X Y : ℝ) := by
  by_contra hcon
  push_neg at hcon
  have h1 : ¬ ((HintParams.D N X Y : ℝ) ≤ (N : ℝ) / P.lgn ^ 10) := by
    intro hc
    have hr : P.rule N X Y = .cheap := by
      unfold HintParams.rule
      rw [if_pos hc]
    rw [hrule] at hr
    exact absurd hr (by decide)
  have hr : P.rule N X Y = .small := by
    unfold HintParams.rule
    rw [if_neg h1, if_pos hcon]
  rw [hrule] at hr
  exact absurd hr (by decide)

lemma lamStar_ge_C (P : HintParams) : (P.C : ℝ) ≤ (P.lamStar : ℝ) := by
  unfold HintParams.lamStar
  have h1 : (0 : ℝ) ≤ (⌈lg (lg ((P.n : ℝ) + 2))⌉₊ : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (P.C : ℝ) := by positivity
  push_cast
  nlinarith [h1, h2]

/-- `1/η² = log^{2A} n`. -/
lemma inv_eta_sq (P : HintParams) : (P.eta ^ 2)⁻¹ = P.lgn ^ (2 * P.A) := by
  have hL : P.eta = (P.lgn ^ P.A)⁻¹ := rfl
  rw [hL, inv_pow, inv_inv, ← pow_mul]
  congr 1
  omega

/-- The recursive rule also rules out small instances: `C⁴ log^{6+2A} n < N`. -/
lemma Nthresh_le_N {P : HintParams} {N X Y : ℕ} (hL : 1 ≤ P.lgn)
    (hrule : P.rule N X Y = .recursive) :
    (P.C : ℝ) ^ 4 * P.lgn ^ (6 + 2 * P.A) < (N : ℝ) := by
  have h1 := Nthresh_lt (P := P) (N := N) (X := X) (Y := Y) hrule
  have h2 := lamStar_ge_C P
  have h3 : (HintParams.D N X Y : ℝ) ≤ (N : ℝ) := by exact_mod_cast D_le_N N X Y
  have hlgn : (0 : ℝ) < P.lgn := by linarith
  have hC : (0 : ℝ) ≤ (P.C : ℝ) := by positivity
  have hL6 : (0 : ℝ) < P.lgn ^ 6 := by positivity
  have hLA : (0 : ℝ) < P.lgn ^ (2 * P.A) := by positivity
  have hLbig : (0 : ℝ) < P.lgn ^ (6 + 2 * P.A) := by positivity
  have heta : ((P.eta ^ 2)⁻¹) = P.lgn ^ (2 * P.A) := inv_eta_sq P
  have hsplit : P.lgn ^ 6 * P.lgn ^ (2 * P.A) = P.lgn ^ (6 + 2 * P.A) := by
    rw [← pow_add]
  have h1' : (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * (P.lgn ^ 6 * P.lgn ^ (2 * P.A))
      < (HintParams.D N X Y : ℝ) := by
    have h := h1
    rw [div_eq_mul_inv, heta] at h
    linarith [h]
  rw [hsplit] at h1'
  have h4 : (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A) < (N : ℝ) := by
    linarith [h1', h3]
  have h5 : (P.C : ℝ) ^ 4 * P.lgn ^ (6 + 2 * P.A)
      = (P.C : ℝ) * ((P.C : ℝ) ^ 3 * P.lgn ^ (6 + 2 * P.A)) := by ring
  have h6 : (P.C : ℝ) * ((P.C : ℝ) ^ 3 * P.lgn ^ (6 + 2 * P.A))
      ≤ (P.lamStar : ℝ) * ((P.C : ℝ) ^ 3 * P.lgn ^ (6 + 2 * P.A)) := by
    apply mul_le_mul_of_nonneg_right h2
    positivity
  have h7 : (P.lamStar : ℝ) * ((P.C : ℝ) ^ 3 * P.lgn ^ (6 + 2 * P.A))
      = (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A) := by ring
  linarith [h4, h5, h6, h7]



/-- For `C ≥ 40`, `60 C² ≤ 2^C / 8`. -/
lemma sixty_sq_le_pow (C : ℕ) (hC : 40 ≤ C) : 60 * (C : ℝ) ^ 2 ≤ (2 : ℝ) ^ C * (1 / 8) := by
  induction C, hC using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      have hm3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 3 ≤ m)
      have hstep : 60 * ((m : ℝ) + 1) ^ 2 ≤ 2 * (60 * (m : ℝ) ^ 2) := by nlinarith
      calc 60 * ((m + 1 : ℕ) : ℝ) ^ 2 = 60 * ((m : ℝ) + 1) ^ 2 := by push_cast; ring
        _ ≤ 2 * (60 * (m : ℝ) ^ 2) := hstep
        _ ≤ 2 * ((2 : ℝ) ^ m * (1 / 8)) := by linarith
        _ = (2 : ℝ) ^ (m + 1) * (1 / 8) := by rw [pow_succ]; ring

lemma two_rpow_neg_sixty (C : ℕ) (hC : 40 ≤ C) :
    (2 : ℝ) ^ (-(C : ℝ)) * (60 * (C : ℝ) ^ 2) ≤ 1 / 8 := by
  have h := sixty_sq_le_pow C hC
  have h2 : (2 : ℝ) ^ (-(C : ℝ)) = ((2 : ℝ) ^ C)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [h2, inv_mul_eq_div, div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ C)]
  linarith

/-- Exponential beats linear: `4096 A + 409600 ≤ 2^(A-30)` for `A ≥ 100`. -/
lemma two_pow_ge_linear : ∀ A : ℕ, 100 ≤ A → 4096 * A + 409600 ≤ 2 ^ (A - 30) := by
  intro A hA
  induction A, hA using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      have hsub : m + 1 - 30 = (m - 30) + 1 := by omega
      rw [hsub, pow_succ]
      have h2 : 4096 ≤ 2 ^ (m - 30) := by
        have h70 : 70 ≤ m - 30 := by omega
        calc (4096 : ℕ) ≤ 2 ^ 70 := by norm_num
          _ ≤ 2 ^ (m - 30) := Nat.pow_le_pow_right (by norm_num) h70
      have hstep : 4096 * (m + 1) + 409600 = (4096 * m + 409600) + 4096 := by ring
      rw [hstep]
      nlinarith [ih, h2]

lemma two_pow_ge_linear_R (A : ℕ) (hA : 100 ≤ A) :
    4096 * (A : ℝ) + 409600 ≤ (2 : ℝ) ^ (A - 30) := by
  have h := two_pow_ge_linear A hA
  have h' : ((4096 * A + 409600 : ℕ) : ℝ) ≤ ((2 ^ (A - 30) : ℕ) : ℝ) := by exact_mod_cast h
  have h2 : ((2 ^ (A - 30) : ℕ) : ℝ) = (2 : ℝ) ^ (A - 30) := by push_cast; ring
  rw [h2] at h'
  push_cast at h'
  linarith

/-- `512 A + 25600 ≤ 2^A` for `A ≥ 100`. -/
lemma linear_le_two_pow (A : ℕ) (hA : 100 ≤ A) : 512 * (A : ℝ) + 25600 ≤ (2 : ℝ) ^ A := by
  have h := two_pow_ge_linear_R A hA
  have h2 : (2 : ℝ) ^ A = (2 : ℝ) ^ (A - 30) * (2 : ℝ) ^ 30 := by
    rw [← pow_add]; congr 1; omega
  have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ (A - 30) := one_le_pow₀ (by norm_num)
  rw [h2]
  nlinarith [h, h3]

/-- `log x ≤ 2x` for `x ≥ 1`. -/
lemma lg_le_two_mul (x : ℝ) (hx : 1 ≤ x) : lg x ≤ 2 * x := by
  have h0 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [lg_eq_log_div, div_le_iff₀ h0]
  have h1 : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos (by linarith)
  nlinarith [Real.log_two_gt_d9]

/-- Monotonicity of `lg` on nonnegative arguments. -/
lemma lg_le_lg_of_le {x y : ℝ} (hx : 0 ≤ x) (hy : 1 ≤ y) (h : x ≤ y) : lg x ≤ lg y := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · rw [← h0]
    simp only [lg, Real.logb_zero]
    exact Real.logb_nonneg (by norm_num) hy
  · exact Real.logb_le_logb_of_le (by norm_num) hpos h

lemma lg_nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 ≤ lg x :=
  Real.logb_nonneg (by norm_num) hx

lemma lg_mul_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : lg (x * y) = lg x + lg y := by
  simp only [lg, Real.logb_mul (ne_of_gt hx) (ne_of_gt hy)]

lemma lg_pow_pos {x : ℝ} (hx : 0 < x) (n : ℕ) : lg (x ^ n) = (n : ℝ) * lg x := by
  rw [lg_eq_log_div, lg_eq_log_div, Real.log_pow]
  push_cast
  field_simp

lemma lg_sixteen : lg (16 : ℝ) = 4 := by
  have h : (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
  rw [h, lg_pow_pos (by norm_num)]
  simp [lg_two]

lemma lg_three_le_two : lg (3 : ℝ) ≤ 2 := by
  have h4 : lg (4 : ℝ) = 2 := by
    have h : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [h, lg_pow_pos (by norm_num)]
    simp [lg_two]
  rw [← h4]
  exact lg_le_lg_of_le (by norm_num) (by norm_num) (by norm_num : (3 : ℝ) ≤ 4)

/-- `L^30 · 2^{A-30} ≤ L^A` for `L ≥ 2`, `A ≥ 30`. -/
lemma lgn_pow_ge {P : HintParams} (hL : 2 ≤ P.lgn) (hA : 30 ≤ P.A) :
    P.lgn ^ 30 * (2 : ℝ) ^ (P.A - 30) ≤ P.lgn ^ P.A := by
  have hp : (2 : ℝ) ^ (P.A - 30) ≤ P.lgn ^ (P.A - 30) :=
    pow_le_pow_left₀ (by norm_num) (by linarith : (2 : ℝ) ≤ P.lgn) _
  have hpos : (0 : ℝ) < P.lgn ^ 30 := by positivity
  calc P.lgn ^ 30 * (2 : ℝ) ^ (P.A - 30) ≤ P.lgn ^ 30 * P.lgn ^ (P.A - 30) := by
        nlinarith [hp, hpos]
    _ = P.lgn ^ (30 + (P.A - 30)) := (pow_add _ _ _).symm
    _ = P.lgn ^ P.A := by rw [show 30 + (P.A - 30) = P.A by omega]

/-- `L^{2A-34} ≥ 2^A` for `L ≥ 2`, `A ≥ 34`. -/
lemma lgn_pow_ge_two {P : HintParams} (hL : 2 ≤ P.lgn) (hA : 34 ≤ P.A) :
    (2 : ℝ) ^ P.A ≤ P.lgn ^ (2 * P.A - 34) := by
  have h1 : (2 : ℝ) ^ P.A ≤ P.lgn ^ P.A :=
    pow_le_pow_left₀ (by norm_num) (by linarith : (2 : ℝ) ≤ P.lgn) _
  have h2 : P.lgn ^ P.A ≤ P.lgn ^ (2 * P.A - 34) :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ P.lgn) (by omega)
  linarith

/-- `384 (4A+200) log^30 n · η ≤ 1`: the margin term of a recursive node is negligible. -/
lemma eta_margin_small {P : HintParams} (hL : 2 ≤ P.lgn) (hA : 100 ≤ P.A) :
    384 * (4 * (P.A : ℝ) + 200) * P.lgn ^ 30 * P.eta ≤ 1 := by
  have hA30 : 30 ≤ P.A := by omega
  have hp : P.lgn ^ 30 * (2 : ℝ) ^ (P.A - 30) ≤ P.lgn ^ P.A := lgn_pow_ge hL hA30
  have hpos : (0 : ℝ) < P.lgn ^ 30 := by positivity
  have hposA : (0 : ℝ) < P.lgn ^ P.A := by positivity
  have hx : (0 : ℝ) < P.lgn ^ 30 * (2 : ℝ) ^ (P.A - 30) := by positivity
  have heta : P.eta = (P.lgn ^ P.A)⁻¹ := rfl
  have hinv : (P.lgn ^ P.A)⁻¹ ≤ (P.lgn ^ 30 * (2 : ℝ) ^ (P.A - 30))⁻¹ :=
    (inv_le_inv₀ hposA hx).mpr hp
  have h1 : P.lgn ^ 30 * P.eta ≤ ((2 : ℝ) ^ (P.A - 30))⁻¹ := by
    rw [heta]
    calc P.lgn ^ 30 * (P.lgn ^ P.A)⁻¹
        ≤ P.lgn ^ 30 * (P.lgn ^ 30 * (2 : ℝ) ^ (P.A - 30))⁻¹ :=
          mul_le_mul_of_nonneg_left hinv hpos.le
      _ = ((2 : ℝ) ^ (P.A - 30))⁻¹ := by
          rw [mul_inv]
          field_simp
  have hnum : 384 * (4 * (P.A : ℝ) + 200) ≤ (2 : ℝ) ^ (P.A - 30) := by
    have h := two_pow_ge_linear_R P.A hA
    have hc : 384 * (4 * (P.A : ℝ) + 200) = 1536 * (P.A : ℝ) + 76800 := by ring
    rw [hc]
    linarith
  have hc0 : (0 : ℝ) ≤ 384 * (4 * (P.A : ℝ) + 200) := by positivity
  calc 384 * (4 * (P.A : ℝ) + 200) * P.lgn ^ 30 * P.eta
      = 384 * (4 * (P.A : ℝ) + 200) * (P.lgn ^ 30 * P.eta) := by ring
    _ ≤ 384 * (4 * (P.A : ℝ) + 200) * ((2 : ℝ) ^ (P.A - 30))⁻¹ :=
        mul_le_mul_of_nonneg_left h1 hc0
    _ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one (by positivity)]
        exact hnum

/-! ### Basic estimates at a recursive node -/

lemma N_lt_two_lgn13 {P : HintParams} {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    (hL : 1 ≤ P.lgn) (hrule : P.rule N X Y = .recursive) :
    (N : ℝ) < 2 * P.lgn ^ 13 * (Y : ℝ) := by
  have hargs' := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  have hlgn : (0 : ℝ) < P.lgn := by linarith
  have hrows := rows_eq_of_rule hrule
  have hX := X_le_of_rows hlgn hrows
  have h1 := N_lt_lgn_D hL hrule
  have h10 : (0 : ℝ) < P.lgn ^ 10 := by positivity
  have hD : (HintParams.D N X Y : ℝ) ≤ (X : ℝ) + (Y : ℝ) := by
    have h := D_le_sum N X Y
    exact_mod_cast h
  have hp10 : P.lgn ^ 13 = P.lgn ^ 10 * P.lgn ^ 3 := by rw [← pow_add]
  have h1013 : P.lgn ^ 10 ≤ P.lgn ^ 13 := by
    rw [hp10]
    have h3 : (1 : ℝ) ≤ P.lgn ^ 3 := one_le_pow₀ hL
    nlinarith [h10.le, h3]
  have hY0 : (0 : ℝ) ≤ (Y : ℝ) := Nat.cast_nonneg Y
  have hid : P.lgn ^ 10 * ((Y : ℝ) * P.lgn ^ 3 + (Y : ℝ))
      = (Y : ℝ) * P.lgn ^ 13 + (Y : ℝ) * P.lgn ^ 10 := by
    have hp : P.lgn ^ 10 * P.lgn ^ 3 = P.lgn ^ 13 := by rw [← pow_add]
    calc P.lgn ^ 10 * ((Y : ℝ) * P.lgn ^ 3 + (Y : ℝ))
        = (Y : ℝ) * (P.lgn ^ 10 * P.lgn ^ 3) + (Y : ℝ) * P.lgn ^ 10 := by ring
      _ = (Y : ℝ) * P.lgn ^ 13 + (Y : ℝ) * P.lgn ^ 10 := by rw [hp]
  have s1 : P.lgn ^ 10 * (HintParams.D N X Y : ℝ) ≤ P.lgn ^ 10 * ((X : ℝ) + (Y : ℝ)) :=
    mul_le_mul_of_nonneg_left hD h10.le
  have s2 : P.lgn ^ 10 * ((X : ℝ) + (Y : ℝ)) ≤ P.lgn ^ 10 * ((Y : ℝ) * P.lgn ^ 3 + (Y : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ h10.le
    linarith
  have s3 : (Y : ℝ) * P.lgn ^ 10 ≤ (Y : ℝ) * P.lgn ^ 13 :=
    mul_le_mul_of_nonneg_left h1013 hY0
  linarith [h1, s1, s2, hid, s3]

lemma Y_ge_one {P : HintParams} {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    (hL : 1 ≤ P.lgn) (hrule : P.rule N X Y = .recursive) : 1 ≤ Y := by
  have h := N_lt_two_lgn13 hargs hL hrule
  have hargs' := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  by_contra hc
  push_neg at hc
  have h0 : Y = 0 := by omega
  rw [h0] at h
  push_cast at h
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h13 : (0 : ℝ) < P.lgn ^ 13 := by
    have : (0 : ℝ) < P.lgn := by linarith
    positivity
  nlinarith [h, hNpos, h13]

lemma dens_gt {P : HintParams} {N X Y : ℕ} (hargs : P.NodeArgs N X Y) (hL : 1 ≤ P.lgn)
    (hrule : P.rule N X Y = .recursive) : densFloor P < nodeDens N Y := by
  have h := N_lt_two_lgn13 hargs hL hrule
  have hargs' := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h13 : (0 : ℝ) < 2 * P.lgn ^ 13 := by
    have : (0 : ℝ) < P.lgn := by linarith
    positivity
  unfold densFloor nodeDens
  rw [inv_eq_one_div, lt_div_iff₀ hNpos]
  have h2 : (N : ℝ) / (2 * P.lgn ^ 13) < (Y : ℝ) :=
    (div_lt_iff₀ h13).mpr (by linarith)
  have heq : 1 / (2 * P.lgn ^ 13) * (N : ℝ) = (N : ℝ) / (2 * P.lgn ^ 13) := by ring
  rw [heq]
  exact h2

lemma Nmax_le {P : HintParams} {N X Y : ℕ} (hargs : P.NodeArgs N X Y) (hL : 1 ≤ P.lgn)
    (hrule : P.rule N X Y = .recursive) : (P.Nmax N X Y : ℝ) ≤ 3 * P.lgn ^ 13 := by
  have h := N_lt_two_lgn13 hargs hL hrule
  have hY1 := Y_ge_one hargs hL hrule
  have hrows := rows_eq_of_rule hrule
  have hargs' := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  have hYposR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
  have hratio : (N : ℝ) / (Y : ℝ) < 2 * P.lgn ^ 13 := by
    rw [div_lt_iff₀ hYposR]
    linarith
  unfold HintParams.Nmax
  rw [hrows]
  have hceil : (⌈(N : ℝ) / (Y : ℝ)⌉₊ : ℝ) < (N : ℝ) / (Y : ℝ) + 1 := by
    apply Nat.ceil_lt_add_one
    positivity
  have h13 : (1 : ℝ) ≤ P.lgn ^ 13 := by
    calc (1 : ℝ) = 1 ^ 13 := by norm_num
      _ ≤ P.lgn ^ 13 := pow_le_pow_left₀ (by norm_num) hL 13
  linarith [hceil, hratio, h13]

/-- `c = 2⌈log(N/Y)⌉ + C` in terms of the density. -/
lemma c_le {P : HintParams} {N X Y : ℕ} (hargs : P.NodeArgs N X Y) (hY : 1 ≤ Y)
    (hrule : P.rule N X Y = .recursive) :
    (P.c N X Y : ℝ) ≤ (P.C : ℝ) + 2 * lg ((N : ℝ) / (Y : ℝ)) + 2 := by
  have hargs' := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  have hYposR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
  have hcdef : P.c N X Y = 2 * ⌈lg ((N : ℝ) / (Y : ℝ))⌉₊ + P.C := by
    unfold HintParams.c
    rw [if_pos hrule]
  rw [hcdef]
  have hM0 : 0 ≤ lg ((N : ℝ) / (Y : ℝ)) := by
    apply Real.logb_nonneg (by norm_num)
    rw [le_div_iff₀ hYposR]
    exact_mod_cast (by omega : 1 * Y ≤ N)
  have hceil : ((⌈lg ((N : ℝ) / (Y : ℝ))⌉₊ : ℕ) : ℝ) ≤ lg ((N : ℝ) / (Y : ℝ)) + 1 := by
    have := Nat.ceil_lt_add_one hM0
    linarith
  push_cast
  linarith

/-- `2^{-c} ≤ 2^{-C} ρ²`. -/
lemma two_rpow_c_inv_le {P : HintParams} {N X Y : ℕ} (hargs : P.NodeArgs N X Y)
    (hY : 1 ≤ Y) (hrule : P.rule N X Y = .recursive) :
    ((2 : ℝ) ^ (P.c N X Y))⁻¹ ≤ (2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y) ^ 2 := by
  have hargs' := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hYposR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
  have hratio : (0 : ℝ) < (N : ℝ) / (Y : ℝ) := div_pos hNposR hYposR
  have hcdef : P.c N X Y = 2 * ⌈lg ((N : ℝ) / (Y : ℝ))⌉₊ + P.C := by
    unfold HintParams.c
    rw [if_pos hrule]
  have hNM : (2 : ℝ) ^ (lg ((N : ℝ) / (Y : ℝ))) = (N : ℝ) / (Y : ℝ) :=
    Real.rpow_logb (b := 2) (x := (N : ℝ) / (Y : ℝ)) (by norm_num) (by norm_num) hratio
  have hk : (N : ℝ) / (Y : ℝ) ≤ (2 : ℝ) ^ (⌈lg ((N : ℝ) / (Y : ℝ))⌉₊) := by
    have h2 : (2 : ℝ) ^ (lg ((N : ℝ) / (Y : ℝ)))
        ≤ (2 : ℝ) ^ ((⌈lg ((N : ℝ) / (Y : ℝ))⌉₊ : ℕ) : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact Nat.le_ceil _
    rw [hNM, Real.rpow_natCast] at h2
    exact h2
  have hsq : ((N : ℝ) / (Y : ℝ)) ^ 2 ≤ (2 : ℝ) ^ (2 * ⌈lg ((N : ℝ) / (Y : ℝ))⌉₊) := by
    have hbase : ((N : ℝ) / (Y : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ (⌈lg ((N : ℝ) / (Y : ℝ))⌉₊)) ^ 2 :=
      pow_le_pow_left₀ hratio.le hk 2
    have heq : ((2 : ℝ) ^ (⌈lg ((N : ℝ) / (Y : ℝ))⌉₊)) ^ 2
        = (2 : ℝ) ^ (2 * ⌈lg ((N : ℝ) / (Y : ℝ))⌉₊) := by
      rw [← pow_mul]; congr 1; omega
    linarith [hbase, heq]
  have hpowc : (2 : ℝ) ^ (P.c N X Y)
      = (2 : ℝ) ^ P.C * (2 : ℝ) ^ (2 * ⌈lg ((N : ℝ) / (Y : ℝ))⌉₊) := by
    rw [hcdef, show 2 * ⌈lg ((N : ℝ) / (Y : ℝ))⌉₊ + P.C
        = P.C + 2 * ⌈lg ((N : ℝ) / (Y : ℝ))⌉₊ by omega, pow_add]
  have key : (2 : ℝ) ^ P.C * ((N : ℝ) / (Y : ℝ)) ^ 2 ≤ (2 : ℝ) ^ (P.c N X Y) := by
    rw [hpowc]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  calc ((2 : ℝ) ^ (P.c N X Y))⁻¹
      ≤ ((2 : ℝ) ^ P.C * ((N : ℝ) / (Y : ℝ)) ^ 2)⁻¹ :=
        (inv_le_inv₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (P.c N X Y)) (by positivity)).mpr key
    _ = (2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y) ^ 2 := by
        rw [mul_inv, ← Real.rpow_natCast (2 : ℝ) P.C,
          ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← inv_pow, inv_div]
        simp only [nodeDens]

/-- The number of children of a recursive node: `ℓ ≤ (4A+200) log¹⁴ n`. -/
lemma ell_le {P : HintParams} {N X Y : ℕ} (hargs : P.NodeArgs N X Y) (hL : 2 ≤ P.lgn)
    (hrule : P.rule N X Y = .recursive) :
    (P.ell N X Y : ℝ) ≤ (4 * (P.A : ℝ) + 200) * P.lgn ^ 14 := by
  have hL1 : (1 : ℝ) ≤ P.lgn := by linarith
  have hlgn : (0 : ℝ) < P.lgn := by linarith
  have hNmax := Nmax_le hargs hL1 hrule
  have hBX : (P.BX N X Y : ℝ) ≤ 3 * P.lgn ^ 13 := by
    have hle : P.BX N X Y ≤ P.Nmax N X Y := by unfold HintParams.BX; exact min_le_left _ _
    have hle' : (P.BX N X Y : ℝ) ≤ (P.Nmax N X Y : ℝ) := by exact_mod_cast hle
    linarith
  have hBY : (P.BY N X Y : ℝ) ≤ 3 * P.lgn ^ 13 := by
    have hle : P.BY N X Y ≤ P.Nmax N X Y := by unfold HintParams.BY; exact min_le_left _ _
    have hle' : (P.BY N X Y : ℝ) ≤ (P.Nmax N X Y : ℝ) := by exact_mod_cast hle
    linarith
  have hK1 : ((⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℕ) : ℝ) ≤ 13 * lg P.lgn + 6 := by
    have hlg0 : (0 : ℝ) ≤ lg P.lgn := lg_nonneg_of_one_le hL1
    rcases Nat.eq_zero_or_pos (P.Nmax N X Y) with h0 | hpos
    · have hzero : lg (Real.exp 1 * (P.Nmax N X Y : ℝ)) = 0 := by
        rw [h0]; push_cast; simp [lg]
      rw [hzero]
      simp only [Nat.ceil_zero, Nat.cast_zero]
      nlinarith
    · have hN1 : (1 : ℝ) ≤ (P.Nmax N X Y : ℝ) := by exact_mod_cast hpos
      have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      have hx0 : (0 : ℝ) ≤ Real.exp 1 * (P.Nmax N X Y : ℝ) := by positivity
      have hge1 : (1 : ℝ) ≤ Real.exp 1 * (P.Nmax N X Y : ℝ) := by nlinarith [he1, hN1]
      have h13 : (1 : ℝ) ≤ P.lgn ^ 13 := by
        calc (1 : ℝ) = 1 ^ 13 := by norm_num
          _ ≤ P.lgn ^ 13 := pow_le_pow_left₀ (by norm_num) hL1 13
      have hge3 : (1 : ℝ) ≤ Real.exp 1 * (3 * P.lgn ^ 13) := by nlinarith [he1, h13]
      have hxle : Real.exp 1 * (P.Nmax N X Y : ℝ) ≤ Real.exp 1 * (3 * P.lgn ^ 13) := by
        have hpos' : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
        nlinarith [hNmax, hpos']
      have hlg : lg (Real.exp 1 * (P.Nmax N X Y : ℝ))
          ≤ lg (Real.exp 1 * (3 * P.lgn ^ 13)) := lg_le_lg_of_le hx0 hge3 hxle
      have hval : lg (Real.exp 1 * (3 * P.lgn ^ 13))
          = lg (Real.exp 1) + lg 3 + 13 * lg P.lgn := by
        have heq : Real.exp 1 * (3 * P.lgn ^ 13) = Real.exp 1 * 3 * P.lgn ^ 13 := by ring
        rw [heq]
        rw [lg_mul_pos (by positivity) (by positivity)]
        rw [lg_mul_pos (Real.exp_pos 1) (by norm_num)]
        rw [lg_pow_pos hlgn]
        push_cast
        ring
      have h1 : lg (Real.exp 1) ≤ 2 := lg_exp_one_le_two
      have h3 : lg 3 ≤ 2 := lg_three_le_two
      have hlg0' : (0 : ℝ) ≤ lg (Real.exp 1 * (P.Nmax N X Y : ℝ)) := lg_nonneg_of_one_le hge1
      have hceil : ((⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℕ) : ℝ)
          ≤ lg (Real.exp 1 * (P.Nmax N X Y : ℝ)) + 1 := by
        have h := Nat.ceil_lt_add_one hlg0'
        linarith
      linarith
  have hK2 : ((⌈lg (16 / P.eta ^ 2)⌉₊ : ℕ) : ℝ) ≤ 2 * (P.A : ℝ) * lg P.lgn + 5 := by
    have heta : (16 : ℝ) / P.eta ^ 2 = 16 * P.lgn ^ (2 * P.A) := by
      rw [div_eq_mul_inv, inv_eta_sq]
    have hval : lg (16 * P.lgn ^ (2 * P.A)) = 4 + (2 : ℝ) * (P.A : ℝ) * lg P.lgn := by
      rw [lg_mul_pos (by norm_num) (by positivity)]
      rw [lg_pow_pos hlgn]
      rw [lg_sixteen]
      push_cast
      ring
    have hgoal : lg (16 / P.eta ^ 2) = 4 + (2 : ℝ) * (P.A : ℝ) * lg P.lgn := by
      rw [heta, hval]
    have hlg0 : (0 : ℝ) ≤ lg P.lgn := lg_nonneg_of_one_le hL1
    have hA0 : (0 : ℝ) ≤ (P.A : ℝ) := by positivity
    have hx0 : (0 : ℝ) ≤ lg (16 / P.eta ^ 2) := by
      rw [hgoal]
      nlinarith [hlg0, hA0]
    have hceil := Nat.ceil_lt_add_one hx0
    linarith [hceil, hgoal]
  have hell : (P.ell N X Y : ℝ) = (P.BX N X Y : ℝ) + (P.BY N X Y : ℝ)
      * ((⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℕ) : ℝ) + (P.BY N X Y : ℝ)
      + ((⌈lg (16 / P.eta ^ 2)⌉₊ : ℕ) : ℝ) + 10 := by
    unfold HintParams.ell
    push_cast
    ring
  rw [hell]
  have h13 : (1 : ℝ) ≤ P.lgn ^ 13 := by
    calc (1 : ℝ) = 1 ^ 13 := by norm_num
      _ ≤ P.lgn ^ 13 := pow_le_pow_left₀ (by norm_num) hL1 13
  have hlg2 : lg P.lgn ≤ 2 * P.lgn := lg_le_two_mul P.lgn hL1
  have hA0 : (0 : ℝ) ≤ (P.A : ℝ) := by positivity
  have h14 : P.lgn ≤ P.lgn ^ 14 := by
    calc P.lgn = P.lgn ^ 1 := by ring
      _ ≤ P.lgn ^ 14 := pow_le_pow_right₀ hL1 (by norm_num)
  have h13' : P.lgn ^ 13 ≤ P.lgn ^ 14 := pow_le_pow_right₀ hL1 (by norm_num)
  have h14' : (1 : ℝ) ≤ P.lgn ^ 14 := by
    calc (1 : ℝ) = 1 ^ 14 := by norm_num
      _ ≤ P.lgn ^ 14 := pow_le_pow_left₀ (by norm_num) hL1 14
  have hBY0 : (0 : ℝ) ≤ (P.BY N X Y : ℝ) := Nat.cast_nonneg _
  have hBX0 : (0 : ℝ) ≤ (P.BX N X Y : ℝ) := Nat.cast_nonneg _
  have hprod : (P.BY N X Y : ℝ) * ((⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℕ) : ℝ)
      ≤ (3 * P.lgn ^ 13) * (13 * lg P.lgn + 6) := by
    apply mul_le_mul hBY hK1 (Nat.cast_nonneg _) (by positivity)
  have hprod2 : (3 * P.lgn ^ 13) * (13 * lg P.lgn + 6)
      ≤ (3 * P.lgn ^ 13) * (13 * (2 * P.lgn) + 6) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have hexpand : (3 * P.lgn ^ 13) * (13 * (2 * P.lgn) + 6)
      = 78 * P.lgn ^ 14 + 18 * P.lgn ^ 13 := by
    have hp : P.lgn ^ 13 * P.lgn = P.lgn ^ 14 := (pow_succ P.lgn 13).symm
    nlinarith [hp]
  nlinarith [hprod, hprod2, hexpand, hBX, hBY, hK1, hK2, hlg2, hA0, h14, h13', h14',
    hBX0, hBY0, hlgn]

/-- Arithmetic of the margin term: `6 a L^17 η Y ≤ ρ Y / 32`. -/
lemma margin_arith {a ρ Y L η : ℝ} (hY : 0 ≤ Y) (hL : 0 < L)
    (hm : 384 * a * L ^ 30 * η ≤ 1) (hρlb : 1 / (2 * L ^ 13) ≤ ρ) :
    6 * a * L ^ 17 * η * Y ≤ ρ * Y / 32 := by
  have hL13 : (0 : ℝ) < 64 * L ^ 13 := by positivity
  have hkey : 384 * a * L ^ 30 * η * Y ≤ Y := by
    have h := mul_le_mul_of_nonneg_right hm hY
    linarith [h]
  have hid : 6 * a * L ^ 17 * η * Y * (64 * L ^ 13) = 384 * a * L ^ 30 * η * Y := by
    have hpw : L ^ 17 * L ^ 13 = L ^ 30 := by rw [← pow_add]
    rw [← hpw]
    ring
  have hK : 6 * a * L ^ 17 * η * Y ≤ Y / (64 * L ^ 13) := by
    rw [le_div_iff₀ hL13, hid]
    exact hkey
  have h1' : (1 : ℝ) ≤ 2 * L ^ 13 * ρ := by
    have h5 := mul_le_mul_of_nonneg_right hρlb (by positivity : (0 : ℝ) ≤ 2 * L ^ 13)
    have h6 : (1 / (2 * L ^ 13)) * (2 * L ^ 13) = 1 := by field_simp
    linarith [h5, h6]
  have h2 : Y / (64 * L ^ 13) ≤ ρ * Y / 32 := by
    rw [div_le_iff₀ hL13]
    nlinarith [h1', hY]
  linarith [hK, h2]

/-- **Density contraction.** At a recursive node the total density of the children is at most `ρ/4`. -/
lemma capY_sum_le {P : HintParams} {N X Y : ℕ} (hargs : P.NodeArgs N X Y) (hL : 2 ≤ P.lgn)
    (hA : 100 ≤ P.A) (hC : 40 ≤ P.C) (hrule : P.rule N X Y = .recursive) :
    ∑ s ∈ range (P.ell N X Y), (P.capY N X Y s : ℝ) ≤ nodeDens N Y * (Y : ℝ) / 4 := by
  classical
  have hargs' := hargs
  obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
  have hL1 : (1 : ℝ) ≤ P.lgn := by linarith
  have hlgn : (0 : ℝ) < P.lgn := by linarith
  have hrows := rows_eq_of_rule hrule
  have hY1 : 1 ≤ Y := Y_ge_one hargs hL1 hrule
  have hYposR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY1
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hrho0 : (0 : ℝ) < nodeDens N Y := nodeDens_pos (by omega) (by omega)
  have hrho_le1 : nodeDens N Y ≤ 1 := nodeDens_le_one hN1 hYN
  have hrho_lb : (1 : ℝ) / (2 * P.lgn ^ 13) ≤ nodeDens N Y := by
    have h := dens_gt hargs hL1 hrule
    unfold densFloor at h
    rw [inv_eq_one_div] at h
    exact le_of_lt h
  have heta0 : (0 : ℝ) < P.eta := by
    unfold HintParams.eta
    positivity
  have hell := ell_le hargs hL hrule
  have hell0 : (0 : ℝ) ≤ (P.ell N X Y : ℝ) := Nat.cast_nonneg _
  -- ## Step 1: the pointwise bound obtained by dropping the `min`
  have hcap : ∀ s ∈ range (P.ell N X Y),
      (P.capY N X Y s : ℝ) ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
        + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1 := by
    intro s _
    have hQ0 : (0 : ℝ) ≤ P.Q N X Y s := Q_nonneg (P := P) hN1 s
    have h1 : (P.capY N X Y s : ℝ)
        ≤ ((⌈((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
            + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ : ℕ) : ℝ) := by
      unfold HintParams.capY
      exact_mod_cast min_le_right Y _
    have h2 : ((⌈((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
            + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ : ℕ) : ℝ)
        < ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
          + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1 := by
      have hz : (0 : ℝ) ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
          + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) := by positivity
      have h := Nat.ceil_lt_add_one hz
      linarith
    linarith
  -- ## Step 2: sum the pointwise bound
  have hsplit : ∑ s ∈ range (P.ell N X Y), (P.capY N X Y s : ℝ)
      ≤ ((2 : ℝ) ^ (P.c N X Y))⁻¹ * (∑ s ∈ range (P.ell N X Y), P.Q N X Y s)
        + (P.ell N X Y : ℝ) * (2 * P.eta * ((HintParams.D N X Y : ℝ) + 1))
        + (P.ell N X Y : ℝ) := by
    calc ∑ s ∈ range (P.ell N X Y), (P.capY N X Y s : ℝ)
        ≤ ∑ s ∈ range (P.ell N X Y), (((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s
            + 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1) := Finset.sum_le_sum hcap
      _ = ((2 : ℝ) ^ (P.c N X Y))⁻¹ * (∑ s ∈ range (P.ell N X Y), P.Q N X Y s)
            + (P.ell N X Y : ℝ) * (2 * P.eta * ((HintParams.D N X Y : ℝ) + 1))
            + (P.ell N X Y : ℝ) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← Finset.mul_sum]
          ring
  -- ## Step 3: the three terms are each at most `ρY/32`
  have hc := c_le hargs hY1 hrule
  have hYleN : (Y : ℝ) ≤ (N : ℝ) := by exact_mod_cast hYN
  have hratio1 : (1 : ℝ) ≤ (N : ℝ) / (Y : ℝ) := by
    rw [le_div_iff₀ hYposR]
    linarith
  have hρM : nodeDens N Y * lg ((N : ℝ) / (Y : ℝ)) ≤ lg (Real.exp 1) := by
    have heq : nodeDens N Y * lg ((N : ℝ) / (Y : ℝ))
        = lg ((N : ℝ) / (Y : ℝ)) / ((N : ℝ) / (Y : ℝ)) := by
      unfold nodeDens
      field_simp
    rw [heq]
    exact lg_div_self_le hratio1
  have hρC : nodeDens N Y * (P.c N X Y : ℝ) ≤ (P.C : ℝ) + 6 := by
    have h1 : nodeDens N Y * (P.c N X Y : ℝ)
        ≤ nodeDens N Y * ((P.C : ℝ) + 2 * lg ((N : ℝ) / (Y : ℝ)) + 2) :=
      mul_le_mul_of_nonneg_left hc hrho0.le
    nlinarith [h1, hρM, hrho_le1, lg_exp_one_le_two]
  have hnum : (2 : ℝ) ^ (-(P.C : ℝ)) * ((P.C : ℝ) + 40) ≤ 1 / 32 := by
    have h1 := two_rpow_neg_sixty P.C hC
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(P.C : ℝ)) := by positivity
    have hC1 : (4 : ℝ) ≤ (P.C : ℝ) := by exact_mod_cast (by omega : 4 ≤ P.C)
    have hle : 4 * ((P.C : ℝ) + 40) ≤ 60 * (P.C : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((P.C : ℝ) - 4)]
    have h2 := mul_le_mul_of_nonneg_left hle hpos.le
    linarith [h1, h2]
  have htermQ : ((2 : ℝ) ^ (P.c N X Y))⁻¹ * (∑ s ∈ range (P.ell N X Y), P.Q N X Y s)
      ≤ nodeDens N Y * (Y : ℝ) / 32 := by
    have h1 : ((2 : ℝ) ^ (P.c N X Y))⁻¹ ≤ (2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y) ^ 2 :=
      two_rpow_c_inv_le hargs hY1 hrule
    have h2 : ∑ s ∈ range (P.ell N X Y), P.Q N X Y s
        ≤ (Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32) :=
      Q_sum_le (P := P) hargs hrows hY1
    have h3 : (0 : ℝ) ≤ ∑ s ∈ range (P.ell N X Y), P.Q N X Y s :=
      Finset.sum_nonneg (fun s _ => Q_nonneg (P := P) hN1 s)
    have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y) ^ 2 := by positivity
    have h5 := mul_le_mul h1 h2 h3 h4
    have hkey : (2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y) ^ 2
        * ((Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32))
        ≤ nodeDens N Y * (Y : ℝ) / 32 := by
      have hfac : (2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y) ^ 2
          * ((Y : ℝ) * (2 * (N : ℝ) / (Y : ℝ) + (P.c N X Y : ℝ) + 32))
          = (2 : ℝ) ^ (-(P.C : ℝ)) * (nodeDens N Y * (Y : ℝ))
            * (2 + nodeDens N Y * (P.c N X Y : ℝ) + 32 * nodeDens N Y) := by
        unfold nodeDens
        field_simp
      rw [hfac]
      have h2 : 2 + nodeDens N Y * (P.c N X Y : ℝ) + 32 * nodeDens N Y ≤ (P.C : ℝ) + 40 := by
        linarith [hρC, hrho_le1]
      have hρY0 : (0 : ℝ) ≤ nodeDens N Y * (Y : ℝ) := by positivity
      have hfac2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(P.C : ℝ)) := by positivity
      have hb := mul_le_mul_of_nonneg_left h2 (mul_nonneg hfac2 hρY0)
      have hfin : (2 : ℝ) ^ (-(P.C : ℝ)) * ((P.C : ℝ) + 40) * (nodeDens N Y * (Y : ℝ))
          ≤ (1 / 32) * (nodeDens N Y * (Y : ℝ)) :=
        mul_le_mul_of_nonneg_right hnum hρY0
      nlinarith [hb, hfin]
    linarith [h5, hkey]
  have hD1 : (HintParams.D N X Y : ℝ) + 1 ≤ 3 * ((Y : ℝ) * P.lgn ^ 3) := by
    have hX := X_le_of_rows hlgn hrows
    have hDle : (HintParams.D N X Y : ℝ) ≤ (X : ℝ) + (Y : ℝ) := by
      have h := D_le_sum N X Y
      exact_mod_cast h
    have hY0 : (0 : ℝ) ≤ (Y : ℝ) := le_of_lt hYposR
    have hY1R : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY1
    have hL3 : (1 : ℝ) ≤ P.lgn ^ 3 := one_le_pow₀ hL1
    have hL3pos : (0 : ℝ) < P.lgn ^ 3 := by positivity
    nlinarith [hX, hDle, hY0, hL3, hY1R, hL3pos]
  have htermM : (P.ell N X Y : ℝ) * (2 * P.eta * ((HintParams.D N X Y : ℝ) + 1))
      ≤ nodeDens N Y * (Y : ℝ) / 32 := by
    have hstep1 : (P.ell N X Y : ℝ) * (2 * P.eta * ((HintParams.D N X Y : ℝ) + 1))
        ≤ (P.ell N X Y : ℝ) * (2 * P.eta * (3 * ((Y : ℝ) * P.lgn ^ 3))) := by
      have h1 : 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)
          ≤ 2 * P.eta * (3 * ((Y : ℝ) * P.lgn ^ 3)) := by
        nlinarith [hD1, heta0]
      exact mul_le_mul_of_nonneg_left h1 hell0
    have hstep2 : (P.ell N X Y : ℝ) * (2 * P.eta * (3 * ((Y : ℝ) * P.lgn ^ 3)))
        ≤ ((4 * (P.A : ℝ) + 200) * P.lgn ^ 14)
          * (2 * P.eta * (3 * ((Y : ℝ) * P.lgn ^ 3))) := by
      apply mul_le_mul_of_nonneg_right hell
      positivity
    have hid2 : ((4 * (P.A : ℝ) + 200) * P.lgn ^ 14)
        * (2 * P.eta * (3 * ((Y : ℝ) * P.lgn ^ 3)))
        = 6 * (4 * (P.A : ℝ) + 200) * P.lgn ^ 17 * P.eta * (Y : ℝ) := by
      have hpw : P.lgn ^ 14 * P.lgn ^ 3 = P.lgn ^ 17 := by rw [← pow_add]
      rw [← hpw]
      ring
    have hmarg := eta_margin_small hL hA
    have hconst := margin_arith (a := 4 * (P.A : ℝ) + 200) (ρ := nodeDens N Y) (Y := (Y : ℝ))
      (L := P.lgn) (η := P.eta) (le_of_lt hYposR) hlgn hmarg hrho_lb
    linarith [hstep1, hstep2, hid2, hconst]
  have htermO : (P.ell N X Y : ℝ) ≤ nodeDens N Y * (Y : ℝ) / 32 := by
    have hNth := Nthresh_le_N hL1 hrule
    have hρ2 : (1 : ℝ) / (4 * P.lgn ^ 26) ≤ (nodeDens N Y) ^ 2 := by
      have h2 : (0 : ℝ) < 1 / (2 * P.lgn ^ 13) := by positivity
      have h3 : (1 / (2 * P.lgn ^ 13)) ^ 2 ≤ (nodeDens N Y) ^ 2 := by
        nlinarith [hrho_lb, h2, hrho0]
      have h4 : (1 / (2 * P.lgn ^ 13)) ^ 2 = 1 / (4 * P.lgn ^ 26) := by
        have hp : P.lgn ^ 13 * P.lgn ^ 13 = P.lgn ^ 26 := by rw [← pow_add]
        field_simp
        nlinarith [hp]
      linarith [h3, h4]
    -- `2^A L^14 ≤ ρ² N`
    have hpowsplit : P.lgn ^ (6 + 2 * P.A)
        = P.lgn ^ (2 * P.A - 34) * P.lgn ^ 14 * P.lgn ^ 26 := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    have hpowbig : 4 * (2 : ℝ) ^ P.A
        ≤ (P.C : ℝ) ^ 4 * P.lgn ^ (2 * P.A - 34) := by
      have h1 : (2 : ℝ) ^ P.A ≤ P.lgn ^ (2 * P.A - 34) := lgn_pow_ge_two hL (by omega)
      have h2 : (4 : ℝ) ≤ (P.C : ℝ) ^ 4 := by
        have hC1 : (4 : ℝ) ≤ (P.C : ℝ) := by exact_mod_cast (by omega : 4 ≤ P.C)
        nlinarith [hC1, sq_nonneg ((P.C : ℝ) - 4)]
      have h3 : (0 : ℝ) < P.lgn ^ (2 * P.A - 34) := by positivity
      nlinarith [h1, h2, h3]
    have hellin : 32 * (P.ell N X Y : ℝ) ≤ (2 : ℝ) ^ P.A * P.lgn ^ 14 := by
      have h1 : 32 * (P.ell N X Y : ℝ) ≤ 32 * ((4 * (P.A : ℝ) + 200) * P.lgn ^ 14) := by
        nlinarith [hell, hell0]
      have h2 : 512 * (P.A : ℝ) + 25600 ≤ (2 : ℝ) ^ P.A := linear_le_two_pow P.A hA
      have h3 : (0 : ℝ) ≤ P.lgn ^ 14 := by positivity
      have h4 : 32 * (4 * (P.A : ℝ) + 200) = 128 * (P.A : ℝ) + 6400 := by ring
      have h5 : 128 * (P.A : ℝ) + 6400 ≤ 512 * (P.A : ℝ) + 25600 := by
        have hA0 : (0 : ℝ) ≤ (P.A : ℝ) := by positivity
        linarith
      nlinarith [h1, h2, h3, h4, h5]
    -- `ρ² N` is bigger than `2^A L^14`
    have h6 : (1 : ℝ) / (4 * P.lgn ^ 26) * (N : ℝ) ≤ (nodeDens N Y) ^ 2 * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hρ2 (le_of_lt hNposR)
    have h7 : (1 : ℝ) / (4 * P.lgn ^ 26) * (N : ℝ)
        = (N : ℝ) / (4 * P.lgn ^ 26) := by ring
    have h8 : ((P.C : ℝ) ^ 4 * P.lgn ^ (6 + 2 * P.A)) / (4 * P.lgn ^ 26) < (N : ℝ) / (4 * P.lgn ^ 26) := by
      have hpos : (0 : ℝ) < 1 / (4 * P.lgn ^ 26) := by positivity
      have h := mul_lt_mul_of_pos_right hNth hpos
      calc ((P.C : ℝ) ^ 4 * P.lgn ^ (6 + 2 * P.A)) / (4 * P.lgn ^ 26)
          = ((P.C : ℝ) ^ 4 * P.lgn ^ (6 + 2 * P.A)) * (1 / (4 * P.lgn ^ 26)) := by ring
        _ < (N : ℝ) * (1 / (4 * P.lgn ^ 26)) := h
        _ = (N : ℝ) / (4 * P.lgn ^ 26) := by ring
    have h10 : (2 : ℝ) ^ P.A * P.lgn ^ 14
        ≤ ((P.C : ℝ) ^ 4 * P.lgn ^ (6 + 2 * P.A)) / (4 * P.lgn ^ 26) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * P.lgn ^ 26)]
      rw [hpowsplit]
      have hpos40 : (0 : ℝ) < P.lgn ^ 14 * P.lgn ^ 26 := by positivity
      have hmul := mul_le_mul_of_nonneg_right hpowbig hpos40.le
      nlinarith [hmul]
    have h11 : (2 : ℝ) ^ P.A * P.lgn ^ 14 ≤ (nodeDens N Y) ^ 2 * (N : ℝ) := by
      linarith [h6, h7, h8, h10]
    have hρY_eq : nodeDens N Y * (Y : ℝ) = (nodeDens N Y) ^ 2 * (N : ℝ) := by
      unfold nodeDens
      field_simp
    have h12 : 32 * (P.ell N X Y : ℝ) ≤ (nodeDens N Y) ^ 2 * (N : ℝ) := le_trans hellin h11
    rw [hρY_eq, le_div_iff₀ (by norm_num : (0 : ℝ) < 32)]
    linarith [h12]
  have hρY0 : (0 : ℝ) ≤ nodeDens N Y * (Y : ℝ) := by positivity
  linarith [hsplit, htermQ, htermM, htermO]

/-! ### The recursion tree -/

/-- Total density of all recursive nodes of a tree, where the root has `(N, Y)`. -/
def massAt : Node → ℕ → ℕ → ℝ
  | .store _, _, _ => 0
  | .cr _ _, _, _ => 0
  | .direct _ _, _, _ => 0
  | .recursive sch _ _ Ys child, N, Y => nodeDens N Y + ∑ s : Fin sch.ℓ, massAt (child s) sch.m (Ys s)

lemma allSome_spec {k : ℕ} {α : Type 1} {f : Fin k → Option α} {g : Fin k → α}
    (h : HintParams.allSome f = some g) : ∀ s, f s = some (g s) := by
  intro s
  unfold HintParams.allSome at h
  split_ifs at h with hall
  · simp only [Option.some.injEq] at h
    subst h
    exact (Option.some_get (hall s)).symm

lemma allSome_eq_none {k : ℕ} {α : Type 1} {f : Fin k → Option α} {s : Fin k}
    (h : f s = none) : HintParams.allSome f = none := by
  unfold HintParams.allSome
  split_ifs with hall
  · have h2 := hall s
    rw [h] at h2
    exact absurd h2 (by simp)
  · rfl

lemma allSome_eq_some {k : ℕ} {α : Type 1} {f : Fin k → Option α}
    (h : ∀ s, ∃ a, f s = some a) : ∃ g, HintParams.allSome f = some g := by
  unfold HintParams.allSome
  split_ifs with hall
  · exact ⟨fun s => (f s).get (hall s), rfl⟩
  · exfalso
    push_neg at hall
    obtain ⟨s, hs⟩ := hall
    obtain ⟨a, ha⟩ := h s
    rw [ha] at hs
    simp at hs

lemma allSome_const_none {k : ℕ} (hk : 0 < k) {α : Type 1} :
    HintParams.allSome (fun _ : Fin k => (none : Option α)) = none := by
  obtain ⟨s⟩ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  exact allSome_eq_none (s := s) rfl

/-- The number of children `ℓ` is at least `10`, in particular nonzero. -/
lemma ten_le_ell (P : HintParams) (N X Y : ℕ) : 10 ≤ P.ell N X Y := by
  unfold HintParams.ell
  omega

/-- At a non-recursive node the tree is a leaf. -/
lemma tree_of_not_recursive {P : HintParams} {N X Y fuel : ℕ} (hr : P.rule N X Y ≠ .recursive)
    (hfuel : 1 ≤ fuel) :
    ∃ T, P.tree fuel N X Y = some T ∧ T.depth = 1 ∧ massAt T N Y = 0 ∧ T.recursiveCount = 0 ∧
      T.nodeCount = 1 := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  rcases hru : P.rule N X Y with _ | _ | _ | _
  · exact ⟨.cr N (HintParams.D N X Y), by rw [HintParams.tree, hru], rfl, rfl, rfl, rfl⟩
  · exact ⟨.cr N (HintParams.D N X Y), by rw [HintParams.tree, hru], rfl, rfl, rfl, rfl⟩
  · exact absurd hru hr
  · exact ⟨.direct (P.scheme N X Y) (P.resid N X Y), by rw [HintParams.tree, hru], rfl, rfl, rfl,
      rfl⟩

/-- **The recursion terminates with the paper's bounds** (induction on the density level). -/
theorem tree_exists_aux {P : HintParams} (hA : 100 ≤ P.A) (hC : 40 ≤ P.C) (hL : 2 ≤ P.lgn) :
    ∀ (h : ℕ) (N X Y : ℕ), P.NodeArgs N X Y →
      nodeDens N Y ≤ 4 ^ h * (2 * P.lgn ^ 13)⁻¹ →
      ∃ T : Node, P.tree (h + 1) N X Y = some T ∧
        (T.depth : ℝ) ≤ (h : ℝ) + 1 ∧
        massAt T N Y ≤ 2 * nodeDens N Y ∧
        (2 * P.lgn ^ 13)⁻¹ * (T.recursiveCount : ℝ) ≤ massAt T N Y ∧
        (T.nodeCount : ℝ) ≤
          1 + (4 * (P.A : ℝ) + 200) * P.lgn ^ 14 * (T.recursiveCount : ℝ) := by
  intro h
  induction h with
  | zero =>
      intro N X Y hargs hρ
      by_cases hr : P.rule N X Y = .recursive
      · exfalso
        have hL1 : (1 : ℝ) ≤ P.lgn := by
          have := hargs.1
          linarith [one_le_lgn (P := P) this]
        have hε : (2 * P.lgn ^ 13)⁻¹ < nodeDens N Y := by
          have h := dens_gt hargs hL1 hr
          unfold densFloor at h
          exact h
        have h2 : (4 : ℝ) ^ 0 * (2 * P.lgn ^ 13)⁻¹ = (2 * P.lgn ^ 13)⁻¹ := by norm_num
        rw [h2] at hρ
        linarith [hε, hρ]
      · obtain ⟨T, hT, hd, hm, hrc, hnc⟩ := tree_of_not_recursive (P := P) (N := N) (X := X)
          (Y := Y) (fuel := 1) hr (le_refl 1)
        refine ⟨T, hT, ?_, ?_, ?_, ?_⟩
        · rw [hd]; push_cast; linarith
        · rw [hm]; have h := nodeDens_nonneg N Y; linarith
        · rw [hrc, hm]; simp
        · rw [hnc, hrc]; push_cast; simp
  | succ h ih =>
      intro N X Y hargs hρ
      by_cases hr : P.rule N X Y = .recursive
      · -- ## the recursive case
        have hargs' := hargs
        obtain ⟨hn2, hlam1, hN1, hNn, hXN, hYN⟩ := hargs'
        have hL1 : (1 : ℝ) ≤ P.lgn := by linarith
        have hlgn : (0 : ℝ) < P.lgn := by linarith
        have hrows := rows_eq_of_rule hr
        have hY1 : 1 ≤ Y := Y_ge_one hargs hL1 hr
        have hYposR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY1
        have hYne : (Y : ℝ) ≠ 0 := ne_of_gt hYposR
        have hρ0 : 0 ≤ nodeDens N Y := nodeDens_nonneg N Y
        have hcontr := capY_sum_le (P := P) hargs hL hA hC hr
        have hsum : ∑ s : Fin (P.ell N X Y), (P.capY N X Y s.val : ℝ)
            ≤ nodeDens N Y * (Y : ℝ) / 4 := by
          rw [Fin.sum_univ_eq_sum_range (fun s => (P.capY N X Y s : ℝ)) (P.ell N X Y)]
          exact hcontr
        have hchild : ∀ s : Fin (P.ell N X Y),
            (P.capY N X Y s.val : ℝ) ≤ nodeDens N Y * (Y : ℝ) / 4 := by
          intro s
          have h1 : (P.capY N X Y s.val : ℝ)
              ≤ ∑ t : Fin (P.ell N X Y), (P.capY N X Y t.val : ℝ) :=
            Finset.single_le_sum (f := fun t : Fin (P.ell N X Y) => (P.capY N X Y t.val : ℝ))
              (fun i _ => Nat.cast_nonneg _) (Finset.mem_univ s)
          linarith
        have hchilddens : ∀ s : Fin (P.ell N X Y),
            nodeDens Y (P.capY N X Y s.val) ≤ 4 ^ h * (2 * P.lgn ^ 13)⁻¹ := by
          intro s
          have h2 : nodeDens Y (P.capY N X Y s.val) ≤ nodeDens N Y / 4 := by
            have h4 : nodeDens Y (P.capY N X Y s.val) = (P.capY N X Y s.val : ℝ) / (Y : ℝ) := rfl
            rw [h4, div_le_iff₀ hYposR]
            have h5 := hchild s
            nlinarith [h5]
          have h3 : nodeDens N Y / 4 ≤ 4 ^ h * (2 * P.lgn ^ 13)⁻¹ := by
            rw [pow_succ] at hρ
            nlinarith [hρ]
          linarith
        have hcapX : ∀ s : Fin (P.ell N X Y), P.capX N X Y s.val ≤ Y := by
          intro s; unfold HintParams.capX; exact min_le_left _ _
        have hcapY : ∀ s : Fin (P.ell N X Y), P.capY N X Y s.val ≤ Y := by
          intro s; unfold HintParams.capY; exact min_le_left _ _
        have hex : ∀ s : Fin (P.ell N X Y), ∃ T : Node,
            P.tree (h + 1) Y (P.capX N X Y s.val) (P.capY N X Y s.val) = some T ∧
              (T.depth : ℝ) ≤ (h : ℝ) + 1 ∧
              massAt T Y (P.capY N X Y s.val) ≤ 2 * nodeDens Y (P.capY N X Y s.val) ∧
              (2 * P.lgn ^ 13)⁻¹ * (T.recursiveCount : ℝ) ≤ massAt T Y (P.capY N X Y s.val) ∧
              (T.nodeCount : ℝ) ≤
                1 + (4 * (P.A : ℝ) + 200) * P.lgn ^ 14 * (T.recursiveCount : ℝ) := by
          intro s
          exact ih Y (P.capX N X Y s.val) (P.capY N X Y s.val)
            ⟨hn2, hlam1, hY1, le_trans hYN hNn, hcapX s, hcapY s⟩ (hchilddens s)
        choose Tfun hTtree hTdepth hTmass hTrc hTnc using hex
        obtain ⟨g, hg⟩ := allSome_eq_some (f := fun s : Fin (P.ell N X Y) =>
            P.tree (h + 1) Y (P.capX N X Y s.val) (P.capY N X Y s.val))
          (fun s => ⟨Tfun s, hTtree s⟩)
        have hgs : ∀ s : Fin (P.ell N X Y), g s = Tfun s := by
          intro s
          have h1 := allSome_spec hg s
          rw [hTtree s] at h1
          exact (Option.some.inj h1).symm
        refine ⟨Node.recursive (P.scheme N X Y) (P.resid N X Y) (fun s => P.capX N X Y s.val)
          (fun s => P.capY N X Y s.val) g, ?_, ?_, ?_, ?_, ?_⟩
        · rw [HintParams.tree, hr, hg]
          rfl
        · -- depth
          have hsup : (Finset.univ.sup fun s : Fin (P.ell N X Y) => (g s).depth) ≤ h + 1 := by
            apply Finset.sup_le
            intro s _
            have h1 : ((Tfun s).depth : ℝ) ≤ (h : ℝ) + 1 := hTdepth s
            have h2 : (Tfun s).depth ≤ h + 1 := by exact_mod_cast h1
            rw [hgs s]
            exact h2
          have hdepth : (Node.recursive (P.scheme N X Y) (P.resid N X Y)
              (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) g).depth
              = 1 + (Finset.univ.sup fun s : Fin (P.ell N X Y) => (g s).depth) := rfl
          rw [hdepth]
          have hnat : 1 + (Finset.univ.sup fun s : Fin (P.ell N X Y) => (g s).depth) ≤ h + 1 + 1 := by
            omega
          have hcast : ((1 + (Finset.univ.sup fun s : Fin (P.ell N X Y) => (g s).depth) : ℕ) : ℝ)
              ≤ ((h + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
          have htarget : ((h + 1 + 1 : ℕ) : ℝ) = ((h + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
          linarith [hcast, htarget]
        · -- mass
          have hmass : massAt (Node.recursive (P.scheme N X Y) (P.resid N X Y)
              (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) g) N Y
              = nodeDens N Y + ∑ s : Fin (P.ell N X Y), massAt (g s) Y (P.capY N X Y s.val) := by
            show nodeDens N Y + ∑ s : Fin (P.ell N X Y),
              massAt (g s) (P.rows X Y) (P.capY N X Y s.val) = _
            rw [hrows]
          rw [hmass]
          have h1 : ∑ s : Fin (P.ell N X Y), massAt (g s) Y (P.capY N X Y s.val)
              ≤ 2 * (∑ s : Fin (P.ell N X Y), (P.capY N X Y s.val : ℝ)) / (Y : ℝ) := by
            have h2 : ∑ s : Fin (P.ell N X Y), massAt (g s) Y (P.capY N X Y s.val)
                ≤ ∑ s : Fin (P.ell N X Y), 2 * nodeDens Y (P.capY N X Y s.val) := by
              apply Finset.sum_le_sum
              intro s _
              have h3 : massAt (Tfun s) Y (P.capY N X Y s.val)
                  ≤ 2 * nodeDens Y (P.capY N X Y s.val) := hTmass s
              rw [hgs s]
              exact h3
            have h3 : ∑ s : Fin (P.ell N X Y), 2 * nodeDens Y (P.capY N X Y s.val)
                = 2 * (∑ s : Fin (P.ell N X Y), (P.capY N X Y s.val : ℝ)) / (Y : ℝ) := by
              calc ∑ s : Fin (P.ell N X Y), 2 * nodeDens Y (P.capY N X Y s.val)
                  = ∑ s : Fin (P.ell N X Y), 2 * ((P.capY N X Y s.val : ℝ) / (Y : ℝ)) :=
                    Finset.sum_congr rfl (fun s _ => by rw [show nodeDens Y (P.capY N X Y s.val)
                      = (P.capY N X Y s.val : ℝ) / (Y : ℝ) from rfl])
                _ = 2 * (∑ s : Fin (P.ell N X Y), ((P.capY N X Y s.val : ℝ) / (Y : ℝ))) :=
                    (Finset.mul_sum (Finset.univ : Finset (Fin (P.ell N X Y))) _ 2).symm
                _ = 2 * ((∑ s : Fin (P.ell N X Y), (P.capY N X Y s.val : ℝ)) / (Y : ℝ)) := by
                    rw [Finset.sum_div]
                _ = 2 * (∑ s : Fin (P.ell N X Y), (P.capY N X Y s.val : ℝ)) / (Y : ℝ) := by ring
            linarith [h2, h3]
          have h4 : 2 * (∑ s : Fin (P.ell N X Y), (P.capY N X Y s.val : ℝ)) / (Y : ℝ)
              ≤ nodeDens N Y / 2 := by
            rw [div_le_iff₀ hYposR]
            nlinarith [hsum, hρ0]
          linarith [h1, h4, hρ0]
        · -- recursive count
          have hε : (2 * P.lgn ^ 13)⁻¹ ≤ nodeDens N Y := by
            have hh := dens_gt hargs hL1 hr
            unfold densFloor at hh
            rw [inv_eq_one_div] at hh
            rw [inv_eq_one_div]
            exact le_of_lt hh
          have hmass : massAt (Node.recursive (P.scheme N X Y) (P.resid N X Y)
              (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) g) N Y
              = nodeDens N Y + ∑ s : Fin (P.ell N X Y), massAt (g s) Y (P.capY N X Y s.val) := by
            show nodeDens N Y + ∑ s : Fin (P.ell N X Y),
              massAt (g s) (P.rows X Y) (P.capY N X Y s.val) = _
            rw [hrows]
          have hrc : (Node.recursive (P.scheme N X Y) (P.resid N X Y)
              (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) g).recursiveCount
              = 1 + ∑ s : Fin (P.ell N X Y), (g s).recursiveCount := rfl
          have h1 : (2 * P.lgn ^ 13)⁻¹ * (∑ s : Fin (P.ell N X Y), ((g s).recursiveCount : ℝ))
              ≤ ∑ s : Fin (P.ell N X Y), massAt (g s) Y (P.capY N X Y s.val) := by
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro s _
            have h3 : (2 * P.lgn ^ 13)⁻¹ * ((Tfun s).recursiveCount : ℝ)
                ≤ massAt (Tfun s) Y (P.capY N X Y s.val) := hTrc s
            rw [hgs s]
            exact h3
          rw [hrc, hmass]
          push_cast
          have hε0 : (0 : ℝ) ≤ (2 * P.lgn ^ 13)⁻¹ := by positivity
          linarith [h1, hε, hε0]
        · -- node count
          have hrc : (Node.recursive (P.scheme N X Y) (P.resid N X Y)
              (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) g).recursiveCount
              = 1 + ∑ s : Fin (P.ell N X Y), (g s).recursiveCount := rfl
          have hnc : (Node.recursive (P.scheme N X Y) (P.resid N X Y)
              (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) g).nodeCount
              = 1 + ∑ s : Fin (P.ell N X Y), (g s).nodeCount := rfl
          have hellb : (P.ell N X Y : ℝ) ≤ (4 * (P.A : ℝ) + 200) * P.lgn ^ 14 :=
            ell_le hargs hL hr
          have h1 : ∑ s : Fin (P.ell N X Y), ((g s).nodeCount : ℝ)
              ≤ ∑ s : Fin (P.ell N X Y),
                (1 + ((4 * (P.A : ℝ) + 200) * P.lgn ^ 14) * ((g s).recursiveCount : ℝ)) := by
            apply Finset.sum_le_sum
            intro s _
            have h3 : ((Tfun s).nodeCount : ℝ) ≤
                1 + (4 * (P.A : ℝ) + 200) * P.lgn ^ 14 * ((Tfun s).recursiveCount : ℝ) := hTnc s
            rw [hgs s]
            exact h3
          have h2 : ∑ s : Fin (P.ell N X Y),
                (1 + ((4 * (P.A : ℝ) + 200) * P.lgn ^ 14) * ((g s).recursiveCount : ℝ))
              = (P.ell N X Y : ℝ) + ((4 * (P.A : ℝ) + 200) * P.lgn ^ 14)
                * (∑ s : Fin (P.ell N X Y), ((g s).recursiveCount : ℝ)) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, Finset.mul_sum]
            ring
          rw [hnc, hrc]
          push_cast
          have hK0 : (0 : ℝ) ≤ (4 * (P.A : ℝ) + 200) * P.lgn ^ 14 := by positivity
          linarith [h1, h2, hellb, hK0]
      · -- ## non-recursive: a leaf
        obtain ⟨T, hT, hd, hm, hrc, hnc⟩ := tree_of_not_recursive (P := P) (N := N) (X := X)
          (Y := Y) (fuel := h + 1 + 1) hr (by omega)
        refine ⟨T, hT, ?_, ?_, ?_, ?_⟩
        · rw [hd]; push_cast; linarith
        · rw [hm]; have h := nodeDens_nonneg N Y; linarith
        · rw [hrc, hm]; simp
        · rw [hnc, hrc]; push_cast; simp

/-- Termination at the root: `⌈log(2 log¹³ n)⌉ + 1` levels always suffice. -/
theorem tree_exists_root {P : HintParams} {N X Y : ℕ} (hA : 100 ≤ P.A) (hC : 40 ≤ P.C)
    (hL : 2 ≤ P.lgn) (hargs : P.NodeArgs N X Y) :
    ∃ T : Node, P.tree (⌈lg (2 * P.lgn ^ 13)⌉₊ + 1) N X Y = some T ∧
      (T.depth : ℝ) ≤ (⌈lg (2 * P.lgn ^ 13)⌉₊ : ℝ) + 1 ∧
      massAt T N Y ≤ 2 * nodeDens N Y ∧
      (T.recursiveCount : ℝ) ≤ 4 * P.lgn ^ 13 ∧
      (T.nodeCount : ℝ) ≤ 40 * (P.A : ℝ) * P.lgn ^ 27 := by
  have hL1 : (1 : ℝ) ≤ P.lgn := by linarith
  have hlgn : (0 : ℝ) < P.lgn := by linarith
  have hN1 : 1 ≤ N := hargs.2.2.1
  have hYN : Y ≤ N := hargs.2.2.2.2.2
  -- `4^h · ε ≥ 1 ≥ ρ`
  have key : 2 * P.lgn ^ 13 ≤ (4 : ℝ) ^ (⌈lg (2 * P.lgn ^ 13)⌉₊) := by
    have hx : (0 : ℝ) < 2 * P.lgn ^ 13 := by positivity
    have h1 : 2 * P.lgn ^ 13 ≤ (2 : ℝ) ^ (⌈lg (2 * P.lgn ^ 13)⌉₊) := by
      have hstep : Real.logb 2 (2 * P.lgn ^ 13) ≤ ((⌈lg (2 * P.lgn ^ 13)⌉₊ : ℕ) : ℝ) := by
        rw [show lg (2 * P.lgn ^ 13) = Real.logb 2 (2 * P.lgn ^ 13) from rfl]
        exact Nat.le_ceil _
      have h2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hstep
      have hlogb : (2 : ℝ) ^ (Real.logb 2 (2 * P.lgn ^ 13)) = 2 * P.lgn ^ 13 :=
        Real.rpow_logb (b := 2) (x := 2 * P.lgn ^ 13) (by norm_num) (by norm_num) hx
      rw [hlogb, Real.rpow_natCast] at h2
      exact h2
    have h2 : (2 : ℝ) ^ (⌈lg (2 * P.lgn ^ 13)⌉₊)
        ≤ (2 : ℝ) ^ (2 * ⌈lg (2 * P.lgn ^ 13)⌉₊) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have h3 : (4 : ℝ) ^ (⌈lg (2 * P.lgn ^ 13)⌉₊)
        = (2 : ℝ) ^ (2 * ⌈lg (2 * P.lgn ^ 13)⌉₊) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]
    rw [h3]
    linarith [h1, h2]
  have h4 : (1 : ℝ) ≤ 4 ^ (⌈lg (2 * P.lgn ^ 13)⌉₊) * (2 * P.lgn ^ 13)⁻¹ := by
    have hx : (0 : ℝ) < 2 * P.lgn ^ 13 := by positivity
    have h6 : (2 * P.lgn ^ 13) * (2 * P.lgn ^ 13)⁻¹
        ≤ (4 : ℝ) ^ (⌈lg (2 * P.lgn ^ 13)⌉₊) * (2 * P.lgn ^ 13)⁻¹ :=
      mul_le_mul_of_nonneg_right key (by positivity)
    rwa [mul_inv_cancel₀ (ne_of_gt hx)] at h6
  have hρ : nodeDens N Y ≤ 4 ^ (⌈lg (2 * P.lgn ^ 13)⌉₊) * (2 * P.lgn ^ 13)⁻¹ := by
    have h1 : nodeDens N Y ≤ 1 := nodeDens_le_one hN1 hYN
    linarith [h1, h4]
  obtain ⟨T, hT, hdepth, hmass, hrc, hnc⟩ :=
    tree_exists_aux (P := P) hA hC hL (⌈lg (2 * P.lgn ^ 13)⌉₊) N X Y hargs hρ
  have hρ1 : nodeDens N Y ≤ 1 := nodeDens_le_one hN1 hYN
  have hε : (0 : ℝ) < (2 * P.lgn ^ 13)⁻¹ := by positivity
  have hrc2 : (T.recursiveCount : ℝ) ≤ 4 * P.lgn ^ 13 := by
    have h1 : (T.recursiveCount : ℝ) * (2 * P.lgn ^ 13)⁻¹ ≤ 2 := by
      linarith [hrc, hmass, hρ1]
    have h2 : (T.recursiveCount : ℝ) ≤ 2 / (2 * P.lgn ^ 13)⁻¹ := by
      rw [le_div_iff₀ hε]
      linarith [h1]
    have h3 : (2 : ℝ) / (2 * P.lgn ^ 13)⁻¹ = 4 * P.lgn ^ 13 := by
      field_simp
      ring
    linarith [h2, h3]
  have hnc2 : (T.nodeCount : ℝ) ≤ 40 * (P.A : ℝ) * P.lgn ^ 27 := by
    have hKA : (4 * (P.A : ℝ) + 200) * P.lgn ^ 14 * (T.recursiveCount : ℝ)
        ≤ (4 * (P.A : ℝ) + 200) * P.lgn ^ 14 * (4 * P.lgn ^ 13) := by
      have h1 : (0 : ℝ) ≤ (4 * (P.A : ℝ) + 200) * P.lgn ^ 14 := by positivity
      nlinarith [hrc2, h1]
    have hid : (4 * (P.A : ℝ) + 200) * P.lgn ^ 14 * (4 * P.lgn ^ 13)
        = (16 * (P.A : ℝ) + 800) * P.lgn ^ 27 := by
      have hpw : P.lgn ^ 14 * P.lgn ^ 13 = P.lgn ^ 27 := by rw [← pow_add]
      rw [← hpw]
      ring
    have hA1 : (100 : ℝ) ≤ (P.A : ℝ) := by exact_mod_cast hA
    have hL27 : (1 : ℝ) ≤ P.lgn ^ 27 := one_le_pow₀ hL1
    have hfin : (1 : ℝ) ≤ (24 * (P.A : ℝ) - 800) * P.lgn ^ 27 := by
      have h24 : (1 : ℝ) ≤ 24 * (P.A : ℝ) - 800 := by linarith
      nlinarith [h24, hL27]
    nlinarith [hnc, hKA, hid, hfin]
  exact ⟨T, hT, hdepth, hmass, hrc2, hnc2⟩

/-- Lemma 5.10 (Size and depth of the recursion), PDF p.25 (printed p.24). The recursion terminates
within the stated number of levels, which is part of the conclusion. -/
theorem lemma_5_10 :
    ∃ K : ℝ, 0 < K ∧ ∃ A₀ : ℕ, ∀ A ≥ A₀, ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ (n lam N X Y : ℕ),
      let P : HintParams := ⟨A, C, n, lam⟩
      P.NodeArgs N X Y →
      ∃ (fuel : ℕ) (T : Node), P.tree fuel N X Y = some T ∧
        (fuel : ℝ) ≤ K * (lg (lg n) + 1) ∧
        (T.depth : ℝ) ≤ K * (lg (lg n) + 1) ∧
        (T.recursiveCount : ℝ) ≤ K * lg n ^ 13 ∧
        (T.nodeCount : ℝ) ≤ K * (A : ℝ) * lg n ^ 27 := by
  refine ⟨40, by norm_num, 100, fun A hA => ⟨40, fun C hC => ?_⟩⟩
  intro n lam N X Y P hargs
  have hA100 : 100 ≤ P.A := hA
  have hC40 : 40 ≤ P.C := hC
  have hn2 : 2 ≤ P.n := hargs.1
  by_cases hL : 2 ≤ P.lgn
  · -- ## main case: `log n ≥ 2`
    obtain ⟨T, hT, hdepth, hmass, hrc, hnc⟩ := tree_exists_root hA100 hC40 hL hargs
    have hL1 : (1 : ℝ) ≤ P.lgn := by linarith
    have hlgn : (0 : ℝ) < P.lgn := by linarith
    have hlg0 : (0 : ℝ) ≤ lg (lg (n : ℝ)) := lg_nonneg_of_one_le (one_le_lgn hn2)
    have hval : lg (2 * P.lgn ^ 13) = 1 + 13 * lg (lg (n : ℝ)) := by
      rw [lg_mul_pos (by norm_num : (0 : ℝ) < 2) (by positivity : (0 : ℝ) < P.lgn ^ 13)]
      rw [lg_pow_pos hlgn]
      rw [lg_two]
      have h2 : lg P.lgn = lg (lg (n : ℝ)) := rfl
      rw [h2]
      push_cast
      ring
    have hceil : ((⌈lg (2 * P.lgn ^ 13)⌉₊ : ℕ) : ℝ) ≤ lg (2 * P.lgn ^ 13) + 1 := by
      have hx : (0 : ℝ) ≤ lg (2 * P.lgn ^ 13) := by
        apply lg_nonneg_of_one_le
        have h13 : (1 : ℝ) ≤ P.lgn ^ 13 := one_le_pow₀ hL1
        nlinarith
      have h := Nat.ceil_lt_add_one hx
      linarith
    refine ⟨⌈lg (2 * P.lgn ^ 13)⌉₊ + 1, T, hT, ?_, ?_, ?_, ?_⟩
    · rw [Nat.cast_add, Nat.cast_one]
      linarith [hceil, hval, hlg0]
    · linarith [hdepth, hceil, hval, hlg0]
    · have hlg_eq : P.lgn = lg (n : ℝ) := rfl
      rw [hlg_eq] at hrc
      linarith [hrc]
    · have hPA : P.A = A := rfl
      have hlg_eq : P.lgn = lg (n : ℝ) := rfl
      rw [hPA, hlg_eq] at hnc
      linarith [hnc]
  · -- ## small case: `log n < 2`, hence no recursive node
    push_neg at hL
    have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lgn hn2
    have hlgn : (0 : ℝ) < P.lgn := by linarith
    have hlg_eq' : P.lgn = lg (n : ℝ) := rfl
    have hlg0 : (0 : ℝ) ≤ lg (lg (n : ℝ)) := lg_nonneg_of_one_le (one_le_lgn hn2)
    have hNr : P.rule N X Y ≠ .recursive := by
      intro hr
      have hNth := Nthresh_le_N (P := P) hL1 hr
      have h1 : (4 : ℝ) ≤ (P.C : ℝ) ^ 4 * P.lgn ^ (6 + 2 * P.A) := by
        have h2 : (4 : ℝ) ≤ (P.C : ℝ) ^ 4 := by
          have h3 : (4 : ℝ) ≤ (P.C : ℝ) := by exact_mod_cast (by omega : 4 ≤ P.C)
          nlinarith [sq_nonneg ((P.C : ℝ) - 4)]
        have h4 : (1 : ℝ) ≤ P.lgn ^ (6 + 2 * P.A) := one_le_pow₀ hL1
        nlinarith [h2, h4]
      have h5 : (N : ℝ) ≤ (P.n : ℝ) := by exact_mod_cast hargs.2.2.2.1
      have hnpos : (0 : ℝ) < (P.n : ℝ) := by
        have : 0 < P.n := by omega
        exact_mod_cast this
      have h6 : (P.n : ℝ) = (2 : ℝ) ^ P.lgn := by
        show (P.n : ℝ) = (2 : ℝ) ^ lg (P.n : ℝ)
        exact (Real.rpow_logb (b := 2) (x := (P.n : ℝ)) (by norm_num) (by norm_num) hnpos).symm
      have h7 : (2 : ℝ) ^ P.lgn ≤ 4 := by
        have h8 : (2 : ℝ) ^ P.lgn ≤ (2 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt hL)
        norm_num at h8
        linarith [h8]
      linarith [hNth, h1, h5, h6, h7]
    obtain ⟨T, hT, hd, hm, hrc, hnc⟩ := tree_of_not_recursive (P := P) (N := N) (X := X)
      (Y := Y) (fuel := 1) hNr (le_refl 1)
    have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast (by omega : 1 ≤ A)
    have hL27 : (0 : ℝ) ≤ P.lgn ^ 27 := by positivity
    refine ⟨1, T, hT, ?_, ?_, ?_, ?_⟩
    · push_cast
      nlinarith [hlg0]
    · rw [hd]
      push_cast
      nlinarith [hlg0]
    · rw [hrc]
      push_cast
      have h1 : (1 : ℝ) ≤ lg (n : ℝ) := by rw [← hlg_eq']; linarith
      have h2 : (1 : ℝ) ≤ (lg (n : ℝ)) ^ 13 := one_le_pow₀ h1
      nlinarith [h2]
    · rw [hnc]
      push_cast
      have h1 : (1 : ℝ) ≤ lg (n : ℝ) := by rw [← hlg_eq']; linarith
      have h2 : (1 : ℝ) ≤ (lg (n : ℝ)) ^ 27 := one_le_pow₀ h1
      nlinarith [h2, hA1]

end LinearSetReconciliation327.Main.HintUpstream510

#print axioms LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10


