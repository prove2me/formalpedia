-- Prove2me | Definitions.Def_DetDLP_W5_M6DriverFrames
-- name    : DetDLP_W5_M6DriverFrames
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T00:25:24.990188+00:00
-- url     : https://prove2.me/theorems/ecaf789b-96e7-4c68-868f-02da528aa012
-- title:
--   M6 Driver Frames
-- statement:
--   A valid divisor split preserves the product and bounds both children by half the parent. These estimates control the factor tree and the tape frames representing its suspended branches.

import Definitions.Def_DetDLP_W5_M6NodeInterface
import Definitions.Def_DetDLP_M89_CompileSpace

set_option autoImplicit false
set_option linter.unusedSimpArgs false
section
set_option autoImplicit false

namespace DetDLP
namespace w5_SplitArithmetic

/-- The exact depth-limited recursion used by `factor_splitting_driver_machine`. -/
def split (f : ℕ → ℕ) : ℕ → ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun x => [x]) (fun _ prev x =>
    let d := f x
    if 2 ≤ d ∧ d < x ∧ d ∣ x then prev d ++ prev (x / d) else [x])

/-- A valid split has two factors at least two, each at most half the parent. -/
theorem proper_divisor_bounds {x d : ℕ}
    (h : 2 ≤ d ∧ d < x ∧ d ∣ x) :
    2 ≤ x / d ∧ 2 * d ≤ x ∧ 2 * (x / d) ≤ x := by
  have heq : d * (x / d) = x := Nat.mul_div_cancel' h.2.2
  have hq : 2 ≤ x / d := by
    by_contra hq
    have hq' : x / d ≤ 1 := by omega
    have hle : d * (x / d) ≤ d := by nlinarith
    omega
  refine ⟨hq, ?_, ?_⟩ <;> nlinarith [h.1]

@[simp] theorem split_zero (f : ℕ → ℕ) (x : ℕ) : split f 0 x = [x] := rfl

@[simp] theorem split_succ (f : ℕ → ℕ) (n x : ℕ) :
    split f (n + 1) x =
      if 2 ≤ f x ∧ f x < x ∧ f x ∣ x then
        split f n (f x) ++ split f n (x / f x)
      else [x] := rfl

/-- Splitting preserves the product, even if `f` returns an invalid divisor. -/
theorem prod_split (f : ℕ → ℕ) (n x : ℕ) : (split f n x).prod = x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [split_succ]
    split_ifs with h
    · rw [List.prod_append, ih, ih]
      exact Nat.mul_div_cancel' h.2.2
    · simp

/-- Every returned factor is at least two and at most the original input. -/
theorem mem_split_bounds (f : ℕ → ℕ) (n x : ℕ) (hx : 2 ≤ x) :
    ∀ a ∈ split f n x, 2 ≤ a ∧ a ≤ x := by
  induction n generalizing x with
  | zero => simpa using hx
  | succ n ih =>
    rw [split_succ]
    split_ifs with h
    · have hq := proper_divisor_bounds h
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨ha2, hax⟩ := ih (f x) h.1 a ha
        exact ⟨ha2, hax.trans h.2.1.le⟩
      · obtain ⟨ha2, hax⟩ := ih (x / f x) hq.1 a ha
        exact ⟨ha2, hax.trans (Nat.div_le_self x (f x))⟩
    · simpa using hx

/-- The product of a list whose entries are at least two controls its length. -/
theorem two_pow_length_le_prod (xs : List ℕ) (h : ∀ a ∈ xs, 2 ≤ a) :
    2 ^ xs.length ≤ xs.prod := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha : 2 ≤ a := h a (by simp)
    have ht : 2 ^ xs.length ≤ xs.prod := ih (fun b hb => h b (by simp [hb]))
    simpa [pow_succ, Nat.mul_comm] using Nat.mul_le_mul ha ht

/-- The leaf count is logarithmic for every oracle, including unsuccessful ones. -/
theorem length_split_le_log (f : ℕ → ℕ) (n x : ℕ) (hx : 2 ≤ x) :
    (split f n x).length ≤ Nat.log 2 x := by
  apply Nat.le_log_of_pow_le (by norm_num)
  have h := two_pow_length_le_prod (split f n x)
    (fun a ha => (mem_split_bounds f n x hx a ha).1)
  simpa only [prod_split] using h

/-- The leaf count is bounded by the input bit length used in the target. -/
theorem length_split_le_bitLen (f : ℕ → ℕ) (n x : ℕ) (hx : 2 ≤ x) :
    (split f n x).length ≤ bitLen (x + 1) := by
  exact (length_split_le_log f n x hx).trans
    ((Nat.log_le_clog 2 x).trans (Nat.clog_mono_right 2 (by omega)))

/-- The sequence of all recursion inputs, including the depth-zero leaves. -/
def calls (f : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | 0, x => [x]
  | n + 1, x =>
    if 2 ≤ f x ∧ f x < x ∧ f x ∣ x then
      x :: (calls f n (f x) ++ calls f n (x / f x))
    else [x]

/-- The recursion tree is a full binary tree. -/
theorem length_calls_add_one (f : ℕ → ℕ) (n x : ℕ) :
    (calls f n x).length + 1 = 2 * (split f n x).length := by
  induction n generalizing x with
  | zero => simp [calls]
  | succ n ih =>
    simp only [calls, split_succ]
    split_ifs with h
    · simp only [List.length_cons, List.length_append]
      have hd := ih (f x)
      have hq := ih (x / f x)
      omega
    · simp

/-- All recursive inputs are between two and the root input. -/
theorem mem_calls_bounds (f : ℕ → ℕ) (n x : ℕ) (hx : 2 ≤ x) :
    ∀ a ∈ calls f n x, 2 ≤ a ∧ a ≤ x := by
  induction n generalizing x with
  | zero => simpa [calls] using hx
  | succ n ih =>
    simp only [calls]
    split_ifs with h
    · have hq := proper_divisor_bounds h
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨hx, le_rfl⟩
      · rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨ha2, hax⟩ := ih (f x) h.1 a ha
          exact ⟨ha2, hax.trans h.2.1.le⟩
        · obtain ⟨ha2, hax⟩ := ih (x / f x) hq.1 a ha
          exact ⟨ha2, hax.trans (Nat.div_le_self x (f x))⟩
    · simpa using hx

/-- At most twice the input bit length many recursive invocations occur. -/
theorem length_calls_lt_two_bitLen (f : ℕ → ℕ) (n x : ℕ) (hx : 2 ≤ x) :
    (calls f n x).length < 2 * bitLen (x + 1) := by
  have heq := length_calls_add_one f n x
  have hle := length_split_le_bitLen f n x hx
  omega

/-- Recursive inputs have no larger bit length than the root. -/
theorem mem_calls_bitLen_le (f : ℕ → ℕ) (n x : ℕ) (hx : 2 ≤ x)
    (a : ℕ) (ha : a ∈ calls f n x) :
    bitLen (a + 1) ≤ bitLen (x + 1) := by
  apply Nat.clog_mono_right
  have hle := (mem_calls_bounds f n x hx a ha).2
  omega

/-- Mathlib's size function agrees with the bit length used by the driver. -/
theorem size_eq_bitLen (x : ℕ) : x.size = bitLen (x + 1) := by
  apply le_antisymm
  · apply Nat.size_le.mpr
    have h : x + 1 ≤ 2 ^ bitLen (x + 1) :=
      Nat.le_pow_clog (by norm_num : 1 < 2) (x + 1)
    omega
  · apply (Nat.clog_le_iff_le_pow (by norm_num)).mpr
    exact Nat.succ_le_of_lt (Nat.lt_size_self x)

/-- Every positive recursive input uses at most the original number of binary cells. -/
theorem countWord_length_eq_bitLen (x : ℕ) (hx : 0 < x) :
    (OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord x).length =
      bitLen (x + 1) := by
  simp only [OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord,
    if_neg (Nat.ne_of_gt hx)]
  exact (Nat.size_eq_bits_len x).trans (size_eq_bitLen x)

/-- Framing a word contributes exactly two bits per input bit and one terminator. -/
theorem length_frame (w : List Bool) :
    (OAI.Algorithms.SubexponentialSAT.Encoding.frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => simp [OAI.Algorithms.SubexponentialSAT.Encoding.frame]
  | cons b w ih =>
    simp only [OAI.Algorithms.SubexponentialSAT.Encoding.frame, List.foldr_cons,
      List.length_cons] at *
    omega

/-- A generic bound for the target's list encoding. -/
theorem length_encodeList_le {α : Type*} (enc : α → List Bool) (xs : List α)
    (b : ℕ) (h : ∀ x ∈ xs, (enc x).length ≤ b) :
    (OAI.Algorithms.SubexponentialSAT.Encoding.encodeList enc xs).length ≤
      (2 * b + 2) * xs.length + 1 := by
  induction xs with
  | nil => simp [OAI.Algorithms.SubexponentialSAT.Encoding.encodeList]
  | cons x xs ih =>
    have hh := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [OAI.Algorithms.SubexponentialSAT.Encoding.encodeList, List.length_cons,
      List.length_append, length_frame]
    nlinarith

/-- Any intermediate integer has a binary encoding bounded by the root bit length. -/
theorem countWord_length_le_bitLen {a x : ℕ} (ha : 0 < a) (hax : a ≤ x) :
    (OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord a).length ≤
      bitLen (x + 1) := by
  rw [countWord_length_eq_bitLen a ha]
  apply Nat.clog_mono_right
  omega

/-- The entire recursion-call log would fit in quadratic space. -/
theorem length_encode_calls_le (f : ℕ → ℕ) (n x : ℕ) (hx : 2 ≤ x) :
    (encodeNatListBin (calls f n x)).length ≤
      (2 * bitLen (x + 1) + 2) * (2 * bitLen (x + 1)) + 1 := by
  have hwords : ∀ a ∈ calls f n x,
      (OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord a).length ≤
        bitLen (x + 1) := by
    intro a ha
    obtain ⟨ha2, hax⟩ := mem_calls_bounds f n x hx a ha
    exact countWord_length_le_bitLen (by omega) hax
  have hlen := length_encodeList_le
    OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord
    (calls f n x) (bitLen (x + 1)) hwords
  have hcalls := length_calls_lt_two_bitLen f n x hx
  dsimp [encodeNatListBin]
  exact hlen.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hcalls.le) 1)

/-- The sorted output occupies only quadratic space, for every oracle. -/
theorem length_encode_split_le (f : ℕ → ℕ) (n x : ℕ) (hx : 2 ≤ x) :
    (encodeNatListBin ((split f n x).mergeSort)).length ≤
      (2 * bitLen (x + 1) + 2) * bitLen (x + 1) + 1 := by
  have hp := List.mergeSort_perm (split f n x) (· ≤ ·)
  have hwords : ∀ a ∈ (split f n x).mergeSort,
      (OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord a).length ≤
        bitLen (x + 1) := by
    intro a ha
    obtain ⟨ha2, hax⟩ := mem_split_bounds f n x hx a (hp.mem_iff.mp ha)
    exact countWord_length_le_bitLen (by omega) hax
  have hlen := length_encodeList_le
    OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord
    ((split f n x).mergeSort) (bitLen (x + 1)) hwords
  rw [hp.length_eq] at hlen
  exact hlen.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left _ (length_split_le_bitLen f n x hx)) 1)


end w5_SplitArithmetic
end DetDLP
end

section
set_option autoImplicit false

namespace DetDLP

/-- The safe logarithm agrees with the usual base-two logarithm above two. -/
theorem w5_logSafe_eq_logb {x : ℝ} (hx : 2 ≤ x) : logSafe x = Real.logb 2 x := by
  have hlog : 1 ≤ Real.logb 2 x := by
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2) hx
  simp only [logSafe, max_eq_right hx, max_eq_right hlog]

/-- A useful elementary logarithm bound, avoiding differentiation in rate comparisons. -/
theorem w5_half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h ⊢
  exact h

/-- `log y / y²` is decreasing for `2 ≤ x ≤ y`, in cross-multiplied form. -/
theorem w5_log_mul_sq_le {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    Real.log y * x ^ 2 ≤ Real.log x * y ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hlx : (1 / 2 : ℝ) ≤ Real.log x :=
    w5_half_le_log_two.trans (Real.log_le_log (by norm_num) hx)
  let t := y / x
  have ht1 : 1 ≤ t := (le_div_iff₀ hx0).mpr (by simpa using hxy)
  have hlt : Real.log y - Real.log x ≤ t - 1 := by
    rw [← Real.log_div (ne_of_gt hy0) (ne_of_gt hx0)]
    exact Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
  have hsq : 0 ≤ t ^ 2 - 1 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hlx hsq
  have hlog : Real.log y ≤ Real.log x * t ^ 2 := by
    nlinarith [sq_nonneg (t - 1)]
  have htx : t * x = y := div_mul_cancel₀ y (ne_of_gt hx0)
  calc
    Real.log y * x ^ 2 ≤ (Real.log x * t ^ 2) * x ^ 2 :=
      mul_le_mul_of_nonneg_right hlog (sq_nonneg x)
    _ = Real.log x * (t * x) ^ 2 := by ring
    _ = Real.log x * y ^ 2 := by rw [htx]

/-- Smaller recursion inputs have no larger square-root-logarithmic exponent. -/
theorem w5_sqrtLogRate_monotoneOn :
    MonotoneOn (fun x : ℝ => x / Real.sqrt (logSafe x)) (Set.Ici 2) := by
  intro x hx y hy hxy
  dsimp only
  have hx2 : 2 ≤ x := hx
  have hy2 : 2 ≤ y := hy
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hlx : 0 < Real.logb 2 x :=
    Real.logb_pos (by norm_num) (by linarith)
  have hly : 0 < Real.logb 2 y :=
    Real.logb_pos (by norm_num) (by linarith)
  rw [w5_logSafe_eq_logb hx2, w5_logSafe_eq_logb hy2]
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hlx) (Real.sqrt_pos.mpr hly)).mpr
  have hbase := w5_log_mul_sq_le hx2 hxy
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : Real.logb 2 y * x ^ 2 ≤ Real.logb 2 x * y ^ 2 := by
    rw [Real.logb, Real.logb]
    simpa only [mul_div_assoc, div_mul_eq_mul_div] using
      (div_le_div_of_nonneg_right hbase hlog2.le)
  have hsx := Real.sq_sqrt hlx.le
  have hsy := Real.sq_sqrt hly.le
  have ha : 0 ≤ x * Real.sqrt (Real.logb 2 y) := by positivity
  have hb' : 0 ≤ y * Real.sqrt (Real.logb 2 x) := by positivity
  apply (sq_le_sq₀ ha hb').mp
  rw [mul_pow, mul_pow, hsx, hsy]
  nlinarith only [hb]

/-- Increasing the polynomial input budget preserves the common bound. -/
theorem w5_polyBound_mono_input (K : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    polyBound K m ≤ polyBound K n := by
  unfold polyBound
  gcongr

/-- A logarithmic overhead is absorbed by the exponent used in the factoring theorem. -/
theorem w5_logSafe_mul_sqrt_le {x : ℝ} (hx : 2 ≤ x) :
    logSafe x * Real.sqrt (logSafe x) ≤ 6 * x := by
  have hx0 : 0 < x := by linarith
  rw [w5_logSafe_eq_logb hx]
  let L := Real.logb 2 x
  have hL0 : 0 ≤ L := (Real.logb_pos (by norm_num) (by linarith : 1 < x)).le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 2 / 3)
  have hL : L ≤ 3 * x ^ ((2 : ℝ) / 3) := by
    change Real.log x / Real.log 2 ≤ _
    apply (div_le_iff₀ hlog2).mpr
    have hp := mul_le_mul_of_nonneg_left w5_half_le_log_two
      (show 0 ≤ 3 * x ^ ((2 : ℝ) / 3) by positivity)
    linarith
  have hL3 : L ^ 3 ≤ 27 * x ^ 2 := by
    have hpow := pow_le_pow_left₀ hL0 hL 3
    have hid : (x ^ ((2 : ℝ) / 3)) ^ 3 = x ^ 2 := by
      rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hx0.le]
      norm_num
    simpa only [mul_pow, hid, show (3 : ℝ) ^ 3 = 27 by norm_num] using hpow
  have hs := Real.sq_sqrt hL0
  change L * Real.sqrt L ≤ 6 * x
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, hs]
  nlinarith only [hL3, sq_nonneg x]

/-- The binary logarithm of a polynomial base costs at most a fixed multiple of the rate. -/
theorem w5_logb_succ_le_rate {x : ℝ} (hx : 2 ≤ x) :
    Real.logb 2 (x + 1) ≤ 12 * (x / Real.sqrt (logSafe x)) := by
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ logSafe x := le_max_left _ _
  have hL0 : 0 < logSafe x := by linarith
  have hlog : Real.logb 2 (x + 1) ≤ 2 * logSafe x := by
    have hm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by linarith : 0 < x + 1) (by nlinarith : x + 1 ≤ 2 * x)
    rw [Real.logb_mul (by norm_num) (ne_of_gt hx0),
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), ← w5_logSafe_eq_logb hx] at hm
    linarith
  have hmul := mul_le_mul_of_nonneg_right hlog (Real.sqrt_nonneg (logSafe x))
  have hbound := w5_logSafe_mul_sqrt_le hx
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hL0)).mpr
  nlinarith only [hmul, hbound]

/-- Every polynomial cost is absorbed with an explicit constant in the subexponential rate. -/
theorem w5_polyBound_le_sqrtLogExp (K n : ℕ) (hn : 2 ≤ n) :
    polyBound K n ≤
      (2 : ℝ) ^ ((24 * K : ℝ) * ((n : ℝ) / Real.sqrt (logSafe (n : ℝ)))) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hK : K ≤ 2 ^ K := by
    induction K with
    | zero => norm_num
    | succ K ih =>
      rw [pow_succ]
      have hp : 1 ≤ 2 ^ K := Nat.one_le_pow K 2 (by norm_num)
      omega
  have hKR : (K : ℝ) ≤ ((n : ℝ) + 1) ^ K := by
    calc
      (K : ℝ) ≤ (2 : ℝ) ^ K := by exact_mod_cast hK
      _ ≤ ((n : ℝ) + 1) ^ K := pow_le_pow_left₀ (by norm_num) (by linarith) _
  calc
    polyBound K n ≤ (((n : ℝ) + 1) ^ K) * (((n : ℝ) + 1) ^ K) := by
      exact mul_le_mul_of_nonneg_right hKR (by positivity)
    _ = ((n : ℝ) + 1) ^ (2 * K) := by rw [two_mul, pow_add]
    _ = (2 : ℝ) ^ (Real.logb 2 ((n : ℝ) + 1) * (2 * K : ℝ)) := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hn0]
      norm_cast
    _ ≤ (2 : ℝ) ^ ((24 * K : ℝ) * ((n : ℝ) / Real.sqrt (logSafe (n : ℝ)))) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h := mul_le_mul_of_nonneg_right (w5_logb_succ_le_rate hnR)
        (show (0 : ℝ) ≤ 2 * K by positivity)
      nlinarith only [h]

/-- A polynomial number of subexponential steps has the same rate after increasing its constant. -/
theorem w5_polyBound_mul_sqrtLogExp_le (K A n : ℕ) (hn : 2 ≤ n) :
    polyBound K n * (2 : ℝ) ^ ((A : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ))) ≤
      (2 : ℝ) ^ (((24 * K + A : ℕ) : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ))) := by
  calc
    _ ≤ (2 : ℝ) ^ ((24 * K : ℝ) * ((n : ℝ) / Real.sqrt (logSafe (n : ℝ)))) *
        (2 : ℝ) ^ ((A : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ))) :=
      mul_le_mul_of_nonneg_right (w5_polyBound_le_sqrtLogExp K n hn) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      push_cast
      ring

end DetDLP
end

section
set_option autoImplicit false

namespace DetDLP.w5_M6CallBudget

/-- Every factorization subproblem has a valid rate parameter. -/
theorem two_le_bitLen_of_two_le {x : ℕ} (hx : 2 ≤ x) : 2 ≤ bitLen (x + 1) := by
  have h : 1 < Nat.clog 2 (x + 1) :=
    (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by simpa using hx)
  exact h

/-- The running-time budget for any recursive divisor call is bounded by the root budget. -/
theorem call_time_le_root (f : ℕ → ℕ) (depth x K : ℕ) (hx : 2 ≤ x)
    (a : ℕ) (ha : a ∈ w5_SplitArithmetic.calls f depth x) :
    (2 : ℝ) ^ ((K : ℝ) * bitLen (a + 1) / Real.sqrt (logSafe (bitLen (a + 1)))) ≤
      (2 : ℝ) ^ ((K : ℝ) * bitLen (x + 1) / Real.sqrt (logSafe (bitLen (x + 1)))) := by
  obtain ⟨ha2, hax⟩ := w5_SplitArithmetic.mem_calls_bounds f depth x hx a ha
  have hn := w5_SplitArithmetic.mem_calls_bitLen_le f depth x hx a ha
  have h2a : (2 : ℝ) ≤ (bitLen (a + 1) : ℝ) := by
    exact_mod_cast two_le_bitLen_of_two_le ha2
  have h2x : (2 : ℝ) ≤ (bitLen (x + 1) : ℝ) := by
    exact_mod_cast two_le_bitLen_of_two_le hx
  have hr := w5_sqrtLogRate_monotoneOn h2a h2x (by exact_mod_cast hn)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg K)

/-- Summing all oracle budgets over the exact recursion tree preserves the desired rate. -/
theorem sum_call_times_le (f : ℕ → ℕ) (depth x K : ℕ) (hx : 2 ≤ x) :
    ((w5_SplitArithmetic.calls f depth x).map fun a =>
      (2 : ℝ) ^ ((K : ℝ) * bitLen (a + 1) / Real.sqrt (logSafe (bitLen (a + 1))))).sum ≤
    (2 : ℝ) ^ (((K + 48 : ℕ) : ℝ) * bitLen (x + 1) /
      Real.sqrt (logSafe (bitLen (x + 1)))) := by
  let n := bitLen (x + 1)
  let B : ℝ := (2 : ℝ) ^ ((K : ℝ) * n / Real.sqrt (logSafe n))
  have hsum : ((w5_SplitArithmetic.calls f depth x).map fun a =>
      (2 : ℝ) ^ ((K : ℝ) * bitLen (a + 1) / Real.sqrt (logSafe (bitLen (a + 1))))).sum ≤
      (w5_SplitArithmetic.calls f depth x).length * B := by
    have hs := List.sum_le_card_nsmul
      ((w5_SplitArithmetic.calls f depth x).map fun a =>
        (2 : ℝ) ^ ((K : ℝ) * bitLen (a + 1) / Real.sqrt (logSafe (bitLen (a + 1))))) B (by
        intro y hy
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
        exact call_time_le_root f depth x K hx a ha)
    simpa only [List.length_map, nsmul_eq_mul] using hs
  have hlen : ((w5_SplitArithmetic.calls f depth x).length : ℝ) ≤ polyBound 2 n := by
    have h : (w5_SplitArithmetic.calls f depth x).length < 2 * n :=
      w5_SplitArithmetic.length_calls_lt_two_bitLen f depth x hx
    have hR : ((w5_SplitArithmetic.calls f depth x).length : ℝ) ≤ 2 * n := by
      exact_mod_cast h.le
    unfold polyBound
    norm_num only [Nat.cast_ofNat]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [sq_nonneg (n : ℝ)]
  have hbudget := w5_polyBound_mul_sqrtLogExp_le 2 K n (two_le_bitLen_of_two_le hx)
  calc
    _ ≤ (w5_SplitArithmetic.calls f depth x).length * B := hsum
    _ ≤ polyBound 2 n * B := mul_le_mul_of_nonneg_right hlen (by positivity)
    _ ≤ _ := by simpa only [show 24 * 2 + K = K + 48 by omega] using hbudget

/-- Every individual oracle call also obeys the root's polynomial space budget. -/
theorem call_space_le_root (f : ℕ → ℕ) (depth x K : ℕ) (hx : 2 ≤ x)
    (a : ℕ) (ha : a ∈ w5_SplitArithmetic.calls f depth x) :
    polyBound K (bitLen (a + 1)) ≤ polyBound K (bitLen (x + 1)) :=
  w5_polyBound_mono_input K (w5_SplitArithmetic.mem_calls_bitLen_le f depth x hx a ha)

end DetDLP.w5_M6CallBudget
end

section
set_option backward.isDefEq.respectTransparency false

namespace DetDLP.w5_M6FrameStack
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP.MachineComposition
open Turing

abbrev BitTape := Tape (Option Bool)

open DetDLP.w5_M6RecursiveDriver (dataTape)

@[simp] theorem dataTape_head_cons (b : Bool) (bs : List Bool) :
    (dataTape (b :: bs)).head = some b := rfl
@[simp] theorem dataTape_head_nil : (dataTape []).head = none := rfl

theorem push_bit (bit : Bool) (bits : List Bool) :
    ((dataTape bits).move .left).write (some bit) = dataTape (bit :: bits) := by
  unfold dataTape Tape.mk₁ Tape.mk₂
  rw [Tape.move_left_mk']
  change (Tape.mk' (ListBlank.mk []) ((ListBlank.mk (bits.map some)).cons none)).write
    (some bit) = _
  rw [Tape.write_mk']
  rfl

theorem pop_bit (bit : Bool) (bits : List Bool) :
    ((dataTape (bit :: bits)).write none).move .right = dataTape bits := by
  unfold dataTape Tape.mk₁ Tape.mk₂
  change ((Tape.mk' (ListBlank.mk [])
    ((ListBlank.mk (bits.map some)).cons (some bit))).write none).move .right = _
  rw [Tape.write_mk', Tape.move_right_mk']
  simp only [ListBlank.head_cons, ListBlank.tail_cons]
  have hblank : (ListBlank.mk ([] : List (Option Bool))).cons none = ListBlank.mk [] := by
    have hdefault : (default : Option Bool) = none := rfl
    simpa [hdefault] using
      ListBlank.cons_head_tail (ListBlank.mk ([] : List (Option Bool)))
  rw [hblank]

def pairs : List Bool → List Bool
  | [] => []
  | b :: bs => true :: b :: pairs bs
@[simp] theorem pairs_append (xs ys : List Bool) : pairs (xs ++ ys) = pairs xs ++ pairs ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pairs, ih]
@[simp] theorem pairs_length (xs : List Bool) : (pairs xs).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pairs, ih]; omega

/-- The top word is reversed: a push reads the source left to right while
writing the stack to the left. Each payload bit has a `true` marker, and a
single `false` terminates the frame. Blanks are never data. -/
def frame (bits : List Bool) : List Bool := pairs bits.reverse ++ [false]

def tapes (buffer stack : BitTape) : Fin 2 → BitTape := ![buffer, stack]
@[simp] theorem tapes_zero (buffer stack : BitTape) : tapes buffer stack 0 = buffer := rfl
@[simp] theorem tapes_one (buffer stack : BitTape) : tapes buffer stack 1 = stack := rfl
@[simp] theorem tapes_update_zero (buffer stack t : BitTape) :
    Function.update (tapes buffer stack) 0 t = tapes t stack := by
  funext i; fin_cases i <;> simp [tapes]
@[simp] theorem tapes_update_one (buffer stack t : BitTape) :
    Function.update (tapes buffer stack) 1 t = tapes buffer t := by
  funext i; fin_cases i <;> simp [tapes]

/-- Thirteen fixed states, independent of the input and stack lengths. Tape 0
is consumed, tape 1 receives a complete self-delimiting frame. -/
def pushMachine : PrimitiveMachine where
  tapeCount := 2
  stateCount := 13
  inputTape := 0
  start := 0
  scan q := if q.val = 2 ∨ q.val = 3 ∨ q.val = 8 then 0 else 1
  transition q symbol :=
    match q.val with
    | 0 => .inr (1, .move .left)
    | 1 => .inr (2, .write (some false))
    | 2 => match symbol with
      | none => .inl true
      | some false => .inr (3, .write none)
      | some true => .inr (8, .write none)
    | 3 => .inr (4, .move .right)
    | 4 => .inr (5, .move .left)
    | 5 => .inr (6, .write (some false))
    | 6 => .inr (7, .move .left)
    | 7 => .inr (2, .write (some true))
    | 8 => .inr (9, .move .right)
    | 9 => .inr (10, .move .left)
    | 10 => .inr (11, .write (some true))
    | 11 => .inr (12, .move .left)
    | _ => .inr (2, .write (some true))

def pushCfg (q : Fin 13) (buffer stack : BitTape) : pushMachine.Cfg :=
  ⟨.inr q, tapes buffer stack⟩
def pushDone (buffer stack : BitTape) : pushMachine.Cfg :=
  ⟨.inl true, tapes buffer stack⟩

def run (A : PrimitiveMachine) : ℕ → A.Cfg → Option A.Cfg
  | 0, c => some c
  | n + 1, c => (A.step c).bind (run A n)

theorem trace_of_run (A : PrimitiveMachine) {n : ℕ} {a b : A.Cfg}
    (h : run A n a = some b) :
    OAI.Algorithms.SubexponentialSAT.Computation.Trace A.step n a b := by
  induction n generalizing a with
  | zero => cases Option.some.inj h; exact .refl _
  | succ n ih =>
    cases hs : A.step a with
    | none => simp [run, hs] at h
    | some c => exact .cons hs (ih (by simpa [run, hs] using h))

/-- Exactly six primitive tape steps transfer one payload bit. -/
theorem push_bit_trace (b : Bool) (bs stack : List Bool) :
    OAI.Algorithms.SubexponentialSAT.Computation.Trace pushMachine.step 6
      (pushCfg 2 (dataTape (b :: bs)) (dataTape stack))
      (pushCfg 2 (dataTape bs) (dataTape (true :: b :: stack))) := by
  apply trace_of_run
  cases b <;>
    simp [run, PrimitiveMachine.step, pushMachine, pushCfg, pop_bit, push_bit]

/-- Initializing the frame delimiter takes exactly two primitive steps. -/
theorem push_start_trace (bits stack : List Bool) :
    OAI.Algorithms.SubexponentialSAT.Computation.Trace pushMachine.step 2
      (pushCfg 0 (dataTape bits) (dataTape stack))
      (pushCfg 2 (dataTape bits) (dataTape (false :: stack))) := by
  apply trace_of_run
  simp [run, PrimitiveMachine.step, pushMachine, pushCfg, push_bit]

/-- Payload loop, including its actual final halting transition. -/
theorem push_loop_trace (bits stack : List Bool) :
    OAI.Algorithms.SubexponentialSAT.Computation.Trace pushMachine.step (6 * bits.length + 1)
      (pushCfg 2 (dataTape bits) (dataTape stack))
      (pushDone (dataTape []) (dataTape (pairs bits.reverse ++ stack))) := by
  induction bits generalizing stack with
  | nil =>
    apply trace_of_run
    simp [run, PrimitiveMachine.step, pushMachine, pushCfg, pushDone, pairs]
  | cons b bs ih =>
    have ht := Trace.append (push_bit_trace b bs stack) (ih (true :: b :: stack))
    simpa [List.reverse_cons, pairs, List.append_assoc, Nat.mul_add,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht

/-- Complete push, not a length-dependent unrolling of a program: the fixed
thirteen-state machine consumes any finite source word and pushes one frame. -/
theorem push_trace (bits stack : List Bool) :
    OAI.Algorithms.SubexponentialSAT.Computation.Trace pushMachine.step (6 * bits.length + 3)
      (pushCfg 0 (dataTape bits) (dataTape stack))
      (pushDone (dataTape []) (dataTape (frame bits ++ stack))) := by
  have ht := Trace.append (push_start_trace bits stack) (push_loop_trace bits (false :: stack))
  convert ht using 1
  · omega
  · simp [frame, List.append_assoc]

/-- Eleven fixed states. The stack's top frame is consumed and its original
payload is restored on the left of tape 0. Malformed or absent frames fail
rather than silently inventing data. -/
def popMachine : PrimitiveMachine where
  tapeCount := 2
  stateCount := 11
  inputTape := 0
  start := 0
  scan q := if q.val = 6 ∨ q.val = 7 ∨ q.val = 9 ∨ q.val = 10 then 0 else 1
  transition q symbol :=
    match q.val with
    | 0 => match symbol with
      | none => .inl false
      | some false => .inr (1, .write none)
      | some true => .inr (3, .write none)
    | 1 => .inr (2, .move .right)
    | 2 => .inl true
    | 3 => .inr (4, .move .right)
    | 4 => match symbol with
      | none => .inl false
      | some false => .inr (5, .write none)
      | some true => .inr (8, .write none)
    | 5 => .inr (6, .move .right)
    | 6 => .inr (7, .move .left)
    | 7 => .inr (0, .write (some false))
    | 8 => .inr (9, .move .right)
    | 9 => .inr (10, .move .left)
    | _ => .inr (0, .write (some true))

def popCfg (q : Fin 11) (buffer stack : BitTape) : popMachine.Cfg :=
  ⟨.inr q, tapes buffer stack⟩
def popDone (buffer stack : BitTape) : popMachine.Cfg :=
  ⟨.inl true, tapes buffer stack⟩

/-- Six real primitive tape steps consume a marker and payload bit and
prepend the bit to the destination, retaining the rest of the stack. -/
theorem pop_bit_trace (b : Bool) (stack acc : List Bool) :
    OAI.Algorithms.SubexponentialSAT.Computation.Trace popMachine.step 6
      (popCfg 0 (dataTape acc) (dataTape (true :: b :: stack)))
      (popCfg 0 (dataTape (b :: acc)) (dataTape stack)) := by
  apply trace_of_run
  cases b <;>
    simp [run, PrimitiveMachine.step, popMachine, popCfg, pop_bit, push_bit]

/-- Removing the delimiter and halting costs exactly three primitive steps. -/
theorem pop_delimiter_trace (stack acc : List Bool) :
    OAI.Algorithms.SubexponentialSAT.Computation.Trace popMachine.step 3
      (popCfg 0 (dataTape acc) (dataTape (false :: stack)))
      (popDone (dataTape acc) (dataTape stack)) := by
  apply trace_of_run
  simp [run, PrimitiveMachine.step, popMachine, popCfg, popDone, pop_bit]

theorem pop_loop_trace (bits stack acc : List Bool) :
    OAI.Algorithms.SubexponentialSAT.Computation.Trace popMachine.step (6 * bits.length + 3)
      (popCfg 0 (dataTape acc) (dataTape (pairs bits ++ false :: stack)))
      (popDone (dataTape (bits.reverse ++ acc)) (dataTape stack)) := by
  induction bits generalizing acc with
  | nil => simpa [pairs] using pop_delimiter_trace stack acc
  | cons b bs ih =>
    have ht := Trace.append (pop_bit_trace b (pairs bs ++ false :: stack) acc) (ih (b :: acc))
    simpa [pairs, List.reverse_cons, List.append_assoc,
      Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht

/-- Complete pop. Combined with `push_trace`, it proves LIFO restoration for
arbitrary Boolean payloads, including empty words and words with zero bits. -/
theorem pop_trace (bits stack acc : List Bool) :
    OAI.Algorithms.SubexponentialSAT.Computation.Trace popMachine.step (6 * bits.length + 3)
      (popCfg 0 (dataTape acc) (dataTape (frame bits ++ stack)))
      (popDone (dataTape (bits ++ acc)) (dataTape stack)) := by
  simpa [frame, List.append_assoc] using pop_loop_trace bits.reverse stack acc

/-- A true primitive step adds at most one newly visited cell. -/
theorem space_monitor_le_succ {A : PrimitiveMachine} {c : LocatedCfg A}
    (hw : LocatedWellFormed c) (d : A.Cfg) :
    visitedSpace (c.monitor d) ≤ visitedSpace c + 1 := by
  unfold LocatedCfg.monitor
  cases hs : c.config.state with
  | inl b => exact Nat.le_succ _
  | inr q =>
    simp only [Sum.elim_inr]
    cases ht : A.transition q (c.config.tapes (A.scan q)).head with
    | inl b => exact Nat.le_succ _
    | inr qa =>
      rcases qa with ⟨q', action⟩
      simp only [Sum.elim_inr, visitedSpace]
      let k := A.scan q
      let p := c.position k + headDisplacement action
      have hk := hw k
      have hd : -1 ≤ headDisplacement action ∧ headDisplacement action ≤ 1 := by
        cases action with
        | write b => simp [headDisplacement]
        | move d => cases d <;> simp [headDisplacement]
      have hi : (max (c.upper k) p - min (c.lower k) p + 1).toNat ≤
          (c.upper k - c.lower k + 1).toNat + 1 := by
        dsimp [p]; omega
      have heq : (fun i =>
          (Function.update c.upper k (max (c.upper k) p) i -
            Function.update c.lower k (min (c.lower k) p) i + 1).toNat) =
          Function.update (fun i => (c.upper i - c.lower i + 1).toNat) k
            (max (c.upper k) p - min (c.lower k) p + 1).toNat := by
        funext i
        by_cases h : i = k
        · subst i; simp
        · simp [h]
      change (∑ i, (Function.update c.upper k (max (c.upper k) p) i -
          Function.update c.lower k (min (c.lower k) p) i + 1).toNat) ≤ _
      rw [heq]
      rw [Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
      have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin A.tapeCount))
        (fun i => (c.upper i - c.lower i + 1).toNat) (Finset.mem_univ k)
      omega

theorem space_step_le_succ {A : PrimitiveMachine} {c d : LocatedCfg A}
    (hw : LocatedWellFormed c) (h : locatedStep A c = some d) :
    visitedSpace d ≤ visitedSpace c + 1 := by
  unfold locatedStep at h
  cases hs : A.step c.config with
  | none => simp [hs] at h
  | some e =>
    have hd : c.monitor e = d := by simpa [hs] using h
    rw [← hd]
    exact space_monitor_le_succ hw e

/-- Lift an actual unmonitored execution to the task's located semantics. The
bound is cumulative from the caller's previous history; no tape is reset. -/
theorem lift_trace_aux {A : PrimitiveMachine} {a' b : A.Cfg} {n : ℕ}
    (ht : OAI.Algorithms.SubexponentialSAT.Computation.Trace A.step n a' b) :
    ∀ a : LocatedCfg A, a.config = a' → LocatedWellFormed a →
    ∃ c : LocatedCfg A, c.config = b ∧
      OAI.Algorithms.SubexponentialSAT.Computation.Trace (locatedStep A) n a c ∧
      visitedSpace c ≤ visitedSpace a + n := by
  induction ht with
  | refl => intro a ha hw; exact ⟨a, ha, .refl _, by omega⟩
  | @cons n a' b' c' hs ht ih =>
    intro a ha hw
    have hloc : locatedStep A a = some (a.monitor b') := by simp [locatedStep, ha, hs]
    have hw' : LocatedWellFormed (a.monitor b') := locatedWellFormed_monitor hw b'
    have heq : (a.monitor b').config = b' := by
      unfold LocatedCfg.monitor
      cases a.config.state with
      | inl b => rfl
      | inr q =>
        simp only [Sum.elim_inr]
        cases A.transition q (a.config.tapes (A.scan q)).head <;> rfl
    obtain ⟨c, hc, htrace, hspace⟩ := ih (a.monitor b') heq hw'
    refine ⟨c, hc, .cons hloc htrace, ?_⟩
    have hinc := space_monitor_le_succ hw b'
    omega

theorem lift_trace {A : PrimitiveMachine} {a : LocatedCfg A} {b : A.Cfg} {n : ℕ}
    (hw : LocatedWellFormed a)
    (ht : OAI.Algorithms.SubexponentialSAT.Computation.Trace A.step n a.config b) :
    ∃ c : LocatedCfg A, c.config = b ∧
      OAI.Algorithms.SubexponentialSAT.Computation.Trace (locatedStep A) n a c ∧
      visitedSpace c ≤ visitedSpace a + n :=
  lift_trace_aux ht a rfl hw

/-- The lifted segment includes every prefix and all history already present
in its caller-supplied entry configuration. -/
theorem lift_segment {A : PrimitiveMachine} {a : LocatedCfg A} {b : A.Cfg} {n : ℕ}
    (hw : LocatedWellFormed a)
    (ht : OAI.Algorithms.SubexponentialSAT.Computation.Trace A.step n a.config b) :
    ∃ c : LocatedCfg A, c.config = b ∧
      Segment A a c n ((visitedSpace a + n : ℕ) : ℝ) := by
  obtain ⟨c, hc, htrace, hs⟩ := lift_trace hw ht
  refine ⟨c, hc, segment_iff_final_space.2 ⟨htrace, ?_⟩⟩
  exact_mod_cast hs

/-- Real push execution from an arbitrary caller-supplied monitor. Its resource
bound includes every previously visited cell, rather than restarting at zero. -/
theorem push_segment {a : LocatedCfg pushMachine} (bits stack : List Bool)
    (hw : LocatedWellFormed a)
    (ha : a.config = pushCfg 0 (dataTape bits) (dataTape stack)) :
    ∃ c : LocatedCfg pushMachine,
      c.config = pushDone (dataTape []) (dataTape (frame bits ++ stack)) ∧
      Segment pushMachine a c (6 * bits.length + 3)
        ((visitedSpace a + (6 * bits.length + 3) : ℕ) : ℝ) := by
  apply lift_segment hw
  rw [ha]
  exact push_trace bits stack

/-- Real pop execution with the same history-preserving space semantics. -/
theorem pop_segment {a : LocatedCfg popMachine} (bits stack acc : List Bool)
    (hw : LocatedWellFormed a)
    (ha : a.config = popCfg 0 (dataTape acc) (dataTape (frame bits ++ stack))) :
    ∃ c : LocatedCfg popMachine,
      c.config = popDone (dataTape (bits ++ acc)) (dataTape stack) ∧
      Segment popMachine a c (6 * bits.length + 3)
        ((visitedSpace a + (6 * bits.length + 3) : ℕ) : ℝ) := by
  apply lift_segment hw
  rw [ha]
  exact pop_trace bits stack acc

/-- One concrete linked finite controller performs push followed by pop; neither
its tape count nor its state count depends on the input's length. -/
def roundTripMachine : PrimitiveMachine :=
  thenMachine pushMachine (Program.ofMachine popMachine)

theorem roundTrip_segment {a : LocatedCfg pushMachine} (bits stack : List Bool)
    (hw : LocatedWellFormed a)
    (ha : a.config = pushCfg 0 (dataTape bits) (dataTape stack)) :
    ∃ c : LocatedCfg roundTripMachine,
      c.config.state = .inl true ∧
      c.config.tapes = tapes (dataTape bits) (dataTape stack) ∧
      Segment roundTripMachine
        (leftCfg pushMachine (Program.ofMachine popMachine) a) c
        (12 * bits.length + 6)
        ((visitedSpace a + (12 * bits.length + 6) : ℕ) : ℝ) := by
  obtain ⟨b, hb, hpush⟩ := push_segment bits stack hw ha
  let P := Program.ofMachine popMachine
  let entry := restartCfg pushMachine P b
  have he : entry.config = popCfg 0 (dataTape []) (dataTape (frame bits ++ stack)) := by
    change (restartCfg pushMachine P b).config = _
    simp [restartCfg, P, Program.ofMachine, hb, pushDone, popCfg, popMachine]
  have hwb : LocatedWellFormed b := locatedWellFormed_trace hw hpush.1
  have hwentry : LocatedWellFormed entry := fun i => hwb i
  obtain ⟨d, hd, hpop⟩ := pop_segment bits stack [] hwentry he
  have hh : ∃ answer, b.config.state = .inl answer := ⟨true, by rw [hb]; rfl⟩
  have hseq := thenMachine_segments pushMachine P hw hpush hh hpop
  refine ⟨rightCfg pushMachine P d, ?_, ?_, ?_⟩
  · simp [rightCfg, hd, popDone]
  · simpa [rightCfg, popDone] using congrArg PrimitiveMachine.Cfg.tapes hd
  · have hs := (segment_iff_final_space.1 hpush).2
    have hsNat : visitedSpace b ≤ visitedSpace a + (6 * bits.length + 3) := by exact_mod_cast hs
    have hentry : visitedSpace entry = visitedSpace b := rfl
    have htime : 6 * bits.length + 3 + (6 * bits.length + 3) = 12 * bits.length + 6 := by omega
    rw [htime] at hseq
    apply hseq.mono
    apply max_le
    · exact_mod_cast (show visitedSpace a + (6 * bits.length + 3) ≤
        visitedSpace a + (12 * bits.length + 6) by omega)
    · change ((visitedSpace entry + (6 * bits.length + 3) : ℕ) : ℝ) ≤ _
      rw [hentry]
      exact_mod_cast (show visitedSpace b + (6 * bits.length + 3) ≤
        visitedSpace a + (12 * bits.length + 6) by omega)

@[simp] theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by simp [frame]

/-- Raw input to a framed stack word on tape 1, in linear time and cumulative
linear space. This theorem uses exactly the task's `RunsWithin` predicate. -/
theorem push_runsWithin (bits : List Bool) :
    DetDLP.RunsWithin pushMachine ⟨1, by decide⟩ bits (frame bits)
      ((6 * bits.length + 3 : ℕ) : ℝ) ((7 * bits.length + 5 : ℕ) : ℝ) := by
  have hi : (locatedInit pushMachine bits).config =
      pushCfg 0 (dataTape bits) (dataTape []) := by
    change (⟨.inr ⟨0, by decide⟩, _⟩ : pushMachine.Cfg) = ⟨.inr ⟨0, by decide⟩, _⟩
    congr 1
    funext i; fin_cases i <;> simp [pushMachine, dataTape, tapes]
  obtain ⟨c, hc, hseg⟩ := push_segment bits [] (locatedWellFormed_init _ _) hi
  have hs : visitedSpace (locatedInit pushMachine bits) ≤ bits.length + 2 := by
    simp [visitedSpace, locatedInit, pushMachine, Fin.sum_univ_two]
  apply (runsWithin_iff_segment _ _ _ _ _ _).2
  refine ⟨6 * bits.length + 3, c, ?_, ⟨true, ?_⟩, ?_, le_rfl⟩
  · apply hseg.mono
    exact_mod_cast (show visitedSpace (locatedInit pushMachine bits) + (6 * bits.length + 3) ≤
      7 * bits.length + 5 by omega)
  · rw [hc]; rfl
  · rw [hc]
    simp [pushDone, dataTape]

end DetDLP.w5_M6FrameStack
end


