-- Prove2me | Definitions.Def_OAI_AlternatingFlow_Part01
-- name    : OAI_AlternatingFlow_Part01
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T03:27:54.468451+00:00
-- url     : https://prove2.me/theorems/ac9da917-8391-4171-9931-1469999f25ee
-- title:
--   Alternating-flow construction, part 1 of 11 (port of OpenAI's formalization): scales, the halting detector, encodings and profiles
-- statement:
--   Part 1 of 11 of a port of OpenAI's Lean formalization of the alternating-flow construction from the manuscript *Computation under Rapidly Vanishing Navier–Stokes Forcing* (OpenAI, September 27, 2026). This part contains scales, the halting detector, encodings and profiles.
--
--   **Attribution.** The code is adapted verbatim from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, modules `Scales`, `Detector`, `Encoding`, `Profiles` of `lean/OAI/MathematicalPhysics/AlternatingFlow`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order with their imports replaced by the previous part. The model definitions come from the platform definition `NavierStokesAlternating`. Part 1 adds compatibility shims for three core lemmas renamed after Lean 4.33.1, and part 3 adjusts one side-goal tactic for Mathlib 0df444a.
--
--   The development is split into eleven parts only so that each compiles within the platform's time limit. Together the parts supply the velocity construction used to prove `OAI.AlternatingNS.velocity_construction`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/MathematicalPhysics/AlternatingFlow: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/Scales.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/Detector.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/Encoding.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/Profiles.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf

/-
Alternating-flow construction (port of OpenAI's formalization), part 1 of 11: scales, the halting detector, encodings and profiles.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/MathematicalPhysics/AlternatingFlow/: Scales.lean, Detector.lean, Encoding.lean, Profiles.lean
These files formalize the manuscript "Computation under Rapidly Vanishing Navier-Stokes Forcing"
(OpenAI, September 27, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions come from the platform definition `NavierStokesAlternating` (only four helper facts of Model.lean are kept, together with compatibility shims for three core lemmas renamed after Lean 4.33.1).
-/
import Mathlib
import Definitions.Def_NavierStokesAlternating

set_option autoImplicit false

-- Compatibility shims: these core lemmas exist in newer Lean versions used upstream, but not in
-- Lean 4.33.1; they are restatements of `if_pos`, `if_neg` and `dif_pos`.
namespace OAI

theorem ite_eq_left {c : Prop} {_ : Decidable c} {α : Sort*} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h

theorem ite_eq_right {c : Prop} {_ : Decidable c} {α : Sort*} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h

theorem dite_eq_left {c : Prop} {_ : Decidable c} {α : Sort*} {t : c → α} {e : ¬c → α}
    (h : c) : dite c t e = t h := dif_pos h

end OAI

-- From Model.lean (only the helper facts; the definitions come from the platform import).
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS

theorem neZeroThree : NeZero 3 := ⟨Nat.succ_ne_zero 2⟩

theorem twoAtLeastTwo : Nat.AtLeastTwo 2 := ⟨Nat.le_refl 2⟩

theorem threeAtLeastTwo : Nat.AtLeastTwo 3 := ⟨Nat.le_succ 2⟩

theorem eightAtLeastTwo : Nat.AtLeastTwo 8 := ⟨by decide⟩

end AlternatingNS
end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Scales.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Scales

def K (N n : ℕ) : ℕ := N + 2 * n + 2

def s (N n : ℕ) : ℕ := (N + 1) * 2 ^ ((n + 3) ^ 2)

noncomputable def ε (b N n : ℕ) : ℝ := ((b : ℝ) ^ s N n)⁻¹

lemma exponent_succ (n : ℕ) : (n + 1 + 3) ^ 2 = (n + 3) ^ 2 + (2 * n + 7) := by
  ring

lemma s_succ (N n : ℕ) : s N (n + 1) = 2 ^ (2 * n + 7) * s N n := by
  simp only [s, exponent_succ, pow_add]
  ring

lemma pow_lower (n : ℕ) : 8 * (n + 1) ≤ 2 ^ ((n + 3) ^ 2) := by
  have h : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have he : n + 3 ≤ (n + 3) ^ 2 := by nlinarith
  calc
    8 * (n + 1) ≤ 8 * 2 ^ n := Nat.mul_le_mul_left 8 h
    _ = 2 ^ (n + 3) := by simp [pow_add]; ring
    _ ≤ 2 ^ ((n + 3) ^ 2) := Nat.pow_le_pow_right (by decide) he

lemma s_lower (N n : ℕ) : 8 * (N + 1) * (n + 1) ≤ s N n := by
  have h := Nat.mul_le_mul_left (N + 1) (pow_lower n)
  simpa only [s, mul_left_comm, mul_assoc] using h

lemma capacity_lt (N n : ℕ) : 1 + 2 * K N n < s N n := by
  have h := s_lower N n
  dsimp [K]
  nlinarith

lemma K_add_one_lt (N n : ℕ) : K N n + 1 < s N n := by
  have := capacity_lt N n
  omega

lemma s_pos (N n : ℕ) : 0 < s N n := by
  unfold s
  positivity

lemma strictMono_s (N : ℕ) : StrictMono (s N) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [s_succ]
  have hp : 1 < 2 ^ (2 * n + 7) := one_lt_pow₀ (by decide) (by omega)
  nlinarith [s_pos N n]

lemma scale_gap (N n : ℕ) : s N n + 1 + 2 * K N n < s N (n + 1) := by
  rw [s_succ]
  have hc := capacity_lt N n
  have hp : 2 ≤ 2 ^ (2 * n + 7) := by
    exact Nat.le_pow (by omega)
  nlinarith [s_pos N n]

lemma old_scale_gap (N j n : ℕ) (hjn : j < n) :
    s N j + (1 + 2 * K N j) ≤ s N n := by
  have h₁ := scale_gap N j
  have h₂ := (strictMono_s N).monotone (Nat.succ_le_of_lt hjn)
  simp only [Nat.succ_eq_add_one] at h₂
  omega

lemma derivative_gap (N r n : ℕ) (hn : r ≤ n) :
    s N n + (r + 1) * (s N n + 1 + K N n) ≤ s N (n + 1) := by
  have hk := K_add_one_lt N n
  have hp : 2 * r + 3 ≤ 2 ^ (2 * n + 7) := by
    have ht : 2 * n + 7 < 2 ^ (2 * n + 7) := Nat.lt_two_pow_self
    omega
  rw [s_succ]
  nlinarith

lemma s_zero_add (N n : ℕ) : s N 0 + n ≤ s N n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := strictMono_s N (Nat.lt_succ_self n)
    simp only [Nat.succ_eq_add_one] at *
    omega

lemma n_le_s (N n : ℕ) : n ≤ s N n := by
  have := s_zero_add N n
  omega

lemma ε_pos (b N n : ℕ) (hb : 0 < b) : 0 < ε b N n := by
  unfold ε
  positivity

lemma ε_nonneg (b N n : ℕ) (hb : 0 < b) : 0 ≤ ε b N n :=
  (ε_pos b N n hb).le

lemma ε_strictAnti (b N : ℕ) (hb : 1 < b) : StrictAnti (ε b N) := by
  intro n m hnm
  unfold ε
  apply inv_strictAnti₀ _ _
  · positivity
  · exact pow_lt_pow_right₀ (by exact_mod_cast hb) (strictMono_s N hnm)

lemma ε_le_geometric (b N n : ℕ) (hb : 2 ≤ b) :
    ε b N n ≤ (1 / 2 : ℝ) ^ n := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  unfold ε
  rw [one_div, inv_pow]
  apply inv_anti₀ (by positivity)
  calc
    (2 : ℝ) ^ n ≤ (2 : ℝ) ^ s N n := pow_le_pow_right₀ (by norm_num) (n_le_s N n)
    _ ≤ (b : ℝ) ^ s N n := pow_le_pow_left₀ (by norm_num) hb' _

lemma ε_le_initial_geometric (b N n : ℕ) (hb : 2 ≤ b) :
    ε b N n ≤ ε b N 0 * (1 / 2 : ℝ) ^ n := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hp : (b : ℝ) ^ s N 0 * 2 ^ n ≤ (b : ℝ) ^ s N n := by
    calc
      (b : ℝ) ^ s N 0 * 2 ^ n ≤ (b : ℝ) ^ s N 0 * (b : ℝ) ^ n := by
        gcongr
      _ = (b : ℝ) ^ (s N 0 + n) := (pow_add _ _ _).symm
      _ ≤ (b : ℝ) ^ s N n := pow_le_pow_right₀ (by linarith) (s_zero_add N n)
  simpa only [ε, one_div, inv_pow, mul_inv_rev, mul_comm] using
    (inv_anti₀ (by positivity : (0 : ℝ) < (b : ℝ) ^ s N 0 * 2 ^ n) hp)

lemma summable_ε (b N : ℕ) (hb : 2 ≤ b) : Summable (ε b N) := by
  exact Summable.of_nonneg_of_le
    (fun n => ε_nonneg b N n (by omega))
    (fun n => ε_le_geometric b N n hb) summable_geometric_two

lemma total_memory_le (b N : ℕ) (hb : 2 ≤ b) :
    (∑' n : ℕ, ε b N n) ≤ 2 * ε b N 0 := by
  have hg := summable_geometric_two.mul_left (ε b N 0)
  have h := (summable_ε b N hb).tsum_le_tsum
    (fun n => ε_le_initial_geometric b N n hb) hg
  calc
    (∑' n : ℕ, ε b N n) ≤ ∑' n : ℕ, ε b N 0 * (1 / 2 : ℝ) ^ n := h
    _ = 2 * ε b N 0 := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
      ring

lemma initial_memory_small (b N : ℕ) (hb : 4 ≤ b) : 2 * ε b N 0 < 1 / 4 := by
  have hs : 2 ≤ s N 0 := by have := s_lower N 0; nlinarith
  have hb' : (4 : ℝ) ≤ b := by exact_mod_cast hb
  have hpow : (16 : ℝ) ≤ (b : ℝ) ^ s N 0 := by
    calc
      (16 : ℝ) = 4 ^ 2 := by norm_num
      _ ≤ (4 : ℝ) ^ s N 0 := pow_le_pow_right₀ (by norm_num) hs
      _ ≤ (b : ℝ) ^ s N 0 := pow_le_pow_left₀ (by norm_num) hb' _
  have hε : ε b N 0 ≤ (16 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hpow
  norm_num at hε
  linarith

lemma derivative_cost_bound (b N r n : ℕ) (hb : 2 ≤ b) (hn : r ≤ n) :
    ε b N (n + 1) * (b : ℝ) ^ ((r + 1) * (s N n + 1 + K N n)) ≤ ε b N n := by
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have h := pow_le_pow_right₀ hb' (derivative_gap N r n hn)
  have hpos : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  dsimp [ε]
  rw [← div_eq_inv_mul, ← one_div]
  apply (div_le_div_iff₀ (pow_pos hpos _) (pow_pos hpos _)).2
  simpa [pow_add, mul_comm] using h

lemma summable_weighted_ε (b N J : ℕ) (hb : 2 ≤ b) :
    Summable (fun n : ℕ => (1 + (n : ℝ)) ^ J * ε b N n) := by
  have h₀ := summable_pow_mul_geometric_of_norm_lt_one J
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have h₁ := ((summable_nat_add_iff 1).2 h₀).mul_left (2 : ℝ)
  have h₂ : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ J * (1 / 2 : ℝ) ^ n) := by
    apply h₁.congr
    intro n
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by positivity) (ε_nonneg b N n (by omega)))
    (fun n => mul_le_mul_of_nonneg_left (ε_le_geometric b N n hb) (by positivity)) h₂

lemma weighted_ε_tendsto_zero (b N J : ℕ) (hb : 2 ≤ b) :
    Filter.Tendsto (fun n : ℕ => (1 + (n : ℝ)) ^ J * ε b N n)
      Filter.atTop (𝓝 0) :=
  (summable_weighted_ε b N J hb).tendsto_atTop_zero

lemma weighted_ε_bounded (b N J : ℕ) (hb : 2 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (1 + (n : ℝ)) ^ J * ε b N n ≤ C := by
  refine ⟨∑' n : ℕ, (1 + (n : ℝ)) ^ J * ε b N n, ?_, ?_⟩
  · apply tsum_nonneg
    intro n
    exact mul_nonneg (by positivity) (ε_nonneg b N n (by omega))
  · intro n
    apply (summable_weighted_ε b N J hb).le_tsum
    intro j _
    exact mul_nonneg (by positivity) (ε_nonneg b N j (by omega))

end Scales
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Detector.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Detector

open Scales

noncomputable def increment (b N : ℕ) (halted : ℕ → Bool) (n : ℕ) : ℝ :=
  ε b N n - ε b N (n + 1) + if halted n then 2 * ε b N (n + 1) else 0

noncomputable def signal (b N : ℕ) (halted : ℕ → Bool) : ℕ → ℝ
  | 0 => -ε b N 0
  | n + 1 => signal b N halted n + increment b N halted n

noncomputable def during (b N : ℕ) (halted : ℕ → Bool) (n : ℕ) (θ : ℝ) : ℝ :=
  signal b N halted n + θ * increment b N halted n

noncomputable def loading (b N : ℕ) (θ : ℝ) : ℝ := -1 + θ * (1 - ε b N 0)

lemma signal_formula (b N : ℕ) (halted : ℕ → Bool) (n : ℕ) :
    signal b N halted n = -ε b N n +
      2 * ∑ j ∈ Finset.range n, if halted j then ε b N (j + 1) else 0 := by
  induction n with
  | zero => simp [signal]
  | succ n ih =>
    simp only [signal, increment, ih, Finset.sum_range_succ]
    split_ifs <;> ring

lemma signal_before_halt (b N : ℕ) (halted : ℕ → Bool) (n : ℕ)
    (hn : ∀ j < n, halted j = false) : signal b N halted n = -ε b N n := by
  rw [signal_formula]
  have hsum : (∑ j ∈ Finset.range n, if halted j then ε b N (j + 1) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [hn j (Finset.mem_range.1 hj)]
  rw [hsum]
  ring

lemma signal_first_halt (b N : ℕ) (halted : ℕ → Bool) (n : ℕ)
    (hprev : ∀ j < n, halted j = false) (hn : halted n = true) :
    signal b N halted (n + 1) = ε b N (n + 1) := by
  rw [signal, signal_before_halt b N halted n hprev]
  simp only [increment, hn, ite_true]
  ring

lemma increment_nonneg (b N : ℕ) (hb : 2 ≤ b) (halted : ℕ → Bool) (n : ℕ) :
    0 ≤ increment b N halted n := by
  have hε := ε_strictAnti b N (by omega) (Nat.lt_succ_self n)
  have hp := ε_pos b N (n + 1) (by omega)
  simp only [Nat.succ_eq_add_one] at hε
  unfold increment
  split_ifs <;> linarith

lemma increment_le (b N : ℕ) (hb : 2 ≤ b) (halted : ℕ → Bool) (n : ℕ) :
    increment b N halted n ≤ ε b N n + ε b N (n + 1) := by
  have hp := ε_pos b N (n + 1) (by omega)
  unfold increment
  split_ifs <;> linarith

lemma signal_monotone (b N : ℕ) (hb : 2 ≤ b) (halted : ℕ → Bool) :
    Monotone (signal b N halted) := by
  apply monotone_nat_of_le_succ
  intro n
  simpa only [signal, le_add_iff_nonneg_right] using increment_nonneg b N hb halted n

lemma during_zero (b N : ℕ) (halted : ℕ → Bool) (n : ℕ) :
    during b N halted n 0 = signal b N halted n := by simp [during]

lemma during_one (b N : ℕ) (halted : ℕ → Bool) (n : ℕ) :
    during b N halted n 1 = signal b N halted (n + 1) := by simp [during, signal]

lemma during_before_halt (b N : ℕ) (hb : 2 ≤ b) (halted : ℕ → Bool) (n : ℕ)
    (hn : ∀ j ≤ n, halted j = false) (θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) :
    during b N halted n θ < 0 := by
  have he := ε_strictAnti b N (by omega) (Nat.lt_succ_self n)
  have hp := ε_pos b N (n + 1) (by omega)
  simp only [Nat.succ_eq_add_one] at he
  have hm := mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr he.le)
  rw [during, signal_before_halt b N halted n (fun j hj => hn j hj.le)]
  simp only [increment, hn n le_rfl, Bool.false_eq_true, ↓reduceIte, add_zero]
  nlinarith

lemma loading_negative (b N : ℕ) (hb : 2 ≤ b) (θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) :
    loading b N θ < 0 := by
  have hp := ε_pos b N 0 (by omega)
  have hle := ε_le_geometric b N 0 hb
  norm_num at hle
  have hm := mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hle)
  unfold loading
  nlinarith

lemma scalar_reachability (b N : ℕ) (hb : 2 ≤ b) (halted : ℕ → Bool) :
    (∃ n : ℕ, ∃ θ ∈ Set.Icc (0 : ℝ) 1, 0 < during b N halted n θ) ↔
      ∃ n : ℕ, halted n = true := by
  constructor
  · rintro ⟨n, θ, hθ, hpos⟩
    by_contra h
    have hfalse : ∀ j, halted j = false := by
      intro j
      exact Bool.eq_false_iff.2 (fun hj => h ⟨j, hj⟩)
    exact (during_before_halt b N hb halted n (fun j _ => hfalse j) θ hθ).not_gt hpos
  · intro h
    let n := Nat.find h
    have hn : halted n = true := Nat.find_spec h
    have hprev : ∀ j < n, halted j = false :=
      fun j hj => Bool.eq_false_iff.2 (Nat.find_min h hj)
    refine ⟨n, 1, ⟨by norm_num, le_rfl⟩, ?_⟩
    rw [during_one, signal_first_halt b N halted n hprev hn]
    exact ε_pos b N (n + 1) (by omega)

lemma signal_upper_bound (b N : ℕ) (hb : 2 ≤ b) (halted : ℕ → Bool) (n : ℕ) :
    signal b N halted n ≤ 2 * ∑' j : ℕ, ε b N j := by
  have hsum : (∑ j ∈ Finset.range n, if halted j then ε b N (j + 1) else 0) ≤
      ∑ j ∈ Finset.range n, ε b N j := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · exact (ε_strictAnti b N (by omega) (Nat.lt_succ_self j)).le
    · exact ε_nonneg b N j (by omega)
  have htotal := (summable_ε b N hb).sum_le_tsum (Finset.range n)
    (fun j _ => ε_nonneg b N j (by omega))
  rw [signal_formula]
  linarith [ε_nonneg b N n (by omega)]

lemma signal_in_plateau (b N : ℕ) (hb : 4 ≤ b) (halted : ℕ → Bool) (n : ℕ) :
    signal b N halted n ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hl := signal_monotone b N (by omega) halted (Nat.zero_le n)
  have hu := signal_upper_bound b N (by omega) halted n
  have hsum := total_memory_le b N (by omega)
  have hs := initial_memory_small b N hb
  simp only [signal] at hl
  constructor <;> linarith

lemma during_in_plateau (b N : ℕ) (hb : 4 ≤ b) (halted : ℕ → Bool) (n : ℕ)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) : during b N halted n θ ∈ Set.Ioo (-1 : ℝ) 1 := by
  have h₀ := signal_in_plateau b N hb halted n
  have h₁ := signal_in_plateau b N hb halted (n + 1)
  have hi := increment_nonneg b N (by omega) halted n
  have hleft := mul_nonneg hθ.1 hi
  have hright := mul_nonneg (sub_nonneg.mpr hθ.2) hi
  simp only [signal] at h₁
  change -1 < signal b N halted n + θ * increment b N halted n ∧
    signal b N halted n + θ * increment b N halted n < 1
  constructor <;> nlinarith [h₀.1, h₁.2]

lemma machine_scalar_reachability (b : ℕ) (hb : 2 ≤ b) (M : Machine) (w : List ℕ) :
    (∃ n : ℕ, ∃ θ ∈ Set.Icc (0 : ℝ) 1,
      0 < during b w.length (fun j => M.isHalting (M.run w j)) n θ) ↔ M.Halts w :=
  scalar_reachability b w.length hb (fun j => M.isHalting (M.run w j))

end Detector
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Encoding.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Encoding

noncomputable def code (b : ℕ) : List ℕ → ℝ
  | [] => 0
  | d :: ds => ((d : ℝ) + code b ds) / b

noncomputable def tailMax (b : ℕ) : ℝ :=
  letI := twoAtLeastTwo
  ((b : ℝ) - 2) / ((b : ℝ) - 1)

lemma tailMax_nonneg (b : ℕ) (hb : 2 ≤ b) : 0 ≤ tailMax b := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  unfold tailMax
  exact div_nonneg (by linarith) (by linarith)

lemma tailMax_lt_one (b : ℕ) (hb : 2 ≤ b) : tailMax b < 1 := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  unfold tailMax
  apply (div_lt_one (by linarith)).2
  linarith

lemma tailMax_identity (b : ℕ) (hb : 2 ≤ b) :
    (b : ℝ) * tailMax b = (b : ℝ) - 2 + tailMax b := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have h : (b : ℝ) - 1 ≠ 0 := by linarith
  unfold tailMax
  field_simp
  ring

lemma code_nonneg (b : ℕ) (L : List ℕ) : 0 ≤ code b L := by
  induction L with
  | nil => simp [code]
  | cons d L ih => simpa only [code] using div_nonneg (by positivity) (Nat.cast_nonneg b)

lemma code_le_tailMax (b : ℕ) (hb : 2 ≤ b) (L : List ℕ)
    (hL : ∀ d ∈ L, d + 2 ≤ b) : code b L ≤ tailMax b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  induction L with
  | nil => exact tailMax_nonneg b hb
  | cons d L ih =>
    have hd : (d : ℝ) + 2 ≤ b := by exact_mod_cast hL d (by simp)
    have ht : code b L ≤ tailMax b := ih (fun a ha => hL a (List.mem_cons_of_mem d ha))
    rw [code, div_le_iff₀ hb']
    have hi := tailMax_identity b hb
    linarith

lemma digit_interval (b d : ℕ) (hb : 2 ≤ b) (L : List ℕ)
    (hL : ∀ a ∈ L, a + 2 ≤ b) :
    (d : ℝ) / b ≤ code b (d :: L) ∧ code b (d :: L) ≤ ((d : ℝ) + 1) / b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  constructor
  · exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (code_nonneg b L)) hb'.le
  · apply div_le_div_of_nonneg_right _ hb'.le
    linarith [code_le_tailMax b hb L hL, tailMax_lt_one b hb]

lemma code_append (b : ℕ) (hb : 0 < b) (L R : List ℕ) :
    code b (L ++ R) = code b L + ((b : ℝ) ^ L.length)⁻¹ * code b R := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  induction L with
  | nil => simp [code]
  | cons d L ih =>
    simp only [List.cons_append, code, List.length_cons, pow_succ, ih]
    field_simp
    ring

lemma code_denominator (b : ℕ) (hb : 0 < b) (L : List ℕ) :
    ∃ a : ℕ, (b : ℝ) ^ L.length * code b L = a := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  induction L with
  | nil => exact ⟨0, by simp [code]⟩
  | cons d L ih =>
    obtain ⟨a, ha⟩ := ih
    refine ⟨b ^ L.length * d + a, ?_⟩
    calc
      (b : ℝ) ^ (d :: L).length * code b (d :: L) =
          (b : ℝ) ^ L.length * d + (b : ℝ) ^ L.length * code b L := by
        simp only [List.length_cons, code, pow_succ]
        field_simp
      _ = ((b ^ L.length * d + a : ℕ) : ℝ) := by rw [ha]; push_cast; rfl

lemma configuration_block (b g : ℕ) (hb : 0 < b) (L R : List ℕ) :
    code b (g :: (L ++ R)) =
      ((g : ℝ) + code b L + ((b : ℝ) ^ L.length)⁻¹ * code b R) / b := by
  rw [code, code_append b hb]
  ring

lemma integral_rescale (b k l : ℕ) (hkl : k ≤ l) {x : ℝ}
    (hx : ∃ a : ℤ, (b : ℝ) ^ k * x = a) :
    ∃ a : ℤ, (b : ℝ) ^ l * x = a := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨(b : ℤ) ^ (l - k) * a, ?_⟩
  calc
    (b : ℝ) ^ l * x = (b : ℝ) ^ (l - k) * ((b : ℝ) ^ k * x) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hkl]
    _ = ((b : ℤ) ^ (l - k) * a : ℤ) := by rw [ha]; push_cast; rfl

lemma sum_integral {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, ∃ a : ℤ, f i = a) : ∃ a : ℤ, ∑ i ∈ S, f i = a := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨a, ha⟩ := hf i (by simp)
    obtain ⟨c, hc⟩ := ih (fun j hj => hf j (by simp [hj]))
    exact ⟨a + c, by simp [Finset.sum_insert hi, ha, hc]⟩

noncomputable def donor (b N : ℕ) (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), if j % 2 = n % 2 then Scales.ε b N j * C j else 0

lemma old_record_integral (b N j n : ℕ) (hb : 0 < b) (hjn : j < n) {C : ℝ}
    (hC : ∃ a : ℤ, (b : ℝ) ^ (1 + 2 * Scales.K N j) * C = a) :
    ∃ a : ℤ, (b : ℝ) ^ Scales.s N n * (Scales.ε b N j * C) = a := by
  apply integral_rescale b (Scales.s N j + (1 + 2 * Scales.K N j))
    (Scales.s N n) (Scales.old_scale_gap N j n hjn)
  obtain ⟨a, ha⟩ := hC
  refine ⟨a, ?_⟩
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  calc
    (b : ℝ) ^ (Scales.s N j + (1 + 2 * Scales.K N j)) * (Scales.ε b N j * C) =
      (b : ℝ) ^ (1 + 2 * Scales.K N j) * C := by
        dsimp [Scales.ε]
        rw [pow_add]
        field_simp
    _ = a := ha

lemma donor_integer_add (b N n : ℕ) (hb : 0 < b) (C : ℕ → ℝ)
    (hC : ∀ j, ∃ a : ℤ, (b : ℝ) ^ (1 + 2 * Scales.K N j) * C j = a) :
    ∃ a : ℤ, (b : ℝ) ^ Scales.s N n * donor b N C n = a + C n := by
  have hI : ∀ j ∈ Finset.range n,
      ∃ a : ℤ, (b : ℝ) ^ Scales.s N n *
        (if j % 2 = n % 2 then Scales.ε b N j * C j else 0) = a := by
    intro j hj
    split_ifs
    · exact old_record_integral b N j n hb (Finset.mem_range.1 hj) (hC j)
    · exact ⟨0, by simp⟩
  obtain ⟨a, ha⟩ := sum_integral (Finset.range n) _ hI
  refine ⟨a, ?_⟩
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  rw [donor, Finset.sum_range_succ]
  simp only [ite_true, mul_add, Finset.mul_sum]
  rw [ha]
  dsimp [Scales.ε]
  field_simp

def DecoderLaw (b : ℕ) (P : ℝ → ℝ) : Prop :=
  Function.Periodic P 1 ∧ ∀ v ∈ Set.Icc 0 (tailMax b), P v = v

lemma decoder_int_add (b : ℕ) (P : ℝ → ℝ) (hP : DecoderLaw b P)
    (a : ℤ) (v : ℝ) (hv : v ∈ Set.Icc 0 (tailMax b)) : P ((a : ℝ) + v) = v := by
  have h := hP.1.int_mul a v
  simpa only [mul_one, add_comm, hP.2 v hv] using h

lemma read_current (b N n : ℕ) (hb : 2 ≤ b) (C : ℕ → ℝ)
    (hC : ∀ j, ∃ a : ℤ, (b : ℝ) ^ (1 + 2 * Scales.K N j) * C j = a)
    (hc : C n ∈ Set.Icc 0 (tailMax b))
    (P : ℝ → ℝ) (hP : DecoderLaw b P) :
    P ((b : ℝ) ^ Scales.s N n * donor b N C n) = C n := by
  obtain ⟨a, ha⟩ := donor_integer_add b N n (by omega) C hC
  rw [ha]
  exact decoder_int_add b P hP a (C n) hc

lemma remove_prefix (b s : ℕ) (hb : 0 < b) (L R : List ℕ) (D : ℝ)
    (hD : ∃ a : ℤ, (b : ℝ) ^ s * D = a + code b (L ++ R)) :
    ∃ a : ℤ, (b : ℝ) ^ (s + L.length) * D = a + code b R := by
  obtain ⟨a, ha⟩ := hD
  obtain ⟨c, hc⟩ := code_denominator b hb L
  refine ⟨(b : ℤ) ^ L.length * a + c, ?_⟩
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  calc
    (b : ℝ) ^ (s + L.length) * D = (b : ℝ) ^ L.length * ((b : ℝ) ^ s * D) := by
      rw [pow_add]; ring
    _ = (b : ℝ) ^ L.length * a + (b : ℝ) ^ L.length * code b L + code b R := by
      rw [ha, code_append b hb]
      field_simp
      ring
    _ = (((b : ℤ) ^ L.length * a + c : ℤ) : ℝ) + code b R := by rw [hc]; push_cast; rfl

lemma read_after_prefix (b s : ℕ) (hb : 2 ≤ b) (L R : List ℕ) (D : ℝ)
    (hD : ∃ a : ℤ, (b : ℝ) ^ s * D = a + code b (L ++ R))
    (hR : ∀ d ∈ R, d + 2 ≤ b) (P : ℝ → ℝ) (hP : DecoderLaw b P) :
    P ((b : ℝ) ^ (s + L.length) * D) = code b R := by
  obtain ⟨a, ha⟩ := remove_prefix b s (by omega) L R D hD
  rw [ha]
  exact decoder_int_add b P hP a _ ⟨code_nonneg b R, code_le_tailMax b hb R hR⟩

lemma read_configuration (b s g : ℕ) (hb : 2 ≤ b) (L R : List ℕ) (D : ℝ)
    (hD : ∃ a : ℤ, (b : ℝ) ^ s * D = a + code b (g :: (L ++ R)))
    (hd : ∀ d ∈ g :: (L ++ R), d + 2 ≤ b)
    (P : ℝ → ℝ) (hP : DecoderLaw b P) :
    P ((b : ℝ) ^ s * D) = code b (g :: (L ++ R)) ∧
    P ((b : ℝ) ^ (s + 1 + L.length) * D) = code b R ∧
    P ((b : ℝ) ^ (s + 1) * D) - ((b : ℝ) ^ L.length)⁻¹ *
      P ((b : ℝ) ^ (s + 1 + L.length) * D) = code b L := by
  have hLR : ∀ d ∈ L ++ R, d + 2 ≤ b :=
    fun d h => hd d (List.mem_cons_of_mem g h)
  have hR : ∀ d ∈ R, d + 2 ≤ b := fun d h => hLR d (List.mem_append_right L h)
  have h₁ := read_after_prefix b s hb [g] (L ++ R) D hD hLR P hP
  have h₂ := read_after_prefix b s hb (g :: L) R D (by simpa using hD) hR P hP
  simp only [List.length_cons, List.length_nil] at h₁ h₂
  have h₂' : P ((b : ℝ) ^ (s + 1 + L.length) * D) = code b R := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₂
  refine ⟨?_, h₂', ?_⟩
  · obtain ⟨a, ha⟩ := hD
    rw [ha]
    exact decoder_int_add b P hP a _
      ⟨code_nonneg b _, code_le_tailMax b hb _ hd⟩
  · rw [h₁, h₂', code_append b (by omega)]
    ring

end Encoding
end AlternatingNS

namespace AlternatingNS
namespace Encoding

lemma donor_in_plateau (b N n : ℕ) (hb : 4 ≤ b) (C : ℕ → ℝ)
    (hC : ∀ j, C j ∈ Set.Icc (0 : ℝ) 1) :
    donor b N C n ∈ Set.Ico (0 : ℝ) (1 / 4) := by
  have hterm : ∀ j : ℕ,
      0 ≤ (if j % 2 = n % 2 then Scales.ε b N j * C j else 0) ∧
        (if j % 2 = n % 2 then Scales.ε b N j * C j else 0) ≤ Scales.ε b N j := by
    intro j
    have hε := Scales.ε_nonneg b N j (by omega)
    split_ifs
    · exact ⟨mul_nonneg hε (hC j).1, mul_le_of_le_one_right hε (hC j).2⟩
    · exact ⟨le_rfl, hε⟩
  constructor
  · apply Finset.sum_nonneg
    intro j _
    exact (hterm j).1
  · apply lt_of_le_of_lt _ (Scales.initial_memory_small b N hb)
    apply le_trans _ (Scales.total_memory_le b N (by omega))
    calc
      donor b N C n ≤ ∑ j ∈ Finset.range (n + 1), Scales.ε b N j :=
        Finset.sum_le_sum (fun j _ => (hterm j).2)
      _ ≤ ∑' j : ℕ, Scales.ε b N j :=
        (Scales.summable_ε b N (by omega)).sum_le_tsum _
          (fun j _ => Scales.ε_nonneg b N j (by omega))

lemma pop_code (b d : ℕ) (hb : 0 < b) (L : List ℕ) :
    (b : ℝ) * code b (d :: L) - d = code b L := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  dsimp [code]
  field_simp
  ring

lemma tape_step_right (b a w : ℕ) (hb : 0 < b) (L R : List ℕ) :
    (((w : ℝ) + code b L) / b, (b : ℝ) * code b (a :: R) - a) =
      (code b (w :: L), code b R) := by
  rw [pop_code b a hb R]
  rfl

lemma tape_step_stay (b a w : ℕ) (hb : 0 < b) (L R : List ℕ) :
    (code b L, ((w : ℝ) + ((b : ℝ) * code b (a :: R) - a)) / b) =
      (code b L, code b (w :: R)) := by
  rw [pop_code b a hb R]
  rfl

lemma tape_step_left (b a w l : ℕ) (hb : 0 < b) (L R : List ℕ) :
    ((b : ℝ) * code b (l :: L) - l,
      ((l : ℝ) + ((w : ℝ) + ((b : ℝ) * code b (a :: R) - a)) / b) / b) =
      (code b L, code b (l :: w :: R)) := by
  rw [pop_code b l hb L, pop_code b a hb R]
  rfl

end Encoding
end AlternatingNS

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/Profiles.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Profiles

noncomputable def clock (t : ℝ) : ℝ :=
  letI := twoAtLeastTwo
  Real.smoothTransition (2 * t - 1 / 2)

lemma clock_smooth : ContDiff ℝ ∞ clock := by
  unfold clock
  fun_prop

lemma clock_mem (t : ℝ) : clock t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma clock_zero (t : ℝ) (ht : t ≤ 1 / 4) : clock t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

lemma clock_one (t : ℝ) (ht : 3 / 4 ≤ t) : clock t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

lemma clock_monotone : Monotone clock := by
  intro a b hab
  apply Real.smoothTransition.monotone
  linarith

noncomputable def periodizer (a c x : ℝ) : ℝ :=
  Int.fract x - Real.smoothTransition ((Int.fract x - a) / (c - a))

lemma periodizer_periodic (a c : ℝ) : Function.Periodic (periodizer a c) 1 := by
  intro x
  simp only [periodizer, Int.fract_add_one]

lemma periodizer_int_add (a c : ℝ) (k : ℤ) (x : ℝ) :
    periodizer a c ((k : ℝ) + x) = periodizer a c x := by
  simp only [periodizer, Int.fract_intCast_add]

lemma periodizer_self (a c x : ℝ) (hac : a < c) (ha : a < 1)
    (hx : x ∈ Set.Icc 0 a) : periodizer a c x = x := by
  have hf : Int.fract x = x := Int.fract_eq_self.2 ⟨hx.1, hx.2.trans_lt ha⟩
  rw [periodizer, hf, Real.smoothTransition.zero_of_nonpos]
  · ring
  · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) (sub_pos.mpr hac).le

lemma periodizer_near_zero (a c : ℝ) (ha : 0 < a) (hac : a < c) (hc : c < 1)
    (x : ℝ) (hx : x ∈ Set.Ioo (c - 1) a) : periodizer a c x = x := by
  by_cases hx0 : 0 ≤ x
  · exact periodizer_self a c x hac (hac.trans hc) ⟨hx0, hx.2.le⟩
  · have hn : ⌊x⌋ = (-1 : ℤ) := Int.floor_eq_iff.2 (by norm_num; constructor <;> linarith [hx.1])
    have hf : Int.fract x = x + 1 := by rw [Int.fract, hn]; norm_num
    have hh : 1 ≤ (x + 1 - a) / (c - a) :=
      (le_div_iff₀ (sub_pos.mpr hac)).2 (by linarith [hx.1])
    rw [periodizer, hf, Real.smoothTransition.one_of_one_le hh]
    ring

lemma periodizer_smooth (a c : ℝ) (ha : 0 < a) (hac : a < c) (hc : c < 1) :
    ContDiff ℝ ∞ (periodizer a c) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = (⌊x⌋ : ℝ)
  · have hg : ContDiff ℝ ∞ (fun y : ℝ => y - (⌊x⌋ : ℝ)) := by fun_prop
    apply hg.contDiffAt.congr_of_eventuallyEq
    have hlo : (⌊x⌋ : ℝ) + (c - 1) < x := by linarith
    have hhi : x < (⌊x⌋ : ℝ) + a := by linarith
    filter_upwards [Ioo_mem_nhds hlo hhi] with y hy
    have hy' : y - (⌊x⌋ : ℝ) ∈ Set.Ioo (c - 1) a := by
      constructor <;> linarith [hy.1, hy.2]
    calc
      periodizer a c y = periodizer a c ((⌊x⌋ : ℝ) + (y - (⌊x⌋ : ℝ))) := by congr 1; ring
      _ = periodizer a c (y - (⌊x⌋ : ℝ)) := periodizer_int_add a c _ _
      _ = y - (⌊x⌋ : ℝ) := periodizer_near_zero a c ha hac hc _ hy'
  · have hg : ContDiff ℝ ∞ (fun y : ℝ => (y - (⌊x⌋ : ℝ)) -
        Real.smoothTransition (((y - (⌊x⌋ : ℝ)) - a) / (c - a))) := by fun_prop
    apply hg.contDiffAt.congr_of_eventuallyEq
    have hlo : (⌊x⌋ : ℝ) < x := (Int.floor_le x).lt_of_ne (Ne.symm hx)
    filter_upwards [Ioo_mem_nhds hlo (Int.lt_floor_add_one x)] with y hy
    have hy' : ⌊y⌋ = ⌊x⌋ := Int.floor_eq_iff.2 ⟨hy.1.le, hy.2⟩
    simp only [periodizer, Int.fract, hy']

noncomputable def decoder (b : ℕ) : ℝ → ℝ :=
  letI := twoAtLeastTwo
  letI := threeAtLeastTwo
  periodizer ((2 * Encoding.tailMax b + 1) / 3) ((Encoding.tailMax b + 2) / 3)

lemma decoder_law (b : ℕ) (hb : 2 ≤ b) : Encoding.DecoderLaw b (decoder b) := by
  have hm := Encoding.tailMax_lt_one b hb
  refine ⟨periodizer_periodic _ _, ?_⟩
  intro x hx
  apply periodizer_self
  · linarith
  · linarith
  · exact ⟨hx.1, by linarith [hx.2]⟩

lemma decoder_smooth (b : ℕ) (hb : 2 ≤ b) : ContDiff ℝ ∞ (decoder b) := by
  have hm0 := Encoding.tailMax_nonneg b hb
  have hm1 := Encoding.tailMax_lt_one b hb
  apply periodizer_smooth <;> linarith

lemma iteratedDeriv_periodic (f : ℝ → ℝ) (hf : Function.Periodic f 1) (r : ℕ) :
    Function.Periodic (iteratedDeriv r f) 1 := by
  have heq : (fun x => f (x + 1)) = f := funext hf
  have h := iteratedDeriv_comp_add_const r f 1
  rw [heq] at h
  exact fun x => (congr_fun h x).symm

lemma periodic_derivatives_bounded (f : ℝ → ℝ) (hf : Function.Periodic f 1)
    (hs : ContDiff ℝ ∞ f) (r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv r f x| ≤ C := by
  have hcont : Continuous (fun x => |iteratedDeriv r f x|) :=
    (hs.continuous_iteratedDeriv r (WithTop.coe_le_coe.mpr le_top)).abs
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (hcont.continuousOn (s := Set.Icc 0 1))
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro x
  obtain ⟨y, hy, hxy⟩ := (iteratedDeriv_periodic f hf r).exists_mem_Ico (by norm_num) x 0
  rw [hxy]
  apply le_trans _ (le_max_right _ _)
  apply hC
  exact ⟨y, ⟨hy.1, by simpa using hy.2.le⟩, rfl⟩

lemma decoder_derivatives_bounded (b : ℕ) (hb : 2 ≤ b) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv r (decoder b) x| ≤ C :=
  periodic_derivatives_bounded (decoder b) (decoder_law b hb).1 (decoder_smooth b hb) r

end Profiles

namespace Encoding

lemma read_donor_configuration (b N n : ℕ) (hb : 2 ≤ b)
    (g : ℕ → ℕ) (L R : ℕ → List ℕ)
    (hL : ∀ j, (L j).length = Scales.K N j)
    (hR : ∀ j, (R j).length = Scales.K N j)
    (hd : ∀ j, ∀ d ∈ g j :: (L j ++ R j), d + 2 ≤ b) :
    let C := fun j => code b (g j :: (L j ++ R j))
    let D := donor b N C n
    Profiles.decoder b ((b : ℝ) ^ Scales.s N n * D) = C n ∧
    Profiles.decoder b ((b : ℝ) ^ (Scales.s N n + 1 + Scales.K N n) * D) =
      code b (R n) ∧
    Profiles.decoder b ((b : ℝ) ^ (Scales.s N n + 1) * D) -
      ((b : ℝ) ^ Scales.K N n)⁻¹ *
        Profiles.decoder b ((b : ℝ) ^ (Scales.s N n + 1 + Scales.K N n) * D) =
      code b (L n) := by
  dsimp only
  have hC : ∀ j, ∃ a : ℤ,
      (b : ℝ) ^ (1 + 2 * Scales.K N j) * code b (g j :: (L j ++ R j)) = a := by
    intro j
    obtain ⟨a, ha⟩ := code_denominator b (by omega) (g j :: (L j ++ R j))
    refine ⟨a, ?_⟩
    simp only [List.length_cons, List.length_append, hL, hR] at ha
    have he : 1 + 2 * Scales.K N j = Scales.K N j + Scales.K N j + 1 := by omega
    simpa only [he, Int.cast_natCast] using ha
  have h := read_configuration b (Scales.s N n) (g n) hb (L n) (R n)
    (donor b N (fun j => code b (g j :: (L j ++ R j))) n)
    (donor_integer_add b N n (by omega) _ hC) (hd n)
    (Profiles.decoder b) (Profiles.decoder_law b hb)
  simpa only [hL] using h

end Encoding
end AlternatingNS

end OAI


