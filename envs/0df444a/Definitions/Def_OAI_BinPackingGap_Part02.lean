-- Prove2me | Definitions.Def_OAI_BinPackingGap_Part02
-- name    : OAI_BinPackingGap_Part02
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T18:10:35.663019+00:00
-- url     : https://prove2.me/theorems/696db426-1353-42ce-afc9-71427c192510
-- title:
--   Structural additive gap for bin packing, part 2 of 10 (port of OpenAI's formalization)
-- statement:
--   Part 2 of 10 of a port of OpenAI's Lean formalization of the structural additive gap from the manuscript *Additive hardness and unbounded configuration gaps in bin packing* (OpenAI, September 24, 2026). For every $c$, it constructs an instance with $5B$ items of sizes in $(1/6,1)$ whose individual and type configuration LPs both equal $B$, while the optimum exceeds $B+c$. This part contains the modules `Trees/CompletionGeometry`, `Inventory/CurrentMatches`, `Packing/K4Graph`, `Machines/IntegerPackingArithmetic`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/BinPacking`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `BinPackingGap`, which matches upstream `Model.lean` up to two private lemmas and a section wrapper.
--
--   The development is split into 10 parts only so that each compiles within the platform's time limit. The final part proves `OAI.BinPackingGap.structural_additive_gap`, the first clause of `OAI.BinPackingGap.main_results`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/BinPacking: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Trees/CompletionGeometry.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Inventory/CurrentMatches.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Packing/K4Graph.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/IntegerPackingArithmetic.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf

/-
Structural additive gap for bin packing (port of OpenAI's formalization), part 2 of 10.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/BinPacking/: Trees/CompletionGeometry.lean, Inventory/CurrentMatches.lean, Packing/K4Graph.lean, Machines/IntegerPackingArithmetic.lean
These files formalize part of the manuscript "Additive hardness and unbounded configuration gaps in
bin packing" (OpenAI, September 24, 2026). Copyright OpenAI. Licensed under the Apache License,
Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same
license, on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Model.lean) come from the platform definition `BinPackingGap`, to which upstream Model.lean
is identical up to two private lemmas and a section wrapper.
-/
import Mathlib
import Definitions.Def_OAI_BinPackingGap_Part01

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/BinPacking/Trees/CompletionGeometry.lean =====
namespace OAI

namespace BinPackingGap.Geometry

abbrev Position (m R : ℕ) := Fin m × Fin R

def theta (R : ℕ) {m : ℕ} (e : Fin m) : ℚ :=
  ((R : ℚ) + 1) ^ e.val - 1

def heightCode (R : ℕ) {m : ℕ} (r : Position m R) : ℚ :=
  ((r.2.val : ℚ) + 1) * ((R : ℚ) + 1) ^ r.1.val - 1

def gap (m R : ℕ) : ℚ := 1 / (16 * ((R : ℚ) + 1) ^ m)

def baseline (m R : ℕ) (r : Position m R) : ℚ :=
  1 / 2 + gap m R * heightCode R r

def beta (m R : ℕ) (e : Fin m) : ℚ := gap m R * theta R e

def lambda (m R D ell : ℕ) : ℚ :=
  gap m R / (100 * ((D : ℚ) + 1)) ^ ell

def delta (m R D L : ℕ) : ℚ := lambda m R D L / 10

theorem base_pos (R : ℕ) : 0 < (R : ℚ) + 1 := by positivity

theorem base_one_le (R : ℕ) : 1 ≤ (R : ℚ) + 1 := by
  have hR : (0 : ℚ) ≤ R := Nat.cast_nonneg R
  linarith

theorem widthScale_pos (D : ℕ) : 0 < 100 * ((D : ℚ) + 1) := by positivity

theorem widthScale_one_le (D : ℕ) : 1 ≤ 100 * ((D : ℚ) + 1) := by
  have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg D
  linarith

theorem gap_pos (m R : ℕ) : 0 < gap m R := by
  unfold gap
  positivity

theorem gap_nonneg (m R : ℕ) : 0 ≤ gap m R := (gap_pos m R).le

theorem gap_le_one_sixteen (m R : ℕ) : gap m R ≤ 1 / 16 := by
  unfold gap
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
  have hp : (1 : ℚ) ≤ ((R : ℚ) + 1) ^ m := one_le_pow₀ (base_one_le R)
  linarith

theorem gap_mul_power (m R : ℕ) : gap m R * ((R : ℚ) + 1) ^ m = 1 / 16 := by
  unfold gap
  have hp : ((R : ℚ) + 1) ^ m ≠ 0 := (pow_pos (base_pos R) m).ne'
  field_simp [hp]

theorem theta_nonneg (R : ℕ) {m : ℕ} (e : Fin m) : 0 ≤ theta R e := by
  exact sub_nonneg.mpr (one_le_pow₀ (base_one_le R))

theorem theta_lt_power (R : ℕ) {m : ℕ} (e : Fin m) :
    theta R e < ((R : ℚ) + 1) ^ m := by
  have hp := pow_le_pow_right₀ (base_one_le R) (Nat.le_of_lt e.isLt)
  unfold theta
  linarith

theorem heightCode_nonneg (R : ℕ) {m : ℕ} (r : Position m R) :
    0 ≤ heightCode R r := by
  have hj : (1 : ℚ) ≤ (r.2.val : ℚ) + 1 := by
    have h := (Nat.cast_nonneg r.2.val : (0 : ℚ) ≤ r.2.val)
    linarith
  have hp : (1 : ℚ) ≤ ((R : ℚ) + 1) ^ r.1.val := one_le_pow₀ (base_one_le R)
  have hprod : (1 : ℚ) * 1 ≤ ((r.2.val : ℚ) + 1) * ((R : ℚ) + 1) ^ r.1.val :=
    mul_le_mul hj hp (by norm_num) (by positivity)
  unfold heightCode
  linarith

theorem heightCode_lt_power (R : ℕ) {m : ℕ} (r : Position m R) :
    heightCode R r < ((R : ℚ) + 1) ^ m := by
  have hj : (r.2.val : ℚ) + 1 < (R : ℚ) + 1 := by
    exact_mod_cast Nat.add_lt_add_right r.2.isLt 1
  have hp : 0 < ((R : ℚ) + 1) ^ r.1.val := pow_pos (base_pos R) _
  have he : r.1.val + 1 ≤ m := r.1.isLt
  have hpow := pow_le_pow_right₀ (base_one_le R) he
  have hmul := mul_lt_mul_of_pos_right hj hp
  rw [pow_succ] at hpow
  unfold heightCode
  nlinarith

theorem baseline_lower (m R : ℕ) (r : Position m R) : 1 / 2 ≤ baseline m R r := by
  unfold baseline
  exact le_add_of_nonneg_right (mul_nonneg (gap_nonneg _ _) (heightCode_nonneg _ _))

theorem baseline_upper (m R : ℕ) (r : Position m R) : baseline m R r < 9 / 16 := by
  have h := mul_lt_mul_of_pos_left (heightCode_lt_power R r) (gap_pos m R)
  rw [gap_mul_power] at h
  unfold baseline
  linarith

theorem baseline_range (m R : ℕ) (r : Position m R) :
    1 / 2 ≤ baseline m R r ∧ baseline m R r < 9 / 16 :=
  ⟨baseline_lower _ _ _, baseline_upper _ _ _⟩

theorem beta_nonneg (m R : ℕ) (e : Fin m) : 0 ≤ beta m R e :=
  mul_nonneg (gap_nonneg _ _) (theta_nonneg _ _)

theorem beta_lt_one_sixteen (m R : ℕ) (e : Fin m) : beta m R e < 1 / 16 := by
  have h := mul_lt_mul_of_pos_left (theta_lt_power R e) (gap_pos m R)
  rwa [gap_mul_power] at h

theorem lambda_pos (m R D ell : ℕ) : 0 < lambda m R D ell :=
  div_pos (gap_pos _ _) (pow_pos (widthScale_pos D) ell)

theorem lambda_nonneg (m R D ell : ℕ) : 0 ≤ lambda m R D ell :=
  (lambda_pos _ _ _ _).le

@[simp] theorem lambda_zero (m R D : ℕ) : lambda m R D 0 = gap m R := by
  simp [lambda]

theorem lambda_succ (m R D ell : ℕ) :
    lambda m R D (ell + 1) = lambda m R D ell / (100 * ((D : ℚ) + 1)) := by
  simp only [lambda, pow_succ, div_div]

theorem lambda_antitone (m R D : ℕ) : Antitone (lambda m R D) := by
  intro a b hab
  exact div_le_div_of_nonneg_left (gap_nonneg m R) (pow_pos (widthScale_pos D) a)
    (pow_le_pow_right₀ (widthScale_one_le D) hab)

theorem lambda_le_gap (m R D ell : ℕ) : lambda m R D ell ≤ gap m R := by
  simpa only [lambda_zero] using lambda_antitone m R D (Nat.zero_le ell)

theorem lambda_le_one (m R D ell : ℕ) : lambda m R D ell ≤ 1 := by
  have h := (lambda_le_gap m R D ell).trans (gap_le_one_sixteen m R)
  linarith

theorem lambda_lt_tenth (m R D ell : ℕ) : lambda m R D ell < 1 / 10 := by
  have h := (lambda_le_gap m R D ell).trans (gap_le_one_sixteen m R)
  linarith

theorem lambda_one_le_hundredth (m R D : ℕ) : lambda m R D 1 ≤ gap m R / 100 := by
  unfold lambda
  rw [pow_one]
  apply div_le_div_of_nonneg_left (gap_nonneg _ _) (by norm_num)
  have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg D
  linarith

theorem delta_pos (m R D L : ℕ) : 0 < delta m R D L :=
  div_pos (lambda_pos _ _ _ _) (by norm_num)

theorem delta_nonneg (m R D L : ℕ) : 0 ≤ delta m R D L := (delta_pos _ _ _ _).le

theorem delta_le_tenth (m R D : ℕ) {ell L : ℕ} (h : ell ≤ L) :
    delta m R D L ≤ lambda m R D ell / 10 :=
  div_le_div_of_nonneg_right (lambda_antitone m R D h) (by norm_num)

theorem delta_lt_gap (m R D L : ℕ) : delta m R D L < gap m R := by
  have hd := delta_le_tenth m R D (Nat.zero_le L)
  rw [lambda_zero] at hd
  have hg := gap_pos m R
  linarith

theorem lambda_one_add_two_delta_lt_gap (m R D : ℕ) {L : ℕ} (hL : 1 ≤ L) :
    lambda m R D 1 + 2 * delta m R D L < gap m R := by
  have hd := delta_le_tenth m R D hL
  have hl := lambda_one_le_hundredth m R D
  have hg := gap_pos m R
  linarith

theorem children_succ_lt_parent (m R D ell : ℕ) :
    (4 * (D : ℚ) + 1) * lambda m R D (ell + 1) < lambda m R D ell := by
  rw [lambda_succ, ← mul_div_assoc]
  apply (div_lt_iff₀ (widthScale_pos D)).2
  have hcoeff : 4 * (D : ℚ) + 1 < 100 * ((D : ℚ) + 1) := by
    have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg D
    linarith
  simpa only [mul_comm] using mul_lt_mul_of_pos_right hcoeff (lambda_pos m R D ell)

theorem first_children_lt_gap_twentyfifth (m R D : ℕ) :
    (4 * (D : ℚ) + 1) * lambda m R D 1 < gap m R / 25 := by
  simp only [lambda, pow_one]
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (widthScale_pos D)).2
  have hcoeff : 25 * (4 * (D : ℚ) + 1) < 100 * ((D : ℚ) + 1) := by
    linarith
  have h := mul_lt_mul_of_pos_right hcoeff (gap_pos m R)
  nlinarith

theorem first_children_lt_tenth (m R D : ℕ) :
    (4 * (D : ℚ) + 1) * lambda m R D 1 < 1 / 10 := by
  have h := first_children_lt_gap_twentyfifth m R D
  have hg := gap_le_one_sixteen m R
  linarith

theorem lambda_add_delta_lt_three (m R D : ℕ) {ell L : ℕ} (h : ell ≤ L) :
    lambda m R D ell + delta m R D L < 3 * lambda m R D ell := by
  have hd := delta_le_tenth m R D h
  have hl := lambda_pos m R D ell
  linarith

end BinPackingGap.Geometry

namespace BinPackingGap

def completion (b : ℚ) (short : Bool) (globalLen localLen delta : ℚ) : ℚ :=
  b - (if short then delta else 0) - globalLen - localLen

def completionInterval (b : ℚ) (short : Bool) (globalLen localLen delta : ℚ) :
    Set ℚ := Set.Ico (completion b short globalLen localLen delta) b

@[simp] theorem completion_false (b globalLen localLen delta : ℚ) :
    completion b false globalLen localLen delta = b - globalLen - localLen := by
  simp [completion]

@[simp] theorem completion_true (b globalLen localLen delta : ℚ) :
    completion b true globalLen localLen delta = b - delta - globalLen - localLen := by
  simp [completion]

theorem baseline_sub_completion (b : ℚ) (short : Bool) (globalLen localLen delta : ℚ) :
    b - completion b short globalLen localLen delta =
      (if short then delta else 0) + globalLen + localLen := by
  unfold completion
  ring

theorem completion_le_baseline (b : ℚ) (short : Bool) (globalLen localLen delta : ℚ)
    (hglobal : 0 ≤ globalLen) (hlocal : 0 ≤ localLen) (hdelta : 0 ≤ delta) :
    completion b short globalLen localLen delta ≤ b := by
  cases short <;> simp only [completion_false, completion_true] <;> linarith

theorem completion_length_nonneg (b : ℚ) (short : Bool) (globalLen localLen delta : ℚ)
    (hglobal : 0 ≤ globalLen) (hlocal : 0 ≤ localLen) (hdelta : 0 ≤ delta) :
    0 ≤ b - completion b short globalLen localLen delta :=
  sub_nonneg.mpr (completion_le_baseline b short globalLen localLen delta
    hglobal hlocal hdelta)

@[simp] theorem mem_completionInterval (b : ℚ) (short : Bool)
    (globalLen localLen delta a : ℚ) :
    a ∈ completionInterval b short globalLen localLen delta ↔
      completion b short globalLen localLen delta ≤ a ∧ a < b := Iff.rfl

theorem completion_le_deadline_iff (b : ℚ) (short : Bool)
    (globalLen localLen delta deadline : ℚ) :
    completion b short globalLen localLen delta ≤ deadline ↔
      b - (if short then delta else 0) - globalLen - localLen - deadline ≤ 0 := by
  unfold completion
  exact sub_nonpos.symm

theorem completion_zero_global_length_le (b : ℚ) (short : Bool) (localLen delta : ℚ)
    (hdelta : 0 ≤ delta) :
    b - completion b short 0 localLen delta ≤ localLen + delta := by
  cases short <;> simp only [completion_false, completion_true] <;> linarith

theorem completion_zero_global_interval_subset (b : ℚ) (short : Bool)
    (localLen delta : ℚ) (hdelta : 0 ≤ delta) :
    completionInterval b short 0 localLen delta ⊆ Set.Ico (b - (localLen + delta)) b := by
  intro a ha
  have hlength := completion_zero_global_length_le b short localLen delta hdelta
  exact ⟨by linarith [ha.1], ha.2⟩

theorem completion_zero_global_bounds (b : ℚ) (short : Bool) (localLen delta : ℚ)
    (hlocal : 0 ≤ localLen) (hdelta : 0 ≤ delta) :
    completion b short 0 localLen delta ∈ Set.Icc (b - (localLen + delta)) b := by
  constructor
  · linarith [completion_zero_global_length_le b short localLen delta hdelta]
  · exact completion_le_baseline b short 0 localLen delta le_rfl hlocal hdelta

@[simp] theorem completion_long_zero_lengths (b delta : ℚ) :
    completion b false 0 0 delta = b := by simp

@[simp] theorem completion_short_zero_lengths (b delta : ℚ) :
    completion b true 0 0 delta = b - delta := by simp

@[simp] theorem completionInterval_long_zero_lengths (b delta : ℚ) :
    completionInterval b false 0 0 delta = ∅ := by
  simp [completionInterval]

theorem completionInterval_short_zero_lengths (b delta : ℚ) :
    completionInterval b true 0 0 delta = Set.Ico (b - delta) b := by
  simp [completionInterval]

theorem completion_plus_le_one (b : ℚ) (short : Bool) (globalLen localLen delta : ℚ)
    (hbaseline : b ≤ 1) (hglobal : 0 ≤ globalLen) (hlocal : 0 ≤ localLen)
    (hdelta : 0 ≤ delta) : completion b short globalLen localLen delta ≤ 1 :=
  (completion_le_baseline b short globalLen localLen delta hglobal hlocal hdelta).trans
    hbaseline

theorem completion_minus_gt_one (b : ℚ) (short : Bool) (globalLen localLen delta lambdaOne : ℚ)
    (hbaseline : 4 ≤ b) (hshort : short = false) (hglobal : globalLen ≤ 1)
    (hlocal : localLen ≤ lambdaOne) (hlambda : lambdaOne < 1) :
    1 < completion b short globalLen localLen delta := by
  subst short
  rw [completion_false]
  linarith

theorem not_mem_plus_completionInterval (b : ℚ) (short : Bool)
    (globalLen localLen delta a : ℚ) (hbaseline : b ≤ 1) (ha : 1 ≤ a) :
    a ∉ completionInterval b short globalLen localLen delta := by
  intro hmem
  linarith [hmem.2]

theorem not_mem_minus_completionInterval (b : ℚ) (short : Bool)
    (globalLen localLen delta lambdaOne a : ℚ) (hbaseline : 4 ≤ b)
    (hshort : short = false) (hglobal : globalLen ≤ 1)
    (hlocal : localLen ≤ lambdaOne) (hlambda : lambdaOne < 1) (ha : a ≤ 1) :
    a ∉ completionInterval b short globalLen localLen delta := by
  intro hmem
  have hh := completion_minus_gt_one b short globalLen localLen delta lambdaOne
    hbaseline hshort hglobal hlocal hlambda
  linarith [hmem.1]

theorem completion_zero_global_geometry_length_le (m R D L ell : ℕ)
    (b : ℚ) (short : Bool) :
    b - completion b short 0 (Geometry.lambda m R D ell) (Geometry.delta m R D L) ≤
      Geometry.lambda m R D ell + Geometry.delta m R D L :=
  completion_zero_global_length_le b short _ _ (Geometry.delta_nonneg m R D L)

theorem completion_minus_geometry_gt_one (m R D L : ℕ) (b : ℚ) (short : Bool)
    (globalLen localLen : ℚ) (hbaseline : 4 ≤ b) (hshort : short = false)
    (hglobal : globalLen ≤ 1) (hlocal : localLen ≤ Geometry.lambda m R D 1) :
    1 < completion b short globalLen localLen (Geometry.delta m R D L) := by
  apply completion_minus_gt_one b short globalLen localLen _ (Geometry.lambda m R D 1)
    hbaseline hshort hglobal hlocal
  linarith [Geometry.lambda_lt_tenth m R D 1]

theorem completion_job_interval (m R D L : ℕ) (r : Geometry.Position m R) :
    completionInterval (Geometry.baseline m R r) true 0 0 (Geometry.delta m R D L) =
      Set.Ico (Geometry.baseline m R r - Geometry.delta m R D L)
        (Geometry.baseline m R r) :=
  completionInterval_short_zero_lengths _ _

end BinPackingGap

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Inventory/CurrentMatches.lean =====
namespace OAI

noncomputable section

namespace BinPackingGap
namespace CoverageCounts

section FiniteCounts

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β]

theorem interval_prefix_card [LinearOrder γ] (s : Finset α) (h b : α → γ)
    (hle : ∀ i ∈ s, h i ≤ b i) (a : γ) :
    (s.filter fun i => h i ≤ a).card =
      (s.filter fun i => b i ≤ a).card +
        (s.filter fun i => h i ≤ a ∧ a < b i).card := by
  classical
  have hunion : (s.filter fun i => h i ≤ a) =
      (s.filter fun i => b i ≤ a) ∪
        (s.filter fun i => h i ≤ a ∧ a < b i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨his, hia⟩
      by_cases hba : b i ≤ a
      · exact Or.inl ⟨his, hba⟩
      · exact Or.inr ⟨his, hia, lt_of_not_ge hba⟩
    · rintro (⟨his, hba⟩ | ⟨his, hia, _⟩)
      · exact ⟨his, (hle i his).trans hba⟩
      · exact ⟨his, hia⟩
  have hdis : Disjoint (s.filter fun i => b i ≤ a)
      (s.filter fun i => h i ≤ a ∧ a < b i) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (not_lt_of_ge (Finset.mem_filter.mp hi).2)
      (Finset.mem_filter.mp hj).2.2
  rw [hunion, Finset.card_union_of_disjoint hdis]

omit [DecidableEq α] in
theorem ordered_short_long_partition [LinearOrder γ]
    (s : Finset α) (position : α → γ) (current : γ) (short : α → Prop)
    [DecidablePred short] (horder : ∀ i ∈ s, position i ≤ current) :
    s.card = (s.filter fun i => position i < current).card +
      (s.filter fun i => position i = current ∧ short i).card +
      (s.filter fun i => position i = current ∧ ¬ short i).card := by
  classical
  have hexact : (s.filter fun i => ¬ position i < current) =
      (s.filter fun i => position i = current) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨his, hi⟩
      exact ⟨his, le_antisymm (horder i his) (le_of_not_gt hi)⟩
    · rintro ⟨his, hi⟩
      exact ⟨his, by rw [hi]; exact lt_irrefl _⟩
  have hpositions := Finset.card_filter_add_card_filter_not
    (s := s) (fun i => position i < current)
  rw [hexact] at hpositions
  have hlengths := Finset.card_filter_add_card_filter_not
    (s := s.filter fun i => position i = current) short
  simp only [Finset.filter_filter] at hlengths
  omega

theorem card_le_good_card_add {s bad : Finset α} {K : ℕ}
    (hbad : bad.card ≤ K) : s.card ≤ (s \ bad).card + K := by
  have hinter : (s ∩ bad).card ≤ K :=
    (Finset.card_le_card Finset.inter_subset_right).trans hbad
  have hsplit := Finset.card_sdiff_add_card_inter s bad
  omega

omit [DecidableEq β] in
theorem card_le_target_add_loss {s bad : Finset α} {t : Finset β} {K : ℕ}
    (f : α → β) (hbad : bad.card ≤ K)
    (hmap : ∀ i ∈ s \ bad, f i ∈ t)
    (hinj : Set.InjOn f (↑(s \ bad : Finset α) : Set α)) : s.card ≤ t.card + K := by
  have hgood := Finset.card_le_card_of_injOn f hmap hinj
  have htotal := card_le_good_card_add (s := s) hbad
  omega

omit [DecidableEq β] in
theorem card_add_card_le_of_disjoint_injections
    (s t : Finset α) (resources : Finset β) (row : α → β)
    (hdis : Disjoint s t)
    (hmap : ∀ i ∈ s ∪ t, row i ∈ resources)
    (hinj : Set.InjOn row (↑(s ∪ t : Finset α) : Set α)) : s.card + t.card ≤ resources.card := by
  rw [← Finset.card_union_of_disjoint hdis]
  exact Finset.card_le_card_of_injOn row hmap hinj

omit [DecidableEq β] in
theorem card_three_le_of_disjoint_injections
    (s t u : Finset α) (resources : Finset β) (row : α → β)
    (hst : Disjoint s t) (hsu : Disjoint s u) (htu : Disjoint t u)
    (hmap : ∀ i ∈ (s ∪ t) ∪ u, row i ∈ resources)
    (hinj : Set.InjOn row (↑((s ∪ t) ∪ u : Finset α) : Set α)) :
    s.card + t.card + u.card ≤ resources.card := by
  have hdis : Disjoint (s ∪ t) u := by
    apply Finset.disjoint_left.mpr
    intro i hi hu
    rcases Finset.mem_union.mp hi with hs | ht
    · exact Finset.disjoint_left.mp hsu hs hu
    · exact Finset.disjoint_left.mp htu ht hu
  have hcount := card_add_card_le_of_disjoint_injections
    (s ∪ t) u resources row hdis hmap hinj
  rwa [Finset.card_union_of_disjoint hst] at hcount

theorem card_le_add_of_subset_union (s t u : Finset α) (h : s ⊆ t ∪ u) :
    s.card ≤ t.card + u.card :=
  (Finset.card_le_card h).trans (Finset.card_union_le _ _)

end FiniteCounts

theorem displaced_baseline_bound {A B tree jobs used goodEarlier ξ K : ℕ}
    (hA : A ≤ tree + used) (hB : B = tree + jobs)
    (hrows : used + goodEarlier + ξ ≤ 2 * jobs)
    (hkeys : jobs ≤ goodEarlier + 3 * K) : A + ξ ≤ B + 3 * K := by
  omega

theorem coverage_lower_bound {A B C I d K : ℕ}
    (hpartition : C = A + I) (hdeadline : B + d ≤ C + 3 * K)
    (hbaseline : A ≤ B + 3 * K) : d ≤ I + 6 * K := by
  omega

theorem displaced_short_correction {A B C I d K ξ xplus shortM : ℕ}
    (hpartition : C = A + I) (hdeadline : B + d ≤ C + 3 * K)
    (hbaseline : A + ξ ≤ B + 3 * K) (hcoverage : I ≤ xplus + shortM) :
    d + ξ ≤ xplus + shortM + 6 * K := by
  omega

theorem short_le_displaced_add_long {d K ξ goodCurrent shortM shortG longG : ℕ}
    (hkeys : d ≤ goodCurrent + 3 * K)
    (hpartition : goodCurrent = ξ + shortG + longG)
    (hshort : shortM + shortG ≤ d) : shortM ≤ ξ + longG + 3 * K := by
  omega

theorem long_match_lower_bound {d K ξ xplus shortM longG : ℕ}
    (hcorrection : d + ξ ≤ xplus + shortM + 6 * K)
    (hshort : shortM ≤ ξ + longG + 3 * K) :
    d ≤ longG + xplus + 9 * K := by
  omega

end CoverageCounts
end BinPackingGap

namespace BinPackingGap.IntervalCoverage

variable {ι κ τ α : Type*} [LinearOrder α]

def prefixSet [Fintype ι] (f : ι → α) (a : α) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => f i ≤ a

def prefixCount [Fintype ι] (f : ι → α) (a : α) : ℕ := (prefixSet f a).card

def coverageSet [Fintype ι] (h b : ι → α) (a : α) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => h i ≤ a ∧ a < b i

def coverageCount [Fintype ι] (h b : ι → α) (a : α) : ℕ :=
  (coverageSet h b a).card

@[simp] theorem mem_prefixSet [Fintype ι] (f : ι → α) (a : α) (i : ι) :
    i ∈ prefixSet f a ↔ f i ≤ a := by
  classical
  simp [prefixSet]

@[simp] theorem mem_coverageSet [Fintype ι] (h b : ι → α) (a : α) (i : ι) :
    i ∈ coverageSet h b a ↔ h i ≤ a ∧ a < b i := by
  classical
  simp [coverageSet]

theorem completion_prefix_identity [Fintype ι] (h b : ι → α)
    (hle : ∀ i, h i ≤ b i) (a : α) :
    prefixCount h a = prefixCount b a + coverageCount h b a := by
  classical
  simpa only [prefixCount, coverageCount, prefixSet, coverageSet] using
    CoverageCounts.interval_prefix_card Finset.univ h b (fun i _ => hle i) a

structure ShiftData (Copy Test : Type*) (d : ℕ) (Coordinate : Type*)
    [LinearOrder Coordinate] where
  baseline : Copy → Coordinate
  left : Test → Coordinate
  right : Test → Coordinate
  designated : (Test × Fin d) ↪ Copy
  baseline_designated : ∀ q, baseline (designated q) = right q.1
  left_le_right : ∀ t, left t ≤ right t

namespace ShiftData

variable {d : ℕ} (D : ShiftData ι τ d α)

local instance : DecidableEq ι := Classical.decEq ι

def deadline (i : ι) : α := by
  classical
  exact if hi : ∃ q, D.designated q = i then D.left (Classical.choose hi).1
    else D.baseline i

@[simp] theorem deadline_designated (q : τ × Fin d) :
    D.deadline (D.designated q) = D.left q.1 := by
  classical
  have hi : ∃ q', D.designated q' = D.designated q := ⟨q, rfl⟩
  have heq : Classical.choose hi = q := D.designated.injective (Classical.choose_spec hi)
  simp only [deadline, dite_eq_left hi, heq]

theorem deadline_undesignated (i : ι) (hi : ∀ q, D.designated q ≠ i) :
    D.deadline i = D.baseline i := by
  classical
  have hn : ¬ ∃ q, D.designated q = i := by
    rintro ⟨q, hq⟩
    exact hi q hq
  simp only [deadline, dite_eq_right hn]

theorem designated_block_card (t : τ) :
    ((Finset.univ : Finset (Fin d)).image (fun j => D.designated (t, j))).card = d := by
  classical
  rw [Finset.card_image_of_injective]
  · exact Fintype.card_fin d
  · intro j k hjk
    exact congrArg Prod.snd (D.designated.injective hjk)

def activeTests [Fintype τ] (a : α) : Finset τ := by
  classical
  exact Finset.univ.filter fun t => D.left t ≤ a ∧ a < D.right t

@[simp] theorem mem_activeTests [Fintype τ] (a : α) (t : τ) :
    t ∈ D.activeTests a ↔ D.left t ≤ a ∧ a < D.right t := by
  classical
  simp [activeTests]

theorem deadline_prefix_of_agrees [Fintype ι] [Fintype τ]
    (z : ι → α)
    (hdesignated : ∀ q, z (D.designated q) = D.left q.1)
    (hother : ∀ i, (∀ q, D.designated q ≠ i) → z i = D.baseline i)
    (a : α) :
    prefixCount z a = prefixCount D.baseline a + d * (D.activeTests a).card := by
  classical
  have hle : ∀ i, z i ≤ D.baseline i := by
    intro i
    by_cases hi : ∃ q, D.designated q = i
    · obtain ⟨q, rfl⟩ := hi
      rw [hdesignated, D.baseline_designated]
      exact D.left_le_right q.1
    · rw [hother i (by simpa only [not_exists] using hi)]
  have hset : coverageSet z D.baseline a =
      ((D.activeTests a).product (Finset.univ : Finset (Fin d))).map D.designated := by
    ext i
    simp only [mem_coverageSet, Finset.mem_map, Finset.product_eq_sprod, Finset.mem_product,
      mem_activeTests, Finset.mem_univ, and_true]
    constructor
    · intro hi
      have hex : ∃ q, D.designated q = i := by
        by_contra hn
        have he := hother i (by simpa only [not_exists] using hn)
        exact (not_lt_of_ge (he ▸ hi.1)) hi.2
      obtain ⟨q, rfl⟩ := hex
      exact ⟨q, by simpa only [hdesignated, D.baseline_designated] using hi, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      simpa only [hdesignated, D.baseline_designated] using hq
  rw [completion_prefix_identity z D.baseline hle a]
  unfold coverageCount
  rw [hset, Finset.card_map, Finset.product_eq_sprod, Finset.card_product,
    Finset.card_univ, Fintype.card_fin]
  rw [Nat.mul_comm]

theorem deadline_prefix [Fintype ι] [Fintype τ] (a : α) :
    prefixCount D.deadline a = prefixCount D.baseline a + d * (D.activeTests a).card :=
  D.deadline_prefix_of_agrees D.deadline D.deadline_designated D.deadline_undesignated a

theorem activeTests_card [Fintype τ]
    (hdisjoint : ∀ s t, s ≠ t →
      Disjoint (Set.Ico (D.left s) (D.right s)) (Set.Ico (D.left t) (D.right t)))
    (a : α) :
    (D.activeTests a).card = if ∃ t, D.left t ≤ a ∧ a < D.right t then 1 else 0 := by
  classical
  have hle : (D.activeTests a).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro s hs t ht
    by_contra hst
    exact Set.disjoint_left.mp (hdisjoint s t hst)
      (D.mem_activeTests a s |>.mp hs) (D.mem_activeTests a t |>.mp ht)
  split_ifs with hex
  · obtain ⟨t, ht⟩ := hex
    have hpos := Finset.card_pos.mpr ⟨t, (D.mem_activeTests a t).mpr ht⟩
    omega
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact hex ⟨t, (D.mem_activeTests a t).mp ht⟩

theorem deadline_prefix_disjoint_of_agrees [Fintype ι] [Fintype τ]
    (z : ι → α)
    (hdesignated : ∀ q, z (D.designated q) = D.left q.1)
    (hother : ∀ i, (∀ q, D.designated q ≠ i) → z i = D.baseline i)
    (hdisjoint : ∀ s t, s ≠ t →
      Disjoint (Set.Ico (D.left s) (D.right s)) (Set.Ico (D.left t) (D.right t)))
    (a : α) :
    prefixCount z a = prefixCount D.baseline a +
      d * (if ∃ t, D.left t ≤ a ∧ a < D.right t then 1 else 0) := by
  rw [D.deadline_prefix_of_agrees z hdesignated hother, D.activeTests_card hdisjoint]

theorem deadline_prefix_disjoint [Fintype ι] [Fintype τ]
    (hdisjoint : ∀ s t, s ≠ t →
      Disjoint (Set.Ico (D.left s) (D.right s)) (Set.Ico (D.left t) (D.right t)))
    (a : α) :
    prefixCount D.deadline a = prefixCount D.baseline a +
      d * (if ∃ t, D.left t ≤ a ∧ a < D.right t then 1 else 0) :=
  D.deadline_prefix_disjoint_of_agrees D.deadline D.deadline_designated
    D.deadline_undesignated hdisjoint a

end ShiftData

theorem exists_equiv_of_prefix_dominance [Fintype ι] [Fintype κ]
    (h : ι → α) (z : κ → α) (hcard : Fintype.card ι = Fintype.card κ)
    (hprefix : ∀ a, prefixCount z a ≤ prefixCount h a) :
    ∃ e : ι ≃ κ, ∀ i, h i ≤ z (e i) := by
  classical
  let neighbors : ι → Finset κ := fun i => Finset.univ.filter fun j => h i ≤ z j
  have hall : ∀ s : Finset ι, s.card ≤ (s.biUnion neighbors).card := by
    intro s
    let N := s.biUnion neighbors
    let bad := (Finset.univ : Finset κ) \ N
    have hpartition : bad.card + N.card = Fintype.card κ := by
      simpa only [bad, Finset.card_univ] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ N)
    by_cases hbad : bad.Nonempty
    · obtain ⟨j, hj, hmax⟩ := bad.exists_max_image z hbad
      have hN : j ∉ N := (Finset.mem_sdiff.mp hj).2
      have hd : Disjoint s (prefixSet h (z j)) := by
        apply Finset.disjoint_left.mpr
        intro i hi hip
        apply hN
        exact Finset.mem_biUnion.mpr ⟨i, hi, by
          simpa only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and,
            mem_prefixSet] using hip⟩
      have hsum : s.card + prefixCount h (z j) ≤ Fintype.card ι := by
        rw [prefixCount, ← Finset.card_union_of_disjoint hd]
        exact Finset.card_le_univ _
      have hb : bad.card ≤ prefixCount z (z j) := by
        apply Finset.card_le_card
        intro k hk
        exact (mem_prefixSet z (z j) k).mpr (hmax k hk)
      have hp := hprefix (z j)
      change s.card ≤ N.card
      omega
    · have hb : bad.card = 0 := Finset.card_eq_zero.mpr
        (Finset.not_nonempty_iff_eq_empty.mp hbad)
      have hs := Finset.card_le_univ s
      change s.card ≤ N.card
      omega
  obtain ⟨f, hf, hmatch⟩ :=
    (FiniteHall.all_card_le_biUnion_card_iff_existsInjective neighbors).mp hall
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩
  refine ⟨Equiv.ofBijective f hbij, ?_⟩
  intro i
  change h i ≤ z (f i)
  have hi := hmatch i
  simpa only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] using hi

end BinPackingGap.IntervalCoverage

namespace BinPackingGap
namespace Coverage

variable {I : Instance} {b n : ℕ}

def goodTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) : Finset (p.TableBin cls) := by
  classical
  exact Finset.univ.filter fun t => p.IsGoodTableBin cls label t ∧
    label (p.itemAtRole cls t .anchor) = some v

def mainTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) : Finset (p.TableBin cls) := by
  classical
  exact (goodTuplesAt p cls label v).filter fun t => p.tablePattern cls t ≠ .edgeJob

def edgeTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) : Finset (p.TableBin cls) := by
  classical
  exact (goodTuplesAt p cls label v).filter fun t => p.tablePattern cls t = .edgeJob

@[simp] theorem mem_goodTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (t : p.TableBin cls) :
    t ∈ goodTuplesAt p cls label v ↔ p.IsGoodTableBin cls label t ∧
      label (p.itemAtRole cls t .anchor) = some v := by
  classical
  simp [goodTuplesAt]

@[simp] theorem mem_mainTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (t : p.TableBin cls) :
    t ∈ mainTuplesAt p cls label v ↔ p.IsGoodTableBin cls label t ∧
      label (p.itemAtRole cls t .anchor) = some v ∧
        p.tablePattern cls t ≠ .edgeJob := by
  classical
  simp [mainTuplesAt, and_assoc]

@[simp] theorem mem_edgeTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (t : p.TableBin cls) :
    t ∈ edgeTuplesAt p cls label v ↔ p.IsGoodTableBin cls label t ∧
      label (p.itemAtRole cls t .anchor) = some v ∧
        p.tablePattern cls t = .edgeJob := by
  classical
  simp [edgeTuplesAt, and_assoc]

theorem mainTuplesAt_subset_good (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) :
    mainTuplesAt p cls label v ⊆ goodTuplesAt p cls label v := by
  classical
  exact Finset.filter_subset _ _

theorem edgeTuplesAt_subset_good (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) :
    edgeTuplesAt p cls label v ⊆ goodTuplesAt p cls label v := by
  classical
  exact Finset.filter_subset _ _

theorem goodTuplesAt_eq_union (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) :
    goodTuplesAt p cls label v =
      mainTuplesAt p cls label v ∪ edgeTuplesAt p cls label v := by
  classical
  ext t
  by_cases h : p.tablePattern cls t = .edgeJob <;>
    simp [mainTuplesAt, edgeTuplesAt, h]

theorem mainTuplesAt_disjoint_edge (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v w : Fin n) :
    Disjoint (mainTuplesAt p cls label v) (edgeTuplesAt p cls label w) := by
  apply Finset.disjoint_left.mpr
  intro t ht hu
  exact ((mem_mainTuplesAt p cls label v t).mp ht).2.2
    (((mem_edgeTuplesAt p cls label w t).mp hu).2.2)

theorem goodTuplesAt_disjoint_label (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) {v w : Fin n} (hvw : v ≠ w) :
    Disjoint (goodTuplesAt p cls label v) (goodTuplesAt p cls label w) := by
  apply Finset.disjoint_left.mpr
  intro t ht hu
  have hv := ((mem_goodTuplesAt p cls label v t).mp ht).2
  have hw := ((mem_goodTuplesAt p cls label w t).mp hu).2
  exact hvw (Option.some.inj (hv.symm.trans hw))

theorem mainTuplesAt_disjoint_label (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) {v w : Fin n} (hvw : v ≠ w) :
    Disjoint (mainTuplesAt p cls label v) (mainTuplesAt p cls label w) :=
  (goodTuplesAt_disjoint_label p cls label hvw).mono
    (mainTuplesAt_subset_good p cls label v) (mainTuplesAt_subset_good p cls label w)

theorem edgeTuplesAt_disjoint_label (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) {v w : Fin n} (hvw : v ≠ w) :
    Disjoint (edgeTuplesAt p cls label v) (edgeTuplesAt p cls label w) :=
  (goodTuplesAt_disjoint_label p cls label hvw).mono
    (edgeTuplesAt_subset_good p cls label v) (edgeTuplesAt_subset_good p cls label w)

def roleItems (p : Packing I b) (cls : I.Item → Subclass)
    (s : Finset (p.TableBin cls)) (role : Role) : Finset I.Item :=
  s.image fun t => p.itemAtRole cls t role

@[simp] theorem roleItems_card (p : Packing I b) (cls : I.Item → Subclass)
    (s : Finset (p.TableBin cls)) (role : Role) : (roleItems p cls s role).card = s.card :=
  Finset.card_image_of_injective s (p.itemAtRole_injective cls role)

def anchorItemsAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i => (cls i).role = .anchor ∧ label i = some v

@[simp] theorem mem_anchorItemsAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (i : I.Item) :
    i ∈ anchorItemsAt (I := I) cls label v ↔
      (cls i).role = .anchor ∧ label i = some v := by
  classical
  simp [anchorItemsAt]

def badAnchorsAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) : Finset I.Item :=
  anchorItemsAt (I := I) cls label v \
    roleItems p cls (goodTuplesAt p cls label v) .anchor

@[simp] theorem mem_badAnchorsAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (i : I.Item) :
    i ∈ badAnchorsAt p cls label v ↔
      i ∈ anchorItemsAt (I := I) cls label v ∧
        i ∉ roleItems p cls (goodTuplesAt p cls label v) .anchor := by
  simp only [badAnchorsAt, Finset.mem_sdiff]

theorem good_anchorItems_subset (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) :
    roleItems p cls (goodTuplesAt p cls label v) .anchor ⊆
      anchorItemsAt (I := I) cls label v := by
  intro i hi
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
  exact (mem_anchorItemsAt cls label v _).mpr
    ⟨p.itemAtRole_role cls t .anchor, ((mem_goodTuplesAt p cls label v t).mp ht).2⟩

theorem card_le_role_resources (p : Packing I b) (cls : I.Item → Subclass)
    (s : Finset (p.TableBin cls)) (role : Role) (resources : Finset I.Item)
    (hmap : ∀ t ∈ s, p.itemAtRole cls t role ∈ resources) : s.card ≤ resources.card :=
  Finset.card_le_card_of_injOn (fun t => p.itemAtRole cls t role) hmap
    (p.itemAtRole_injective cls role).injOn

theorem card_three_le_row_resources (p : Packing I b) (cls : I.Item → Subclass)
    (s t u : Finset (p.TableBin cls)) (resources : Finset I.Item)
    (hst : Disjoint s t) (hsu : Disjoint s u) (htu : Disjoint t u)
    (hmap : ∀ x ∈ (s ∪ t) ∪ u, p.itemAtRole cls x .x ∈ resources) :
    s.card + t.card + u.card ≤ resources.card :=
  CoverageCounts.card_three_le_of_disjoint_injections s t u resources
    (fun x => p.itemAtRole cls x .x) hst hsu htu hmap
    (p.itemAtRole_injective cls .x).injOn

def tupleCompletion (p : Packing I b) (cls : I.Item → Subclass)
    (baseline : I.Item → ℚ) (short : I.Item → Bool)
    (globalLen localLen : I.Item → ℚ) (delta : ℚ) (t : p.TableBin cls) : ℚ :=
  completion (baseline (p.itemAtRole cls t .x)) (short (p.itemAtRole cls t .x))
    (globalLen (p.itemAtRole cls t .«global»))
    (localLen (p.itemAtRole cls t .«local»)) delta

theorem tupleCompletion_le_baseline (p : Packing I b) (cls : I.Item → Subclass)
    (baseline : I.Item → ℚ) (short : I.Item → Bool)
    (globalLen localLen : I.Item → ℚ) (delta : ℚ)
    (hglobal : ∀ i, 0 ≤ globalLen i) (hlocal : ∀ i, 0 ≤ localLen i)
    (hdelta : 0 ≤ delta) (t : p.TableBin cls) :
    tupleCompletion p cls baseline short globalLen localLen delta t ≤
      baseline (p.itemAtRole cls t .x) :=
  completion_le_baseline _ _ _ _ _ (hglobal _) (hlocal _) hdelta

def baselinePrefixAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (a : ℚ) : Finset (p.TableBin cls) :=
  (mainTuplesAt p cls label v).filter fun t => baseline (p.itemAtRole cls t .x) ≤ a

def completionPrefixAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (finish : p.TableBin cls → ℚ) (a : ℚ) : Finset (p.TableBin cls) :=
  (mainTuplesAt p cls label v).filter fun t => finish t ≤ a

def coveringTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (finish : p.TableBin cls → ℚ) (a : ℚ) :
    Finset (p.TableBin cls) :=
  (mainTuplesAt p cls label v).filter fun t =>
    finish t ≤ a ∧ a < baseline (p.itemAtRole cls t .x)

theorem completion_prefix_decomposition (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (finish : p.TableBin cls → ℚ)
    (hle : ∀ t ∈ mainTuplesAt p cls label v, finish t ≤ baseline (p.itemAtRole cls t .x))
    (a : ℚ) :
    (completionPrefixAt p cls label v finish a).card =
      (baselinePrefixAt p cls label v baseline a).card +
        (coveringTuplesAt p cls label v baseline finish a).card :=
  CoverageCounts.interval_prefix_card (mainTuplesAt p cls label v) finish
    (fun t => baseline (p.itemAtRole cls t .x)) hle a

theorem literal_completion_prefix_decomposition
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (short : I.Item → Bool)
    (globalLen localLen : I.Item → ℚ) (delta a : ℚ)
    (hglobal : ∀ i, 0 ≤ globalLen i) (hlocal : ∀ i, 0 ≤ localLen i)
    (hdelta : 0 ≤ delta) :
    (completionPrefixAt p cls label v
      (tupleCompletion p cls baseline short globalLen localLen delta) a).card =
      (baselinePrefixAt p cls label v baseline a).card +
        (coveringTuplesAt p cls label v baseline
          (tupleCompletion p cls baseline short globalLen localLen delta) a).card :=
  completion_prefix_decomposition p cls label v baseline _
    (fun t _ => tupleCompletion_le_baseline p cls baseline short globalLen localLen delta
      hglobal hlocal hdelta t) a

def deadlinePrefixAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (deadline : I.Item → ℚ) (a : ℚ) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i => cls i = .z ∧ label i = some v ∧ deadline i ≤ a

@[simp] theorem mem_deadlinePrefixAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (deadline : I.Item → ℚ) (a : ℚ) (i : I.Item) :
    i ∈ deadlinePrefixAt (I := I) cls label v deadline a ↔
      cls i = .z ∧ label i = some v ∧ deadline i ≤ a := by
  classical
  simp [deadlinePrefixAt]

theorem good_deadline_subset_completed_anchor_image
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (deadline : I.Item → ℚ) (finish : p.TableBin cls → ℚ) (a : ℚ)
    (hfeasible : ∀ t ∈ mainTuplesAt p cls label v,
      finish t ≤ deadline (p.itemAtRole cls t .anchor)) :
    deadlinePrefixAt (I := I) cls label v deadline a \ badAnchorsAt p cls label v ⊆
      roleItems p cls (completionPrefixAt p cls label v finish a) .anchor := by
  classical
  intro i hi
  obtain ⟨hi, hnotbad⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨hcls, hlabel, hdeadline⟩ :=
    (mem_deadlinePrefixAt cls label v deadline a i).mp hi
  have hanchor : i ∈ anchorItemsAt (I := I) cls label v := by
    apply (mem_anchorItemsAt cls label v i).mpr
    exact ⟨by rw [hcls]; rfl, hlabel⟩
  have hused : i ∈ roleItems p cls (goodTuplesAt p cls label v) .anchor := by
    by_contra h
    exact hnotbad ((mem_badAnchorsAt p cls label v i).mpr ⟨hanchor, h⟩)
  obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hused
  have hM : t ∈ mainTuplesAt p cls label v := by
    have htgood := (mem_goodTuplesAt p cls label v t).mp ht
    refine (mem_mainTuplesAt p cls label v t).mpr ⟨htgood.1, htgood.2, ?_⟩
    intro hedge
    have hsub := p.itemAtRole_subclass cls t .anchor
    rw [hedge] at hsub
    have hnot : (Subclass.z : Subclass) = .y := by
      calc
        Subclass.z = cls i := hcls.symm
        _ = cls (p.itemAtRole cls t .anchor) := congrArg cls hti.symm
        _ = Subclass.y := hsub
    cases hnot
  apply Finset.mem_image.mpr
  refine ⟨t, ?_, hti⟩
  apply Finset.mem_filter.mpr
  refine ⟨hM, (hfeasible t hM).trans ?_⟩
  simpa only [hti] using hdeadline

theorem deadline_prefix_le_completion_add_loss
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (deadline : I.Item → ℚ) (finish : p.TableBin cls → ℚ) (a : ℚ) (K : ℕ)
    (hbad : (badAnchorsAt p cls label v).card ≤ 3 * K)
    (hfeasible : ∀ t ∈ mainTuplesAt p cls label v,
      finish t ≤ deadline (p.itemAtRole cls t .anchor)) :
    (deadlinePrefixAt (I := I) cls label v deadline a).card ≤
      (completionPrefixAt p cls label v finish a).card + 3 * K := by
  have hcount := Finset.card_le_card
    (good_deadline_subset_completed_anchor_image p cls label v deadline finish a hfeasible)
  rw [roleItems_card] at hcount
  have hloss := CoverageCounts.card_le_good_card_add
    (s := deadlinePrefixAt (I := I) cls label v deadline a) hbad
  omega

def jobRowPrefixAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (a : ℚ) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i => cls i = .s ∧ label i = some v ∧ baseline i ≤ a

def treeRowPrefixAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (a : ℚ) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i =>
    (cls i = .tp ∨ cls i = .tm) ∧ label i = some v ∧ baseline i ≤ a

def keyPrefixAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (a : ℚ) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i => cls i = .y ∧ label i = some v ∧ keyBaseline i ≤ a

def edgePrefixAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (a : ℚ) : Finset (p.TableBin cls) :=
  (edgeTuplesAt p cls label v).filter fun t => keyBaseline (p.itemAtRole cls t .anchor) ≤ a

def mainJobPrefixAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (a : ℚ) : Finset (p.TableBin cls) := by
  classical
  exact (baselinePrefixAt p cls label v baseline a).filter fun t =>
    cls (p.itemAtRole cls t .x) = .s

def mainTreePrefixAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (a : ℚ) : Finset (p.TableBin cls) := by
  classical
  exact (baselinePrefixAt p cls label v baseline a).filter fun t =>
    cls (p.itemAtRole cls t .x) ≠ .s

theorem baseline_prefix_row_partition
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (baseline : I.Item → ℚ) (a : ℚ) :
    (baselinePrefixAt p cls label v baseline a).card =
      (mainTreePrefixAt p cls label v baseline a).card +
        (mainJobPrefixAt p cls label v baseline a).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := baselinePrefixAt p cls label v baseline a)
    (fun t => cls (p.itemAtRole cls t .x) = .s)
  simpa only [mainTreePrefixAt, mainJobPrefixAt, Nat.add_comm] using h.symm

theorem main_tree_prefix_le_inventory
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (baseline : I.Item → ℚ) (a : ℚ) :
    (mainTreePrefixAt p cls label v baseline a).card ≤
      (treeRowPrefixAt (I := I) cls label v baseline a).card := by
  classical
  apply card_le_role_resources p cls _ .x _
  intro t ht
  obtain ⟨ht, hnots⟩ := Finset.mem_filter.mp ht
  obtain ⟨ht, hbase⟩ := Finset.mem_filter.mp ht
  obtain ⟨hgood, hlabel, _⟩ := (mem_mainTuplesAt p cls label v t).mp ht
  have hrole := (role_eq_x_iff (cls (p.itemAtRole cls t .x))).mp
    (p.itemAtRole_role cls t .x)
  have htree : cls (p.itemAtRole cls t .x) = .tp ∨
      cls (p.itemAtRole cls t .x) = .tm := by
    rcases hrole with hp | hm | hs
    · exact Or.inl hp
    · exact Or.inr hm
    · exact False.elim (hnots hs)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htree, hgood.1.trans hlabel, hbase⟩

theorem good_key_subset_edge_anchor_image
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (a : ℚ) :
    keyPrefixAt (I := I) cls label v keyBaseline a \ badAnchorsAt p cls label v ⊆
      roleItems p cls (edgePrefixAt p cls label v keyBaseline a) .anchor := by
  classical
  intro i hi
  obtain ⟨hi, hnotbad⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨_, hcls, hlabel, hbase⟩ := Finset.mem_filter.mp hi
  have hanchor : i ∈ anchorItemsAt (I := I) cls label v :=
    (mem_anchorItemsAt cls label v i).mpr ⟨by rw [hcls]; rfl, hlabel⟩
  have hused : i ∈ roleItems p cls (goodTuplesAt p cls label v) .anchor := by
    by_contra h
    exact hnotbad ((mem_badAnchorsAt p cls label v i).mpr ⟨hanchor, h⟩)
  obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hused
  have hpattern : p.tablePattern cls t = .edgeJob := by
    have hsub : patternSubclass (p.tablePattern cls t) .anchor = .y :=
      (p.itemAtRole_subclass cls t .anchor).symm.trans ((congrArg cls hti).trans hcls)
    cases hp : p.tablePattern cls t <;> simp_all [patternSubclass]
  have htgood := (mem_goodTuplesAt p cls label v t).mp ht
  have hG : t ∈ edgeTuplesAt p cls label v :=
    (mem_edgeTuplesAt p cls label v t).mpr ⟨htgood.1, htgood.2, hpattern⟩
  apply Finset.mem_image.mpr
  refine ⟨t, Finset.mem_filter.mpr ⟨hG, ?_⟩, hti⟩
  simpa only [hti] using hbase

theorem key_prefix_le_edge_prefix_add_loss
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (a : ℚ) (K : ℕ)
    (hbad : (badAnchorsAt p cls label v).card ≤ 3 * K) :
    (keyPrefixAt (I := I) cls label v keyBaseline a).card ≤
      (edgePrefixAt p cls label v keyBaseline a).card + 3 * K := by
  have hcount := Finset.card_le_card
    (good_key_subset_edge_anchor_image p cls label v keyBaseline a)
  rw [roleItems_card] at hcount
  have hloss := CoverageCounts.card_le_good_card_add
    (s := keyPrefixAt (I := I) cls label v keyBaseline a) hbad
  omega

theorem edge_row_mem_job_prefix
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (baseline : I.Item → ℚ) (a : ℚ)
    {t : p.TableBin cls} (ht : t ∈ edgeTuplesAt p cls label v)
    (hbase : baseline (p.itemAtRole cls t .x) ≤ a) :
    p.itemAtRole cls t .x ∈ jobRowPrefixAt (I := I) cls label v baseline a := by
  obtain ⟨hgood, hlabel, hpattern⟩ := (mem_edgeTuplesAt p cls label v t).mp ht
  have hcls : cls (p.itemAtRole cls t .x) = .s := by
    rw [p.itemAtRole_subclass cls t .x, hpattern]
    rfl
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcls, hgood.1.trans hlabel, hbase⟩

theorem displaced_baseline_prefix_le
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (a : ℚ)
    (extra : Finset (p.TableBin cls)) (B jobs K : ℕ)
    (hbad : (badAnchorsAt p cls label v).card ≤ 3 * K)
    (horder : ∀ t ∈ edgeTuplesAt p cls label v,
      baseline (p.itemAtRole cls t .x) ≤ keyBaseline (p.itemAtRole cls t .anchor))
    (hextra : extra ⊆ edgeTuplesAt p cls label v)
    (hextraRows : ∀ t ∈ extra, baseline (p.itemAtRole cls t .x) ≤ a)
    (hextraDis : Disjoint (edgePrefixAt p cls label v keyBaseline a) extra)
    (hjobStock : (jobRowPrefixAt (I := I) cls label v baseline a).card = 2 * jobs)
    (hkeyStock : (keyPrefixAt (I := I) cls label v keyBaseline a).card = jobs)
    (hbaselineStock : B = (treeRowPrefixAt (I := I) cls label v baseline a).card + jobs) :
    (baselinePrefixAt p cls label v baseline a).card + extra.card ≤ B + 3 * K := by
  classical
  let M := mainJobPrefixAt p cls label v baseline a
  let E := edgePrefixAt p cls label v keyBaseline a
  have hMsub : M ⊆ mainTuplesAt p cls label v := by
    intro t ht
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  have hEsub : E ⊆ edgeTuplesAt p cls label v := Finset.filter_subset _ _
  have hME : Disjoint M E :=
    (mainTuplesAt_disjoint_edge p cls label v v).mono hMsub hEsub
  have hMX : Disjoint M extra :=
    (mainTuplesAt_disjoint_edge p cls label v v).mono hMsub hextra
  have hmap : ∀ t ∈ (M ∪ E) ∪ extra,
      p.itemAtRole cls t .x ∈ jobRowPrefixAt (I := I) cls label v baseline a := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases Finset.mem_union.mp ht with ht | ht
      · obtain ⟨hprefix, hcls⟩ := Finset.mem_filter.mp ht
        obtain ⟨htM, hbase⟩ := Finset.mem_filter.mp hprefix
        obtain ⟨hgood, hlabel, _⟩ := (mem_mainTuplesAt p cls label v t).mp htM
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hcls, hgood.1.trans hlabel, hbase⟩
      · obtain ⟨htG, hbase⟩ := Finset.mem_filter.mp ht
        exact edge_row_mem_job_prefix p cls label v baseline a htG
          ((horder t htG).trans hbase)
    · exact edge_row_mem_job_prefix p cls label v baseline a (hextra ht)
        (hextraRows t ht)
  have hrows := card_three_le_row_resources p cls M E extra
    (jobRowPrefixAt (I := I) cls label v baseline a) hME hMX hextraDis hmap
  rw [hjobStock] at hrows
  have hkeys := key_prefix_le_edge_prefix_add_loss p cls label v keyBaseline a K hbad
  rw [hkeyStock] at hkeys
  have hsplit := baseline_prefix_row_partition p cls label v baseline a
  have htrees := main_tree_prefix_le_inventory p cls label v baseline a
  have hmain : (baselinePrefixAt p cls label v baseline a).card ≤
      (treeRowPrefixAt (I := I) cls label v baseline a).card + M.card := by
    dsimp only [M]
    omega
  exact CoverageCounts.displaced_baseline_bound hmain hbaselineStock hrows hkeys

def currentKeyItemsAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (current : ℚ) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i =>
    cls i = .y ∧ label i = some v ∧ keyBaseline i = current

def currentEdgeTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (current : ℚ) : Finset (p.TableBin cls) :=
  (edgeTuplesAt p cls label v).filter fun t =>
    keyBaseline (p.itemAtRole cls t .anchor) = current

def displacedTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (current : ℚ) : Finset (p.TableBin cls) :=
  (currentEdgeTuplesAt p cls label v keyBaseline current).filter fun t =>
    baseline (p.itemAtRole cls t .x) < current

def currentShortMainAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ) :
    Finset (p.TableBin cls) :=
  (mainTuplesAt p cls label v).filter fun t =>
    baseline (p.itemAtRole cls t .x) = current ∧ short (p.itemAtRole cls t .x) = true

def currentShortEdgeAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ) :
    Finset (p.TableBin cls) :=
  (currentEdgeTuplesAt p cls label v keyBaseline current).filter fun t =>
    baseline (p.itemAtRole cls t .x) = current ∧ short (p.itemAtRole cls t .x) = true

def currentLongEdgeAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ) :
    Finset (p.TableBin cls) :=
  (currentEdgeTuplesAt p cls label v keyBaseline current).filter fun t =>
    baseline (p.itemAtRole cls t .x) = current ∧ short (p.itemAtRole cls t .x) ≠ true

def currentShortItemsAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i => cls i = .s ∧ label i = some v ∧
    baseline i = current ∧ short i = true

theorem key_subset_le_matching_add_loss
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keys : Finset I.Item) (matchedTuples : Finset (p.TableBin cls)) (K : ℕ)
    (hkeys : ∀ i ∈ keys, cls i = .y ∧ label i = some v)
    (hselect : ∀ t ∈ edgeTuplesAt p cls label v,
      p.itemAtRole cls t .anchor ∈ keys → t ∈ matchedTuples)
    (hbad : (badAnchorsAt p cls label v).card ≤ 3 * K) :
    keys.card ≤ matchedTuples.card + 3 * K := by
  classical
  have hsubset : keys \ badAnchorsAt p cls label v ⊆ roleItems p cls matchedTuples .anchor := by
    intro i hi
    obtain ⟨hi, hnotbad⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨hcls, hlabel⟩ := hkeys i hi
    have hanchor : i ∈ anchorItemsAt (I := I) cls label v :=
      (mem_anchorItemsAt cls label v i).mpr ⟨by rw [hcls]; rfl, hlabel⟩
    have hused : i ∈ roleItems p cls (goodTuplesAt p cls label v) .anchor := by
      by_contra h
      exact hnotbad ((mem_badAnchorsAt p cls label v i).mpr ⟨hanchor, h⟩)
    obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hused
    have hpattern : p.tablePattern cls t = .edgeJob := by
      have hsub : patternSubclass (p.tablePattern cls t) .anchor = .y :=
        (p.itemAtRole_subclass cls t .anchor).symm.trans ((congrArg cls hti).trans hcls)
      cases hp : p.tablePattern cls t <;> simp_all [patternSubclass]
    have htgood := (mem_goodTuplesAt p cls label v t).mp ht
    have hG : t ∈ edgeTuplesAt p cls label v :=
      (mem_edgeTuplesAt p cls label v t).mpr ⟨htgood.1, htgood.2, hpattern⟩
    refine Finset.mem_image.mpr ⟨t, hselect t hG ?_, hti⟩
    simpa only [hti] using hi
  have hcount := Finset.card_le_card hsubset
  rw [roleItems_card] at hcount
  have hloss := CoverageCounts.card_le_good_card_add (s := keys) hbad
  omega

theorem current_key_count_le_matches_add_loss
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (current : ℚ) (K : ℕ)
    (hbad : (badAnchorsAt p cls label v).card ≤ 3 * K) :
    (currentKeyItemsAt (I := I) cls label v keyBaseline current).card ≤
      (currentEdgeTuplesAt p cls label v keyBaseline current).card + 3 * K := by
  apply key_subset_le_matching_add_loss p cls label v _ _ K _ _ hbad
  · intro i hi
    obtain ⟨_, hcls, hlabel, _⟩ := Finset.mem_filter.mp hi
    exact ⟨hcls, hlabel⟩
  · intro t ht hi
    exact Finset.mem_filter.mpr ⟨ht, (Finset.mem_filter.mp hi).2.2.2⟩

theorem current_match_partition
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ)
    (horder : ∀ t ∈ edgeTuplesAt p cls label v,
      baseline (p.itemAtRole cls t .x) ≤ keyBaseline (p.itemAtRole cls t .anchor)) :
    (currentEdgeTuplesAt p cls label v keyBaseline current).card =
      (displacedTuplesAt p cls label v baseline keyBaseline current).card +
      (currentShortEdgeAt p cls label v baseline keyBaseline short current).card +
      (currentLongEdgeAt p cls label v baseline keyBaseline short current).card := by
  apply CoverageCounts.ordered_short_long_partition
    (currentEdgeTuplesAt p cls label v keyBaseline current)
    (fun t => baseline (p.itemAtRole cls t .x)) current
    (fun t => short (p.itemAtRole cls t .x) = true)
  intro t ht
  obtain ⟨ht, hcurrent⟩ := Finset.mem_filter.mp ht
  exact (horder t ht).trans_eq hcurrent

theorem current_short_consumption_le_stock
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ)
    (hshortJob : ∀ i, short i = true → cls i = .s) :
    (currentShortMainAt p cls label v baseline short current).card +
      (currentShortEdgeAt p cls label v baseline keyBaseline short current).card ≤
        (currentShortItemsAt (I := I) cls label v baseline short current).card := by
  classical
  let M := currentShortMainAt p cls label v baseline short current
  let G := currentShortEdgeAt p cls label v baseline keyBaseline short current
  have hMsub : M ⊆ mainTuplesAt p cls label v := Finset.filter_subset _ _
  have hGsub : G ⊆ edgeTuplesAt p cls label v := by
    intro t ht
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  apply CoverageCounts.card_add_card_le_of_disjoint_injections M G
    (currentShortItemsAt (I := I) cls label v baseline short current)
    (fun t => p.itemAtRole cls t .x)
    ((mainTuplesAt_disjoint_edge p cls label v v).mono hMsub hGsub)
    _ (p.itemAtRole_injective cls .x).injOn
  intro t ht
  rcases Finset.mem_union.mp ht with ht | ht
  · obtain ⟨ht, hbase, hshort⟩ := Finset.mem_filter.mp ht
    obtain ⟨hgood, hlabel, _⟩ := (mem_mainTuplesAt p cls label v t).mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hshortJob _ hshort,
      hgood.1.trans hlabel, hbase, hshort⟩
  · obtain ⟨ht, hbase, hshort⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht, _⟩ := Finset.mem_filter.mp ht
    obtain ⟨hgood, hlabel, _⟩ := (mem_edgeTuplesAt p cls label v t).mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hshortJob _ hshort,
      hgood.1.trans hlabel, hbase, hshort⟩

theorem current_long_matches_from_correction
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ)
    (d K xplus : ℕ)
    (hbad : (badAnchorsAt p cls label v).card ≤ 3 * K)
    (horder : ∀ t ∈ edgeTuplesAt p cls label v,
      baseline (p.itemAtRole cls t .x) ≤ keyBaseline (p.itemAtRole cls t .anchor))
    (hshortJob : ∀ i, short i = true → cls i = .s)
    (hkeys : (currentKeyItemsAt (I := I) cls label v keyBaseline current).card = d)
    (hshortStock : (currentShortItemsAt (I := I) cls label v baseline short current).card = d)
    (hcorrection : d + (displacedTuplesAt p cls label v baseline keyBaseline current).card ≤
      xplus + (currentShortMainAt p cls label v baseline short current).card + 6 * K) :
    d ≤ (currentLongEdgeAt p cls label v baseline keyBaseline short current).card +
      xplus + 9 * K := by
  have hgood := current_key_count_le_matches_add_loss p cls label v keyBaseline current K hbad
  rw [hkeys] at hgood
  have hpartition := current_match_partition p cls label v baseline keyBaseline short current horder
  have hshort := current_short_consumption_le_stock p cls label v baseline keyBaseline
    short current hshortJob
  rw [hshortStock] at hshort
  exact CoverageCounts.long_match_lower_bound hcorrection
    (CoverageCounts.short_le_displaced_add_long hgood hpartition hshort)

end Coverage
end BinPackingGap

end

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Packing/K4Graph.lean =====
namespace OAI

noncomputable section

namespace BinPackingGap

def primaryScoreBound : ℕ := 100 ^ 11

def lossAllowance (c : ℕ) : ℕ := 25 * (c + 1) * (1 + 5 * primaryScoreBound)

def depthDemand (c : ℕ) (ρ : ℝ) : ℕ :=
  Nat.ceil (max (72 * (lossAllowance c : ℝ)) (120 * (lossAllowance c : ℝ) / ρ))

def repetitions (P n K : ℕ) : ℕ := 100 * (P + n * K + 1)

theorem primaryScoreBound_pos : 0 < primaryScoreBound := by
  unfold primaryScoreBound
  positivity

theorem lossAllowance_pos (c : ℕ) : 0 < lossAllowance c := by
  unfold lossAllowance
  positivity

theorem primary_loss_lt_lossAllowance (c : ℕ) :
    25 * c * (1 + 5 * primaryScoreBound) < lossAllowance c := by
  unfold lossAllowance
  apply mul_lt_mul_of_pos_right _ (by positivity)
  exact mul_lt_mul_of_pos_left (Nat.lt_succ_self c) (by norm_num)

theorem depthDemand_ge_72_real (c : ℕ) (ρ : ℝ) :
    72 * (lossAllowance c : ℝ) ≤ (depthDemand c ρ : ℝ) := by
  exact (le_max_left _ _).trans (Nat.le_ceil _)

theorem depthDemand_ge_72 (c : ℕ) (ρ : ℝ) :
    72 * lossAllowance c ≤ depthDemand c ρ := by
  exact_mod_cast depthDemand_ge_72_real c ρ

theorem depthDemand_ge_120_div (c : ℕ) (ρ : ℝ) :
    120 * (lossAllowance c : ℝ) / ρ ≤ (depthDemand c ρ : ℝ) := by
  exact (le_max_right _ _).trans (Nat.le_ceil _)

theorem depthDemand_pos (c : ℕ) (ρ : ℝ) : 0 < depthDemand c ρ :=
  lt_of_lt_of_le (Nat.mul_pos (by norm_num) (lossAllowance_pos c))
    (depthDemand_ge_72 c ρ)

theorem depthDemand_one_le (c : ℕ) (ρ : ℝ) : 1 ≤ depthDemand c ρ :=
  Nat.succ_le_of_lt (depthDemand_pos c ρ)

theorem depthDemand_ge_12 (c : ℕ) (ρ : ℝ) :
    12 * lossAllowance c ≤ depthDemand c ρ := by
  exact (Nat.mul_le_mul_right (lossAllowance c) (by norm_num : 12 ≤ 72)).trans
    (depthDemand_ge_72 c ρ)

theorem depthDemand_spec (c : ℕ) (ρ : ℝ) :
    1 ≤ depthDemand c ρ ∧
      max (72 * (lossAllowance c : ℝ)) (120 * (lossAllowance c : ℝ) / ρ) ≤
        (depthDemand c ρ : ℝ) :=
  ⟨depthDemand_one_le c ρ, Nat.le_ceil _⟩

theorem threshold_gap {d K : ℝ} (hd : 0 < d) (h72 : 72 * K ≤ d) :
    d / 8 < d - 6 * K := by
  linarith

theorem three_quarter_lower {d K x L : ℝ} (h72 : 72 * K ≤ d)
    (hx : x ≤ d / 8) (hL : d - x - 9 * K ≤ L) : 3 * d / 4 ≤ L := by
  linarith

theorem depthDemand_threshold_gap (c : ℕ) (ρ : ℝ) :
    (depthDemand c ρ : ℝ) / 8 < (depthDemand c ρ : ℝ) - 6 * (lossAllowance c : ℝ) :=
  threshold_gap (Nat.cast_pos.mpr (depthDemand_pos c ρ)) (depthDemand_ge_72_real c ρ)

theorem repetitions_pos (P n K : ℕ) : 0 < repetitions P n K := by
  unfold repetitions
  positivity

theorem repetitions_gt_P (P n K : ℕ) : P < repetitions P n K := by
  have hnK : 0 ≤ n * K := Nat.zero_le _
  unfold repetitions
  nlinarith

theorem repetitions_cast (P n K : ℕ) :
    (repetitions P n K : ℝ) = 100 * ((P : ℝ) + (n : ℝ) * K + 1) := by
  simp [repetitions]

theorem edge_demand_exceeds_capacity_real {P n K d : ℝ}
    (hP : 0 ≤ P) (hn : 0 ≤ n) (hK : 0 ≤ K) (hd : 1 ≤ d) :
    d * (100 * (P + n * K + 1)) + 3 * n * K <
      2 * (100 * (P + n * K + 1) - P) * (3 * d / 4) := by
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  have hdP : 0 ≤ d * P := mul_nonneg hd0 hP
  have hnK : 0 ≤ n * K := mul_nonneg hn hK
  have hrest : 0 ≤ (50 * d - 3) * (n * K) :=
    mul_nonneg (by linarith) hnK
  nlinarith

theorem edge_demand_exceeds_capacity (P n K d : ℕ) (hd : 1 ≤ d) :
    (d : ℝ) * (repetitions P n K : ℝ) + 3 * (n : ℝ) * K <
      2 * ((repetitions P n K : ℝ) - P) * (3 * (d : ℝ) / 4) := by
  rw [repetitions_cast]
  exact edge_demand_exceeds_capacity_real (Nat.cast_nonneg P) (Nat.cast_nonneg n)
    (Nat.cast_nonneg K) (by exact_mod_cast hd)

theorem sixty_loss_div_le {ρ d K n : ℝ} (hρ : 0 < ρ) (hd : 0 < d)
    (hK : 0 ≤ K) (hn : 0 ≤ n) (h120 : 120 * K / ρ ≤ d) :
    60 * K * n / d ≤ ρ * n := by
  have hmul := (div_le_iff₀ hρ).mp h120
  have h60 : 60 * K ≤ ρ * d := by nlinarith
  apply (div_le_iff₀ hd).mpr
  calc
    60 * K * n ≤ (ρ * d) * n := mul_le_mul_of_nonneg_right h60 hn
    _ = (ρ * n) * d := by ring

theorem depthDemand_sixty_loss_div_le (c n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    60 * (lossAllowance c : ℝ) * (n : ℝ) / (depthDemand c ρ : ℝ) ≤ ρ * n :=
  sixty_loss_div_le hρ (Nat.cast_pos.mpr (depthDemand_pos c ρ))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (depthDemand_ge_120_div c ρ)

structure GraphInput where
  n : ℕ
  edges : List (Fin n × Fin n)
  ordered : ∀ e ∈ edges, e.1 < e.2
  distinct : edges.Nodup

namespace GraphInput

abbrev Vertex (G : GraphInput) := Fin G.n

abbrev Edge (G : GraphInput) := Fin G.edges.length

def left (G : GraphInput) (e : G.Edge) : G.Vertex := (G.edges[e]).1

def right (G : GraphInput) (e : G.Edge) : G.Vertex := (G.edges[e]).2

def IsCover (G : GraphInput) (C : Finset G.Vertex) : Prop :=
  ∀ e ∈ G.edges, e.1 ∈ C ∨ e.2 ∈ C

def CoverAtMost (G : GraphInput) (k : ℕ) : Prop :=
  ∃ C : Finset G.Vertex, G.IsCover C ∧ C.card ≤ k

end GraphInput

open scoped BigOperators

namespace GraphInput

def endpoint (G : GraphInput) (e : G.Edge) (s : Fin 2) : G.Vertex :=
  if s = 0 then G.left e else G.right e

@[simp] theorem endpoint_zero (G : GraphInput) (e : G.Edge) :
    G.endpoint e 0 = G.left e := by simp [endpoint]

@[simp] theorem endpoint_one (G : GraphInput) (e : G.Edge) :
    G.endpoint e 1 = G.right e := by simp [endpoint]

theorem left_lt_right (G : GraphInput) (e : G.Edge) : G.left e < G.right e :=
  G.ordered _ (List.getElem_mem e.isLt)

theorem left_ne_right (G : GraphInput) (e : G.Edge) : G.left e ≠ G.right e :=
  (G.left_lt_right e).ne

theorem endpoint_injective (G : GraphInput) (e : G.Edge) :
    Function.Injective (G.endpoint e) := by
  intro s t h
  have hs : s = 0 ∨ s = 1 := by omega
  have ht : t = 0 ∨ t = 1 := by omega
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · rfl
  · exact False.elim (G.left_ne_right e (by simpa using h))
  · exact False.elim (G.left_ne_right e (by simpa using h.symm))
  · rfl

abbrev Incidence (G : GraphInput) (v : G.Vertex) :=
  {es : G.Edge × Fin 2 // G.endpoint es.1 es.2 = v}

def incidenceEquiv (G : GraphInput) :
    (Σ v : G.Vertex, G.Incidence v) ≃ G.Edge × Fin 2 :=
  Equiv.sigmaFiberEquiv (fun es : G.Edge × Fin 2 => G.endpoint es.1 es.2)

def degree (G : GraphInput) (v : G.Vertex) : ℕ :=
  Fintype.card (G.Incidence v)

theorem sum_degree (G : GraphInput) :
    (∑ v : G.Vertex, G.degree v) = 2 * G.edges.length := by
  have h := Fintype.card_congr (G.incidenceEquiv)
  simpa [degree, Fintype.card_sigma, Fintype.card_prod, Nat.mul_comm] using h

abbrev IncidencePosition (G : GraphInput) (R : ℕ) (v : G.Vertex) :=
  G.Incidence v × Fin R

abbrev JobCopy (G : GraphInput) (R d : ℕ) (v : G.Vertex) :=
  G.IncidencePosition R v × Fin d

theorem card_incidencePosition (G : GraphInput) (R : ℕ) (v : G.Vertex) :
    Fintype.card (G.IncidencePosition R v) = R * G.degree v := by
  simp [IncidencePosition, degree, Nat.mul_comm]

theorem card_jobCopy (G : GraphInput) (R d : ℕ) (v : G.Vertex) :
    Fintype.card (G.JobCopy R d v) = d * R * G.degree v := by
  simp [JobCopy, IncidencePosition, degree, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc]

theorem sum_card_jobCopy (G : GraphInput) (R d : ℕ) :
    (∑ v : G.Vertex, Fintype.card (G.JobCopy R d v)) =
      2 * d * G.edges.length * R := by
  simp_rw [card_jobCopy]
  rw [← Finset.mul_sum, sum_degree]
  ac_rfl

end GraphInput

end BinPackingGap

section
open scoped BigOperators

namespace BinPackingGap

variable {V : Type*} [Fintype V] [DecidableEq V]

def thresholdCover (d : ℕ) (xplus : V → ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => (d : ℝ) / 8 < (xplus v : ℝ)

def largePlus (d K : ℕ) (xplus : V → ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => (d : ℝ) - 6 * K ≤ (xplus v : ℝ)

theorem residual_plus_le {d K : ℕ} (xplus xminus : V → ℕ)
    (htotal : (∑ v, (xplus v + xminus v)) ≤ d * Fintype.card V)
    (hside : ∀ v, d ≤ xplus v + 6 * K ∨ d ≤ xminus v + 6 * K) :
    (∑ v, if v ∈ largePlus d K xplus then (0 : ℝ) else (xplus v : ℝ)) ≤
      6 * (K : ℝ) * Fintype.card V := by
  classical
  let charge : V → ℝ := fun v =>
    if v ∈ largePlus d K xplus then (xplus v : ℝ) else (xminus v : ℝ)
  let rest : V → ℝ := fun v =>
    if v ∈ largePlus d K xplus then 0 else (xplus v : ℝ)
  have hcharge : ∀ v, (d : ℝ) - 6 * K ≤ charge v := by
    intro v
    by_cases hv : v ∈ largePlus d K xplus
    · simpa only [charge, ite_eq_left hv] using (Finset.mem_filter.mp hv).2
    · have hnot : ¬ ((d : ℝ) - 6 * K ≤ (xplus v : ℝ)) := by
        simpa [largePlus] using hv
      rcases hside v with hp | hm
      · have hp' : (d : ℝ) ≤ (xplus v : ℝ) + 6 * K := by exact_mod_cast hp
        exact (hnot (by linarith)).elim
      · have hm' : (d : ℝ) ≤ (xminus v : ℝ) + 6 * K := by exact_mod_cast hm
        simp only [charge, ite_eq_right hv]
        linarith
  have hcharged : (Fintype.card V : ℝ) * ((d : ℝ) - 6 * K) ≤ ∑ v, charge v := by
    calc
      _ = ∑ _v : V, ((d : ℝ) - 6 * K) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ v, charge v := Finset.sum_le_sum fun v _ => hcharge v
  have hpoint : ∀ v, charge v + rest v ≤ (xplus v : ℝ) + xminus v := by
    intro v
    dsimp only [charge, rest]
    split_ifs <;> nlinarith [show (0 : ℝ) ≤ xplus v from Nat.cast_nonneg _,
      show (0 : ℝ) ≤ xminus v from Nat.cast_nonneg _]
  have hsum : (∑ v, charge v) + (∑ v, rest v) ≤
      (d : ℝ) * Fintype.card V := by
    calc
      _ = ∑ v, (charge v + rest v) := (Finset.sum_add_distrib).symm
      _ ≤ ∑ v, ((xplus v : ℝ) + xminus v) := Finset.sum_le_sum fun v _ => hpoint v
      _ ≤ (d : ℝ) * Fintype.card V := by exact_mod_cast htotal
  change (∑ v, rest v) ≤ _
  nlinarith

theorem thresholdCover_card_le_fractions {d K k : ℕ} (xplus xminus : V → ℕ)
    (hd : 0 < d) (h72 : 72 * K ≤ d)
    (hplus : (∑ v, xplus v) ≤ d * k)
    (htotal : (∑ v, (xplus v + xminus v)) ≤ d * Fintype.card V)
    (hside : ∀ v, d ≤ xplus v + 6 * K ∨ d ≤ xminus v + 6 * K) :
    ((thresholdCover d xplus).card : ℝ) ≤
      (d : ℝ) * k / ((d : ℝ) - 6 * K) + 48 * (K : ℝ) * Fintype.card V / d := by
  classical
  let A := largePlus d K xplus
  let C := thresholdCover d xplus
  let B := C \ A
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h72' : 72 * (K : ℝ) ≤ d := by exact_mod_cast h72
  have hgap := threshold_gap hd0 h72'
  have hden : 0 < (d : ℝ) - 6 * K := lt_trans (by positivity) hgap
  have hAC : A ⊆ C := by
    intro v hv
    have hv' : (d : ℝ) - 6 * K ≤ (xplus v : ℝ) := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hgap.trans_le hv'⟩
  have hAlower : (A.card : ℝ) * ((d : ℝ) - 6 * K) ≤ ∑ v, (xplus v : ℝ) := by
    calc
      _ = ∑ _v ∈ A, ((d : ℝ) - 6 * K) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ v ∈ A, (xplus v : ℝ) :=
        Finset.sum_le_sum fun v hv => (Finset.mem_filter.mp hv).2
      _ ≤ ∑ v, (xplus v : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
  have hA : (A.card : ℝ) ≤ (d : ℝ) * k / ((d : ℝ) - 6 * K) := by
    apply (le_div_iff₀ hden).mpr
    exact hAlower.trans (by exact_mod_cast hplus)
  let rest : V → ℝ := fun v => if v ∈ A then 0 else (xplus v : ℝ)
  have hrest : (∑ v, rest v) ≤ 6 * (K : ℝ) * Fintype.card V :=
    residual_plus_le xplus xminus htotal hside
  have hBlower : (B.card : ℝ) * ((d : ℝ) / 8) ≤ ∑ v, rest v := by
    calc
      _ = ∑ _v ∈ B, ((d : ℝ) / 8) := by simp
      _ ≤ ∑ v ∈ B, rest v := by
        apply Finset.sum_le_sum
        intro v hv
        obtain ⟨hvC, hvA⟩ := Finset.mem_sdiff.mp hv
        have hv' : (d : ℝ) / 8 < (xplus v : ℝ) := (Finset.mem_filter.mp hvC).2
        simpa only [rest, ite_eq_right hvA] using hv'.le
      _ ≤ ∑ v, rest v := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro v _ _
        dsimp only [rest]
        split_ifs <;> positivity
  have hB : (B.card : ℝ) ≤ 48 * (K : ℝ) * Fintype.card V / d := by
    apply (le_div_iff₀ hd0).mpr
    nlinarith
  have hcard : (C.card : ℝ) = (A.card : ℝ) + B.card := by
    have hh := Finset.card_sdiff_add_card_eq_card hAC
    dsimp only [B]
    exact_mod_cast hh.symm.trans (Nat.add_comm _ _)
  change (C.card : ℝ) ≤ _
  rw [hcard]
  exact add_le_add hA hB

theorem cover_fraction_bound {d K k n : ℝ} (hd : 0 < d) (hK : 0 ≤ K)
    (hk0 : 0 ≤ k) (hkn : k ≤ n) (h12 : 12 * K ≤ d) :
    d * k / (d - 6 * K) + 48 * K * n / d ≤ k + 60 * K * n / d := by
  have hn : 0 ≤ n := hk0.trans hkn
  have hden : 0 < d - 6 * K := by linarith
  have hmult := mul_le_mul_of_nonneg_left hkn (show 0 ≤ 6 * K * d by positivity)
  have hslack := mul_nonneg (show 0 ≤ 6 * K * n by positivity) (sub_nonneg.mpr h12)
  have hfrac : 6 * K * k / (d - 6 * K) ≤ 12 * K * n / d := by
    apply (div_le_div_iff₀ hden hd).mpr
    nlinarith
  have hid : d * k / (d - 6 * K) = k + 6 * K * k / (d - 6 * K) := by
    field_simp [hden.ne']; ring
  rw [hid]
  have hsplit : 60 * K * n / d = 12 * K * n / d + 48 * K * n / d := by ring
  rw [hsplit]
  linarith

theorem thresholdCover_card_le {d K k : ℕ} {ρ : ℝ} (xplus xminus : V → ℕ)
    (hd : 0 < d) (h72 : 72 * K ≤ d) (hk : k ≤ Fintype.card V)
    (hρ : 0 < ρ) (h120 : 120 * (K : ℝ) / ρ ≤ d)
    (hplus : (∑ v, xplus v) ≤ d * k)
    (htotal : (∑ v, (xplus v + xminus v)) ≤ d * Fintype.card V)
    (hside : ∀ v, d ≤ xplus v + 6 * K ∨ d ≤ xminus v + 6 * K) :
    ((thresholdCover d xplus).card : ℝ) ≤ (k : ℝ) + ρ * Fintype.card V := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h72' : 72 * (K : ℝ) ≤ d := by exact_mod_cast h72
  calc
    _ ≤ (d : ℝ) * k / ((d : ℝ) - 6 * K) + 48 * (K : ℝ) * Fintype.card V / d :=
      thresholdCover_card_le_fractions xplus xminus hd h72 hplus htotal hside
    _ ≤ (k : ℝ) + 60 * (K : ℝ) * Fintype.card V / d :=
      cover_fraction_bound hd0 (Nat.cast_nonneg K) (Nat.cast_nonneg k)
        (by exact_mod_cast hk) (by linarith)
    _ ≤ (k : ℝ) + ρ * Fintype.card V :=
      add_le_add (le_refl (k : ℝ)) (sixty_loss_div_le hρ hd0 (Nat.cast_nonneg K)
        (Nat.cast_nonneg _) h120)

theorem longMatch_sum_lower {R P : ℕ} (S : Finset (Fin R)) (L : Fin R → ℕ)
    {a : ℝ} (ha : 0 ≤ a) (hS : (R : ℝ) - P ≤ (S.card : ℝ))
    (hL : ∀ j ∈ S, a ≤ (L j : ℝ)) :
    ((R : ℝ) - P) * a ≤ ∑ j, (L j : ℝ) := by
  calc
    _ ≤ (S.card : ℝ) * a := mul_le_mul_of_nonneg_right hS ha
    _ = ∑ _j ∈ S, a := by simp
    _ ≤ ∑ j ∈ S, (L j : ℝ) := Finset.sum_le_sum hL
    _ ≤ ∑ j, (L j : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)

theorem thresholdCover_isCover (G : GraphInput) {d K P R : ℕ}
    (xplus : G.Vertex → ℕ)
    (Sleft Sright : G.Edge → Finset (Fin R))
    (Lleft Lright : G.Edge → Fin R → ℕ)
    (hd : 1 ≤ d) (h72 : 72 * K ≤ d) (hR : R = repetitions P G.n K)
    (hSleft : ∀ e, (R : ℝ) - P ≤ ((Sleft e).card : ℝ))
    (hSright : ∀ e, (R : ℝ) - P ≤ ((Sright e).card : ℝ))
    (hLleft : ∀ e j, j ∈ Sleft e → d ≤ Lleft e j + xplus (G.left e) + 9 * K)
    (hLright : ∀ e j, j ∈ Sright e → d ≤ Lright e j + xplus (G.right e) + 9 * K)
    (hcapacity : ∀ e, (∑ j, Lleft e j) + (∑ j, Lright e j) ≤
      d * R + 3 * G.n * K) :
    G.IsCover (thresholdCover d xplus) := by
  classical
  let C := thresholdCover d xplus
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  have h72' : 72 * (K : ℝ) ≤ d := by exact_mod_cast h72
  have hstrict : (d : ℝ) * R + 3 * (G.n : ℝ) * K <
      2 * ((R : ℝ) - P) * (3 * (d : ℝ) / 4) := by
    rw [hR]
    exact edge_demand_exceeds_capacity P G.n K d hd
  have hindex : ∀ e : G.Edge, G.left e ∈ C ∨ G.right e ∈ C := by
    intro e
    by_cases hv : G.left e ∈ C
    · exact Or.inl hv
    right
    by_contra hw
    have hxleft : (xplus (G.left e) : ℝ) ≤ (d : ℝ) / 8 := by
      apply le_of_not_gt
      simpa [C, thresholdCover] using hv
    have hxright : (xplus (G.right e) : ℝ) ≤ (d : ℝ) / 8 := by
      apply le_of_not_gt
      simpa [C, thresholdCover] using hw
    have hleft : ((R : ℝ) - P) * (3 * (d : ℝ) / 4) ≤
        ∑ j, (Lleft e j : ℝ) := by
      apply longMatch_sum_lower _ _ (by positivity) (hSleft e)
      intro j hj
      have hmatch : (d : ℝ) ≤ (Lleft e j : ℝ) + xplus (G.left e) + 9 * K := by
        exact_mod_cast hLleft e j hj
      exact three_quarter_lower h72' hxleft (by linarith)
    have hright : ((R : ℝ) - P) * (3 * (d : ℝ) / 4) ≤
        ∑ j, (Lright e j : ℝ) := by
      apply longMatch_sum_lower _ _ (by positivity) (hSright e)
      intro j hj
      have hmatch : (d : ℝ) ≤ (Lright e j : ℝ) + xplus (G.right e) + 9 * K := by
        exact_mod_cast hLright e j hj
      exact three_quarter_lower h72' hxright (by linarith)
    have hcap : (∑ j, (Lleft e j : ℝ)) + (∑ j, (Lright e j : ℝ)) ≤
        (d : ℝ) * R + 3 * (G.n : ℝ) * K := by exact_mod_cast hcapacity e
    linarith
  intro e he
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp he
  have h := hindex ⟨i, hi⟩
  change (G.edges[i]).1 ∈ C ∨ (G.edges[i]).2 ∈ C at h
  rw [heq] at h
  exact h

theorem thresholdCover_card_le_graph (G : GraphInput) {d K k : ℕ} {ρ : ℝ}
    (xplus xminus : G.Vertex → ℕ)
    (hd : 0 < d) (h72 : 72 * K ≤ d) (hk : k ≤ G.n)
    (hρ : 0 < ρ) (h120 : 120 * (K : ℝ) / ρ ≤ d)
    (hplus : (∑ v, xplus v) ≤ d * k)
    (htotal : (∑ v, (xplus v + xminus v)) ≤ d * G.n)
    (hside : ∀ v, d ≤ xplus v + 6 * K ∨ d ≤ xminus v + 6 * K) :
    ((thresholdCover d xplus).card : ℝ) ≤ (k : ℝ) + ρ * G.n := by
  simpa only [Fintype.card_fin] using
    thresholdCover_card_le xplus xminus hd h72
      (by simpa only [Fintype.card_fin] using hk) hρ h120 hplus
      (by simpa only [Fintype.card_fin] using htotal) hside

end BinPackingGap

end

namespace BinPackingGap

def completeFourGraph : GraphInput where
  n := 4
  edges := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
  ordered := by decide
  distinct := by decide

theorem completeFourGraph_edge_pos : 0 < completeFourGraph.edges.length := by decide

theorem completeFourGraph_cover_card {C : Finset completeFourGraph.Vertex}
    (hC : completeFourGraph.IsCover C) : 3 ≤ C.card := by
  classical
  change Finset (Fin 4) at C
  change 3 ≤ C.card
  change ∀ e : Fin 4 × Fin 4,
    e ∈ [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] →
      e.1 ∈ C ∨ e.2 ∈ C at hC
  have h01 : (0 : Fin 4) ∈ C ∨ (1 : Fin 4) ∈ C :=
    hC ((0 : Fin 4), (1 : Fin 4)) (by decide)
  have h02 : (0 : Fin 4) ∈ C ∨ (2 : Fin 4) ∈ C :=
    hC ((0 : Fin 4), (2 : Fin 4)) (by decide)
  have h03 : (0 : Fin 4) ∈ C ∨ (3 : Fin 4) ∈ C :=
    hC ((0 : Fin 4), (3 : Fin 4)) (by decide)
  have h12 : (1 : Fin 4) ∈ C ∨ (2 : Fin 4) ∈ C :=
    hC ((1 : Fin 4), (2 : Fin 4)) (by decide)
  have h13 : (1 : Fin 4) ∈ C ∨ (3 : Fin 4) ∈ C :=
    hC ((1 : Fin 4), (3 : Fin 4)) (by decide)
  have h23 : (2 : Fin 4) ∈ C ∨ (3 : Fin 4) ∈ C :=
    hC ((2 : Fin 4), (3 : Fin 4)) (by decide)
  have hsmall : (Finset.univ \ C).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hxC : x ∉ C := (Finset.mem_sdiff.mp hx).2
    have hyC : y ∉ C := (Finset.mem_sdiff.mp hy).2
    fin_cases x <;> fin_cases y <;> simp_all
  have htotal : (Finset.univ \ C).card + C.card = 4 := by
    simpa only [Finset.card_univ, Fintype.card_fin, completeFourGraph] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
  omega

theorem completeFourGraph_cover_three : completeFourGraph.CoverAtMost 3 := by
  change ∃ C : Finset (Fin 4),
    (∀ e : Fin 4 × Fin 4,
      e ∈ [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] →
        e.1 ∈ C ∨ e.2 ∈ C) ∧ C.card ≤ 3
  exact ⟨{0, 1, 2}, by decide, by decide⟩

theorem completeFourGraph_no_small_cover :
    ¬ ∃ C : Finset completeFourGraph.Vertex,
      completeFourGraph.IsCover C ∧
        (C.card : ℝ) ≤ 2 + (1 / 8 : ℝ) * completeFourGraph.n := by
  rintro ⟨C, hC, hcard⟩
  have hthree : (3 : ℝ) ≤ C.card := by exact_mod_cast completeFourGraph_cover_card hC
  norm_num [completeFourGraph] at hcard
  linarith

end BinPackingGap

end

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Machines/IntegerPackingArithmetic.lean =====
namespace OAI

namespace BinPackingGap.IntegerPackingArithmetic

def widthRadix (D : ℕ) : ℕ := 100 * (D + 1)

def geomDenominator (m R D L : ℕ) : ℕ :=
  160 * (R + 1) ^ m * widthRadix D ^ L

def sizeDenominator (n geom : ℕ) : ℕ :=
  10 ^ 9 * primaryBound * 3 ^ n * geom

def signedNumerator (n geom : ℕ) (p q W : ℤ) : ℤ :=
  200000000 * (primaryBound : ℤ) * 3 ^ n * geom +
    1000000 * 3 ^ n * geom * p + 1000 * geom * q + W

def itemNumerator {n : ℕ} (geom : ℕ) (subclass : Subclass)
    (label : Option (Fin n)) (W : ℤ) : ℤ :=
  signedNumerator n geom (primaryScore subclass) (secondaryScore subclass label) W

theorem widthRadix_pos (D : ℕ) : 0 < widthRadix D := by
  unfold widthRadix
  positivity

theorem geomDenominator_pos (m R D L : ℕ) : 0 < geomDenominator m R D L := by
  unfold geomDenominator
  exact Nat.mul_pos (by positivity) (pow_pos (widthRadix_pos D) L)

theorem sizeDenominator_pos (n geom : ℕ) (hgeom : 0 < geom) :
    0 < sizeDenominator n geom := by
  unfold sizeDenominator primaryBound
  positivity

theorem signedNumerator_ratio (n geom : ℕ) (hgeom : 0 < geom)
    (p q W : ℤ) :
    (signedNumerator n geom p q W : ℚ) / (sizeDenominator n geom : ℚ) =
      1 / 5 + gamma * (p : ℚ) + mu n * (q : ℚ) +
        nu n * ((W : ℚ) / geom) := by
  have hg : (geom : ℚ) ≠ 0 := by exact_mod_cast hgeom.ne'
  have hp : (primaryBound : ℚ) ≠ 0 := by norm_num [primaryBound]
  have hq : (3 : ℚ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  simp only [signedNumerator, sizeDenominator, nu, mu, gamma]
  push_cast
  field_simp [hg, hp, hq]
  ring

theorem itemNumerator_ratio {n : ℕ} (geom : ℕ) (hgeom : 0 < geom)
    (subclass : Subclass) (label : Option (Fin n)) (W : ℤ) :
    (itemNumerator geom subclass label W : ℚ) / (sizeDenominator n geom : ℚ) =
      encodedSize subclass label ((W : ℚ) / geom) := by
  exact signedNumerator_ratio n geom hgeom (primaryScore subclass) (secondaryScore subclass label) W

theorem itemNumerator_pos_lt {n : ℕ} (geom : ℕ) (hgeom : 0 < geom)
    (subclass : Subclass) (label : Option (Fin n)) (W : ℤ)
    (hW : |(W : ℚ) / geom| ≤ 6) :
    0 < itemNumerator geom subclass label W ∧
      itemNumerator geom subclass label W < (sizeDenominator n geom : ℤ) := by
  have hd : (0 : ℚ) < sizeDenominator n geom := by
    exact_mod_cast sizeDenominator_pos n geom hgeom
  have hs := encodedSize_mem_interval subclass label ((W : ℚ) / geom) hW
  rw [← itemNumerator_ratio geom hgeom subclass label W] at hs
  have hpos : (0 : ℚ) < (itemNumerator geom subclass label W : ℚ) := by
    have hdiv : (0 : ℚ) < (itemNumerator geom subclass label W : ℚ) /
        (sizeDenominator n geom : ℚ) := lt_trans (by norm_num) hs.1
    rcases div_pos_iff.mp hdiv with h | h
    · exact h.1
    · exact (not_lt_of_ge hd.le h.2).elim
  have hlt : (itemNumerator geom subclass label W : ℚ) < (sizeDenominator n geom : ℚ) := by
    have h := (div_lt_iff₀ hd).mp hs.2
    simpa only [one_mul] using h
  constructor
  · exact_mod_cast hpos
  · exact_mod_cast hlt

def rawItem {n : ℕ} (geom : ℕ) (subclass : Subclass)
    (label : Option (Fin n)) (W : ℤ) : ℕ × ℕ :=
  ((itemNumerator geom subclass label W).toNat, sizeDenominator n geom)

theorem rawItem_numerator_cast {n : ℕ} (geom : ℕ) (hgeom : 0 < geom)
    (subclass : Subclass) (label : Option (Fin n)) (W : ℤ)
    (hW : |(W : ℚ) / geom| ≤ 6) :
    ((rawItem geom subclass label W).1 : ℤ) = itemNumerator geom subclass label W := by
  exact Int.toNat_of_nonneg (itemNumerator_pos_lt geom hgeom subclass label W hW).1.le

theorem rawItem_valid {n : ℕ} (geom : ℕ) (hgeom : 0 < geom)
    (subclass : Subclass) (label : Option (Fin n)) (W : ℤ)
    (hW : |(W : ℚ) / geom| ≤ 6) :
    0 < (rawItem geom subclass label W).1 ∧
      (rawItem geom subclass label W).1 < (rawItem geom subclass label W).2 := by
  have hs := itemNumerator_pos_lt geom hgeom subclass label W hW
  rw [← rawItem_numerator_cast geom hgeom subclass label W hW] at hs
  exact_mod_cast hs

theorem rawItem_ratio {n : ℕ} (geom : ℕ) (hgeom : 0 < geom)
    (subclass : Subclass) (label : Option (Fin n)) (W : ℤ)
    (hW : |(W : ℚ) / geom| ≤ 6) :
    ((rawItem geom subclass label W).1 : ℚ) / (rawItem geom subclass label W).2 =
      encodedSize subclass label ((W : ℚ) / geom) := by
  have hc : ((rawItem geom subclass label W).1 : ℚ) =
      (itemNumerator geom subclass label W : ℚ) := by
    exact_mod_cast rawItem_numerator_cast geom hgeom subclass label W hW
  rw [hc]
  exact itemNumerator_ratio geom hgeom subclass label W

def localNumerator (D L ell : ℕ) : ℕ := 10 * widthRadix D ^ (L - ell)

theorem geomDenominator_mul_gap (m R D L : ℕ) :
    (geomDenominator m R D L : ℚ) * Geometry.gap m R =
      10 * (widthRadix D : ℚ) ^ L := by
  have hp : ((R : ℚ) + 1) ^ m ≠ 0 :=
    pow_ne_zero m (by positivity)
  unfold geomDenominator Geometry.gap
  push_cast
  field_simp [hp]
  ring

theorem geomDenominator_mul_lambda (m R D L ell : ℕ) (hell : ell ≤ L) :
    (geomDenominator m R D L : ℚ) * Geometry.lambda m R D ell =
      (localNumerator D L ell : ℚ) := by
  have hc : (widthRadix D : ℚ) ≠ 0 := by
    exact_mod_cast (widthRadix_pos D).ne'
  have hpow : (widthRadix D : ℚ) ^ L =
      (widthRadix D : ℚ) ^ ell * (widthRadix D : ℚ) ^ (L - ell) := by
    rw [← pow_add, Nat.add_sub_of_le hell]
  have hrad : (100 * ((D : ℚ) + 1)) = (widthRadix D : ℚ) := by
    simp [widthRadix]
  rw [Geometry.lambda, ← mul_div_assoc, geomDenominator_mul_gap, hrad, hpow]
  simp only [localNumerator, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  field_simp [hc]

theorem geomDenominator_mul_delta (m R D L : ℕ) :
    (geomDenominator m R D L : ℚ) * Geometry.delta m R D L = 1 := by
  rw [Geometry.delta, ← mul_div_assoc, geomDenominator_mul_lambda m R D L L le_rfl]
  norm_num [localNumerator]

def baselineNumerator (m R D L : ℕ) (r : Geometry.Position m R) : ℤ :=
  80 * (R + 1 : ℤ) ^ m * (widthRadix D : ℤ) ^ L +
    10 * (widthRadix D : ℤ) ^ L *
      (((r.2.val : ℤ) + 1) * (R + 1 : ℤ) ^ r.1.val - 1)

def betaNumerator (m R D L : ℕ) (e : Fin m) : ℤ :=
  10 * (widthRadix D : ℤ) ^ L * ((R + 1 : ℤ) ^ e.val - 1)

theorem geomDenominator_mul_baseline (m R D L : ℕ) (r : Geometry.Position m R) :
    (geomDenominator m R D L : ℚ) * Geometry.baseline m R r =
      (baselineNumerator m R D L r : ℚ) := by
  rw [Geometry.baseline, mul_add, ← mul_assoc, geomDenominator_mul_gap]
  simp only [baselineNumerator, Geometry.heightCode, geomDenominator]
  push_cast
  ring

theorem geomDenominator_mul_beta (m R D L : ℕ) (e : Fin m) :
    (geomDenominator m R D L : ℚ) * Geometry.beta m R e =
      (betaNumerator m R D L e : ℚ) := by
  rw [Geometry.beta, ← mul_assoc, geomDenominator_mul_gap]
  simp only [betaNumerator, Geometry.theta]
  push_cast
  ring

end BinPackingGap.IntegerPackingArithmetic

end OAI


