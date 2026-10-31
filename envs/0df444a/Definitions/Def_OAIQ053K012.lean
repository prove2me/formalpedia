-- Prove2me | Definitions.Def_OAIQ053K012
-- name    : OAIQ053K012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:54:33.476807+00:00
-- url     : https://prove2.me/theorems/76cc6deb-70ac-43fa-8331-492c39c35516
-- title:
--   Definitions bundle OAIQ053K012 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 38 declarations of OpenAI's Lean: 15 definitions, 1 inductive type or structure, 4 instances and 18 theorems. The definitions and types are `OAI.MetricKMedian.FiniteLaw.bitsConsEquiv`, `OAI.MetricKMedian.FiniteLaw.bitsEquiv`, `OAI.MetricKMedian.SourceBalance.amount`, `OAI.MetricKMedian.SourceBalance.bias`, `OAI.MetricKMedian.SourceBalance.negative`, `OAI.MetricKMedian.SourceBalance.nonzero`, `OAI.MetricKMedian.SparseBernoulli.countCoefficients`, `OAI.MetricKMedian.SparseBernoulli.countSets`, `OAI.MetricKMedian.SparseBernoulli.pairCoefficient`, `OAI.MetricKMedian.SparseBernoulli.pairSet`, `OAI.MetricKMedian.Taper.GraphData`, `OAI.MetricKMedian.Taper.GraphData.Good`, `OAI.MetricKMedian.Taper.colocatedMass`, `OAI.MetricKMedian.Taper.marginal`, `OAI.MetricKMedian.Taper.mass`, `OAI.MetricKMedian.WeightedRounding.indicator`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedian_Geometry_RationalBrackets`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Geometry/RationalBrackets.lean), [`KMedian_Probability_BernoulliReindex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Probability/BernoulliReindex.lean), [`KMedian_Probability_BernoulliSquare`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Probability/BernoulliSquare.lean), [`KMedian_Probability_BernoulliVariance`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Probability/BernoulliVariance.lean), [`KMedian_Process_CountSource`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/CountSource.lean), [`KMedian_Process_SourceBalance`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/SourceBalance.lean), [`KMedian_Process_Taper`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/Taper.lean), [`KMedian_Process_TaperGraph`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/TaperGraph.lean), [`KMedian_Rounding_RationalTaperAffine`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Rounding/RationalTaperAffine.lean), [`KMedian_Rounding_WeightedRounding`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Rounding/WeightedRounding.lean), [`KMedian_Sparse_SparseCountStatistic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseCountStatistic.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ053K027`; the statements `OAI.MetricKMedian.CopyState.unbalanced_small_change_s53`, `OAI.MetricKMedian.CopyState.valid_advance_s53`, `OAI.MetricKMedian.FixedBatch.masked_biased_linear_bound_s53`, `OAI.MetricKMedian.FixedBatch.masked_mass_sum_s53`, `OAI.MetricKMedian.FixedBatch.masked_total_bound_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.graph_data_all_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.graph_data_s53`, `OAI.MetricKMedian.SparseCopyState.physical_count_tail_s53` and `OAI.MetricKMedian.SparseFixedCount.actual_count_tail_s53`; the proofs of `OAI.MetricKMedian.CopyState.unbalanced_small_change_s53`, `OAI.MetricKMedian.CopyState.valid_advance_s53`, `OAI.MetricKMedian.CountStatistic.variance_bound_s53`, `OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts_spec_s53`, `OAI.MetricKMedian.FixedBatch.masked_biased_linear_bound_s53`, `OAI.MetricKMedian.FixedBatch.masked_mass_sum_s53`, `OAI.MetricKMedian.FixedBatch.masked_total_bound_s53` and `OAI.MetricKMedian.SparseCopyState.physical_count_tail_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ053_KM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalBrackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

theorem rational_bracket (B : Finset ℚ) (r : ℝ) (lo hi : ℚ)
    (hlo : lo ∈ B) (hhi : hi ∈ B) (hlor : (lo:ℝ) < r) (hrhi : r < (hi:ℝ))
    (hnot : ∀ q ∈ B, (q:ℝ) ≠ r) :
    ∃ a ∈ B, ∃ b ∈ B, (a:ℝ) < r ∧ r < (b:ℝ) ∧
      ∀ q ∈ B, q ≤ a ∨ b ≤ q := by
  classical
  let A : Finset ℚ := B.filter (fun q : ℚ => (q:ℝ) < r)
  let C : Finset ℚ := B.filter (fun q : ℚ => r < (q:ℝ))
  have hA : A.Nonempty := ⟨lo,mem_filter.mpr ⟨hlo,hlor⟩⟩
  have hC : C.Nonempty := ⟨hi,mem_filter.mpr ⟨hhi,hrhi⟩⟩
  let a := A.max' hA
  let b := C.min' hC
  have ha := mem_filter.mp (max'_mem A hA)
  have hb := mem_filter.mp (min'_mem C hC)
  refine ⟨a,ha.1,b,hb.1,ha.2,hb.2,?_⟩
  intro q hq
  rcases lt_or_gt_of_ne (hnot q hq) with hqlo | hqhi
  · exact Or.inl (le_max' A q (mem_filter.mpr ⟨hq,hqlo⟩))
  · exact Or.inr (min'_le C q (mem_filter.mpr ⟨hq,hqhi⟩))

theorem same_interval_cuts (B : Finset ℚ) (a b : ℚ)
    (hgap : ∀ q ∈ B, q ≤ a ∨ b ≤ q) (x y : ℝ)
    (hx : (a:ℝ) < x ∧ x < (b:ℝ)) (hy : (a:ℝ) < y ∧ y < (b:ℝ)) :
    ∀ q ∈ B, (x ≤ (q:ℝ) ↔ y ≤ (q:ℝ)) ∧ ((q:ℝ) ≤ x ↔ (q:ℝ) ≤ y) := by
  intro q hq
  rcases hgap q hq with hq | hq
  · have hq' : (q:ℝ) ≤ a := by exact_mod_cast hq
    exact ⟨iff_of_false (not_le_of_gt (hq'.trans_lt hx.1))
      (not_le_of_gt (hq'.trans_lt hy.1)),iff_of_true (hq'.trans hx.1.le) (hq'.trans hy.1.le)⟩
  · have hq' : (b:ℝ) ≤ q := by exact_mod_cast hq
    exact ⟨iff_of_true (hx.2.le.trans hq') (hy.2.le.trans hq'),
      iff_of_false (not_le_of_gt (hx.2.trans_le hq')) (not_le_of_gt (hy.2.trans_le hq'))⟩

end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw

def bitsConsEquiv (n : ℕ) : Bool × (Fin n → Bool) ≃ (Fin (n+1) → Bool) where
  toFun z := Fin.cons z.1 z.2
  invFun ω := (ω 0, Fin.tail ω)
  left_inv z := by cases z; simp
  right_inv ω := Fin.cons_self_tail ω

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def bitsEquiv (e : I ≃ J) : (J → Bool) ≃ (I → Bool) where
  toFun ω := ω ∘ e
  invFun ω := ω ∘ e.symm
  left_inv ω := by funext i; simp
  right_inv ω := by funext i; simp

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n m : ℕ}

def pairSet (S : Fin m → Finset (Fin n)) (a : Fin (m*m)) : Finset (Fin n) :=
  S (finProdFinEquiv.symm a).1 ∪ S (finProdFinEquiv.symm a).2

def pairCoefficient (c : Fin m → ℚ) (a : Fin (m*m)) : ℚ :=
  c (finProdFinEquiv.symm a).1*c (finProdFinEquiv.symm a).2

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_SourceBalance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SourceBalance
open Finset
variable {I : Type*} [Fintype I]

noncomputable def negative (m : I → ℝ) : Finset I := univ.filter (fun i => 1 < m i)
noncomputable def nonzero (m : I → ℝ) : Finset I := univ.filter (fun i => m i ≠ 1)
noncomputable def amount (m : I → ℝ) : ℝ := ∑ i, max (1-m i) 0

end MetricKMedian.SourceBalance
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SourceBalance
open Finset
variable {I : Type*} [Fintype I]

noncomputable def bias (m : I → ℝ) (p φ : ℝ) (i : I) : ℝ :=
  if 1 < m i then (1+φ)*p else p

end MetricKMedian.SourceBalance

end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_Taper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper

noncomputable def marginal (P d r : ℝ) : ℝ := min 1 (max (1-r*d) 0/P)

theorem marginal_nonneg {P d r : ℝ} (hP : 0 < P) : 0 ≤ marginal P d r :=
  le_min (by norm_num) (div_nonneg (le_max_right _ _) hP.le)

theorem marginal_le_one (P d r : ℝ) : marginal P d r ≤ 1 := min_le_left _ _

theorem marginal_antitone {P d : ℝ} (hP : 0 < P) (hd : 0 ≤ d) : Antitone (marginal P d) := by
  intro r s hrs
  apply min_le_min_left
  apply div_le_div_of_nonneg_right _ hP.le
  apply max_le_max_right
  nlinarith only [mul_le_mul_of_nonneg_right hrs hd]

theorem marginal_one {P d r : ℝ} (hP : 0 < P) (h : r*d ≤ 1-P) : marginal P d r=1 := by
  apply min_eq_left
  apply (le_div_iff₀ hP).mpr
  have hh := le_max_left (1-r*d) 0
  linarith only [h, hh]

theorem marginal_zero {P d r : ℝ} (h : 1 ≤ r*d) : marginal P d r=0 := by
  simp only [marginal, max_eq_right (by linarith : 1-r*d ≤ 0), zero_div]
  norm_num

theorem marginal_at_zero_distance {P r : ℝ} (hP : 0 < P) (hP1 : P ≤ 1) : marginal P 0 r=1 := by
  apply marginal_one hP
  simpa only [mul_zero] using sub_nonneg.mpr hP1

theorem lower_comparison {P d r : ℝ} (hP : 0 < P) (h : marginal P d r < 1) :
    1-P*marginal P d r ≤ r*d := by
  have hright : max (1-r*d) 0/P < 1 := by
    by_contra hn
    have heq : marginal P d r=1 := min_eq_left (le_of_not_gt hn)
    rw [heq] at h
    exact lt_irrefl _ h
  have heq : marginal P d r=max (1-r*d) 0/P := min_eq_right hright.le
  rw [heq, mul_div_cancel₀ _ (ne_of_gt hP)]
  have hh := le_max_left (1-r*d) 0
  linarith only [hh]

theorem upper_comparison {P d r : ℝ} (hP : 0 < P) (h : 0 < marginal P d r) :
    r*d ≤ 1-P*marginal P d r := by
  have hrd : r*d < 1 := by
    by_contra hn
    rw [marginal_zero (le_of_not_gt hn)] at h
    exact lt_irrefl _ h
  have hh : marginal P d r ≤ (1-r*d)/P := by
    unfold marginal
    rw [max_eq_left (by linarith only [hrd])]
    exact min_le_right _ _
  have hb := (le_div_iff₀ hP).mp hh
  nlinarith only [hb]

variable {I : Type*} [Fintype I]

noncomputable def mass (g P : ℝ) (d : I → ℝ) (r : ℝ) : ℝ := ∑ i, g*marginal P (d i) r

noncomputable def colocatedMass (g : ℝ) (d : I → ℝ) : ℝ := ∑ i, if d i=0 then g else 0

theorem mass_antitone {g P : ℝ} {d : I → ℝ} (hg : 0 ≤ g) (hP : 0 < P)
    (hd : ∀ i, 0 ≤ d i) : Antitone (mass g P d) := by
  intro r s hrs
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (marginal_antitone hP (hd i) hrs) hg)

theorem continuous_mass {g P : ℝ} {d : I → ℝ} : Continuous (mass g P d) := by
  unfold mass marginal
  fun_prop

theorem exists_full_inverse {P : ℝ} (hP : 0 < P) (hP1 : P ≤ 1/2)
    (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    ∃ r > 0, ∀ i, marginal P (d i) r=1 := by
  let D := ∑ i, d i
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ => hd i)
  have hden : 0 < 2*(1+D) := by linarith only [hD]
  refine ⟨1/(2*(1+D)), one_div_pos.mpr hden, ?_⟩
  intro i
  apply marginal_one hP
  have hi : d i ≤ D := Finset.single_le_sum (fun t _ => hd t) (Finset.mem_univ i)
  have hh : (1/(2*(1+D)))*d i ≤ 1/2 := by
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hden).mpr
    linarith only [hi]
  linarith only [hh, hP1]

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_TaperGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I X : Type*} [Fintype I] [DecidableEq I] [PseudoMetricSpace X]

structure GraphData (Δ : ℕ) (g P : ℝ) (location : I → X) (own : I → Finset I) where
  radius : I → ℝ
  marginal : I → I → ℝ
  radius_nonneg : ∀ i, 0 ≤ radius i
  marginal_nonneg : ∀ h i, 0 ≤ marginal h i
  marginal_le_one : ∀ h i, marginal h i ≤ 1
  incoming_mass : ∀ i, ∑ h, g*marginal h i=1
  incoming_count : ∀ i, ∑ h, marginal h i=Δ
  own_certain : ∀ i h, h ∈ own i → marginal h i=1
  lower : ∀ h i, marginal h i < 1 →
    radius i*(1-P*marginal h i) ≤ dist (location i) (location h)
  upper : ∀ h i, 0 < marginal h i →
    dist (location i) (location h) ≤ radius i*(1-P*marginal h i)
  minimal : ∀ i R, 0 < R →
    1 ≤ mass g P (fun h => dist (location i) (location h)) (1/R) → radius i ≤ R

def GraphData.Good {Δ : ℕ} {g P : ℝ} {location : I → X} {own : I → Finset I}
    (D : GraphData Δ g P location own) (G : I → Finset I) : Prop :=
  (∀ i, (G i).card=Δ) ∧ (∀ i, own i ⊆ G i) ∧
    (∀ h i, h ∈ G i → 0 < D.marginal h i)

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalTaperAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset

theorem marginal_piecewise {P d r : ℝ} (hP : 0 < P) :
    marginal P d r=if r*d ≤ 1-P then 1 else
      if 1 ≤ r*d then 0 else (1-r*d)/P := by
  split_ifs with hs hz
  · exact marginal_one hP hs
  · exact marginal_zero hz
  · have hp : 0 ≤ 1-r*d := by linarith
    have hh : (1-r*d)/P ≤ 1 := (div_le_one₀ hP).mpr (by linarith)
    exact (congrArg (min 1) (congrArg (fun a => a/P) (max_eq_left hp))).trans (min_eq_right hh)

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_WeightedRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.WeightedRounding

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def indicator (S : Finset I) (i : I) : ℝ := if i ∈ S then 1 else 0

end MetricKMedian.WeightedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCountStatistic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseBernoulli
open Finset
variable {n : ℕ}

def countSets (a : Fin (n+n*n)) : Finset (Fin n) :=
  (finSumFinEquiv.symm a).elim (fun i => {i})
    (fun ij => {(finProdFinEquiv.symm ij).1} ∪ {(finProdFinEquiv.symm ij).2})

def countCoefficients (b : Fin n → ℚ) (c : Fin n → Fin n → ℚ) (a : Fin (n+n*n)) : ℚ :=
  (finSumFinEquiv.symm a).elim b
    (fun ij => (1/2)*c (finProdFinEquiv.symm ij).1 (finProdFinEquiv.symm ij).2)

end MetricKMedian.SparseBernoulli
end
end

end OAI
end


