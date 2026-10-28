-- Prove2me | Definitions.Def_OAIQ035K012
-- name    : OAIQ035K012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:54:21.037928+00:00
-- url     : https://prove2.me/theorems/d0211b02-f948-4746-b0ac-44efa6a57cae
-- title:
--   Definitions bundle OAIQ035K012 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 3 definitions, 4 instances and 5 theorems. The definitions and types are `OAI.MetricKMedian.FiniteLaw.bitsConsEquiv`, `OAI.MetricKMedian.FiniteLaw.bitsEquiv`, `OAI.MetricKMedian.WeightedRounding.indicator`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Geometry_RationalBrackets`, `KMedian_Probability_BernoulliReindex`, `KMedian_Probability_BernoulliVariance`, `KMedian_Rounding_WeightedRounding`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ035K036`; the statements `OAI_MetricKMedian_GraphComparison_uniform_drift_le` and `OAI.MetricKMedian.WeightedRounding.exact_law`; the proofs of `OAI.MetricKMedian.CountStatistic.variance_bound`, `OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts_spec`, `OAI_MetricKMedian_GraphComparison_uniform_drift_le` and `OAI.MetricKMedian.WeightedRounding.exact_law`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ035_KM.Compat
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
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalBrackets
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

end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliVariance
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
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliReindex
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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_WeightedRounding
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


