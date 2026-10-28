-- Prove2me | Definitions.Def_OAIQ3Ro000
-- name    : OAIQ3Ro000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:37:37.510952+00:00
-- url     : https://prove2.me/theorems/fcabab8a-63a7-4f78-a460-a902f83b221d
-- title:
--   Definitions bundle OAIQ3Ro000 of the split of OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 626 declarations of OpenAI's Lean: 266 definitions, 14 inductive types or structures, 56 instances and 290 theorems. The definitions and types are `OAI.Rokhlin.ArrayObjects.Arr`, `OAI.Rokhlin.ArrayObjects.DataKind`, `OAI.Rokhlin.ArrayObjects.Index`, `OAI.Rokhlin.ArrayObjects.InitialLaws`, `OAI.Rokhlin.ArrayObjects.Object`, `OAI.Rokhlin.ArrayObjects.Object.Extension`, `OAI.Rokhlin.ArrayObjects.Object.Extension.comp`, `OAI.Rokhlin.ArrayObjects.Object.Extension.pull`, `OAI.Rokhlin.ArrayObjects.Object.Extension.refl`, `OAI.Rokhlin.ArrayObjects.Object.IsSaturated`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.Cell`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.CellAt`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.GroupData`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.GroupedPolarData`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.IsConditional`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.OldData`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.Outside`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.Parameter`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.ParentData`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.ParentOutside`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.PositiveRawBlock`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.RawData`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.RawLabel`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.RawLabelSquare`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.RawLabelTuple`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.RevealData`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.RollData`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.ScreenData`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.State`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.WholeGroupData`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.allSplitExact`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.cellLaw`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.cells`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.collapseCell`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.columnActive`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.columnCellLaw`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.columnEdge`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.columnGroupKernel`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.columnKernel`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.columnOwnData` and 240 more.
--
--   **Sources.** They come from these modules of lean/OAI/Dynamics/MultipleMixing, in whole or in part: [`MultipleMixing_Arrays`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Arrays.lean), [`MultipleMixing_ExactLines`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/ExactLines.lean), [`MultipleMixing_FibreMeasures`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/FibreMeasures.lean), [`MultipleMixing_HilbertCodes`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/HilbertCodes.lean), [`MultipleMixing_Joinings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Joinings.lean), [`MultipleMixing_OrbitCancellation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/OrbitCancellation.lean), [`MultipleMixing_Saturation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Saturation.lean), [`MultipleMixing_Tensors`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tensors.lean), [`MultipleMixing_WeakLimits`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/WeakLimits.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ3Ro002`; the statements `OAI_Rokhlin_ArrayObjects_Object_Rolled_exists_commonLocalLineGraph`, `OAI_Rokhlin_ArrayObjects_Object_Rolled_exists_positive_raw_block`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_active_commutes`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_active_intersections`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_exact_split_span`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_polar_a_field`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_polar_b_field`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_polar_data`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_restricted_fixed_squares`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.rawCounting_partial_unitary`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_correlation_forces_coefficient`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_correlation_zero`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_active_to_column_exact`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_indicators_equal`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_line_projection`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.saturated_correlation_zero`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.slot_conditional_exactness`, `OAI.Rokhlin.ArrayObjects.compact_zero_entropy_no_witness` and `OAI_Rokhlin_finite_alphabet_correlation_zero`; the proofs of `OAI_Rokhlin_ArrayObjects_Object_Rolled_exists_positive_raw_block`, `OAI_Rokhlin_finite_alphabet_correlation_zero`, `OAI.Rokhlin.finite_tail_entropy_zero`, `OAI.Rokhlin.last_centered_correlation_zero`, `OAI.Rokhlin.sequential_mixing_all` and `OAI.Rokhlin.tail_finite_correlation_zero`.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Dynamics/MultipleMixing at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ3_Rok.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- Mathlib d13f23b's `condDistrib_ae_eq_of_measure_eq_compProd hX hY hκ`; ours takes `X` explicitly and
no `hX` (MultipleMixing Arrays, 2026-10-26). Declared in `OAI`, so a use under `open ProbabilityTheory`
is an overload and the one that typechecks wins. -/
theorem condDistrib_ae_eq_of_measure_eq_compProd
    {Ω β 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {mβ : MeasurableSpace β} {m𝓨 : MeasurableSpace 𝓨}
    [StandardBorelSpace 𝓨] [Nonempty 𝓨] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ] {X : Ω → β} {Y : Ω → 𝓨}
    (_hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    {κ : ProbabilityTheory.Kernel β 𝓨} [ProbabilityTheory.IsFiniteKernel κ]
    (hκ : μ.map (fun x => (X x, Y x)) = (μ.map X).compProd κ) :
    ProbabilityTheory.condDistrib Y X μ =ᵐ[μ.map X] κ :=
  ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd X hY hκ
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_HilbertCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section

open scoped InnerProductSpace CStarAlgebra
open ContinuousLinearMap

open MeasureTheory Filter
open scoped BigOperators Topology


variable {Ω : Type*} [MeasurableSpace Ω]

section Polar
variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def operatorAbs (T : E →L[ℂ] H) : E →L[ℂ] E :=
  CFC.sqrt (T.adjoint ∘L T)

end Polar

end

section
open MeasureTheory MeasurableSpace
open scoped ENNReal
variable {Y : Type*} [m : MeasurableSpace Y] [CountablyGenerated Y]
local instance instFactNeENNRealOfNatTop_solutions : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

def hilbertTestAlgebra : Set (Set Y) := generateSetAlgebra (Set.range (natGeneratingSequence Y))

lemma hilbertTestAlgebra_algebra : IsSetAlgebra (hilbertTestAlgebra (Y := Y)) :=
  isSetAlgebra_generateSetAlgebra

lemma hilbertTestAlgebra_countable : (hilbertTestAlgebra (Y := Y)).Countable :=
  countable_generateSetAlgebra (Set.countable_range _)

lemma hilbertTestAlgebra_generates : m = generateFrom (hilbertTestAlgebra (Y := Y)) := by
  rw [hilbertTestAlgebra,generateFrom_generateSetAlgebra_eq,generateFrom_natGeneratingSequence]

lemma hilbertTestAlgebra_measurable {s : Set Y} (hs : s ∈ hilbertTestAlgebra) : MeasurableSet s := by
  rw [hilbertTestAlgebra_generates (Y := Y)]
  exact measurableSet_generateFrom hs

lemma hilbertTestAlgebra_dense (μ : Measure Y) [IsFiniteMeasure μ] :
    (Submodule.span ℂ (Set.range (fun s : hilbertTestAlgebra (Y := Y) =>
      indicatorConstLp 2 (hilbertTestAlgebra_measurable s.property) (measure_ne_top μ s) (1 : ℂ)))).topologicalClosure = ⊤ := by
  let D := (Submodule.span ℂ (Set.range (fun s : hilbertTestAlgebra (Y := Y) =>
      indicatorConstLp 2 (hilbertTestAlgebra_measurable s.property) (measure_ne_top μ s) (1 : ℂ)))).topologicalClosure
  have hd := Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite μ hilbertTestAlgebra_algebra hilbertTestAlgebra_generates
  have hunit (s : Set Y) (hs : s ∈ hilbertTestAlgebra) (hμs : μ s ≠ ∞) (c : ℂ) :
      indicatorConstLp 2 (hd.measurable s hs) hμs c ∈ D := by
    have he : indicatorConstLp 2 (hd.measurable s hs) hμs c =
        c • indicatorConstLp 2 (hilbertTestAlgebra_measurable hs) (measure_ne_top μ s) (1 : ℂ) := by
      apply Lp.ext
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hd.measurable s hs) (hμs := hμs) (c := c),
        Lp.coeFn_smul c (indicatorConstLp 2 (hilbertTestAlgebra_measurable hs) (measure_ne_top μ s) (1 : ℂ)),
        indicatorConstLp_coeFn (p := 2) (hs := hilbertTestAlgebra_measurable hs) (hμs := measure_ne_top μ s) (c := (1 : ℂ))] with y hy hsm h1
      rw [hy,hsm]
      change s.indicator (fun _ => c) y = c • indicatorConstLp 2 (hilbertTestAlgebra_measurable hs) (measure_ne_top μ s) (1 : ℂ) y
      rw [h1]
      by_cases hys : y ∈ s <;> simp [hys]
    rw [he]
    exact D.smul_mem c (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨s,hs⟩,rfl⟩))
  apply top_unique
  intro v _
  change v ∈ D
  apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (fun v => v ∈ D)
  · intro c s hs hμs
    have hm := hd.indicatorConstLp_subset_closure (p := 2) c ⟨s,hs,hμs.ne,rfl⟩
    exact (closure_minimal (by rintro _ ⟨s,hs,hμs,rfl⟩; exact hunit s hs hμs c) (Submodule.isClosed_topologicalClosure _)) hm
  · intro f g hf hg hfg hF hG
    exact D.add_mem hF hG
  · exact (Submodule.isClosed_topologicalClosure _)

end

section
open MeasureTheory MeasurableSpace Topology
open scoped ENNReal
variable {Y : Type*} [MeasurableSpace Y] [CountablyGenerated Y]

abbrev HilbertTestKey (Y : Type*) [MeasurableSpace Y] [CountablyGenerated Y] :=
  List ((ℚ × ℚ) × hilbertTestAlgebra (Y := Y))

instance instCountableHilbertTestKey : Countable (HilbertTestKey Y) := by
  have : Countable (hilbertTestAlgebra (Y := Y)) := hilbertTestAlgebra_countable.to_subtype
  infer_instance

def hilbertTestFunction (t : HilbertTestKey Y) : Y → ℂ :=
  fun y => (t.map (fun p => ((p.1.1 : ℂ) + p.1.2 * Complex.I) *
    (p.2.val.indicator (fun _ => (1 : ℂ))) y)).sum

lemma hilbertTestFunction_measurable (t : HilbertTestKey Y) : Measurable (hilbertTestFunction t) := by
  induction t with
  | nil =>
    change Measurable (fun _ : Y => (0 : ℂ))
    exact measurable_const
  | cons p t ih =>
    change Measurable (fun y => ((p.1.1 : ℂ) + p.1.2 * Complex.I) *
      (p.2.val.indicator (fun _ => (1 : ℂ))) y + hilbertTestFunction t y)
    exact (measurable_const.mul (measurable_const.indicator (hilbertTestAlgebra_measurable p.2.property))).add ih

def hilbertTestVector (μ : Measure Y) [IsFiniteMeasure μ] (t : HilbertTestKey Y) : Lp ℂ 2 μ :=
  (t.map (fun p => ((p.1.1 : ℂ) + p.1.2 * Complex.I) •
    indicatorConstLp 2 (hilbertTestAlgebra_measurable p.2.property) (measure_ne_top μ p.2.val) (1 : ℂ))).sum

lemma hilbertTestVector_append (μ : Measure Y) [IsFiniteMeasure μ] (s t : HilbertTestKey Y) :
    hilbertTestVector μ (s ++ t) = hilbertTestVector μ s + hilbertTestVector μ t := by
  simp [hilbertTestVector]

lemma rationalComplex_dense : DenseRange (fun p : ℚ × ℚ => (p.1 : ℂ) + p.2 * Complex.I) := by
  have h := Rat.denseRange_cast (𝕜 := ℝ)
  have hh := h.prodMap h
  have hsurj : Function.Surjective (fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * Complex.I) := by
    intro z
    exact ⟨(z.re,z.im),Complex.re_add_im z⟩
  convert hsurj.denseRange.comp hh (by fun_prop) using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp

lemma hilbertTestVector_dense (μ : Measure Y) [IsFiniteMeasure μ] :
    DenseRange (hilbertTestVector μ) := by
  let S : AddSubmonoid (Lp ℂ 2 μ) := {
    carrier := Set.range (hilbertTestVector μ)
    zero_mem' := ⟨[],by simp [hilbertTestVector]⟩
    add_mem' := by
      rintro _ _ ⟨s,rfl⟩ ⟨t,rfl⟩
      exact ⟨s ++ t,hilbertTestVector_append μ s t⟩ }
  let D := S.topologicalClosure
  have hd : IsClosed (D : Set (Lp ℂ 2 μ)) := AddSubmonoid.isClosed_topologicalClosure S
  have hsingle (t : hilbertTestAlgebra (Y := Y)) (c : ℂ) :
      c • indicatorConstLp 2 (hilbertTestAlgebra_measurable t.property)
        (measure_ne_top μ t.val) (1 : ℂ) ∈ D := by
    refine rationalComplex_dense.induction_on c
      (hd.preimage (continuous_id.smul continuous_const)) ?_
    intro q
    apply (show (S : Set (Lp ℂ 2 μ)) ⊆ D from subset_closure)
    exact ⟨[(q,t)],by simp [hilbertTestVector]⟩
  have hspan : (Submodule.span ℂ (Set.range (fun t : hilbertTestAlgebra (Y := Y) =>
      indicatorConstLp 2 (hilbertTestAlgebra_measurable t.property)
        (measure_ne_top μ t.val) (1 : ℂ))) : Set (Lp ℂ 2 μ)) ⊆ D := by
    intro v hv
    have h : ∀ c : ℂ, c • v ∈ D := by
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨t,rfl⟩ := hx
        exact hsingle t
      | zero => intro c; simp only [smul_zero]; exact D.zero_mem
      | add x y hx hy ihx ihy =>
        intro c
        simpa only [smul_add] using D.add_mem (ihx c) (ihy c)
      | smul a x hx ih => intro c; simpa only [smul_smul] using ih (c*a)
    simpa using h 1
  intro v
  have hall : (Submodule.span ℂ (Set.range (fun t : hilbertTestAlgebra (Y := Y) =>
      indicatorConstLp 2 (hilbertTestAlgebra_measurable t.property)
        (measure_ne_top μ t.val) (1 : ℂ)))).topologicalClosure = ⊤ := hilbertTestAlgebra_dense μ
  have hv : v ∈ (Submodule.span ℂ (Set.range (fun t : hilbertTestAlgebra (Y := Y) =>
      indicatorConstLp 2 (hilbertTestAlgebra_measurable t.property)
        (measure_ne_top μ t.val) (1 : ℂ)))).topologicalClosure := by rw [hall]; trivial
  exact closure_minimal hspan hd hv
end

section
open Filter Topology MeasureTheory

def IsDistanceCode (d : ℕ → ℕ → ℝ) (z : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ z n) ∧ (∀ n m, z n ≤ d n m + z m) ∧
    (∀ n m, d n m ≤ z n + z m) ∧ ∀ m : ℕ, ∃ n, z n < (1/2 : ℝ)^m

variable {H : Type*} [MetricSpace H] [CompleteSpace H]
omit [CompleteSpace H] in
lemma distance_isCode {a : ℕ → H} (ha : DenseRange a) (v : H) :
    IsDistanceCode (fun n m => dist (a n) (a m)) (fun n => dist v (a n)) := by
  refine ⟨fun n => dist_nonneg, ?_, ?_, ?_⟩
  · intro n m
    simpa [dist_comm,add_comm] using dist_triangle v (a m) (a n)
  · intro n m
    simpa [dist_comm] using dist_triangle (a n) v (a m)
  · intro m
    exact ha.exists_dist_lt v (by positivity : 0 < (1/2 : ℝ)^m)

lemma IsDistanceCode.exists_eq {a : ℕ → H} {z : ℕ → ℝ}
    (hz : IsDistanceCode (fun n m => dist (a n) (a m)) z) :
    ∃ v : H, ∀ n, dist v (a n) = z n := by
  choose b hb using hz.2.2.2
  have ht : Tendsto (fun m => z (b m)) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => hz.1 _)
      (Eventually.of_forall fun m => (hb m).le)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have hc : CauchySeq (fun m => a (b m)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (half_pos hε)))
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := hz.2.2.1 (b m) (b n)
    have := hN m hm
    have := hN n hn
    linarith
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨v,fun n => le_antisymm ?_ ?_⟩
  · have h := le_of_tendsto_of_tendsto (hv.dist tendsto_const_nhds)
      (ht.add_const (z n)) (Eventually.of_forall fun m => hz.2.2.1 (b m) n)
    simpa using h
  · have h := le_of_tendsto_of_tendsto tendsto_const_nhds
      ((tendsto_const_nhds.dist hv).add ht)
      (Eventually.of_forall fun m => hz.2.1 n (b m))
    simpa [dist_comm] using h

omit [CompleteSpace H] in
lemma distance_code_injective {a : ℕ → H} (ha : DenseRange a) :
    Function.Injective (fun v : H => fun n => dist v (a n)) := by
  intro v w he
  have hh : ∀ b : H, dist v b = dist w b := fun b => ha.induction_on b
    (isClosed_eq (continuous_const.dist continuous_id) (continuous_const.dist continuous_id))
    (fun n => congrFun he n)
  simpa [dist_comm] using (hh v).symm

variable {U : Type*} [MeasurableSpace U]
lemma measurableSet_distanceCode (d : U → ℕ → ℕ → ℝ)
    (hd : ∀ n m, Measurable (fun u => d u n m)) :
    MeasurableSet {p : U × (ℕ → ℝ) | IsDistanceCode (d p.1) p.2} := by
  have hz (n : ℕ) : Measurable (fun p : U × (ℕ → ℝ) => p.2 n) :=
    (measurable_pi_apply n).comp measurable_snd
  have hd' (n m : ℕ) : Measurable (fun p : U × (ℕ → ℝ) => d p.1 n m) :=
    (hd n m).comp measurable_fst
  simp only [IsDistanceCode, Set.ofPred_and, Set.ofPred_forall, Set.ofPred_exists]
  exact (MeasurableSet.iInter fun n => measurableSet_le measurable_const (hz n)).inter
    ((MeasurableSet.iInter fun n => MeasurableSet.iInter fun m =>
      measurableSet_le (hz n) ((hd' n m).add (hz m))).inter
    ((MeasurableSet.iInter fun n => MeasurableSet.iInter fun m =>
      measurableSet_le (hd' n m) ((hz n).add (hz m))).inter
    (MeasurableSet.iInter fun m : ℕ => MeasurableSet.iUnion fun n : ℕ =>
      measurableSet_lt (hz n) measurable_const)))
end

section
open MeasureTheory MeasurableSpace ProbabilityTheory
open scoped ENNReal InnerProductSpace
variable {Y : Type*} [MeasurableSpace Y] [CountablyGenerated Y]

lemma hilbertTestVector_coe (μ : Measure Y) [IsFiniteMeasure μ] (t : HilbertTestKey Y) :
    ↑(hilbertTestVector μ t) =ᵐ[μ] hilbertTestFunction t := by
  induction t with
  | nil => exact Lp.coeFn_zero _ _ _
  | cons p t ih =>
    let c : ℂ := (p.1.1 : ℂ) + p.1.2 * Complex.I
    let f := indicatorConstLp 2 (hilbertTestAlgebra_measurable p.2.property)
      (measure_ne_top μ p.2.val) (1 : ℂ)
    change ↑(c • f + hilbertTestVector μ t) =ᵐ[μ] _
    filter_upwards [Lp.coeFn_add (c • f) (hilbertTestVector μ t),Lp.coeFn_smul c f,
      indicatorConstLp_coeFn (p := 2) (hs := hilbertTestAlgebra_measurable p.2.property)
        (hμs := measure_ne_top μ p.2.val) (c := (1 : ℂ)),ih] with y hadd hsm hf ht
    change (c • f + hilbertTestVector μ t) y = c * _ + hilbertTestFunction t y
    rw [hadd]
    change (c • f) y + hilbertTestVector μ t y = _
    rw [hsm]
    change c * f y + hilbertTestVector μ t y = _
    rw [hf,ht]

def hilbertTestKeys : ℕ → HilbertTestKey Y := Classical.choose (exists_surjective_nat (HilbertTestKey Y))
lemma hilbertTestKeys_surjective : Function.Surjective (hilbertTestKeys (Y := Y)) :=
  Classical.choose_spec (exists_surjective_nat (HilbertTestKey Y))

def hilbertTests (μ : Measure Y) [IsFiniteMeasure μ] (n : ℕ) : Lp ℂ 2 μ :=
  hilbertTestVector μ (hilbertTestKeys n)
lemma hilbertTests_dense (μ : Measure Y) [IsFiniteMeasure μ] : DenseRange (hilbertTests μ) :=
  by
    have hr : Set.range (hilbertTests μ) = Set.range (hilbertTestVector μ) := by
      ext v
      constructor
      · rintro ⟨n,rfl⟩
        exact ⟨hilbertTestKeys n,rfl⟩
      · rintro ⟨t,rfl⟩
        obtain ⟨n,rfl⟩ := hilbertTestKeys_surjective t
        exact ⟨n,rfl⟩
    intro v
    simpa only [hr] using hilbertTestVector_dense μ v

lemma hilbertTestVector_dist (μ : Measure Y) [IsFiniteMeasure μ] (s t : HilbertTestKey Y) :
    dist (hilbertTestVector μ s) (hilbertTestVector μ t) =
      Real.sqrt (Complex.re (∫ y, inner ℂ (hilbertTestFunction s y - hilbertTestFunction t y)
        (hilbertTestFunction s y - hilbertTestFunction t y) ∂μ)) := by
  rw [dist_eq_norm]
  have he : (∫ y, inner ℂ ((hilbertTestVector μ s - hilbertTestVector μ t) y)
      ((hilbertTestVector μ s - hilbertTestVector μ t) y) ∂μ) =
      ∫ y, inner ℂ (hilbertTestFunction s y - hilbertTestFunction t y)
        (hilbertTestFunction s y - hilbertTestFunction t y) ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (hilbertTestVector μ s) (hilbertTestVector μ t),
      hilbertTestVector_coe μ s,hilbertTestVector_coe μ t] with y hd hs ht
    rw [hd]
    change inner ℂ (hilbertTestVector μ s y - hilbertTestVector μ t y)
      (hilbertTestVector μ s y - hilbertTestVector μ t y) = _
    rw [hs,ht]
  rw [←he,←L2.inner_def]
  exact norm_eq_sqrt_re_inner (𝕜 := ℂ) _

variable {U : Type*} [MeasurableSpace U]
lemma hilbertTests_dist_measurable (κ : Kernel U Y) [IsMarkovKernel κ] (n m : ℕ) :
    Measurable (fun u => dist (hilbertTests (κ u) n) (hilbertTests (κ u) m)) := by
  simp only [hilbertTests,hilbertTestVector_dist]
  apply Real.continuous_sqrt.measurable.comp
  apply Complex.continuous_re.measurable.comp
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_kernel
  exact ((hilbertTestFunction_measurable _).sub (hilbertTestFunction_measurable _)).stronglyMeasurable.inner
    ((hilbertTestFunction_measurable _).sub (hilbertTestFunction_measurable _)).stronglyMeasurable

end

section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  (κ : Kernel U Y) [IsMarkovKernel κ]

def HilbertCode := {p : U × (ℕ → ℝ) //
  IsDistanceCode (fun n m => dist (hilbertTests (κ p.1) n) (hilbertTests (κ p.1) m)) p.2}

instance instMeasurableSpaceHilbertCode : MeasurableSpace (HilbertCode κ) := inferInstanceAs (MeasurableSpace (Subtype _))
instance instStandardBorelSpaceHilbertCode [StandardBorelSpace U] : StandardBorelSpace (HilbertCode κ) := by
  apply MeasurableSet.standardBorel
  exact measurableSet_distanceCode _ (hilbertTests_dist_measurable κ)

namespace HilbertCode
variable {κ}
def base (p : HilbertCode κ) : U := p.val.1
def code (p : HilbertCode κ) : ℕ → ℝ := p.val.2
lemma measurable_code (n : ℕ) : Measurable (fun p : HilbertCode κ => p.code n) :=
  ((measurable_pi_apply n).comp measurable_snd).comp measurable_subtype_coe

def decode (p : HilbertCode κ) : Lp ℂ 2 (κ p.base) := p.property.exists_eq.choose
lemma decode_dist (p : HilbertCode κ) (n : ℕ) :
    dist p.decode (hilbertTests (κ p.base) n) = p.code n := p.property.exists_eq.choose_spec n

def encode (u : U) (v : Lp ℂ 2 (κ u)) : HilbertCode κ :=
  ⟨(u,fun n => dist v (hilbertTests (κ u) n)),distance_isCode (hilbertTests_dense (κ u)) v⟩
lemma decode_encode (u : U) (v : Lp ℂ 2 (κ u)) : (encode u v).decode = v := by
  apply distance_code_injective (hilbertTests_dense (κ u))
  funext n
  exact (encode u v).decode_dist n

lemma encode_decode (p : HilbertCode κ) : encode p.base p.decode = p := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  funext n
  exact p.decode_dist n

def approxIndex (p : HilbertCode κ) (m : ℕ) : ℕ := Nat.find (p.property.2.2.2 m)
lemma approxIndex_spec (p : HilbertCode κ) (m : ℕ) :
    dist (hilbertTests (κ p.base) (approxIndex p m)) p.decode < (1/2 : ℝ)^m := by
  rw [dist_comm,decode_dist]
  exact Nat.find_spec (p.property.2.2.2 m)

lemma measurable_approxIndex (m : ℕ) : Measurable (fun p : HilbertCode κ => approxIndex p m) := by
  exact Measurable.find (f := fun n (_ : HilbertCode κ) => n) (fun _ => measurable_const)
    (fun n => measurableSet_lt (measurable_code (κ := κ) n) measurable_const)
    (fun p => p.property.2.2.2 m)

def approximant (m : ℕ) (p : HilbertCode κ × Y) : ℂ :=
  hilbertTestFunction (hilbertTestKeys (approxIndex p.1 m)) p.2

lemma measurable_approximant (m : ℕ) : Measurable (approximant (κ := κ) m) := by
  have hm : Measurable (fun p : ℕ × Y => hilbertTestFunction (hilbertTestKeys p.1) p.2) :=
    measurable_from_prod_countable_right fun n => hilbertTestFunction_measurable (hilbertTestKeys n)
  exact hm.comp (((measurable_approxIndex m).comp measurable_fst).prodMk measurable_snd)

def representative (p : HilbertCode κ × Y) : ℂ :=
  limUnder atTop (fun m => approximant m p)
lemma measurable_representative : Measurable (representative (κ := κ)) := by
  exact (StronglyMeasurable.limUnder fun m => (measurable_approximant m).stronglyMeasurable).measurable

lemma representative_eq_decode (p : HilbertCode κ) :
    (fun y => representative (p,y)) =ᵐ[κ p.base] (p.decode : Y → ℂ) := by
  let v (m : ℕ) : Lp ℂ 2 (κ p.base) :=
    hilbertTests (κ p.base) (approxIndex p m) - p.decode
  have hvnorm (m) : ‖v m‖ ≤ (1/2 : ℝ)^m := by
    simpa only [v,←dist_eq_norm] using (approxIndex_spec p m).le
  have hsum : Summable (fun m => ‖v m‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hvnorm summable_geometric_two
  have hfinite : ∑' m, eLpNorm (v m : Y → ℂ) 2 (κ p.base) ≠ ⊤ := by
    have he (m) : eLpNorm (v m : Y → ℂ) 2 (κ p.base) = (‖v m‖₊ : ℝ≥0∞) := by
      rw [Lp.nnnorm_def,ENNReal.coe_toNNReal (Lp.eLpNorm_ne_top _)]
    simp only [he]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp hsum)
  have hae := summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (fun m => Lp.aestronglyMeasurable (v m)) hfinite
  have heq : ∀ᵐ y ∂κ p.base, ∀ m, v m y = approximant m (p,y) - p.decode y := by
    rw [ae_all_iff]
    intro m
    filter_upwards [Lp.coeFn_sub (hilbertTests (κ p.base) (approxIndex p m)) p.decode,
      hilbertTestVector_coe (κ p.base) (hilbertTestKeys (approxIndex p m))] with y hd hf
    change (hilbertTests (κ p.base) (approxIndex p m) - p.decode) y = _
    rw [hd]
    change hilbertTestVector (κ p.base) (hilbertTestKeys (approxIndex p m)) y - p.decode y = _
    rw [hf]
    rfl
  filter_upwards [hae,heq] with y hy he
  apply Tendsto.limUnder_eq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := hy.tendsto_atTop_zero
  simpa only [he] using ht

end HilbertCode
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  {κ : Kernel U Y} [IsMarkovKernel κ]

omit [MeasurableSpace.CountablyGenerated Y] in
lemma lp_dist_of_representatives {μ : Measure Y} (v w : Lp ℂ 2 μ)
    (f g : Y → ℂ) (hf : (v : Y → ℂ) =ᵐ[μ] f) (hg : (w : Y → ℂ) =ᵐ[μ] g) :
    dist v w = Real.sqrt (Complex.re (∫ y, inner ℂ (f y - g y) (f y - g y) ∂μ)) := by
  rw [dist_eq_norm]
  have he : (∫ y, inner ℂ ((v-w) y) ((v-w) y) ∂μ) =
      ∫ y, inner ℂ (f y-g y) (f y-g y) ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub v w,hf,hg] with y hd hv hw
    rw [hd]
    change inner ℂ (v y-w y) (v y-w y) = _
    rw [hv,hw]
  rw [←he,←L2.inner_def]
  exact norm_eq_sqrt_re_inner (𝕜 := ℂ) _

namespace HilbertCode

def distance (p q : HilbertCode κ) : ℝ := Real.sqrt (Complex.re (∫ y,
  inner ℂ (representative (p,y) - representative (q,y))
    (representative (p,y) - representative (q,y)) ∂κ p.base))

lemma distance_encode (u : U) (v w : Lp ℂ 2 (κ u)) :
    distance (encode u v) (encode u w) = dist v w := by
  have hv := representative_eq_decode (encode u v)
  have hw := representative_eq_decode (encode u w)
  simp only [decode_encode] at hv hw
  exact (lp_dist_of_representatives v w _ _ hv.symm hw.symm).symm

end HilbertCode

end

section
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def RayCanonical (t : ℕ → H) (v : H) : Prop :=
  ∃ n, (∀ m < n, inner ℂ (t m) v = 0) ∧
    0 < (inner ℂ (t n) v).re ∧ (inner ℂ (t n) v).im = 0

lemma exists_inner_ne_zero_of_dense (t : ℕ → H) (ht : DenseRange t) {v : H} (hv : v ≠ 0) :
    ∃ n, inner ℂ (t n) v ≠ 0 := by
  by_contra! h
  have he : ∀ w, inner ℂ w v = 0 := by
    intro w
    exact ht.induction_on w (isClosed_eq (continuous_id.inner continuous_const) continuous_const) h
  exact hv ((inner_self_eq_zero (𝕜 := ℂ)).mp (he v))

lemma rayCanonical_unique {t : ℕ → H} {v w : H}
    (hv : RayCanonical t v) (hw : RayCanonical t w)
    {a : ℂ} (ha : ‖a‖ = 1) (he : v = a • w) : v = w := by
  obtain ⟨n,hn,hpn,hin⟩ := hv
  obtain ⟨m,hm,hpm,him⟩ := hw
  have hne : inner ℂ (t n) v ≠ 0 := by
    intro h; rw [h] at hpn; simp at hpn
  have hme : inner ℂ (t m) w ≠ 0 := by
    intro h; rw [h] at hpm; simp at hpm
  have han : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  have hnm : n = m := by
    rcases lt_trichotomy n m with h | h | h
    · have hh := hm n h
      rw [he,inner_smul_right,hh,mul_zero] at hne
      exact (hne rfl).elim
    · exact h
    · have hh := hn m h
      rw [he,inner_smul_right] at hh
      exact (mul_ne_zero han hme hh).elim
  subst m
  have hev : inner ℂ (t n) v = ((inner ℂ (t n) v).re : ℂ) := by
    apply Complex.ext <;> simp [hin]
  have hew : inner ℂ (t n) w = ((inner ℂ (t n) w).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hnorm : ‖inner ℂ (t n) v‖ = ‖inner ℂ (t n) w‖ := by
    rw [he,inner_smul_right,norm_mul,ha,one_mul]
  have hcoeff : inner ℂ (t n) v = inner ℂ (t n) w := by
    rw [hev,hew] at hnorm ⊢
    have hh : (inner ℂ (t n) v).re = (inner ℂ (t n) w).re := by
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpn,abs_of_pos hpm] using hnorm
    rw [hh]
  have ha1 : a = 1 := by
    apply (mul_right_cancel₀ hme)
    simpa only [one_mul,←inner_smul_right,←he,one_smul] using hcoeff
  simpa [ha1] using he
end

namespace HilbertCode
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ]

def coefficient (p : HilbertCode κ) (n : ℕ) : ℂ :=
  ∫ y, inner ℂ (hilbertTestFunction (hilbertTestKeys n) y) (representative (p,y)) ∂κ p.base

lemma coefficient_eq (p : HilbertCode κ) (n : ℕ) :
    coefficient p n = inner ℂ (hilbertTests (κ p.base) n) p.decode := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hilbertTestVector_coe (κ p.base) (hilbertTestKeys n),representative_eq_decode p]
    with y ht hv
  rw [hv]
  change inner ℂ _ _ = inner ℂ (hilbertTestVector _ _ y) _
  rw [ht]

def IsCanonical (p : HilbertCode κ) : Prop := RayCanonical (hilbertTests (κ p.base)) p.decode

def IsUnimodular (p : HilbertCode κ) : Prop :=
  ∀ᵐ y ∂κ p.base, ‖representative (p,y)‖ = 1

lemma norm_decode_eq_one {p : HilbertCode κ} (hp : IsUnimodular p) : ‖p.decode‖ = 1 := by
  have hn : ∀ᵐ y ∂κ p.base, ‖p.decode y‖ = ‖(1 : ℂ)‖ := by
    filter_upwards [hp,representative_eq_decode p] with y hy he
    simpa only [norm_one,he] using hy
  rw [Lp.norm_def,eLpNorm_congr_norm_ae hn,eLpNorm_const (1 : ℂ) (by norm_num) (IsProbabilityMeasure.ne_zero (κ p.base))]
  simp

end HilbertCode

section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ComplexConjugate


theorem exact_mean_dichotomy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hk : 3 ≤ Fintype.card ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (heq : ∀ i, a i = ∏ j ∈ Finset.univ.erase i, a j) :
    (∀ i, a i = 0) ∨ (∀ i, a i = 1) := by
  classical
  by_cases hz : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := hz
    left
    intro j
    by_cases hij : i = j
    · simpa [← hij] using hi
    · rw [heq j]
      exact Finset.prod_eq_zero (by simp [hij]) hi
  · have hn (i) : a i ≠ 0 := fun hi => hz ⟨i, hi⟩
    have hp (i) : 0 < a i := lt_of_le_of_ne (ha i) (hn i).symm
    have hl (i) : 2 * Real.log (a i) = ∑ j, Real.log (a j) := by
      have hh := congrArg Real.log (heq i)
      rw [Real.log_prod (fun j _ => hn j)] at hh
      have hs := Finset.sum_erase_add (s := Finset.univ)
        (fun j => Real.log (a j)) (Finset.mem_univ i)
      linarith
    have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ)
      rfl (fun i _ => hl i)
    simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    have hc : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hk
    have hsum : ∑ j, Real.log (a j) = 0 := by nlinarith
    right
    intro i
    have hi : Real.log (a i) = 0 := by simpa [hsum] using hl i
    rw [← Real.exp_log (hp i), hi, Real.exp_zero]

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in

theorem exact_tuple_mean_equations
    (f : ι → Ω → ℂ) (hm : ∀ i, AEStronglyMeasurable (f i) μ)
    (hn : ∀ i, ∀ᵐ ω ∂μ, ‖f i ω‖ = 1)
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset ι) => f j) μ)
    (c : ℂ) (hc : ‖c‖ = 1) (hprod : ∀ᵐ ω ∂μ, ∏ i, f i ω = c) :
    ∀ i, ‖∫ ω, f i ω ∂μ‖ = ∏ j ∈ Finset.univ.erase i, ‖∫ ω, f j ω ∂μ‖ := by
  intro i
  have hi : (fun ω => ∏ j ∈ Finset.univ.erase i, f j ω) =ᵐ[μ]
      (fun ω => c * conj (f i ω)) := by
    filter_upwards [hprod, hn i] with ω hω hnω
    rw [← Complex.inv_eq_conj hnω, ← hω]
    rw [← Finset.prod_erase_mul Finset.univ (fun j => f j ω) (Finset.mem_univ i)]
    have hne : f i ω ≠ 0 := by intro hh; simp [hh] at hnω
    rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
  have hp : ∫ ω, ∏ j ∈ Finset.univ.erase i, f j ω ∂μ =
      ∏ j ∈ Finset.univ.erase i, ∫ ω, f j ω ∂μ := by
    have h := (hind i).integral_fun_prod_eq_prod_integral (fun j => hm j)
    have hh (g : ι → ℂ) : ∏ j : (Finset.univ.erase i : Finset ι), g j =
        ∏ j ∈ Finset.univ.erase i, g j := Finset.prod_coe_sort _ _
    refine (integral_congr_ae (Filter.Eventually.of_forall fun ω => (hh (fun j => f j ω)).symm)).trans ?_
    exact h.trans (hh (fun j => ∫ ω, f j ω ∂μ))
  have hh : ∏ j ∈ Finset.univ.erase i, ∫ ω, f j ω ∂μ =
      c * conj (∫ ω, f i ω ∂μ) := by
    rw [← hp, integral_congr_ae hi, integral_const_mul, integral_conj]
  have hw := congrArg norm hh
  simpa only [norm_prod, norm_mul, hc, Complex.norm_conj, one_mul] using hw.symm

theorem ae_eq_mean_of_norm_mean_eq_one (f : Ω → ℂ)
    (hn : ∀ᵐ ω ∂μ, ‖f ω‖ = 1) (hi : ‖∫ ω, f ω ∂μ‖ = 1) :
    f =ᵐ[μ] (fun _ => ∫ ω, f ω ∂μ) := by
  rcases ae_eq_const_or_norm_integral_lt_of_norm_le_const (hn.mono fun _ h => h.le)
      with h | h
  · simpa only [average_eq_integral, Function.const_def] using h
  · simp [hi] at h

theorem exact_tuple_dichotomy
    (hk : 3 ≤ Fintype.card ι)
    (f : ι → Ω → ℂ) (hm : ∀ i, AEStronglyMeasurable (f i) μ)
    (hn : ∀ i, ∀ᵐ ω ∂μ, ‖f i ω‖ = 1)
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset ι) => f j) μ)
    (c : ℂ) (hc : ‖c‖ = 1) (hprod : ∀ᵐ ω ∂μ, ∏ i, f i ω = c) :
    (∀ i, ∫ ω, f i ω ∂μ = 0) ∨
      (∀ i, f i =ᵐ[μ] (fun _ => ∫ ω, f i ω ∂μ) ∧ ‖∫ ω, f i ω ∂μ‖ = 1) := by
  rcases exact_mean_dichotomy hk (fun i => ‖∫ ω, f i ω ∂μ‖)
      (fun _ => norm_nonneg _) (exact_tuple_mean_equations f hm hn hind c hc hprod)
      with h | h
  · exact Or.inl fun i => norm_eq_zero.mp (h i)
  · exact Or.inr fun i => ⟨ae_eq_mean_of_norm_mean_eq_one (f i) (hn i) (h i), h i⟩

theorem exact_quotient_dichotomy
    {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (hk : 3 ≤ Fintype.card ι) (X : ∀ i, Ω → S i)
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset ι) => X j) μ)
    (f g : ∀ i, S i → ℂ) (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hnf : ∀ i, ∀ᵐ ω ∂μ, ‖f i (X i ω)‖ = 1)
    (hng : ∀ i, ∀ᵐ ω ∂μ, ‖g i (X i ω)‖ = 1)
    (c d : ℂ) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hpf : ∀ᵐ ω ∂μ, ∏ i, f i (X i ω) = c)
    (hpg : ∀ᵐ ω ∂μ, ∏ i, g i (X i ω) = d) :
    (∀ i, ∫ ω, f i (X i ω) * conj (g i (X i ω)) ∂μ = 0) ∨
    (∀ i, ∃ a : ℂ, ‖a‖ = 1 ∧
      (fun ω => f i (X i ω)) =ᵐ[μ] (fun ω => a * g i (X i ω))) := by
  let q (i : ι) (ω : Ω) := f i (X i ω) * conj (g i (X i ω))
  have hqm (i) : AEStronglyMeasurable (q i) μ :=
    ((hf i).comp_aemeasurable (hX i)).aestronglyMeasurable.mul
      (((hg i).comp_aemeasurable (hX i)).aestronglyMeasurable.star)
  have hqn (i) : ∀ᵐ ω ∂μ, ‖q i ω‖ = 1 := by
    filter_upwards [hnf i, hng i] with ω hfω hgω
    simp [q, hfω, hgω]
  have hqi (i) : iIndepFun (fun j : (Finset.univ.erase i : Finset ι) => q j) μ := by
    exact (hind i).comp (fun j y => f j y * conj (g j y))
      (fun j => (hf j).mul (Complex.continuous_conj.measurable.comp (hg j)))
  have hqp : ∀ᵐ ω ∂μ, ∏ i, q i ω = c * conj d := by
    filter_upwards [hpf, hpg] with ω hfω hgω
    simp only [q, Finset.prod_mul_distrib, ← map_prod, hfω, hgω]
  have hcd : ‖c * conj d‖ = 1 := by simp [hc, hd]
  rcases exact_tuple_dichotomy hk q hqm hqn hqi (c * conj d) hcd hqp with h | h
  · exact Or.inl h
  · right
    intro i
    refine ⟨∫ ω, q i ω ∂μ, (h i).2, ?_⟩
    filter_upwards [(h i).1, hng i] with ω hh hn
    rw [← hh]
    change f i (X i ω) = (f i (X i ω) * conj (g i (X i ω))) * g i (X i ω)
    rw [← Complex.inv_eq_conj hn, mul_assoc, inv_mul_cancel₀, mul_one]
    intro hz
    simp [hz] at hn

end

namespace HilbertCode

open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace ComplexConjugate

section DecodingInnerProducts
variable {U Y I : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ]
  [Fintype I] [DecidableEq I]

lemma inner_decode (p q : HilbertCode κ) (he : p.base = q.base) :
    ∫ y, representative (p,y) * conj (representative (q,y)) ∂κ p.base =
      inner ℂ (he ▸ q.decode) p.decode := by
  cases p with | mk p hp =>
    cases q with | mk q hq =>
      rcases p with ⟨u,a⟩
      rcases q with ⟨v,b⟩
      change u = v at he
      subst v
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [representative_eq_decode (⟨(u,a),hp⟩ : HilbertCode κ),
        representative_eq_decode (⟨(u,b),hq⟩ : HilbertCode κ)] with y hy hz
      rw [hy,hz]
      exact (RCLike.inner_apply _ _).symm

lemma eq_of_decode_smul {p q : HilbertCode κ} (he : p.base = q.base)
    (hp : IsCanonical p) (hq : IsCanonical q) {a : ℂ} (ha : ‖a‖ = 1)
    (hv : (fun y => representative (p,y)) =ᵐ[κ p.base]
      (fun y => a * representative (q,y))) : p = q := by
  rcases p with ⟨⟨u,f⟩,hf⟩
  rcases q with ⟨⟨v,g⟩,hg⟩
  change u = v at he
  subst v
  let p : HilbertCode κ := ⟨(u,f),hf⟩
  let q : HilbertCode κ := ⟨(u,g),hg⟩
  have hs : (p.decode : Lp ℂ 2 (κ u)) = a • (q.decode : Lp ℂ 2 (κ u)) := by
    apply Lp.ext
    change (fun y => (p.decode : Lp ℂ 2 (κ u)) y) =ᵐ[κ u]
      (fun y => (a • (q.decode : Lp ℂ 2 (κ u)) : Lp ℂ 2 (κ u)) y)
    filter_upwards [hv,representative_eq_decode p,representative_eq_decode q,
      Lp.coeFn_smul a (q.decode : Lp ℂ 2 (κ u))] with y hy hpy hqy hs
    exact hpy.symm.trans ((hy.trans (congrArg (a*·) hqy)).trans hs.symm)
  have hvv : (p.decode : Lp ℂ 2 (κ u)) = (q.decode : Lp ℂ 2 (κ u)) :=
    rayCanonical_unique hp hq ha hs
  exact (encode_decode p).symm.trans ((congrArg (encode u) hvv).trans (encode_decode q))

lemma distance_ge_one_of_orthogonal {p q : HilbertCode κ} (he : p.base = q.base)
    (hp : IsUnimodular p) (hq : IsUnimodular q)
    (hz : ∫ y, representative (p,y) * conj (representative (q,y)) ∂κ p.base = 0) :
    1 ≤ distance p q := by
  rcases p with ⟨⟨u,a⟩,ha⟩
  rcases q with ⟨⟨t,b⟩,hb⟩
  change u = t at he
  subst t
  let p : HilbertCode κ := ⟨(u,a),ha⟩
  let q : HilbertCode κ := ⟨(u,b),hb⟩
  let v : Lp ℂ 2 (κ u) := p.decode
  let w : Lp ℂ 2 (κ u) := q.decode
  have hid : inner ℂ w v = 0 := (inner_decode p q rfl).symm.trans hz
  have hn1 : ‖v‖ = 1 := norm_decode_eq_one hp
  have hn2 : ‖w‖ = 1 := norm_decode_eq_one hq
  have hn := norm_sub_sq (𝕜 := ℂ) w v
  rw [hid,hn1,hn2] at hn
  have hd : distance p q = dist v w :=
    (congrArg₂ distance (encode_decode p) (encode_decode q)).symm.trans
      (distance_encode u v w)
  change 1 ≤ distance p q
  rw [hd,dist_comm,dist_eq_norm]
  norm_num at hn
  have hh := norm_nonneg (w-v)
  nlinarith

omit [Fintype I] [DecidableEq I] in
lemma ae_norm_representative_comp (μ : Measure (I → Y)) (p q : HilbertCode κ)
    (he : p.base = q.base) (hq : IsUnimodular q) (i : I)
    (hm : MeasurePreserving (fun y : I → Y => y i) μ (κ p.base)) :
    ∀ᵐ y ∂μ, ‖representative (q,y i)‖ = 1 := by
  have h : ∀ᵐ y ∂κ p.base, ‖representative (q,y)‖ = 1 := by rw [he]; exact hq
  exact hm.quasiMeasurePreserving.ae h

omit [DecidableEq I] in
lemma ae_norm_prod_representative (μ : Measure (I → Y)) (p : I → HilbertCode κ)
    (hn : ∀ i, ∀ᵐ y ∂μ, ‖representative (p i,y i)‖ = 1) :
    ∀ᵐ y ∂μ, ‖∏ i, representative (p i,y i)‖ = 1 := by
  filter_upwards [ae_all_iff.mpr hn] with y hy
  simp only [norm_prod,hy,Finset.prod_const_one]

lemma code_tuple_quotient (hk : 3 ≤ Fintype.card I)
    (μ : Measure (I → Y)) [IsProbabilityMeasure μ]
    (p q : I → HilbertCode κ) (he : ∀ i, (p i).base = (q i).base)
    (hp : ∀ i, IsUnimodular (p i))
    (hq : ∀ i, IsUnimodular (q i))
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) μ (κ (p i).base))
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) μ)
    (hpe : ‖∫ y, ∏ i, representative (p i,y i) ∂μ‖ = 1)
    (hqe : ‖∫ y, ∏ i, representative (q i,y i) ∂μ‖ = 1) :
    (∀ i, ∫ y, representative (p i,y i) * conj (representative (q i,y i)) ∂μ = 0) ∨
    (∀ i, ∃ a : ℂ, ‖a‖ = 1 ∧ (fun y : I → Y => representative (p i,y i)) =ᵐ[μ]
       (fun y => a * representative (q i,y i))) := by
  have hpm (i) : Measurable (fun y => representative (p i,y)) :=
    measurable_representative.comp measurable_prodMk_left
  have hqm (i) : Measurable (fun y => representative (q i,y)) :=
    measurable_representative.comp measurable_prodMk_left
  have hpn (i) := (hm i).quasiMeasurePreserving.ae (hp i)
  have hqn (i) := ae_norm_representative_comp μ (p i) (q i) (he i) (hq i) i (hm i)
  have hpProd := ae_norm_prod_representative μ p hpn
  have hqProd := ae_norm_prod_representative μ q hqn
  exact exact_quotient_dichotomy (μ := μ) (S := fun _ : I => Y) hk (fun i y => y i) (fun i => (hm i).measurable.aemeasurable)
    hind (fun i y => representative (p i,y)) (fun i y => representative (q i,y))
    hpm hqm hpn hqn _ _ hpe hqe
    (ae_eq_mean_of_norm_mean_eq_one _ hpProd hpe)
    (ae_eq_mean_of_norm_mean_eq_one _ hqProd hqe)

lemma exact_codes_dichotomy (hk : 3 ≤ Fintype.card I)
    (μ : Measure (I → Y)) [IsProbabilityMeasure μ]
    (p q : I → HilbertCode κ) (he : ∀ i, (p i).base = (q i).base)
    (hp : ∀ i, IsCanonical (p i) ∧ IsUnimodular (p i))
    (hq : ∀ i, IsCanonical (q i) ∧ IsUnimodular (q i))
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) μ (κ (p i).base))
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) μ)
    (hpe : ‖∫ y, ∏ i, representative (p i,y i) ∂μ‖ = 1)
    (hqe : ‖∫ y, ∏ i, representative (q i,y i) ∂μ‖ = 1) :
    p = q ∨ ∀ i, 1 ≤ distance (p i) (q i) := by
  have hpm (i) : Measurable (fun y => representative (p i,y)) :=
    measurable_representative.comp measurable_prodMk_left
  have hqm (i) : Measurable (fun y => representative (q i,y)) :=
    measurable_representative.comp measurable_prodMk_left
  rcases code_tuple_quotient hk μ p q he (fun i => (hp i).2) (fun i => (hq i).2)
    hm hind hpe hqe with hz | hs
  · right
    intro i
    have hz' : ∫ y, representative (p i,y) * conj (representative (q i,y)) ∂κ (p i).base = 0 := by
      rw [←(hm i).map_eq]
      have hf : Measurable (fun y => representative (p i,y) * conj (representative (q i,y))) :=
        (hpm i).mul (Complex.continuous_conj.measurable.comp (hqm i))
      exact (integral_map (hm i).measurable.aemeasurable hf.aestronglyMeasurable).trans (hz i)
    exact distance_ge_one_of_orthogonal (he i) (hp i).2 (hq i).2 hz'
  · left
    funext i
    obtain ⟨a,ha,hv⟩ := hs i
    apply eq_of_decode_smul (he i) (hp i).1 (hq i).1 ha
    rw [←(hm i).map_eq]
    apply (ae_map_iff (hm i).measurable.aemeasurable
      (measurableSet_eq_fun (hpm i) (measurable_const.mul (hqm i)))).mpr
    exact hv
end DecodingInnerProducts


end HilbertCode

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
variable {P U Y I : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

def exactCodeMean (t : P × (I → HilbertCode κ)) : ℂ :=
  ∫ y, ∏ i, HilbertCode.representative (t.2 i,y i) ∂Λ t.1

def exactCodeSet : Set (P × (I → HilbertCode κ)) :=
  {t | (∀ i, (t.2 i).base = u t.1 i) ∧
    (∀ i, HilbertCode.IsCanonical (t.2 i) ∧ HilbertCode.IsUnimodular (t.2 i)) ∧
    ‖exactCodeMean κ Λ t‖ = 1}

abbrev ExactCodeTuple := exactCodeSet κ Λ u

end

section
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
local instance instMeasurableSpaceCircle_circleLp : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
local instance instBorelSpaceCircle_circleLp : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

lemma circle_memLp (f : X → Circle) (hf : Measurable f) :
    MemLp (fun x => (f x : ℂ)) 2 μ :=
  MemLp.of_bound (measurable_subtype_coe.comp hf).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => (Circle.norm_coe (f x)).le)

def circleLp (f : X → Circle) (hf : Measurable f) : Lp ℂ 2 μ :=
  (circle_memLp μ f hf).toLp (fun x => (f x : ℂ))

lemma circleLp_coe (f : X → Circle) (hf : Measurable f) :
    circleLp μ f hf =ᵐ[μ] (fun x => (f x : ℂ)) := MemLp.coeFn_toLp _

end

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp

def circleOfValue (z : ℂ) : Circle := by
  classical
  exact ⟨if ‖z‖ = 1 then z else 1, by
    split_ifs with h
    · exact mem_sphere_zero_iff_norm.mpr h
    · exact mem_sphere_zero_iff_norm.mpr (norm_one : ‖(1 : ℂ)‖ = 1)⟩
lemma measurable_circleOfValue : Measurable circleOfValue := by
  classical
  apply Measurable.subtype_mk
  exact measurable_id.ite (measurableSet_eq_fun measurable_norm measurable_const) measurable_const

variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

namespace HilbertCode
variable {κ}
def circleRep (q : HilbertCode κ) (y : Y) : Circle := circleOfValue (representative (κ := κ) (q,y))
lemma measurable_circleRep_fixed (q : HilbertCode κ) : Measurable (circleRep (κ := κ) q) := by
  have h : Measurable (fun y : Y => (q,y)) := measurable_const.prodMk measurable_id
  have hh : Measurable (fun y : Y => representative (κ := κ) (q,y)) :=
    (measurable_representative (κ := κ)).comp h
  exact measurable_circleOfValue.comp hh
end HilbertCode

end

namespace HilbertCode

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ]

abbrev UnitCode (κ : Kernel U Y) [IsMarkovKernel κ] := {q : HilbertCode κ // q.IsUnimodular}

lemma unitCode_exists_coefficient (q : UnitCode κ) : ∃ n, coefficient q.val n ≠ 0 := by
  have hne : q.val.decode ≠ 0 := norm_ne_zero_iff.mp (by rw [norm_decode_eq_one q.property]; norm_num)
  simpa only [coefficient_eq] using exists_inner_ne_zero_of_dense
    (hilbertTests (κ q.val.base)) (hilbertTests_dense _) hne

def firstCoefficient (q : UnitCode κ) : ℕ := Nat.find (unitCode_exists_coefficient q)

def unitPhase (q : UnitCode κ) : ℂ :=
  (‖coefficient q.val (firstCoefficient q)‖ : ℂ) / coefficient q.val (firstCoefficient q)

def normalizeUnit (q : UnitCode κ) : HilbertCode κ := encode q.val.base (unitPhase q • q.val.decode)

def transportRaw (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ) : HilbertCode κ :=
  encode (F q.base) (circleLp (κ (F q.base)) (circleRep (κ := κ) q ∘ E.symm)
    ((measurable_circleRep_fixed q).comp E.symm.measurable))

lemma transportRaw_representative (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ) :
    (fun y => representative (transportRaw F E q,y)) =ᵐ[κ (F q.base)]
      (fun y => (circleRep (κ := κ) q (E.symm y) : ℂ)) := by
  have h := representative_eq_decode (transportRaw F E q)
  change (fun y => representative (transportRaw F E q,y)) =ᵐ[κ (F q.base)]
    (decode (encode _ _) : Y → ℂ) at h
  rw [decode_encode] at h
  exact h.trans (circleLp_coe _ _ _)

lemma transportRaw_unimodular (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ) :
    (transportRaw F E q).IsUnimodular := by
  filter_upwards [transportRaw_representative F E q] with y hy
  rw [hy,Circle.norm_coe]

def transport (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ) : HilbertCode κ :=
  normalizeUnit ⟨transportRaw F E q,transportRaw_unimodular F E q⟩

end HilbertCode

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Arrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section

open MeasureTheory ProbabilityTheory
universe u
namespace ArrayObjects

section

structure StandardSpace where
  α : Type u
  measurableSpace : MeasurableSpace α
  standardBorel : @StandardBorelSpace α measurableSpace
  nonempty : Nonempty α

instance instCoeSortStandardSpaceType : CoeSort StandardSpace (Type u) := ⟨StandardSpace.α⟩
instance instMeasurableSpaceα (S : StandardSpace) : MeasurableSpace S := S.measurableSpace
instance instStandardBorelSpaceα (S : StandardSpace) : StandardBorelSpace S := S.standardBorel
instance instNonemptyα (S : StandardSpace) : Nonempty S := S.nonempty

abbrev Index (I : Type u) (n : ℕ) := Fin n → I
abbrev Arr (I Y : Type u) (n : ℕ) := Index I n → Y

def amap {I Y Z : Type u} (f : Y → Z) (n : ℕ) : Arr I Y n → Arr I Z n :=
  fun y v => f (y v)

def plane {I Y : Type u} (n : ℕ) (a : Fin (n + 1)) (i : I) :
    Arr I Y (n + 1) → Arr I Y n := fun y v => y (a.insertNth i v)

def planes {I Y : Type u} (n : ℕ) (J : Finset I) :
    Arr I Y (n + 1) → (j : J) → Arr I Y n :=
  fun y j => plane n (Fin.last n) j y

def zeroEquiv (I Y : Type u) [MeasurableSpace Y] : Arr I Y 0 ≃ᵐ Y where
  toFun y := y Fin.elim0
  invFun y := fun _ => y
  left_inv y := by funext v; exact congrArg y (Subsingleton.elim _ _)
  right_inv _ := rfl
  measurable_toFun := measurable_pi_apply _
  measurable_invFun := Measurable.of_eval (fun _ => measurable_id)

@[fun_prop] lemma measurable_amap {I Y Z : Type u}
    [MeasurableSpace Y] [MeasurableSpace Z] {f : Y → Z} (hf : Measurable f) (n : ℕ) :
    Measurable (amap (I := I) f n) :=
  Measurable.of_eval (fun _ => hf.comp (measurable_pi_apply _))

@[fun_prop] lemma measurable_plane {I Y : Type u} [MeasurableSpace Y]
    (n : ℕ) (a : Fin (n + 1)) (i : I) : Measurable (plane (Y := Y) n a i) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

@[fun_prop] lemma measurable_planes {I Y : Type u} [MeasurableSpace Y]
    (n : ℕ) (J : Finset I) : Measurable (planes (Y := Y) n J) :=
  Measurable.of_eval (fun _ => measurable_plane _ _ _)

@[simp] lemma amap_id {I Y : Type u} (n : ℕ) : amap (I := I) (id : Y → Y) n = id := rfl
@[simp] lemma amap_comp {I X Y Z : Type u} (g : Y → Z) (f : X → Y) (n : ℕ) :
    amap (I := I) (g ∘ f) n = amap g n ∘ amap f n := rfl
@[simp] lemma plane_amap {I Y Z : Type u} (f : Y → Z) (n : ℕ)
    (a : Fin (n + 1)) (i : I) :
    plane n a i ∘ amap f (n + 1) = amap f n ∘ plane n a i := rfl

variable (I : Type u) [Fintype I]

structure InitialLaws (X : StandardSpace.{u}) (T : X ≃ᵐ X) where
  law : (n : ℕ) → Measure (Arr I X n)
  probability : ∀ n, IsProbabilityMeasure (law n)
  invariant : ∀ n, MeasurePreserving (amap T n) (law n) (law n)
  consistent : ∀ n (a : Fin (n + 1)) i,
    (law (n + 1)).map (plane n a i) = law n
  proper : ∀ n (J : Finset I), J ≠ Finset.univ →
    (law (n + 1)).map (planes n J) = Measure.pi (fun _ : J => law n)

attribute [instance] InitialLaws.probability

structure Object {X : StandardSpace.{u}} {T : X ≃ᵐ X} (base : InitialLaws I X T) where
  Y : StandardSpace.{u}
  U : StandardSpace.{u}
  timeY : Y ≃ᵐ Y
  timeU : U ≃ᵐ U
  x : Y → X
  par : Y → U
  measurable_x : Measurable x
  measurable_par : Measurable par
  time_x : x ∘ timeY = T ∘ x
  time_par : par ∘ timeY = timeU ∘ par
  law : (n : ℕ) → Measure (Arr I Y n)
  probability : ∀ n, IsProbabilityMeasure (law n)
  invariant : ∀ n, MeasurePreserving (amap timeY n) (law n) (law n)
  over_base : ∀ n, (law n).map (amap x n) = base.law n
  consistent : ∀ n (a : Fin (n + 1)) i,
    (law (n + 1)).map (plane n a i) = law n
  proper : ∀ n (J : Finset I), J ≠ Finset.univ →
    (law (n + 1)).map (planes n J) = Measure.pi (fun _ : J => law n)
  conditional : ∀ n (J : Finset I), J ≠ Finset.univ →
    condDistrib (planes n J) (amap par (n + 1)) (law (n + 1))
      =ᵐ[(law (n + 1)).map (amap par (n + 1))]
    fun p => Measure.pi (fun j : J =>
      condDistrib (id : Arr I Y n → Arr I Y n) (amap par n) (law n)
        (plane n (Fin.last n) j p))
  local_independent : IndepFun x par ((law 0).map (zeroEquiv I Y))

attribute [instance] Object.probability

namespace Object
variable {I} {X : StandardSpace.{u}} {T : X ≃ᵐ X} {base : InitialLaws I X T}

noncomputable def localLaw (M : Object I base) : Measure M.Y :=
  (M.law 0).map (zeroEquiv I M.Y)
instance instIsProbabilityMeasureαYLocalLaw (M : Object I base) : IsProbabilityMeasure M.localLaw := by
  dsimp [localLaw]
  exact (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (zeroEquiv I M.Y).measurable.aemeasurable

noncomputable def parameter (M : Object I base) : Measure M.U := M.localLaw.map M.par
instance instIsProbabilityMeasureαUParameter (M : Object I base) : IsProbabilityMeasure M.parameter :=
  (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) M.measurable_par.aemeasurable

structure Extension (M N : Object I base) where
  state : N.Y → M.Y
  parameter : N.U → M.U
  measurable_state : Measurable state
  measurable_parameter : Measurable parameter
  time_state : state ∘ N.timeY = M.timeY ∘ state
  time_parameter : parameter ∘ N.timeU = M.timeU ∘ parameter
  state_x : M.x ∘ state = N.x
  state_par : M.par ∘ state = parameter ∘ N.par
  laws : ∀ n, (N.law n).map (amap state n) = M.law n

namespace Extension

def refl (M : Object I base) : Extension M M where
  state := id
  parameter := id
  measurable_state := measurable_id
  measurable_parameter := measurable_id
  time_state := rfl
  time_parameter := rfl
  state_x := rfl
  state_par := rfl
  laws n := by simp

def comp {M N P : Object I base} (e : Extension M N) (f : Extension N P) :
    Extension M P where
  state := e.state ∘ f.state
  parameter := e.parameter ∘ f.parameter
  measurable_state := e.measurable_state.comp f.measurable_state
  measurable_parameter := e.measurable_parameter.comp f.measurable_parameter
  time_state := by rw [Function.comp_assoc, f.time_state, ← Function.comp_assoc,
    e.time_state, Function.comp_assoc]
  time_parameter := by rw [Function.comp_assoc, f.time_parameter, ← Function.comp_assoc,
    e.time_parameter, Function.comp_assoc]
  state_x := by rw [← Function.comp_assoc, e.state_x, f.state_x]
  state_par := by rw [← Function.comp_assoc, e.state_par, Function.comp_assoc,
    f.state_par, ← Function.comp_assoc]
  laws n := by
    rw [amap_comp, ← Measure.map_map (measurable_amap e.measurable_state n)
      (measurable_amap f.measurable_state n), f.laws, e.laws]

lemma measurePreserving {M N : Object I base} (e : Extension M N) (n : ℕ) :
    MeasurePreserving (amap e.state n) (N.law n) (M.law n) :=
  ⟨measurable_amap e.measurable_state n, e.laws n⟩

lemma localLaw_map {M N : Object I base} (e : Extension M N) :
    N.localLaw.map e.state = M.localLaw := by
  rw [localLaw, localLaw, Measure.map_map e.measurable_state (zeroEquiv I N.Y).measurable,
    ← e.laws 0, Measure.map_map (zeroEquiv I M.Y).measurable
      (measurable_amap e.measurable_state 0)]
  rfl

lemma parameter_map {M N : Object I base} (e : Extension M N) :
    N.parameter.map e.parameter = M.parameter := by
  rw [Object.parameter, Object.parameter, Measure.map_map e.measurable_parameter N.measurable_par,
    ← e.state_par, ← Measure.map_map M.measurable_par e.measurable_state, e.localLaw_map]

end Extension
end Object
end


lemma condDistrib_condition_const {Ω E P : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    [MeasurableSpace P] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → E) (hf : Measurable f) (c : P) :
    condDistrib f (fun _ : Ω => c) μ c = μ.map f := by
  have h := condDistrib_comp_map (μ := μ) (X := fun _ : Ω => c) measurable_const.aemeasurable
    hf.aemeasurable
  simpa only [Measure.map_const, measure_univ, one_smul,
    Measure.dirac_bind (condDistrib f (fun _ : Ω => c) μ).measurable] using h

noncomputable def trivialSpace : StandardSpace.{u} where
  α := PUnit.{u + 1}
  measurableSpace := inferInstance
  standardBorel := inferInstance
  nonempty := inferInstance

variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}

noncomputable def initialObject (base : InitialLaws I X T) : Object I base where
  Y := X
  U := trivialSpace
  timeY := T
  timeU := MeasurableEquiv.refl _
  x := id
  par := fun _ => PUnit.unit
  measurable_x := measurable_id
  measurable_par := measurable_const
  time_x := rfl
  time_par := rfl
  law := base.law
  probability := base.probability
  invariant := base.invariant
  over_base n := by simp
  consistent := base.consistent
  proper := base.proper
  conditional n J hJ := by
    have hleft := condDistrib_condition_const (base.law (n + 1))
      (planes n J) (measurable_planes n J) (fun _ : Index I (n + 1) => PUnit.unit)
    have hright := condDistrib_condition_const (base.law n)
      (id : Arr I X n → Arr I X n) measurable_id (fun _ : Index I n => PUnit.unit)
    apply Filter.Eventually.of_forall
    intro p
    have hp : p = fun _ => PUnit.unit := by
      funext v
      cases p v
      rfl
    subst p
    change condDistrib (planes n J)
      (fun _ => (fun _ : Index I (n + 1) => PUnit.unit)) (base.law (n + 1))
      (fun _ => PUnit.unit) = _
    rw [hleft, base.proper n J hJ]
    congr 1
    funext j
    change base.law n = condDistrib id
      (fun _ => (fun _ : Index I n => PUnit.unit)) (base.law n) (fun _ => PUnit.unit)
    simpa using hright.symm
  local_independent := by
    let : IsProbabilityMeasure ((base.law 0).map (zeroEquiv I X)) := inferInstance
    exact indepFun_const_right id PUnit.unit


end ArrayObjects

open scoped InnerProductSpace

namespace ArrayObjects

inductive DataKind (I : Type u)
  | parameter
  | outside (j : I)
  | enlarged (j : I)
  deriving Fintype

namespace Object
open scoped ENNReal
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T}

noncomputable abbrev data (M : Object I base) (n : ℕ) (d : DataKind I) :
    MeasurableSpace (Arr I M.Y (n + 1)) := by
  classical
  exact match d with
  | .parameter => MeasurableSpace.comap (amap M.par (n + 1)) inferInstance
  | .outside j => MeasurableSpace.comap (planes n (Finset.univ.erase j)) inferInstance
  | .enlarged j => MeasurableSpace.comap (amap M.par (n + 1)) inferInstance ⊔
      MeasurableSpace.comap (planes n (Finset.univ.erase j)) inferInstance

lemma data_le (M : Object I base) (n : ℕ) (d : DataKind I) : M.data n d ≤ (inferInstance : MeasurableSpace (Arr I M.Y (n + 1))) := by
  classical
  cases d with
  | parameter => exact (measurable_amap M.measurable_par _).comap_le
  | outside j => exact (measurable_planes _ _).comap_le
  | enlarged j =>
    exact sup_le ((measurable_amap M.measurable_par _).comap_le)
      ((measurable_planes _ _).comap_le)

namespace Extension
variable {M N P : Object I base}

noncomputable def pull (e : Extension M N) (n : ℕ) :
    Lp ℂ 2 (M.law n) →ₗᵢ[ℂ] Lp ℂ 2 (N.law n) :=
  Lp.compMeasurePreservingₗᵢ ℂ (amap e.state n) (e.measurePreserving n)

end Extension
end Object
end ArrayObjects

namespace ArrayObjects.Object
open scoped ENNReal
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T}

noncomputable def project (M : Object I base) (n : ℕ) (d : DataKind I) :
    Lp ℂ 2 (M.law (n + 1)) →L[ℂ] Lp ℂ 2 (M.law (n + 1)) :=
  haveI : Fact (M.data n d ≤ (inferInstance : MeasurableSpace (Arr I M.Y (n + 1)))) :=
    ⟨M.data_le n d⟩
  (lpMeas ℂ ℂ (M.data n d) 2 (M.law (n + 1))).starProjection

lemma project_norm_le (M : Object I base) (n : ℕ) (d : DataKind I)
    (F : Lp ℂ 2 (M.law (n + 1))) : ‖M.project n d F‖ ≤ ‖F‖ :=
  norm_condExpL2_coe_le (M.data_le n d) F

def IsSaturated (M : Object I base) : Prop :=
  ∀ (N : Object I base) (e : Extension M N) n d (F : Lp ℂ 2 (M.law (n + 1))),
    N.project n d (e.pull (n + 1) F) = e.pull (n + 1) (M.project n d F)

end ArrayObjects.Object

namespace KernelTests
variable {Ω U B : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]

omit [Nonempty B] in
lemma ae_eq_of_evaluations (ν : Measure U) [IsFiniteMeasure ν]
    (κ η : Kernel U B) [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : ∀ S : Set B, MeasurableSet S →
      (fun u => κ u S) =ᵐ[ν] (fun u => η u S)) : κ =ᵐ[ν] η := by
  apply Kernel.ae_eq_of_compProd_eq
  apply Measure.ext_prod
  intro A S hA hS
  rw [Measure.compProd_apply_prod hA hS, Measure.compProd_apply_prod hA hS]
  exact lintegral_congr_ae ((h S hS).filter_mono ae_restrict_le)

lemma hasCondDistrib_of_indicators (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Ω → U) (O : Ω → B) (hE : Measurable E) (hO : Measurable O)
    (κ : Kernel U B) [IsMarkovKernel κ]
    (h : ∀ S : Set B, MeasurableSet S →
      μ⟦O ⁻¹' S | MeasurableSpace.comap E inferInstance⟧ =ᵐ[μ]
        fun ω => (κ (E ω)).real S) : HasCondDistrib O E κ μ := by
  have he : condDistrib O E μ =ᵐ[μ.map E] κ := by
    apply ae_eq_of_evaluations
    intro S hS
    apply (ae_map_iff hE.aemeasurable
      (measurableSet_eq_fun ((condDistrib O E μ).measurable_coe hS) (κ.measurable_coe hS))).mpr
    filter_upwards [condDistrib_ae_eq_condExp hE hO hS, h S hS] with ω h1 h2
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
      (h1.trans h2)
  exact ⟨(hE.prodMk hO).aemeasurable,
    (compProd_map_condDistrib hO.aemeasurable).symm.trans (Measure.compProd_congr he)⟩

end KernelTests

namespace ArrayObjects.Object

section
open scoped ENNReal
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} {M N : Object I base}

lemma project_ae_eq_condExp (M : Object I base) (n : ℕ) (d : DataKind I)
    (F : Lp ℂ 2 (M.law (n + 1))) :
    (M.project n d F : Arr I M.Y (n + 1) → ℂ) =ᵐ[M.law (n + 1)]
      (M.law (n + 1))[F | M.data n d] := by
  have h := (Lp.memLp F).condExpL2_ae_eq_condExp (𝕜 := ℂ) (M.data_le n d)
  rw [Lp.toLp_coeFn] at h
  exact h

lemma IsSaturated.condExp (hM : M.IsSaturated) (e : Extension M N)
    (n : ℕ) (d : DataKind I) (f : Arr I M.Y (n + 1) → ℂ)
    (hf : MemLp f 2 (M.law (n + 1))) :
    (N.law (n + 1))[f ∘ amap e.state (n + 1) | N.data n d] =ᵐ[N.law (n + 1)]
      ((M.law (n + 1))[f | M.data n d] ∘ amap e.state (n + 1)) := by
  let F := hf.toLp f
  have hp := Lp.coeFn_compMeasurePreserving F (e.measurePreserving (n + 1))
  have hp' := (e.measurePreserving (n + 1)).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp
  have hout := (e.measurePreserving (n + 1)).quasiMeasurePreserving.ae_eq_comp
    ((M.project_ae_eq_condExp n d F).trans (condExp_congr_ae hf.coeFn_toLp))
  have hi := N.project_ae_eq_condExp n d (e.pull (n + 1) F)
  have hh := hM N e n d F
  have hl := Lp.coeFn_compMeasurePreserving (M.project n d F) (e.measurePreserving (n + 1))
  rw [hh] at hi
  exact (condExp_congr_ae (hp.trans hp')).symm.trans (hi.symm.trans (hl.trans hout))

lemma IsSaturated.indicator (hM : M.IsSaturated) (e : Extension M N)
    (n : ℕ) (d : DataKind I) (S : Set (Arr I M.Y (n + 1))) (hS : MeasurableSet S) :
    (N.law (n + 1))⟦amap e.state (n + 1) ⁻¹' S | N.data n d⟧ =ᵐ[N.law (n + 1)]
      ((M.law (n + 1))⟦S | M.data n d⟧ ∘ amap e.state (n + 1)) := by
  let f : Arr I M.Y (n + 1) → ℝ := S.indicator (fun _ => 1)
  have hf : Integrable f (M.law (n + 1)) := (integrable_const 1).indicator hS
  have hfeq : (fun y => (f y : ℂ)) = S.indicator (fun _ => (1 : ℂ)) := by
    funext y; by_cases hy : y ∈ S <;> simp [f, hy]
  have hg : MemLp (fun y => (f y : ℂ)) 2 (M.law (n + 1)) := by
    rw [hfeq]
    exact
      memLp_indicator_const (μ := M.law (n + 1)) 2 hS (1 : ℂ) (Or.inr (measure_ne_top _ _))
  have h := hM.condExp e n d (fun y => (f y : ℂ)) hg
  have hnew := Complex.ofRealCLM.comp_condExp_comm (m := N.data n d)
    ((e.measurePreserving (n + 1)).integrable_comp_of_integrable hf)
  have hold := (e.measurePreserving (n + 1)).quasiMeasurePreserving.ae_eq_comp
    (Complex.ofRealCLM.comp_condExp_comm (m := M.data n d) hf)
  have he := hnew.trans (h.trans hold.symm)
  have hpre : f ∘ amap e.state (n + 1) =
      (amap e.state (n + 1) ⁻¹' S).indicator (fun _ => (1 : ℝ)) := by
    funext y
    exact (Set.indicator_comp_right (s := S) (g := fun _ => (1 : ℝ))
      (amap e.state (n + 1))).symm
  filter_upwards [he] with y hy
  have hr := Complex.ofReal_injective hy
  change (N.law (n + 1))[f ∘ amap e.state (n + 1) | N.data n d] y = _ at hr
  rw [hpre] at hr
  exact hr

end

variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} {M N : Object I base}

lemma IsSaturated.hasCondDistrib (hM : M.IsSaturated) (e : Extension M N)
    (n : ℕ) (d : DataKind I) {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [StandardBorelSpace B] [Nonempty B]
    (E : Arr I M.Y (n + 1) → A) (E' : Arr I N.Y (n + 1) → C)
    (F : Arr I M.Y (n + 1) → B) (p : C → A)
    (hE : Measurable E) (hE' : Measurable E') (hF : Measurable F) (hp : Measurable p)
    (hdata : M.data n d = MeasurableSpace.comap E inferInstance)
    (hdata' : N.data n d = MeasurableSpace.comap E' inferInstance)
    (hobs : E ∘ amap e.state (n + 1) = p ∘ E') :
    HasCondDistrib (F ∘ amap e.state (n + 1)) E'
      ((condDistrib F E (M.law (n + 1))).comap p hp) (N.law (n + 1)) := by
  apply KernelTests.hasCondDistrib_of_indicators _ E' _ hE'
    (hF.comp (measurable_amap e.measurable_state _))
  intro S hS
  have hi := hM.indicator e n d (F ⁻¹' S) (hF hS)
  rw [hdata, hdata'] at hi
  have ho := (e.measurePreserving (n + 1)).quasiMeasurePreserving.ae_eq_comp
    (condDistrib_ae_eq_condExp (μ := M.law (n + 1)) hE hF hS)
  filter_upwards [hi, ho] with y h1 h2
  exact h1.trans (h2.symm.trans (by
    change ((condDistrib F E (M.law (n + 1))) (E (amap e.state (n + 1) y))).real S =
      ((condDistrib F E (M.law (n + 1))) (p (E' y))).real S
    exact congrArg (fun a => ((condDistrib F E (M.law (n + 1))) a).real S)
      (congrFun hobs y)))


end ArrayObjects.Object

namespace ArrayObjects
variable {I : Type u}

def roll {Y : Type u} [MeasurableSpace Y] (n : ℕ) :
    Arr I Y (n + 1) ≃ᵐ Arr I (I → Y) n where
  toFun y w c := y (Fin.cons c w)
  invFun y v := y (Fin.tail v) (v 0)
  left_inv y := by funext v; simp
  right_inv y := by funext w c; simp
  measurable_toFun := by exact Measurable.of_eval (fun _ =>
    Measurable.of_eval (fun _ => measurable_pi_apply _))
  measurable_invFun := by
    change Measurable (fun y : Arr I (I → Y) n => fun v : Fin (n + 1) → I => y (Fin.tail v) (v 0))
    exact Measurable.of_eval (fun _ =>
      (measurable_pi_apply _).comp (measurable_pi_apply _))

lemma select_roll {Y : Type u} [MeasurableSpace Y] (n : ℕ) (a : I) :
    amap (Function.eval a) n ∘ roll (I := I) (Y := Y) n = plane n 0 a := by
  funext y w
  simp [amap, roll, plane, Fin.insertNth_zero']

lemma plane_roll {Y : Type u} [MeasurableSpace Y] (n : ℕ)
    (a : Fin (n + 1)) (i : I) :
    plane n a i ∘ roll (I := I) (Y := Y) (n + 1) =
      roll n ∘ plane (n + 1) a.succ i := by
  funext y w c
  exact congrArg y (Fin.insertNth_succ_cons a i c w).symm

lemma planes_roll {Y : Type u} [MeasurableSpace Y] (n : ℕ) (J : Finset I) :
    planes n J ∘ roll (I := I) (Y := Y) (n + 1) =
      (fun z j => roll n (z j)) ∘ planes (n + 1) J := by
  funext y j
  exact congrFun (plane_roll n (Fin.last n) (j : I)) y

namespace Object
variable [Fintype I]
variable {X : StandardSpace.{u}} {T : X ≃ᵐ X} {base : InitialLaws I X T}
variable (M : Object I base)
namespace Rolled

noncomputable abbrev State : StandardSpace.{u} where
  α := I → M.Y
  measurableSpace := inferInstance
  standardBorel := inferInstance
  nonempty := inferInstance

noncomputable abbrev Parameter (R : Finset I) : StandardSpace.{u} where
  α := (I → M.U) × (R → M.Y)
  measurableSpace := inferInstance
  standardBorel := inferInstance
  nonempty := inferInstance

def timeState : State M ≃ᵐ State M :=
  MeasurableEquiv.piCongrRight (fun _ : I => M.timeY)

def timeParameter (R : Finset I) : Parameter M R ≃ᵐ Parameter M R :=
  (MeasurableEquiv.piCongrRight (fun _ : I => M.timeU)).prodCongr
    (MeasurableEquiv.piCongrRight (fun _ : R => M.timeY))

def parameter (R : Finset I) (y : State M) : Parameter M R :=
  (fun c => M.par (y c), fun c => y c)

@[fun_prop] lemma measurable_parameter (R : Finset I) : Measurable (parameter M R) := by
  exact (Measurable.of_eval (fun c => M.measurable_par.comp (measurable_pi_apply c))).prodMk
    (Measurable.of_eval (fun c => measurable_pi_apply (c : I)))

lemma time_parameter (R : Finset I) :
    parameter M R ∘ timeState M = timeParameter M R ∘ parameter M R := by
  funext y
  apply Prod.ext
  · funext c; exact congrFun M.time_par (y c)
  · rfl

noncomputable def law (n : ℕ) : Measure (Arr I (State M) n) :=
  (M.law (n + 1)).map (roll n)
instance law_probability (n : ℕ) : IsProbabilityMeasure (law M n) :=
  (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (roll n).measurable.aemeasurable

lemma invariant (n : ℕ) : MeasurePreserving (amap (timeState M) n) (law M n) (law M n) := by
  refine ⟨measurable_amap (timeState M).measurable n, ?_⟩
  dsimp only [law]
  rw [Measure.map_map (measurable_amap (timeState M).measurable n) (roll n).measurable]
  change (M.law (n + 1)).map (roll n ∘ amap M.timeY (n + 1)) = _
  rw [← Measure.map_map (roll n).measurable (measurable_amap M.timeY.measurable _),
    (M.invariant (n + 1)).map_eq]

lemma select_law (n : ℕ) (a : I) :
    (law M n).map (amap (Function.eval a) n) = M.law n := by
  dsimp only [law]
  rw [Measure.map_map (measurable_amap (measurable_pi_apply a) n) (roll n).measurable,
    select_roll, M.consistent]

lemma over_base (n : ℕ) (a : I) :
    (law M n).map (amap (M.x ∘ Function.eval a) n) = base.law n := by
  rw [amap_comp, ← Measure.map_map (measurable_amap M.measurable_x n)
    (measurable_amap (measurable_pi_apply a) n), select_law, M.over_base]

lemma consistent (n : ℕ) (a : Fin (n + 1)) (i : I) :
    (law M (n + 1)).map (plane n a i) = law M n := by
  dsimp only [law]
  rw [Measure.map_map (measurable_plane _ _ _) (roll _).measurable, plane_roll,
    ← Measure.map_map (roll _).measurable (measurable_plane _ _ _), M.consistent]

lemma proper (n : ℕ) (J : Finset I) (hJ : J ≠ Finset.univ) :
    (law M (n + 1)).map (planes n J) = Measure.pi (fun _ : J => law M n) := by
  have hm : Measurable (fun z : (j : J) → Arr I M.Y (n + 1) => fun j => roll n (z j)) :=
    Measurable.of_eval (fun j => (roll n).measurable.comp (measurable_pi_apply j))
  dsimp only [law]
  rw [Measure.map_map (measurable_planes _ _) (roll _).measurable, planes_roll,
    ← Measure.map_map hm (measurable_planes _ _), M.proper _ _ hJ]
  exact Measure.pi_map_pi (fun _ : J => (roll n).measurable.aemeasurable)

end Rolled
end Object
end ArrayObjects

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FiniteKernel

variable {ι X : Type*} {Y : ι → Type*}
  [Fintype ι] [MeasurableSpace X] [∀ i, MeasurableSpace (Y i)]

noncomputable def pi (κ : ∀ i, Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)] :
    Kernel X (∀ i, Y i) where
  toFun x := Measure.pi (fun i => κ i x)
  measurable' := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      generateFrom_pi.symm isPiSystem_pi
    rintro _ ⟨s, hs, rfl⟩
    simp only [Measure.pi_pi]
    exact Finset.measurable_prod _ (fun i _ => (κ i).measurable_coe (hs i (Set.mem_univ i)))

@[simp] theorem pi_apply (κ : ∀ i, Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)] (x : X) :
    pi κ x = Measure.pi (fun i => κ i x) := rfl

instance instIsMarkovKernelForallPi (κ : ∀ i, Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)] : IsMarkovKernel (pi κ) :=
  ⟨fun _ => inferInstanceAs (IsProbabilityMeasure (Measure.pi _))⟩

@[simp] theorem pi_box (κ : ∀ i, Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)]
    (x : X) (s : ∀ i, Set (Y i)) :
    pi κ x (Set.pi Set.univ s) = ∏ i, κ i x (s i) := Measure.pi_pi _ _

def zipEquiv (Y Z : ι → Type*) [∀ i, MeasurableSpace (Y i)]
    [∀ i, MeasurableSpace (Z i)] :
    ((∀ i, Y i) × (∀ i, Z i)) ≃ᵐ (∀ i, Y i × Z i) where
  toFun p i := (p.1 i, p.2 i)
  invFun p := (fun i => (p i).1, fun i => (p i).2)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable (fun p : (∀ i, Y i) × (∀ i, Z i) => fun i => (p.1 i, p.2 i))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : ∀ i, Y i × Z i => (fun i => (p i).1, fun i => (p i).2))
    fun_prop

theorem compProd_pi {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)]
    (μ : ∀ i, Measure (Y i)) [∀ i, IsProbabilityMeasure (μ i)]
    (κ : ∀ i, Kernel (Y i) (Z i)) [∀ i, IsMarkovKernel (κ i)] :
    (Measure.pi μ ⊗ₘ pi (fun i => (κ i).comap (Function.eval i) (measurable_pi_apply i))).map
        (zipEquiv Y Z) = Measure.pi (fun i => μ i ⊗ₘ κ i) := by
  apply (Measure.pi_eq _).symm
  intro s hs
  rw [Measure.map_apply (zipEquiv Y Z).measurable (.univ_pi hs),
    Measure.compProd_apply ((zipEquiv Y Z).measurable (.univ_pi hs))]
  have hbox (y : ∀ i, Y i) :
      Prod.mk y ⁻¹' ((zipEquiv Y Z) ⁻¹' Set.pi Set.univ s) =
        Set.pi Set.univ (fun i => Prod.mk (y i) ⁻¹' s i) := rfl
  simp_rw [hbox, pi_box, Kernel.comap_apply]
  have hm (i : ι) : Measurable (fun y => κ i y (Prod.mk y ⁻¹' s i)) :=
    (κ i).measurable_kernel_prodMk_left (hs i)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _
    (iIndepFun_pi fun i => (hm i).aemeasurable) (fun i => (hm i).comp (measurable_pi_apply i))]
  congr 1
  funext i
  rw [(measurePreserving_eval μ i).lintegral_comp (hm i)]
  rw [← Measure.compProd_apply (hs i)]

theorem pi_compProd {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)]
    (κ : ∀ i, Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)]
    (η : ∀ i, Kernel (X × Y i) (Z i)) [∀ i, IsMarkovKernel (η i)] :
    (pi κ ⊗ₖ pi (fun i => (η i).comap (fun p : X × (∀ i, Y i) => (p.1, p.2 i))
      (by fun_prop))).map (zipEquiv Y Z) = pi (fun i => κ i ⊗ₖ η i) := by
  ext x : 1
  rw [Kernel.map_apply _ (zipEquiv Y Z).measurable,
    Kernel.compProd_apply_eq_compProd_sectR]
  have heq : Kernel.sectR
      (pi (fun i => (η i).comap (fun p : X × (∀ i, Y i) => (p.1, p.2 i))
        (by fun_prop))) x =
      pi (fun i => (Kernel.sectR (η i) x).comap (Function.eval i) (measurable_pi_apply i)) := by
    ext y : 1
    rfl
  rw [heq]
  simp only [pi_apply]
  rw [compProd_pi]
  simp only [Kernel.compProd_apply_eq_compProd_sectR]

end FiniteKernel

open MeasureTheory ProbabilityTheory

namespace ConditionalScreens

variable {Ω X Y Z : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {P : Measure Ω} [SFinite P]
  {x : Ω → X} {y : Ω → Y} {z : Ω → Z}
  {κ : Kernel X Y} [IsMarkovKernel κ]
  {η : Kernel (X × Y) Z} [IsMarkovKernel η]

omit [SFinite P] [IsMarkovKernel κ] [IsMarkovKernel η] in

theorem chain (hy : HasCondDistrib y x κ P)
    (hz : HasCondDistrib z (fun ω => (x ω, y ω)) η P) :
    HasCondDistrib (fun ω => (y ω, z ω)) x (κ ⊗ₖ η) P := by
  refine ⟨hy.aemeasurable_fst.prodMk
    (hy.aemeasurable_snd.prodMk hz.aemeasurable_snd), ?_⟩
  calc
    P.map (fun ω => (x ω, y ω, z ω)) =
        (P.map (fun ω => ((x ω, y ω), z ω))).map MeasurableEquiv.prodAssoc := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hz.aemeasurable]
      rfl
    _ = ((P.map x ⊗ₘ κ) ⊗ₘ η).map MeasurableEquiv.prodAssoc := by
      rw [hz.map_eq, hy.map_eq]
    _ = P.map x ⊗ₘ (κ ⊗ₖ η) := Measure.compProd_assoc'

theorem compProd_prodMkRight (κ : Kernel X Y) [IsSFiniteKernel κ]
    (l : Kernel X Z) [IsSFiniteKernel l] :
    κ ⊗ₖ l.prodMkRight Y = κ ×ₖ l := by
  ext a s hs
  rw [Kernel.compProd_apply hs, Kernel.prod_apply' _ _ _ hs]
  rfl

theorem screening (hy : HasCondDistrib y x κ P)
    (l : Kernel X Z) [IsMarkovKernel l]
    (hz : HasCondDistrib z (fun ω => (x ω, y ω)) (l.prodMkRight Y) P) :
    HasCondDistrib y (fun ω => (x ω, z ω)) (κ.prodMkRight Z) P := by
  have h := chain hy hz
  rw [compProd_prodMkRight] at h
  have h' := h.comp_left measurable_swap
  simp only [Function.comp_def, Prod.swap_prod_mk, Kernel.map_prod_swap] at h'
  rw [← compProd_prodMkRight] at h'
  exact h'.of_compProd

end ConditionalScreens

namespace ConditionalReveal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι Y : Type*} [DecidableEq ι] [MeasurableSpace Y]

def insertTuple (S : Finset ι) (i : ι) (p : (S → Y) × Y) : ↥(insert i S) → Y :=
  fun j => if h : j.val = i then p.2 else
    p.1 ⟨j.val, Finset.mem_of_mem_insert_of_ne j.property h⟩

theorem measurable_insertTuple (S : Finset ι) (i : ι) :
    Measurable (insertTuple (Y := Y) S i) := by
  apply Measurable.of_eval
  intro j
  unfold insertTuple
  split_ifs
  · exact measurable_snd
  · exact (measurable_pi_apply _).comp measurable_fst

theorem map_insertTuple (S : Finset ι) (i : ι) (hi : i ∉ S)
    (μ : ι → Measure Y) [∀ i, IsProbabilityMeasure (μ i)] :
    ((Measure.pi (fun j : S => μ j)).prod (μ i)).map (insertTuple S i) =
      Measure.pi (fun j : ↥(insert i S) => μ j) := by
  apply (Measure.pi_eq _).symm
  intro s hs
  rw [Measure.map_apply (measurable_insertTuple S i) (.univ_pi hs)]
  have hpre : insertTuple S i ⁻¹' Set.pi Set.univ s =
      (Set.pi Set.univ (fun j : S => s ⟨j, Finset.mem_insert_of_mem j.property⟩)) ×ˢ
        s ⟨i, Finset.mem_insert_self i S⟩ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
      Set.mem_prod]
    constructor
    · intro h
      constructor
      · intro j
        have hji : (j : ι) ≠ i := fun e => hi (e ▸ j.property)
        simpa only [insertTuple, dite_eq_right hji] using
          h ⟨j, Finset.mem_insert_of_mem j.property⟩
      · simpa [insertTuple] using h ⟨i, Finset.mem_insert_self i S⟩
    · rintro ⟨hp, hq⟩ j
      by_cases hji : (j : ι) = i
      · have ej : j = ⟨i, Finset.mem_insert_self i S⟩ := Subtype.ext hji
        rw [ej]
        simpa [insertTuple] using hq
      · simpa only [insertTuple, dite_eq_right hji] using
          hp ⟨j, Finset.mem_of_mem_insert_of_ne j.property hji⟩
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  classical
  let g : ι → ℝ≥0∞ := fun j => if h : j ∈ insert i S then μ j (s ⟨j, h⟩) else 1
  have hg (j : ↥(insert i S)) : g j = μ j (s j) := by simp only [g, dite_eq_left j.property]
  have hgS (j : S) : g j = μ j (s ⟨j, Finset.mem_insert_of_mem j.property⟩) := by
    exact dite_eq_left (Finset.mem_insert_of_mem j.property)
  simp_rw [← hg, ← hgS]
  rw [Finset.prod_coe_sort, Finset.prod_coe_sort, Finset.prod_insert hi]
  have hgi : g i = μ i (s ⟨i, Finset.mem_insert_self i S⟩) :=
    dite_eq_left (Finset.mem_insert_self i S)
  rw [hgi]
  exact mul_comm _ _

def splitTuple (S : Finset ι) (i : ι) (z : ↥(insert i S) → Y) : (S → Y) × Y :=
  (fun j => z ⟨j, Finset.mem_insert_of_mem j.property⟩,
    z ⟨i, Finset.mem_insert_self i S⟩)

theorem measurable_splitTuple (S : Finset ι) (i : ι) :
    Measurable (splitTuple (Y := Y) S i) := by
  exact (Measurable.of_eval (fun _ => measurable_pi_apply _)).prodMk
    (measurable_pi_apply _)

omit [MeasurableSpace Y] in
theorem split_insertTuple (S : Finset ι) (i : ι) (hi : i ∉ S) :
    splitTuple (Y := Y) S i ∘ insertTuple S i = id := by
  funext p
  apply Prod.ext
  · funext j
    have hji : (j : ι) ≠ i := fun h => hi (h ▸ j.property)
    exact dite_eq_right hji
  · simp [splitTuple, insertTuple]

theorem map_splitTuple (S : Finset ι) (i : ι) (hi : i ∉ S)
    (μ : ι → Measure Y) [∀ i, IsProbabilityMeasure (μ i)] :
    (Measure.pi (fun j : ↥(insert i S) => μ j)).map (splitTuple S i) =
      (Measure.pi (fun j : S => μ j)).prod (μ i) := by
  rw [← map_insertTuple S i hi μ,
    Measure.map_map (measurable_splitTuple S i) (measurable_insertTuple S i),
    split_insertTuple S i hi, Measure.map_id]

theorem probability_eq_of_subsingleton {Z : Type*} [MeasurableSpace Z] [Subsingleton Z]
    (μ ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : μ = ν := by
  ext s
  by_cases h : s.Nonempty
  · obtain ⟨z, hz⟩ := h
    have hs : s = Set.univ := Set.eq_univ_of_forall (fun w =>
      (Subsingleton.elim z w) ▸ hz)
    simp [hs]
  · simp [Set.not_nonempty_iff_eq_empty.mp h]

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

theorem finite_reveal (P : Measure Ω) [IsProbabilityMeasure P]
    (E : Ω → X) (hE : Measurable E) (y : ι → Ω → Y)
    (κ : ι → Kernel X Y) [∀ i, IsMarkovKernel (κ i)] (R : Finset ι)
    (h : ∀ (S : Finset ι), S ⊆ R → ∀ i ∈ R, i ∉ S →
      HasCondDistrib (y i) (fun ω => (E ω, fun j : S => y j ω))
        ((κ i).prodMkRight (S → Y)) P) :
    HasCondDistrib (fun ω => fun j : R => y j ω) E
      (FiniteKernel.pi (fun j : R => κ j)) P := by
  classical
  revert h
  induction R using Finset.induction_on with
  | empty =>
    intro _
    let z : (∅ : Finset ι) → Y := fun i => False.elim (Finset.notMem_empty _ i.property)
    have hk : FiniteKernel.pi (fun j : (∅ : Finset ι) => κ j) =
        Kernel.deterministic (fun _ : X => z) measurable_const := by
      ext x : 1
      exact probability_eq_of_subsingleton _ _
    have hy : (fun ω => fun j : (∅ : Finset ι) => y j ω) = fun _ => z := by
      funext ω j
      exact False.elim (Finset.notMem_empty _ j.property)
    rw [hy, hk]
    refine ⟨(hE.prodMk measurable_const).aemeasurable, ?_⟩
    rw [Measure.compProd_deterministic, Measure.map_map (by fun_prop) hE]
    rfl
  | @insert i S hi ih =>
    intro h
    have hS := ih (fun A hA j hj hnot => h A
      (hA.trans (Finset.subset_insert i S)) j (Finset.mem_insert_of_mem hj) hnot)
    have hi' := h S (Finset.subset_insert i S) i (Finset.mem_insert_self i S) hi
    have hh := ConditionalScreens.chain hS hi'
    rw [ConditionalScreens.compProd_prodMkRight] at hh
    have hout := hh.comp_left (measurable_insertTuple S i)
    have hk : ((FiniteKernel.pi (fun j : S => κ j)) ×ₖ κ i).map
        (insertTuple S i) = FiniteKernel.pi (fun j : ↥(insert i S) => κ j) := by
      ext x : 1
      rw [Kernel.map_apply _ (measurable_insertTuple S i), Kernel.prod_apply]
      exact map_insertTuple S i hi (fun j => κ j x)
    rw [hk] at hout
    have hy : insertTuple S i ∘ (fun ω => ((fun j : S => y j ω), y i ω)) =
        (fun ω => fun j : ↥(insert i S) => y j ω) := by
      funext ω j
      simp only [Function.comp_def, insertTuple]
      split_ifs with hji
      · rw [hji]
      · rfl
    rwa [hy] at hout

end ConditionalReveal
open MeasureTheory ProbabilityTheory

namespace ConditionalTransport
variable {Ω Ω' A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

theorem pullback {P : Measure Ω} {Q : Measure Ω'} {f : Ω → Ω'}
    {E : Ω' → A} {O : Ω' → B} {κ : Kernel A B}
    (hf : MeasurePreserving f P Q) (hE : Measurable E)
    (h : HasCondDistrib O E κ Q) : HasCondDistrib (O ∘ f) (E ∘ f) κ P := by
  have hh := h.comp hf.hasLaw
  have he : P.map (E ∘ f) = Q.map E := by
    rw [← Measure.map_map hE hf.measurable, hf.map_eq]
  change HasLaw (fun ω => (E (f ω), O (f ω))) (P.map (E ∘ f) ⊗ₘ κ) P
  rw [he]
  exact hh

theorem recondition [StandardBorelSpace B] [Nonempty B]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Ω → A} {D : Ω → C} {O : Ω → B}
    {κ : Kernel A B} [IsMarkovKernel κ] {η : Kernel C B} [IsMarkovKernel η]
    (hE : Measurable E) (hD : Measurable D) (hO : Measurable O)
    (h : HasCondDistrib O E κ P)
    (hfield : MeasurableSpace.comap E inferInstance = MeasurableSpace.comap D inferInstance)
    (hk : (fun ω => κ (E ω)) =ᵐ[P] fun ω => η (D ω)) : HasCondDistrib O D η P := by
  apply KernelTests.hasCondDistrib_of_indicators _ D O hD hO
  intro S hS
  have hc := ae_of_ae_map hE.aemeasurable
    (condDistrib_ae_eq_of_measure_eq_compProd hE.aemeasurable hO.aemeasurable h.map_eq)
  have hi := condDistrib_ae_eq_condExp (μ := P) hE hO hS
  rw [hfield] at hi
  filter_upwards [hc, hi, hk] with ω h1 h2 h3
  exact h2.symm.trans (by rw [h1, h3])

theorem of_indep {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Ω → A} {O : Ω → B} (hE : Measurable E) (hO : Measurable O)
    (h : IndepFun E O P) : HasCondDistrib O E (Kernel.const A (P.map O)) P := by
  refine ⟨(hE.prodMk hO).aemeasurable, ?_⟩
  rw [Measure.compProd_const]
  exact h.map_prod_eq_prod_map_map hE.aemeasurable hO.aemeasurable

theorem indep_of_const {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Ω → A} {O : Ω → B} (hE : Measurable E) (hO : Measurable O)
    (Q : Measure B) [IsProbabilityMeasure Q]
    (h : HasCondDistrib O E (Kernel.const A Q) P) : IndepFun E O P := by
  apply (indepFun_iff_map_prod_eq_prod_map_map hE.aemeasurable hO.aemeasurable).mpr
  rw [h.map_eq, h.hasLaw_of_const.map_eq, Measure.compProd_const]

end ConditionalTransport

namespace ConditionalReveal
variable {ι Ω X Y Z : Type*} [DecidableEq ι] [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

theorem independent_image (P : Measure Ω) [IsProbabilityMeasure P]
    (E : Ω → X) (hE : Measurable E) (y : ι → Ω → Y) (hy : ∀ i, Measurable (y i))
    (κ : ι → Kernel X Y) [∀ i, IsMarkovKernel (κ i)]
    (R : Finset ι) (i : ι) (hi : i ∉ R) (f : Y → Z) (hf : Measurable f)
    (Q : Measure Z) [IsProbabilityMeasure Q]
    (h : HasCondDistrib (fun ω => fun j : ↥(insert i R) => y j ω) E
      (FiniteKernel.pi (fun j : ↥(insert i R) => κ j)) P)
    (hk : (fun x => (κ i x).map f) =ᵐ[P.map E] fun _ => Q) :
    IndepFun (fun ω => (E ω, fun j : R => y j ω)) (f ∘ y i) P := by
  have hs := h.comp_left (measurable_splitTuple R i)
  have hsk : (FiniteKernel.pi (fun j : ↥(insert i R) => κ j)).map (splitTuple R i) =
      (FiniteKernel.pi (fun j : R => κ j)) ×ₖ κ i := by
    ext x : 1
    rw [Kernel.map_apply _ (measurable_splitTuple R i), Kernel.prod_apply]
    exact map_splitTuple R i hi (fun j => κ j x)
  rw [hsk] at hs
  change HasCondDistrib (fun ω => ((fun j : R => y j ω), y i ω)) E
    ((FiniteKernel.pi (fun j : R => κ j)) ×ₖ κ i) P at hs
  have hx := hs.comp_left (measurable_id.prodMap hf)
  rw [← Kernel.map_prod_map _ _ measurable_id hf, Kernel.map_id] at hx
  have hprod : ((FiniteKernel.pi (fun j : R => κ j)) ×ₖ (κ i).map f) =ᵐ[P.map E]
      ((FiniteKernel.pi (fun j : R => κ j)) ×ₖ Kernel.const X Q) := by
    filter_upwards [hk] with x hx
    rw [Kernel.prod_apply, Kernel.prod_apply, Kernel.map_apply _ hf, hx]
    rfl
  have hout : HasCondDistrib (fun ω => ((fun j : R => y j ω), f (y i ω))) E
      ((FiniteKernel.pi (fun j : R => κ j)) ×ₖ Kernel.const X Q) P :=
    ⟨hx.aemeasurable, hx.map_eq.trans (Measure.compProd_congr hprod)⟩
  rw [← ConditionalScreens.compProd_prodMkRight] at hout
  have hout' := hout.of_compProd
  have hc : (Kernel.const X Q).prodMkRight (R → Y) = Kernel.const (X × (R → Y)) Q := rfl
  rw [hc] at hout'
  exact ConditionalTransport.indep_of_const
    (hE.prodMk (Measurable.of_eval (fun j => hy j))) (hf.comp (hy i)) Q hout'

end ConditionalReveal

namespace ConditionalTransport
variable {Ω Ω' A B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [MeasurableSpace B]
lemma map_indep {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → Ω'} {E : Ω' → A} {O : Ω' → B}
    (hf : Measurable f) (hE : Measurable E) (hO : Measurable O)
    (h : IndepFun (E ∘ f) (O ∘ f) P) : IndepFun E O (P.map f) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map hE.aemeasurable hO.aemeasurable).mpr
  rw [Measure.map_map (hE.prodMk hO) hf, Measure.map_map hE hf, Measure.map_map hO hf]
  exact h.map_prod_eq_prod_map_map (hE.comp hf).aemeasurable (hO.comp hf).aemeasurable
end ConditionalTransport

namespace ArrayObjects.Object
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

noncomputable def ownKernel (n : ℕ) : Kernel (Arr I M.U n) (Arr I M.Y n) :=
  condDistrib id (amap M.par n) (M.law n)
instance ownKernel_markov (n : ℕ) : IsMarkovKernel (ownKernel M n) := by
  unfold ownKernel
  infer_instance

lemma ownKernel_conditional (n : ℕ) :
    HasCondDistrib id (amap M.par n) (M.ownKernel n) (M.law n) :=
  ⟨((measurable_amap M.measurable_par n).prodMk measurable_id).aemeasurable,
    (compProd_map_condDistrib measurable_id.aemeasurable).symm⟩

lemma planes_conditional (n : ℕ) (J : Finset I) (hJ : J ≠ Finset.univ) :
    HasCondDistrib (planes n J) (amap M.par (n + 1))
      (FiniteKernel.pi (fun j : J => (M.ownKernel n).comap
        (plane n (Fin.last n) j) (measurable_plane _ _ _))) (M.law (n + 1)) := by
  refine ⟨((measurable_amap M.measurable_par _).prodMk (measurable_planes _ _)).aemeasurable, ?_⟩
  exact (compProd_map_condDistrib (measurable_planes n J).aemeasurable).symm.trans
    (Measure.compProd_congr (M.conditional n J hJ))

lemma ownKernel_zero_image :
    (fun p => (M.ownKernel 0 p).map (M.x ∘ zeroEquiv I M.Y)) =ᵐ[
      (M.law 0).map (amap M.par 0)] fun _ => M.localLaw.map M.x := by
  have h := ConditionalTransport.of_indep (P := M.localLaw) M.measurable_par M.measurable_x M.local_independent.symm
  have h0 := ConditionalTransport.pullback
    (show MeasurePreserving (zeroEquiv I M.Y) (M.law 0) M.localLaw from
      ⟨(zeroEquiv I M.Y).measurable, rfl⟩) M.measurable_par h
  have h1 := h0.measurableEquiv_comp_right (zeroEquiv I M.U).symm
  have hpar : (zeroEquiv I M.U).symm ∘ M.par ∘ zeroEquiv I M.Y = amap M.par 0 := by
    funext y w
    exact congrArg (fun v => M.par (y v)) (Subsingleton.elim _ _)
  rw [hpar] at h1
  have h2 := (M.ownKernel_conditional 0).comp_left
    (M.measurable_x.comp (zeroEquiv I M.Y).measurable)
  have hk := Kernel.ae_eq_of_compProd_eq (h2.map_eq.symm.trans h1.map_eq)
  filter_upwards [hk] with p hp
  rw [← Kernel.map_apply _ (M.measurable_x.comp (zeroEquiv I M.Y).measurable)]
  exact hp

namespace Rolled
lemma local_independent [DecidableEq I] (R : Finset I) (a : I)
    (ha : a ∉ R) (hR : insert a R ≠ Finset.univ) :
    IndepFun (M.x ∘ Function.eval a) (parameter M R)
      ((law M 0).map (zeroEquiv I (State M))) := by
  let E := amap (I := I) M.par 1
  let y := fun c : I => plane 0 (Fin.last 0) c (Y := M.Y)
  let κ := fun c : I => (M.ownKernel 0).comap
    (plane 0 (Fin.last 0) c) (measurable_plane _ _ _)
  have hE : Measurable E := measurable_amap M.measurable_par 1
  have hfield : MeasurePreserving (plane 0 (Fin.last 0) a)
      ((M.law 1).map E) ((M.law 0).map (amap M.par 0)) := by
    refine ⟨measurable_plane _ _ _, ?_⟩
    rw [Measure.map_map (measurable_plane _ _ _) hE, plane_amap,
      ← Measure.map_map (measurable_amap M.measurable_par 0) (measurable_plane _ _ _),
      M.consistent]
  let Q := M.localLaw.map M.x
  have : IsProbabilityMeasure Q := (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) M.measurable_x.aemeasurable
  have hk := hfield.quasiMeasurePreserving.ae_eq_comp M.ownKernel_zero_image
  have h := ConditionalReveal.independent_image (M.law 1) E hE y
    (fun c => measurable_plane 0 (Fin.last 0) c) κ R a ha
    (M.x ∘ zeroEquiv I M.Y) (M.measurable_x.comp (zeroEquiv I M.Y).measurable) Q
    (M.planes_conditional 0 (insert a R) hR) hk
  let e : Arr I M.U 1 × (R → Arr I M.Y 0) → Parameter M R := fun p =>
    (fun c => p.1 (Fin.cons c Fin.elim0), fun c => zeroEquiv I M.Y (p.2 c))
  have he : Measurable e := by
    exact (Measurable.of_eval (fun _ => (measurable_pi_apply _).comp measurable_fst)).prodMk
      (Measurable.of_eval (fun _ => (zeroEquiv I M.Y).measurable.comp
        ((measurable_pi_apply _).comp measurable_snd)))
  have hh := (h.comp he measurable_id).symm
  rw [law, Measure.map_map (zeroEquiv I (State M)).measurable (roll 0).measurable]
  apply ConditionalTransport.map_indep ((zeroEquiv I (State M)).measurable.comp (roll 0).measurable)
    (M.measurable_x.comp (measurable_pi_apply a)) (measurable_parameter M R)
  convert hh using 1 <;> funext z <;> simp [E, e, y, parameter, roll, zeroEquiv, plane,
    amap, Function.comp_def, Fin.insertNth_zero']

end Rolled
end ArrayObjects.Object

namespace ArrayObjects
variable {I : Type u}

lemma cons_snoc {n : ℕ} (c j : I) (v : Fin n → I) :
    (Fin.cons c (Fin.snoc (α := fun _ => I) v j) : Fin (n + 2) → I) =
      Fin.snoc (α := fun _ => I) (Fin.cons c v) j := by
  simpa only [show (Fin.last n).succ = Fin.last (n + 1) from rfl,
    Fin.insertNth_last'] using (Fin.insertNth_succ_cons (Fin.last n) j c v).symm

namespace Object.Rolled
variable [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

noncomputable abbrev Outside (j : I) : Finset I := by
  classical
  exact Finset.univ.erase j

variable [DecidableEq I]

abbrev RawData (n : ℕ) (j : I) :=
  Arr I M.U (n + 2) × (Outside j → Arr I M.Y (n + 1))

abbrev RevealData (R : Finset I) (n : ℕ) (j : I) :=
  RawData M n j × (R → Arr I M.Y n)

abbrev RollData (R : Finset I) (n : ℕ) (j : I) :=
  Arr I (Parameter M R) (n + 1) × (Outside j → Arr I (State M) n)

def rawData (n : ℕ) (j : I) (y : Arr I M.Y (n + 2)) : RawData M n j :=
  (amap M.par (n + 2) y, planes (n + 1) (Outside j) y)

def missingRow (n : ℕ) (j c : I) (y : Arr I M.Y (n + 2)) : Arr I M.Y n :=
  plane n (Fin.last n) j (plane (n + 1) 0 c y)

def revealData (R : Finset I) (n : ℕ) (j : I) (y : Arr I M.Y (n + 2)) :
    RevealData M R n j := (rawData M n j y, fun c => missingRow M n j c y)

def rollData (R : Finset I) (n : ℕ) (j : I) (y : Arr I (State M) (n + 1)) :
    RollData M R n j := (amap (parameter M R) (n + 1) y, planes n (Outside j) y)

omit [DecidableEq I] in
@[fun_prop] lemma measurable_rawData (n : ℕ) (j : I) : Measurable (rawData M n j) :=
  (measurable_amap M.measurable_par _).prodMk (measurable_planes _ _)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_missingRow (n : ℕ) (j c : I) :
    Measurable (missingRow M n j c) :=
  (measurable_plane _ _ _).comp (measurable_plane _ _ _)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_revealData (R : Finset I) (n : ℕ) (j : I) :
    Measurable (revealData M R n j) :=
  (measurable_rawData M n j).prodMk
    (Measurable.of_eval (fun c => measurable_missingRow M n j c))
omit [DecidableEq I] in
@[fun_prop] lemma measurable_rollData (R : Finset I) (n : ℕ) (j : I) :
    Measurable (rollData M R n j) :=
  (measurable_amap (measurable_parameter M R) _).prodMk (measurable_planes _ _)

def rollToReveal (R : Finset I) (n : ℕ) (j : I) (p : RollData M R n j) :
    RevealData M R n j :=
  ((fun v => (p.1 (Fin.tail v)).1 (v 0), fun k => (roll n).symm (p.2 k)),
    fun c v => (p.1 (Fin.snoc v j)).2 c)

omit [DecidableEq I] in
@[fun_prop] lemma measurable_rollToReveal (R : Finset I) (n : ℕ) (j : I) :
    Measurable (rollToReveal M R n j) := by
  unfold rollToReveal
  fun_prop

def revealToRoll (R : Finset I) (n : ℕ) (j : I) (p : RevealData M R n j) :
    RollData M R n j :=
  (fun w => (fun c => p.1.1 (Fin.cons c w), fun c =>
    if h : w (Fin.last n) = j then p.2 c (Fin.init w) else
      p.1.2 ⟨w (Fin.last n), by simp [Outside, h]⟩ (Fin.cons c (Fin.init w))),
    fun k => roll n (p.1.2 k))

@[fun_prop] lemma measurable_revealToRoll (R : Finset I) (n : ℕ) (j : I) :
    Measurable (revealToRoll M R n j) := by
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro w
    apply Measurable.prodMk
    · fun_prop
    · apply Measurable.of_eval
      intro c
      split_ifs <;> fun_prop
  · exact Measurable.of_eval (fun k => (roll n).measurable.comp
      ((measurable_pi_apply k).comp (measurable_snd.comp measurable_fst)))

omit [DecidableEq I] in
lemma rollToReveal_observation (R : Finset I) (n : ℕ) (j : I) :
    rollToReveal M R n j ∘ rollData M R n j ∘ roll (n + 1) = revealData M R n j := by
  funext y
  apply Prod.ext
  · apply Prod.ext
    · funext v
      simp [rollToReveal, rollData, revealData, rawData, amap, parameter, roll]
    · funext k
      change (roll n).symm ((planes n (Outside j) ∘ roll (n + 1)) y k) = _
      rw [planes_roll]
      exact (roll n).symm_apply_apply _
  · funext c v
    simp [rollToReveal, rollData, revealData, missingRow, amap, parameter, roll,
      plane, Fin.insertNth_zero', Fin.insertNth_last']

lemma revealToRoll_observation (R : Finset I) (n : ℕ) (j : I) :
    revealToRoll M R n j ∘ revealData M R n j = rollData M R n j ∘ roll (n + 1) := by
  funext y
  apply Prod.ext
  · funext w
    apply Prod.ext
    · rfl
    · funext c
      change (if h : w (Fin.last n) = j then missingRow M n j c y (Fin.init w) else
        planes (n + 1) (Outside j) y
          ⟨w (Fin.last n), by simp [Outside, h]⟩ (Fin.cons c (Fin.init w))) = _
      split_ifs with h
      · simp only [missingRow, plane, Fin.insertNth_zero', Fin.insertNth_last']
        rw [← h, Fin.snoc_init_self]
        rfl
      · simp only [planes, plane, Fin.insertNth_last']
        rw [← cons_snoc, Fin.snoc_init_self]
        rfl
  · funext k
    exact congrFun (congrFun (planes_roll n (Outside j)) y) k |>.symm

lemma comap_reveal_eq_rollData (R : Finset I) (n : ℕ) (j : I) :
    MeasurableSpace.comap (revealData M R n j) inferInstance =
      MeasurableSpace.comap (rollData M R n j ∘ roll (n + 1)) inferInstance := by
  apply le_antisymm
  · rw [← rollToReveal_observation M R n j, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_rollToReveal M R n j).comap_le
  · rw [← revealToRoll_observation M R n j, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_revealToRoll M R n j).comap_le

abbrev OldData (n : ℕ) (j : I) :=
  Arr I M.U (n + 1) × (Outside j → Arr I M.Y n)

def oldData (n : ℕ) (j : I) (y : Arr I M.Y (n + 1)) : OldData M n j :=
  (amap M.par (n + 1) y, planes n (Outside j) y)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_oldData (n : ℕ) (j : I) : Measurable (oldData M n j) :=
  (measurable_amap M.measurable_par _).prodMk (measurable_planes _ _)

def rowData (n : ℕ) (j c : I) (p : RawData M n j) : OldData M n j :=
  (plane (n + 1) 0 c p.1, fun k => plane n 0 c (p.2 k))
omit [DecidableEq I] in
@[fun_prop] lemma measurable_rowData (n : ℕ) (j c : I) : Measurable (rowData M n j c) :=
  ((measurable_plane _ _ _).comp measurable_fst).prodMk
    (Measurable.of_eval (fun _ => (measurable_plane _ _ _).comp
      ((measurable_pi_apply _).comp measurable_snd)))

def selectData (R : Finset I) (n : ℕ) (j c : I) (p : RollData M R n j) : OldData M n j :=
  (amap (fun q => q.1 c) (n + 1) p.1, fun k => amap (Function.eval c) n (p.2 k))
omit [DecidableEq I] in
@[fun_prop] lemma measurable_selectData (R : Finset I) (n : ℕ) (j c : I) :
    Measurable (selectData M R n j c) := by
  unfold selectData
  fun_prop

omit [DecidableEq I] in
lemma selectData_observation (R : Finset I) (n : ℕ) (j c : I) :
    selectData M R n j c ∘ rollData M R n j ∘ roll (n + 1) =
      rowData M n j c ∘ rawData M n j := by
  funext y
  apply Prod.ext
  · funext v
    simp [selectData, rollData, rowData, rawData, amap, parameter, roll, plane,
      Fin.insertNth_zero']
  · funext k v
    simp [selectData, rollData, rowData, rawData, amap, roll, plane, planes,
      Fin.insertNth_zero', Fin.insertNth_last', cons_snoc]

end Object.Rolled
end ArrayObjects
namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def IsConditional (R : Finset I) : Prop :=
  ∀ n (J : Finset I), J ≠ Finset.univ →
    condDistrib (planes n J) (amap (parameter M R) (n + 1)) (law M (n + 1))
      =ᵐ[(law M (n + 1)).map (amap (parameter M R) (n + 1))]
    fun p => Measure.pi (fun j : J =>
      condDistrib (id : Arr I (State M) n → Arr I (State M) n)
        (amap (parameter M R) n) (law M n) (plane n (Fin.last n) j p))

noncomputable def makeObject (R : Finset I) (hc : IsConditional M R)
    (a : I) (ha : a ∉ R) (hR : insert a R ≠ Finset.univ) : Object I base where
  Y := State M
  U := Parameter M R
  timeY := timeState M
  timeU := timeParameter M R
  x := M.x ∘ Function.eval a
  par := parameter M R
  measurable_x := M.measurable_x.comp (measurable_pi_apply a)
  measurable_par := measurable_parameter M R
  time_x := by funext y; exact congrFun M.time_x (y a)
  time_par := time_parameter M R
  law := law M
  probability := law_probability M
  invariant := invariant M
  over_base := fun n => over_base M n a
  consistent := consistent M
  proper := proper M
  conditional := hc
  local_independent := local_independent M R a ha hR

noncomputable def extension (R : Finset I) (hc : IsConditional M R)
    (a : I) (ha : a ∉ R) (hR : insert a R ≠ Finset.univ) :
    Extension M (makeObject M R hc a ha hR) where
  state := Function.eval a
  parameter := fun p => p.1 a
  measurable_state := measurable_pi_apply a
  measurable_parameter := (measurable_pi_apply a).comp measurable_fst
  time_state := rfl
  time_parameter := rfl
  state_x := rfl
  state_par := rfl
  laws n := select_law M n a

noncomputable def rowKernel (n : ℕ) (j c : I) : Kernel (RawData M n j) (Arr I M.Y n) :=
  (condDistrib (plane n (Fin.last n) j) (oldData M n j) (M.law (n + 1))).comap
    (rowData M n j c) (measurable_rowData M n j c)
instance rowKernel_markov (n : ℕ) (j c : I) : IsMarkovKernel (rowKernel M n j c) := by
  unfold rowKernel
  infer_instance

lemma parent_reveal (hM : M.IsSaturated) (R : Finset I) (hc : IsConditional M R)
    (c : I) (hcR : c ∉ R) (hR : insert c R ≠ Finset.univ) (n : ℕ) (j : I) :
    HasCondDistrib (missingRow M n j c) (revealData M R n j)
      ((rowKernel M n j c).prodMkRight (R → Arr I M.Y n)) (M.law (n + 2)) := by
  let N := makeObject M R hc c hcR hR
  let ext := extension M R hc c hcR hR
  have hs := hM.hasCondDistrib ext n (.enlarged j)
    (oldData M n j) (rollData M R n j) (plane n (Fin.last n) j)
    (selectData M R n j c) (measurable_oldData M n j) (measurable_rollData M R n j)
    (measurable_plane _ _ _) (measurable_selectData M R n j c)
    (by
      unfold Object.data oldData Outside
      exact (MeasurableSpace.comap_prodMk (mβ := inferInstance) (mγ := inferInstance)
        (amap M.par (n + 1)) (planes n (Outside j))).symm)
    (by
      unfold Object.data rollData Outside makeObject
      exact (MeasurableSpace.comap_prodMk (mβ := inferInstance) (mγ := inferInstance)
        (amap (parameter M R) (n + 1)) (planes n (Outside j))).symm) rfl
  have hp := ConditionalTransport.pullback
    (show MeasurePreserving (roll (Y := M.Y) (n + 1)) (M.law (n + 2)) (N.law (n + 1)) from
      ⟨(roll (n + 1)).measurable, rfl⟩) (measurable_rollData M R n j) hs
  have hobs : (plane n (Fin.last n) j ∘ amap (Function.eval c) (n + 1)) ∘ roll (n + 1) =
      missingRow M n j c := by
    rw [Function.comp_assoc, select_roll]
    rfl
  change HasCondDistrib ((plane n (Fin.last n) j ∘ amap (Function.eval c) (n + 1)) ∘
      roll (n + 1)) (rollData M R n j ∘ roll (n + 1)) _ (M.law _) at hp
  rw [hobs] at hp
  apply ConditionalTransport.recondition
    ((measurable_rollData M R n j).comp (roll (n + 1)).measurable)
    (measurable_revealData M R n j) (measurable_missingRow M n j c) hp
    (comap_reveal_eq_rollData M R n j).symm
  apply Filter.Eventually.of_forall
  intro y
  change (condDistrib (plane n (Fin.last n) j) (oldData M n j) (M.law (n + 1)))
      ((selectData M R n j c ∘ rollData M R n j ∘ roll (n + 1)) y) =
    (condDistrib (plane n (Fin.last n) j) (oldData M n j) (M.law (n + 1)))
      ((rowData M n j c ∘ rawData M n j) y)
  rw [selectData_observation]


lemma parent_joint (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I)
    (ih : ∀ S : Finset I, S ⊂ R → IsConditional M S) (n : ℕ) (j : I) :
    HasCondDistrib (fun y => fun c : R => missingRow M n j c y) (rawData M n j)
      (FiniteKernel.pi (fun c : R => rowKernel M n j c)) (M.law (n + 2)) := by
  apply ConditionalReveal.finite_reveal _ _ (measurable_rawData M n j)
  intro S hS c hc hcS
  have hstrict : S ⊂ R := (Finset.ssubset_iff_subset_ne).mpr ⟨hS, by
    intro he; subst S; exact hcS hc⟩
  have hproper : insert c S ≠ Finset.univ := by
    intro he
    have hle : (insert c S).card ≤ R.card := Finset.card_le_card
      (Finset.insert_subset hc hS)
    rw [he, Finset.card_univ] at hle
    omega
  exact parent_reveal M hM S (ih S hstrict) c hcS hproper n j

end ArrayObjects.Object.Rolled

namespace LocalConditioning
open FiniteKernel ConditionalScreens

variable {Ω X Y A : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace A]

noncomputable def observe (κ : Kernel X Y) (a : X × Y → A) (ha : Measurable a) :
    Kernel X (A × Y) :=
  (κ ⊗ₖ Kernel.deterministic a ha).map Prod.swap

instance instIsMarkovKernelProdObserve (κ : Kernel X Y) [IsMarkovKernel κ] (a : X × Y → A) (ha : Measurable a) :
    IsMarkovKernel (observe κ a ha) :=
  Kernel.IsMarkovKernel.map _ measurable_swap

theorem observe_apply (κ : Kernel X Y) [IsMarkovKernel κ]
    (a : X × Y → A) (ha : Measurable a) (x : X) :
    observe κ a ha x = (κ x).map (fun y => (a (x, y), y)) := by
  rw [observe, Kernel.map_apply _ measurable_swap,
    Kernel.compProd_apply_eq_compProd_sectR]
  have heq : Kernel.sectR (Kernel.deterministic a ha) x =
      Kernel.deterministic (fun y => a (x, y)) (ha.comp measurable_prodMk_left) := by
    ext y : 1
    rfl
  rw [heq, Measure.compProd_deterministic]
  rw [Measure.map_map measurable_swap (by fun_prop)]
  rfl

theorem deterministic {P : Measure Ω} [SFinite P] {x : Ω → X}
    (hx : AEMeasurable x P) (a : X → A) (ha : Measurable a) :
    HasCondDistrib (a ∘ x) x (Kernel.deterministic a ha) P := by
  refine ⟨hx.prodMk (ha.comp_aemeasurable hx), ?_⟩
  rw [Measure.compProd_deterministic,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) hx]
  rfl

theorem hasCondDistrib_observe {P : Measure Ω} [SFinite P] {x : Ω → X} {y : Ω → Y}
    {κ : Kernel X Y} [IsMarkovKernel κ] (h : HasCondDistrib y x κ P)
    (a : X × Y → A) (ha : Measurable a) :
    HasCondDistrib (fun ω => (a (x ω, y ω), y ω)) x (observe κ a ha) P := by
  have h' := chain h (deterministic h.aemeasurable a ha)
  exact h'.comp_left measurable_swap

variable {ι : Type*} [Fintype ι]
  {O C : ι → Type*} [∀ i, MeasurableSpace (O i)] [∀ i, MeasurableSpace (C i)]

theorem observe_pi (κ : ∀ i, Kernel X (O i)) [∀ i, IsMarkovKernel (κ i)]
    (a : ∀ i, X × O i → C i) (ha : ∀ i, Measurable (a i)) :
    observe (pi κ) (fun p : X × (∀ i, O i) => fun i => a i (p.1, p.2 i)) (by fun_prop) =
      (pi (fun i => observe (κ i) (a i) (ha i))).map (zipEquiv C O).symm := by
  ext x : 1
  rw [observe_apply, Kernel.map_apply _ (zipEquiv C O).symm.measurable]
  simp only [pi_apply, observe_apply]
  rw [← Measure.pi_map_pi (fun i => (show Measurable (fun o => (a i (x, o), o)) by
    fun_prop).aemeasurable), Measure.map_map (zipEquiv C O).symm.measurable (by fun_prop)]
  rfl

theorem compProd_comap {E : Type*} [MeasurableSpace E]
    (κ : Kernel E A) [IsMarkovKernel κ] (η : Kernel (E × A) Y) [IsMarkovKernel η]
    (e : X → E) (he : Measurable e) :
    (κ ⊗ₖ η).comap e he = κ.comap e he ⊗ₖ
      η.comap (fun p : X × A => (e p.1, p.2)) (by fun_prop) := by
  ext x s hs
  simp only [Kernel.comap_apply, Kernel.compProd_apply hs]

theorem observe_comap {E : Type*} [MeasurableSpace E]
    (κ : Kernel E Y) [IsMarkovKernel κ] (a : E × Y → A) (ha : Measurable a)
    (e : X → E) (he : Measurable e) :
    observe (κ.comap e he) (fun p : X × Y => a (e p.1, p.2)) (by fun_prop) =
      (observe κ a ha).comap e he := by
  ext x : 1
  simp only [observe_apply, Kernel.comap_apply]

theorem disintegrate_pi (κ : ∀ i, Kernel X (C i)) [∀ i, IsMarkovKernel (κ i)]
    (η : ∀ i, Kernel (X × C i) (O i)) [∀ i, IsMarkovKernel (η i)] :
    (pi (fun i => κ i ⊗ₖ η i)).map (zipEquiv C O).symm =
      pi κ ⊗ₖ pi (fun i => (η i).comap
        (fun p : X × (∀ i, C i) => (p.1, p.2 i)) (by fun_prop)) := by
  rw [← pi_compProd, ← Kernel.map_comp_right _ (zipEquiv C O).measurable
    (zipEquiv C O).symm.measurable]
  convert Kernel.map_id _ using 1
  all_goals try with_reducible_and_instances rfl
  ext x i
  rfl

theorem hasCondDistrib_update {P : Measure Ω} [SFinite P]
    {x : Ω → X} {o : Ω → ∀ i, O i}
    (κ : ∀ i, Kernel X (O i)) [∀ i, IsMarkovKernel (κ i)]
    (a : ∀ i, X × O i → C i) (ha : ∀ i, Measurable (a i))
    (M : ∀ i, Kernel X (C i)) [∀ i, IsMarkovKernel (M i)]
    (Q : ∀ i, Kernel (X × C i) (O i)) [∀ i, IsMarkovKernel (Q i)]
    (hd : ∀ i, observe (κ i) (a i) (ha i) = M i ⊗ₖ Q i)
    (ho : HasCondDistrib o x (pi κ) P) :
    HasCondDistrib o (fun ω => (x ω, fun i => a i (x ω, o ω i)))
      (pi (fun i => (Q i).comap
        (fun p : X × (∀ i, C i) => (p.1, p.2 i)) (by fun_prop))) P := by
  have h := hasCondDistrib_observe ho
    (fun p : X × (∀ i, O i) => fun i => a i (p.1, p.2 i)) (by fun_prop)
  have hpi : pi (fun i => observe (κ i) (a i) (ha i)) = pi (fun i => M i ⊗ₖ Q i) := by
    ext x : 1
    simp only [pi_apply, hd]
  rw [observe_pi κ a ha, hpi, disintegrate_pi] at h
  exact h.of_compProd

theorem hasCondDistrib_local_update {P : Measure Ω} [SFinite P]
    {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    [∀ i, MeasurableSpace.CountablyGenerated (C i)]
    [∀ i, StandardBorelSpace (O i)] [∀ i, Nonempty (O i)]
    {x : Ω → X} {o : Ω → ∀ i, O i}
    (e : ∀ i, X → E i) (he : ∀ i, Measurable (e i))
    (κ : ∀ i, Kernel (E i) (O i)) [∀ i, IsMarkovKernel (κ i)]
    (a : ∀ i, E i × O i → C i) (ha : ∀ i, Measurable (a i))
    (ho : HasCondDistrib o x (pi (fun i => (κ i).comap (e i) (he i))) P) :
    HasCondDistrib o (fun ω => (x ω, fun i => a i (e i (x ω), o ω i)))
      (pi (fun i => (observe (κ i) (a i) (ha i)).condKernel.comap
        (fun p : X × (∀ i, C i) => (e i p.1, p.2 i)) (by fun_prop))) P := by
  let M (i : ι) : Kernel X (C i) :=
    (observe (κ i) (a i) (ha i)).fst.comap (e i) (he i)
  let Q (i : ι) : Kernel (X × C i) (O i) :=
    (observe (κ i) (a i) (ha i)).condKernel.comap
      (fun p : X × C i => (e i p.1, p.2)) (by fun_prop)
  have hd (i : ι) : observe ((κ i).comap (e i) (he i))
      (fun p : X × O i => a i (e i p.1, p.2)) (by fun_prop) = M i ⊗ₖ Q i := by
    rw [observe_comap]
    dsimp only [M, Q]
    rw [← compProd_comap, Kernel.disintegrate]
  have h := hasCondDistrib_update (fun i => (κ i).comap (e i) (he i))
    (fun i => fun p : X × O i => a i (e i p.1, p.2)) (by intro i; fun_prop)
    M Q hd ho
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext x : 1
  rfl

theorem hasCondDistrib_posterior [MeasurableSpace.CountablyGenerated A]
    [StandardBorelSpace Y] [Nonempty Y]
    {P : Measure Ω} [SFinite P] {x : Ω → X} {y : Ω → Y}
    {κ : Kernel X Y} [IsMarkovKernel κ] (ho : HasCondDistrib y x κ P)
    (a : X × Y → A) (ha : Measurable a) :
    HasCondDistrib y (fun ω => (x ω, a (x ω, y ω)))
      (observe κ a ha).condKernel P := by
  have h := hasCondDistrib_observe ho a ha
  rw [← Kernel.disintegrate (observe κ a ha) (observe κ a ha).condKernel] at h
  exact h.of_compProd

theorem local_conditioning {P : Measure Ω} [SFinite P]
    {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    [∀ i, MeasurableSpace.CountablyGenerated (C i)]
    [∀ i, StandardBorelSpace (O i)] [∀ i, Nonempty (O i)]
    {B : Type*} [MeasurableSpace B]
    {x : Ω → X} {o : Ω → ∀ i, O i} {b : Ω → B}
    (e : ∀ i, X → E i) (he : ∀ i, Measurable (e i))
    (κ : ∀ i, Kernel (E i) (O i)) [∀ i, IsMarkovKernel (κ i)]
    (a : ∀ i, E i × O i → C i) (ha : ∀ i, Measurable (a i))
    (L : Kernel (X × (∀ i, C i)) B) [IsMarkovKernel L]
    (ho : HasCondDistrib o x (pi (fun i => (κ i).comap (e i) (he i))) P)
    (hb : HasCondDistrib b (fun ω => (x ω, o ω))
      (L.comap (fun p : X × (∀ i, O i) => (p.1, fun i => a i (e i p.1, p.2 i)))
        (by fun_prop)) P) :
    HasCondDistrib o (fun ω => ((x ω, fun i => a i (e i (x ω), o ω i)), b ω))
      ((pi (fun i => (observe (κ i) (a i) (ha i)).condKernel.comap
        (fun p : X × (∀ i, C i) => (e i p.1, p.2 i)) (by fun_prop))).prodMkRight B) P := by
  have hu := hasCondDistrib_local_update e he κ a ha ho
  let f : X × (∀ i, O i) → (X × (∀ i, C i)) × (∀ i, O i) :=
    fun p => ((p.1, fun i => a i (e i p.1, p.2 i)), p.2)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have heq : (L.prodMkRight (∀ i, O i)).comap f hf =
      L.comap (fun p : X × (∀ i, O i) => (p.1, fun i => a i (e i p.1, p.2 i)))
        (by fun_prop) := by
    ext p : 1
    rfl
  have hb' : HasCondDistrib b (fun ω => (x ω, o ω))
      ((L.prodMkRight (∀ i, O i)).comap f hf) P := by rw [heq]; exact hb
  exact screening hu L hb'.comp_right

end LocalConditioning

namespace ArrayObjects.Object.Rolled

section
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def parameterEquiv (R : Finset I) (n : ℕ) :
    Arr I (Parameter M R) n ≃ᵐ (Arr I M.U (n + 1) × (R → Arr I M.Y n)) where
  toFun p := (fun v => (p (Fin.tail v)).1 (v 0), fun c w => (p w).2 c)
  invFun p w := (fun c => p.1 (Fin.cons c w), fun c => p.2 c w)
  left_inv p := by funext w; rfl
  right_inv p := by apply Prod.ext <;> funext v <;> simp
  measurable_toFun := by
    exact (Measurable.of_eval (fun _ => (measurable_pi_apply _).comp
      (measurable_fst.comp (measurable_pi_apply _)))).prodMk
      (Measurable.of_eval (fun _ => Measurable.of_eval (fun _ =>
        (measurable_pi_apply _).comp (measurable_snd.comp (measurable_pi_apply _)))))
  measurable_invFun := by
    exact Measurable.of_eval (fun _ =>
      (Measurable.of_eval (fun _ => (measurable_pi_apply _).comp measurable_fst)).prodMk
        (Measurable.of_eval (fun _ => (measurable_pi_apply _).comp
          ((measurable_pi_apply _).comp measurable_snd))))

def parents (R : Finset I) (n : ℕ) (y : Arr I M.Y (n + 1)) : R → Arr I M.Y n :=
  fun c => plane n 0 c y
@[fun_prop] lemma measurable_parents (R : Finset I) (n : ℕ) : Measurable (parents M R n) :=
  Measurable.of_eval (fun _ => measurable_plane _ _ _)

lemma parameterEquiv_observation (R : Finset I) (n : ℕ) :
    parameterEquiv M R n ∘ amap (parameter M R) n ∘ roll n =
      fun y => (amap M.par (n + 1) y, parents M R n y) := by
  funext y
  apply Prod.ext
  · funext v; simp [parameterEquiv, amap, parameter, roll]
  · funext c w; simp [parameterEquiv, amap, parameter, roll, parents, plane,
      Fin.insertNth_zero']

def posterior (R : Finset I) (n : ℕ) :
    Kernel (Arr I M.U (n + 1) × (R → Arr I M.Y n)) (Arr I M.Y (n + 1)) :=
  (LocalConditioning.observe (M.ownKernel (n + 1))
    (fun p => parents M R n p.2) ((measurable_parents M R n).comp measurable_snd)).condKernel
instance posterior_markov (R : Finset I) (n : ℕ) : IsMarkovKernel (posterior M R n) := by
  unfold posterior
  infer_instance

def ownPosterior (R : Finset I) (n : ℕ) :
    Kernel (Arr I (Parameter M R) n) (Arr I (State M) n) :=
  ((posterior M R n).map (roll n)).comap (parameterEquiv M R n)
    (parameterEquiv M R n).measurable
instance ownPosterior_markov (R : Finset I) (n : ℕ) : IsMarkovKernel (ownPosterior M R n) := by
  unfold ownPosterior
  let := Kernel.IsMarkovKernel.map (posterior M R n) (roll n).measurable
  infer_instance

lemma roll_symm_preserving (n : ℕ) :
    MeasurePreserving (roll (I := I) (Y := M.Y) n).symm (law M n) (M.law (n + 1)) := by
  refine ⟨(roll n).symm.measurable, ?_⟩
  rw [law, Measure.map_map (roll n).symm.measurable (roll n).measurable]
  simp

lemma ownPosterior_conditional (R : Finset I) (n : ℕ) :
    HasCondDistrib id (amap (parameter M R) n) (ownPosterior M R n) (law M n) := by
  have h := LocalConditioning.hasCondDistrib_posterior (M.ownKernel_conditional (n + 1))
    (fun p => parents M R n p.2) ((measurable_parents M R n).comp measurable_snd)
  change HasCondDistrib id
    (fun y => (amap M.par (n + 1) y, parents M R n y)) (posterior M R n) (M.law _) at h
  have h' := (h.comp_left (roll n).measurable).measurableEquiv_comp_right
    (parameterEquiv M R n).symm
  have hobs : (parameterEquiv M R n).symm ∘
      (fun y => (amap M.par (n + 1) y, parents M R n y)) =
        amap (parameter M R) n ∘ roll n := by
    rw [← parameterEquiv_observation]
    funext y
    exact (parameterEquiv M R n).symm_apply_apply _
  rw [hobs] at h'
  have hout := ConditionalTransport.pullback (roll_symm_preserving M n)
    ((measurable_amap (measurable_parameter M R) n).comp (roll n).measurable) h'
  simpa only [ownPosterior, MeasurableEquiv.symm_symm, Function.comp_assoc, MeasurableEquiv.self_comp_symm,
    Function.comp_id, Function.id_comp] using hout

end

variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

abbrev ParentOutside (R : Finset I) (n : ℕ) (j : I) :=
  Arr I M.U (n + 2) × (Outside j → R → Arr I M.Y n)
abbrev ScreenData (R : Finset I) (n : ℕ) (j : I) :=
  ParentOutside M R n j × (R → Arr I M.Y n)

def parentOutside (R : Finset I) (n : ℕ) (j : I) (p : RawData M n j) :
    ParentOutside M R n j := (p.1, fun k => parents M R n (p.2 k))
omit [DecidableEq I] in
@[fun_prop] lemma measurable_parentOutside (R : Finset I) (n : ℕ) (j : I) :
    Measurable (parentOutside M R n j) := by
  unfold parentOutside
  fun_prop

def parentRow (R : Finset I) (n : ℕ) (j : I) (c : R) (p : ParentOutside M R n j) :
    OldData M n j := (plane (n + 1) 0 c p.1, fun k => p.2 k c)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_parentRow (R : Finset I) (n : ℕ) (j : I) (c : R) :
    Measurable (parentRow M R n j c) := by
  unfold parentRow
  fun_prop

def parentsKernel (R : Finset I) (n : ℕ) (j : I) :
    Kernel (ParentOutside M R n j) (R → Arr I M.Y n) :=
  FiniteKernel.pi (fun c : R =>
    (condDistrib (plane n (Fin.last n) j) (oldData M n j) (M.law (n + 1))).comap
      (parentRow M R n j c) (measurable_parentRow M R n j c))
instance parentsKernel_markov (R : Finset I) (n : ℕ) (j : I) :
    IsMarkovKernel (parentsKernel M R n j) := by
  unfold parentsKernel
  infer_instance

omit [DecidableEq I] in
lemma parentsKernel_comap (R : Finset I) (n : ℕ) (j : I) :
    (parentsKernel M R n j).comap (parentOutside M R n j)
      (measurable_parentOutside M R n j) =
        FiniteKernel.pi (fun c : R => rowKernel M n j c) := by
  ext p : 1
  rfl

def screenData (R : Finset I) (n : ℕ) (j : I) (y : Arr I M.Y (n + 2)) :
    ScreenData M R n j :=
  (parentOutside M R n j (rawData M n j y), fun c => missingRow M n j c y)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_screenData (R : Finset I) (n : ℕ) (j : I) :
    Measurable (screenData M R n j) := by
  unfold screenData
  exact ((measurable_parentOutside M R n j).comp (measurable_rawData M n j)).prodMk
    (Measurable.of_eval (fun c => measurable_missingRow M n j c))

def screenKernel (R : Finset I) (n : ℕ) (j : I) :
    Kernel (ScreenData M R n j) (Outside j → Arr I M.Y (n + 1)) :=
  (FiniteKernel.pi (fun k : Outside j => (posterior M R n).comap
    (fun p : ParentOutside M R n j => (plane (n + 1) (Fin.last (n + 1)) k p.1, p.2 k))
      (by fun_prop))).prodMkRight (R → Arr I M.Y n)
instance screenKernel_markov (R : Finset I) (n : ℕ) (j : I) :
    IsMarkovKernel (screenKernel M R n j) := by
  unfold screenKernel
  infer_instance

lemma screen_conditional (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I)
    (ih : ∀ S : Finset I, S ⊂ R → IsConditional M S) (n : ℕ) (j : I) :
    HasCondDistrib (planes (n + 1) (Outside j)) (screenData M R n j)
      (screenKernel M R n j) (M.law (n + 2)) := by
  have hproper : Outside j ≠ Finset.univ := by
    intro he
    have hj : j ∈ Outside j := he.symm ▸ Finset.mem_univ j
    simp [Outside] at hj
  have hb := parent_joint M hM R hR ih n j
  rw [← parentsKernel_comap] at hb
  exact LocalConditioning.local_conditioning
    (fun k : Outside j => plane (n + 1) (Fin.last (n + 1)) (k : I))
    (fun _ => measurable_plane _ _ _) (fun _ => M.ownKernel (n + 1))
    (fun _ => fun p => parents M R n p.2)
    (fun _ => (measurable_parents M R n).comp measurable_snd)
    (parentsKernel M R n j) (M.planes_conditional (n + 1) (Outside j) hproper) hb

def screenEquiv (R : Finset I) (n : ℕ) (j : I) :
    Arr I (Parameter M R) (n + 1) ≃ᵐ ScreenData M R n j where
  toFun p := ((fun v => (p (Fin.tail v)).1 (v 0),
    fun k c v => (p (Fin.snoc v (k : I))).2 c), fun c v => (p (Fin.snoc v j)).2 c)
  invFun p w := (fun c => p.1.1 (Fin.cons c w), fun c =>
    if h : w (Fin.last n) = j then p.2 c (Fin.init w) else
      p.1.2 ⟨w (Fin.last n), by simp [Outside, h]⟩ c (Fin.init w))
  left_inv p := by
    funext w
    apply Prod.ext
    · rfl
    · funext c
      dsimp only
      split_ifs with h
      · rw [← h, Fin.snoc_init_self]
      · rw [Fin.snoc_init_self]
  right_inv p := by
    apply Prod.ext
    · apply Prod.ext
      · funext v; simp
      · funext k c v
        have hk : (k : I) ≠ j :=
          @Finset.ne_of_mem_erase I (fun a b => Classical.propDecidable (a = b))
            _ _ _ k.property
        simp [hk]
    · funext c v
      simp
  measurable_toFun := by
    exact ((Measurable.of_eval (fun _ => (measurable_pi_apply _).comp
      (measurable_fst.comp (measurable_pi_apply _)))).prodMk
      (Measurable.of_eval (fun _ => Measurable.of_eval (fun _ =>
        Measurable.of_eval (fun _ => (measurable_pi_apply _).comp
          (measurable_snd.comp (measurable_pi_apply _))))))).prodMk
      (Measurable.of_eval (fun _ => Measurable.of_eval (fun _ =>
        (measurable_pi_apply _).comp (measurable_snd.comp (measurable_pi_apply _)))))
  measurable_invFun := by
    apply Measurable.of_eval
    intro w
    apply Measurable.prodMk
    · fun_prop
    · apply Measurable.of_eval
      intro c
      split_ifs <;> fun_prop

lemma screenEquiv_observation (R : Finset I) (n : ℕ) (j : I) :
    screenEquiv M R n j ∘ amap (parameter M R) (n + 1) ∘ roll (n + 1) =
      screenData M R n j := by
  funext y
  apply Prod.ext
  · apply Prod.ext
    · funext v; simp [screenEquiv, screenData, parentOutside, rawData, amap, parameter, roll]
    · funext k c v
      simp [screenEquiv, screenData, parentOutside, rawData, parents, planes, plane,
        amap, parameter, roll, Fin.insertNth_zero', Fin.insertNth_last', cons_snoc]
  · funext c v
    simp [screenEquiv, screenData, amap, parameter, roll, missingRow, plane,
      Fin.insertNth_zero', Fin.insertNth_last']


lemma screen_plane_parameters (R : Finset I) (n : ℕ) (j : I)
    (p : Arr I (Parameter M R) (n + 1)) (k : Outside j) :
    (plane (n + 1) (Fin.last (n + 1)) (k : I) (screenEquiv M R n j p).1.1,
      (screenEquiv M R n j p).1.2 k) =
        parameterEquiv M R n (plane n (Fin.last n) (k : I) p) := by
  apply Prod.ext
  · funext v
    obtain ⟨c, w, rfl⟩ := Fin.exists_cons v
    simp [screenEquiv, parameterEquiv, plane, Fin.insertNth_last', ← cons_snoc]
  · funext c w
    simp [screenEquiv, parameterEquiv, plane, Fin.insertNth_last']

lemma screenKernel_roll (R : Finset I) (n : ℕ) (j : I) :
    ((screenKernel M R n j).map (fun z k => roll n (z k))).comap
      (screenEquiv M R n j) (screenEquiv M R n j).measurable =
    FiniteKernel.pi (fun k : Outside j => (ownPosterior M R n).comap
      (plane n (Fin.last n) k) (measurable_plane _ _ _)) := by
  ext p : 1
  rw [Kernel.comap_apply]
  have hm : Measurable (fun z : Outside j → Arr I M.Y (n + 1) =>
      fun k => roll n (z k)) := by fun_prop
  rw [Kernel.map_apply _ hm]
  change (Measure.pi (fun k : Outside j => posterior M R n
    (plane (n + 1) (Fin.last (n + 1)) (k : I) (screenEquiv M R n j p).1.1,
      (screenEquiv M R n j p).1.2 k))).map (fun z k => roll n (z k)) = _
  rw [Measure.pi_map_pi (fun _ => (roll n).measurable.aemeasurable)]
  congr 1
  funext k
  rw [screen_plane_parameters]
  change _ = ((posterior M R n).map (roll n)) _
  rw [Kernel.map_apply _ (roll n).measurable]

lemma outside_conditional (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I)
    (ih : ∀ S : Finset I, S ⊂ R → IsConditional M S) (n : ℕ) (j : I) :
    HasCondDistrib (planes n (Outside j)) (amap (parameter M R) (n + 1))
      (FiniteKernel.pi (fun k : Outside j => (ownPosterior M R n).comap
        (plane n (Fin.last n) k) (measurable_plane _ _ _))) (law M (n + 1)) := by
  have h := screen_conditional M hM R hR ih n j
  have h' := (h.comp_left (Measurable.of_eval (fun k =>
    (roll n).measurable.comp (measurable_pi_apply k)))).measurableEquiv_comp_right
      (screenEquiv M R n j).symm
  change HasCondDistrib ((fun z k => roll n (z k)) ∘ planes (n + 1) (Outside j))
    ((screenEquiv M R n j).symm ∘ screenData M R n j)
    (((screenKernel M R n j).map (fun z k => roll n (z k))).comap
      (screenEquiv M R n j) (screenEquiv M R n j).measurable) (M.law (n + 2)) at h'
  rw [screenKernel_roll, ← planes_roll] at h'
  have hobs : (screenEquiv M R n j).symm ∘ screenData M R n j =
      amap (parameter M R) (n + 1) ∘ roll (n + 1) := by
    rw [← screenEquiv_observation]
    funext y
    exact (screenEquiv M R n j).symm_apply_apply _
  rw [hobs] at h'
  have hout := ConditionalTransport.pullback (roll_symm_preserving M (n + 1))
    ((measurable_amap (measurable_parameter M R) _).comp (roll (n + 1)).measurable) h'
  simpa only [Function.comp_assoc, MeasurableEquiv.self_comp_symm, Function.comp_id] using hout


end ArrayObjects.Object.Rolled

namespace FiniteKernel
open MeasureTheory ProbabilityTheory

lemma measure_pi_precomp {ι τ : Type*} [Fintype ι] [Fintype τ]
    {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (Y i)) [∀ i, IsProbabilityMeasure (μ i)] (e : τ ↪ ι) :
    (Measure.pi μ).map (fun y i => y (e i)) = Measure.pi (fun i => μ (e i)) := by
  have hi : iIndepFun (fun i : ι => Function.eval i) (Measure.pi μ) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  rw [(hi.precomp e.injective).map_fun_eq_pi_map
    (fun i => (measurable_pi_apply (e i)).aemeasurable)]
  congr 1
  funext i
  exact (measurePreserving_eval μ (e i)).map_eq

lemma pi_precomp {ι τ X : Type*} [Fintype ι] [Fintype τ]
    {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)] [MeasurableSpace X]
    (κ : ∀ i, Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)] (e : τ ↪ ι) :
    (pi κ).map (fun y i => y (e i)) = pi (fun i => κ (e i)) := by
  ext x : 1
  rw [Kernel.map_apply _ (by fun_prop)]
  exact measure_pi_precomp _ e

end FiniteKernel

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma proper_conditional (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I)
    (ih : ∀ S : Finset I, S ⊂ R → IsConditional M S) (n : ℕ)
    (J : Finset I) (hJ : J ≠ Finset.univ) :
    HasCondDistrib (planes n J) (amap (parameter M R) (n + 1))
      (FiniteKernel.pi (fun k : J => (ownPosterior M R n).comap
        (plane n (Fin.last n) k) (measurable_plane _ _ _))) (law M (n + 1)) := by
  have hj : ∃ j, j ∉ J := by
    by_contra! h
    exact hJ (Finset.eq_univ_of_forall h)
  obtain ⟨j, hj⟩ := hj
  let e : J ↪ Outside j := ⟨fun k => ⟨k, by
    have hk : (k : I) ≠ j := by intro he; exact hj (he ▸ k.property)
    simpa [Outside] using And.intro hk (Finset.mem_univ (k : I))⟩,
      fun x y h => Subtype.ext (show (x : I) = (y : I) from
        congrArg (fun v : Outside j => (v : I)) h)⟩
  have h := (outside_conditional M hM R hR ih n j).comp_left
    (show Measurable (fun z : Outside j → Arr I (State M) n => fun k => z (e k)) by fun_prop)
  rw [FiniteKernel.pi_precomp] at h
  exact h

omit [DecidableEq I] in
lemma parameter_plane_preserving (R : Finset I) (n : ℕ) (j : I) :
    MeasurePreserving (plane n (Fin.last n) j)
      ((law M (n + 1)).map (amap (parameter M R) (n + 1)))
      ((law M n).map (amap (parameter M R) n)) := by
  refine ⟨measurable_plane _ _ _, ?_⟩
  rw [Measure.map_map (measurable_plane _ _ _)
    (measurable_amap (measurable_parameter M R) _), plane_amap,
    ← Measure.map_map (measurable_amap (measurable_parameter M R) _)
      (measurable_plane _ _ _), consistent]

lemma conditional_step (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I)
    (ih : ∀ S : Finset I, S ⊂ R → IsConditional M S) : IsConditional M R := by
  intro n J hJ
  have ho := condDistrib_ae_eq_of_measure_eq_compProd (ownPosterior_conditional M R n).aemeasurable_fst
    measurable_id.aemeasurable (ownPosterior_conditional M R n).map_eq
  have hp := condDistrib_ae_eq_of_measure_eq_compProd (proper_conditional M hM R hR ih n J hJ).aemeasurable_fst
    (measurable_planes n J).aemeasurable (proper_conditional M hM R hR ih n J hJ).map_eq
  have hplanes : ∀ᵐ p ∂(law M (n + 1)).map (amap (parameter M R) (n + 1)),
      ∀ j : J, condDistrib id (amap (parameter M R) n) (law M n)
        (plane n (Fin.last n) j p) = ownPosterior M R n (plane n (Fin.last n) j p) := by
    rw [ae_all_iff]
    intro j
    exact (parameter_plane_preserving M R n j).quasiMeasurePreserving.ae_eq_comp ho
  filter_upwards [hp, hplanes] with p hp he
  exact hp.trans (congrArg Measure.pi (funext fun j => (he j).symm))

theorem isConditional (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I) : IsConditional M R := by
  have hall : ∀ R : Finset I, R.card + 2 ≤ Fintype.card I → IsConditional M R := by
    intro R
    refine Finset.strongInductionOn R ?_
    intro R ih hc
    apply conditional_step M hM R hc
    intro S hS
    exact ih S hS (le_trans (Nat.add_le_add_right (Finset.card_le_card hS.1) 2) hc)
  exact hall R hR

lemma insert_proper (R : Finset I) (hR : R.card + 2 ≤ Fintype.card I)
    (a : I) (ha : a ∉ R) : insert a R ≠ Finset.univ := by
  intro he
  have h := congrArg Finset.card he
  rw [Finset.card_insert_of_notMem ha, Finset.card_univ] at h
  omega

def object (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I) (a : I) (ha : a ∉ R) : Object I base :=
  makeObject M R (isConditional M hM R hR) a ha (insert_proper R hR a ha)

def objectExtension (hM : M.IsSaturated) (R : Finset I)
    (hR : R.card + 2 ≤ Fintype.card I) (a : I) (ha : a ∉ R) :
    Extension M (object M hM R hR a ha) :=
  extension M R (isConditional M hM R hR) a ha (insert_proper R hR a ha)


end ArrayObjects.Object.Rolled

namespace ArrayObjects.Object
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in
noncomputable def parameterLaw (n : ℕ) : Measure (Arr I M.U n) :=
  (M.law n).map (amap M.par n)
omit [DecidableEq I] in
instance parameterLaw_probability (n : ℕ) : IsProbabilityMeasure (M.parameterLaw n) :=
  (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (measurable_amap M.measurable_par n).aemeasurable

omit [DecidableEq I] in

noncomputable def parameterCoordinateKernel (a : I) :
    Kernel (Arr I M.U 0) (Arr I M.U 1) :=
  condDistrib id (plane 0 0 a) (M.parameterLaw 1)
omit [DecidableEq I] in
instance parameterCoordinateKernel_markov (a : I) :
    IsMarkovKernel (M.parameterCoordinateKernel a) := by
  unfold parameterCoordinateKernel
  infer_instance

end ArrayObjects.Object

namespace ArrayObjects.Object
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma parameterLaw_consistent (n : ℕ) (a : Fin (n + 1)) (i : I) :
    (M.parameterLaw (n + 1)).map (plane n a i) = M.parameterLaw n := by
  unfold parameterLaw
  rw [Measure.map_map (measurable_plane _ _ _) (measurable_amap M.measurable_par _),
    plane_amap, ← Measure.map_map (measurable_amap M.measurable_par _)
      (measurable_plane _ _ _), M.consistent]

end ArrayObjects.Object

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

abbrev ParentData (R : Finset I) (n : ℕ) :=
  Arr I M.U (n + 2) × (R → Arr I M.Y (n + 1))

def parentData (R : Finset I) (n : ℕ) (y : Arr I M.Y (n + 2)) : ParentData M R n :=
  (amap M.par (n + 2) y, parents M R (n + 1) y)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_parentData (R : Finset I) (n : ℕ) :
    Measurable (parentData M R n) :=
  (measurable_amap M.measurable_par _).prodMk (measurable_parents M R _)

def columnKernel (R : Finset I) (n : ℕ) (j : I) :
    Kernel (ParentData M R n) (Arr I M.Y (n + 1)) :=
  ((ownPosterior M R n).map (roll n).symm).comap
    (plane n (Fin.last n) j ∘ (parameterEquiv M R (n + 1)).symm)
    ((measurable_plane _ _ _).comp (parameterEquiv M R (n + 1)).symm.measurable)
instance columnKernel_markov (R : Finset I) (n : ℕ) (j : I) :
    IsMarkovKernel (columnKernel M R n j) := by
  unfold columnKernel
  have : IsMarkovKernel ((ownPosterior M R n).map (roll n).symm) :=
    Kernel.IsMarkovKernel.map _ (roll n).symm.measurable
  infer_instance


def cells (A J : Finset I) (n : ℕ) (y : Arr I M.Y (n + 2)) : J → A → Arr I M.Y n :=
  fun j a => missingRow M n j a y
omit [DecidableEq I] in
@[fun_prop] lemma measurable_cells (A J : Finset I) (n : ℕ) : Measurable (cells M A J n) :=
  Measurable.of_eval (fun _ => Measurable.of_eval (fun _ => measurable_missingRow M _ _ _))

def rowRestrict (A J : Finset I) (n : ℕ) (y : A → Arr I M.Y (n + 1)) : J → A → Arr I M.Y n :=
  fun j a => plane n (Fin.last n) j (y a)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_rowRestrict (A J : Finset I) (n : ℕ) :
    Measurable (rowRestrict M A J n) := by
  unfold rowRestrict
  exact Measurable.of_eval (fun _ => Measurable.of_eval (fun _ =>
    (measurable_plane _ _ _).comp (measurable_pi_apply _)))

def columnRestrict (A J : Finset I) (n : ℕ) (y : J → Arr I M.Y (n + 1)) : J → A → Arr I M.Y n :=
  fun j a => plane n 0 a (y j)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_columnRestrict (A J : Finset I) (n : ℕ) :
    Measurable (columnRestrict M A J n) := by
  unfold columnRestrict
  exact Measurable.of_eval (fun _ => Measurable.of_eval (fun _ =>
    (measurable_plane _ _ _).comp (measurable_pi_apply _)))

def rowFamilyKernel (A : Finset I) (n : ℕ) :
    Kernel (Arr I M.U (n + 2)) (A → Arr I M.Y (n + 1)) :=
  FiniteKernel.pi (fun a : A => (M.ownKernel (n + 1)).comap
    (plane (n + 1) 0 a) (measurable_plane _ _ _))
instance rowFamilyKernel_markov (A : Finset I) (n : ℕ) :
    IsMarkovKernel (rowFamilyKernel M A n) := by unfold rowFamilyKernel; infer_instance

def groupMarginal (A J : Finset I) (n : ℕ) :
    Kernel (Arr I M.U (n + 2)) (J → A → Arr I M.Y n) :=
  (rowFamilyKernel M A n).map (rowRestrict M A J n)
instance groupMarginal_markov (A J : Finset I) (n : ℕ) :
    IsMarkovKernel (groupMarginal M A J n) :=
  Kernel.IsMarkovKernel.map _ (measurable_rowRestrict M A J n)


abbrev GroupData (A C : Finset I) (n : ℕ) :=
  Arr I M.U (n + 2) × (C → A → Arr I M.Y n)
abbrev WholeGroupData (P C : Finset I) (n : ℕ) :=
  ParentData M P n × (C → Arr I M.Y (n + 1))

def groupData (A C : Finset I) (n : ℕ) (y : Arr I M.Y (n + 2)) : GroupData M A C n :=
  (amap M.par (n + 2) y, cells M A C n y)
def wholeGroupData (P C : Finset I) (n : ℕ) (y : Arr I M.Y (n + 2)) : WholeGroupData M P C n :=
  (parentData M P n y, planes (n + 1) C y)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_groupData (A C : Finset I) (n : ℕ) :
    Measurable (groupData M A C n) :=
  (measurable_amap M.measurable_par _).prodMk (measurable_cells M A C n)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_wholeGroupData (P C : Finset I) (n : ℕ) :
    Measurable (wholeGroupData M P C n) :=
  (measurable_parentData M P n).prodMk (measurable_planes _ _)

def groupSelect (P A C : Finset I) (n : ℕ) (p : WholeGroupData M P C n) : GroupData M A C n :=
  (p.1.1, columnRestrict M A C n p.2)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_groupSelect (P A C : Finset I) (n : ℕ) :
    Measurable (groupSelect M P A C n) :=
  (measurable_fst.comp measurable_fst).prodMk ((measurable_columnRestrict M A C n).comp measurable_snd)

def revealParent (P : Finset I) (n : ℕ) (j : I) (p : RevealData M P n j) : ParentData M P n :=
  parameterEquiv M P (n + 1) (revealToRoll M P n j p).1
@[fun_prop] lemma measurable_revealParent (P : Finset I) (n : ℕ) (j : I) :
    Measurable (revealParent M P n j) :=
  (parameterEquiv M P (n + 1)).measurable.comp
    (measurable_fst.comp (measurable_revealToRoll M P n j))

def revealSelect (P A C J : Finset I) (n : ℕ) (j : I)
    (hC : C ⊆ Outside j) (hJ : J ⊆ Outside j) (p : RevealData M P n j) :
    WholeGroupData M P C n × (J → A → Arr I M.Y n) :=
  ((revealParent M P n j p, fun c => p.1.2 ⟨c, hC c.property⟩),
    fun k a => plane n 0 a (p.1.2 ⟨k, hJ k.property⟩))
@[fun_prop] lemma measurable_revealSelect (P A C J : Finset I) (n : ℕ) (j : I)
    (hC : C ⊆ Outside j) (hJ : J ⊆ Outside j) :
    Measurable (revealSelect M P A C J n j hC hJ) := by
  unfold revealSelect
  exact ((measurable_revealParent M P n j).prodMk (by fun_prop)).prodMk (by fun_prop)

def groupLastData (A C J : Finset I) (n : ℕ) (j : I) (hCJ : C ∪ J = Outside j)
    (a : A) (p : GroupData M A C n × (J → A → Arr I M.Y n)) : OldData M n j :=
  (plane (n + 1) 0 a p.1.1, fun k =>
    if h : (k : I) ∈ C then p.1.2 ⟨k, h⟩ a else
      p.2 ⟨k, (Finset.mem_union.mp (hCJ.symm ▸ k.property)).resolve_left h⟩ a)
@[fun_prop] lemma measurable_groupLastData (A C J : Finset I) (n : ℕ) (j : I)
    (hCJ : C ∪ J = Outside j) (a : A) : Measurable (groupLastData M A C J n j hCJ a) := by
  unfold groupLastData
  apply Measurable.prodMk (by fun_prop)
  apply Measurable.of_eval
  intro k
  split_ifs <;> fun_prop

def groupLastKernel (A C J : Finset I) (n : ℕ) (j : I) (hCJ : C ∪ J = Outside j) :
    Kernel (GroupData M A C n × (J → A → Arr I M.Y n)) (A → Arr I M.Y n) :=
  FiniteKernel.pi (fun a =>
    (condDistrib (plane n (Fin.last n) j) (oldData M n j) (M.law (n + 1))).comap
      (groupLastData M A C J n j hCJ a) (measurable_groupLastData M A C J n j hCJ a))
instance groupLastKernel_markov (A C J : Finset I) (n : ℕ) (j : I)
    (hCJ : C ∪ J = Outside j) : IsMarkovKernel (groupLastKernel M A C J n j hCJ) := by
  unfold groupLastKernel
  infer_instance

def wholeLastSelect (P A C J : Finset I) (n : ℕ)
    (p : WholeGroupData M P C n × (J → A → Arr I M.Y n)) :
    GroupData M A C n × (J → A → Arr I M.Y n) :=
  (groupSelect M P A C n p.1, p.2)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_wholeLastSelect (P A C J : Finset I) (n : ℕ) :
    Measurable (wholeLastSelect M P A C J n) :=
  ((measurable_groupSelect M P A C n).comp measurable_fst).prodMk measurable_snd

end ArrayObjects.Object.Rolled

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def joinOutput (A J : Finset I) (n : ℕ) (j : I)
    (p : (J → A → Arr I M.Y n) × (A → Arr I M.Y n)) :
    ↥(insert j J) → A → Arr I M.Y n := fun k =>
  if h : (k : I) = j then p.2 else p.1 ⟨k, (Finset.mem_insert.mp k.property).resolve_left h⟩
@[fun_prop] lemma measurable_joinOutput (A J : Finset I) (n : ℕ) (j : I) :
    Measurable (joinOutput M A J n j) := by
  unfold joinOutput
  apply Measurable.of_eval
  intro k
  split_ifs <;> fun_prop

end ArrayObjects.Object.Rolled
end

namespace ArrayObjects
open MeasureTheory ProbabilityTheory
universe u
variable {I Y Z : Type u} [MeasurableSpace Y] [MeasurableSpace Z]

def amapEquiv (E : Y ≃ᵐ Z) (n : ℕ) : Arr I Y n ≃ᵐ Arr I Z n where
  toFun := amap E n
  invFun := amap E.symm n
  left_inv x := by funext a; exact E.symm_apply_apply _
  right_inv x := by funext a; exact E.apply_symm_apply _
  measurable_toFun := measurable_amap E.measurable n
  measurable_invFun := measurable_amap E.symm.measurable n

end ArrayObjects

open MeasureTheory ProbabilityTheory

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Joinings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

namespace JoiningOperator

open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal


section
variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {τ : Measure Z}
  {x : Ω → X} {y : Ω → Y} {z : X → Z}

abbrev pull (hx : MeasurePreserving x μ ν) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ x hx).toContinuousLinearMap

def operator (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ) :
    Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ν := (pull hx).adjoint ∘L pull hy

end


end JoiningOperator

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory

section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def tupleUnion {Z : Type*} (R S : Finset I) (v : (R → Z) × (S → Z)) : ↥(R ∪ S) → Z :=
  fun i => if h : (i : I) ∈ R then v.1 ⟨i,h⟩ else v.2 ⟨i,(Finset.mem_union.mp i.property).resolve_left h⟩
omit [Fintype I] in
@[fun_prop] lemma measurable_tupleUnion {Z : Type*} [MeasurableSpace Z] (R S : Finset I) :
    Measurable (tupleUnion (Z := Z) R S) := by
  unfold tupleUnion
  apply Measurable.of_eval
  intro i
  split_ifs <;> fun_prop

def tupleSelect {Z : Type*} (R S : Finset I) (h : R ⊆ S) (v : S → Z) : R → Z :=
  fun i => v ⟨i,h i.property⟩
omit [Fintype I] [DecidableEq I] in
@[fun_prop] lemma measurable_tupleSelect {Z : Type*} [MeasurableSpace Z]
    (R S : Finset I) (h : R ⊆ S) : Measurable (tupleSelect (Z := Z) R S h) := by
  unfold tupleSelect
  fun_prop

def splitOwnData (P A R S : Finset I) (n : ℕ)
    (v : WholeGroupData M P R n × (S → A → Arr I M.Y n)) : GroupData M A (R ∪ S) n :=
  (v.1.1.1, tupleUnion R S (columnRestrict M A R n v.1.2, v.2))
@[fun_prop] lemma measurable_splitOwnData (P A R S : Finset I) (n : ℕ) :
    Measurable (splitOwnData M P A R S n) := by
  unfold splitOwnData
  fun_prop

def splitRowKernel (P A R S D : Finset I) (n : ℕ) :
    Kernel (WholeGroupData M P R n × (S → A → Arr I M.Y n)) (D → A → Arr I M.Y n) :=
  (condDistrib (cells M A D n) (groupData M A (R ∪ S) n) (M.law (n+2))).comap
    (splitOwnData M P A R S n) (measurable_splitOwnData M P A R S n)
instance splitRowKernel_markov (P A R S D : Finset I) (n : ℕ) :
    IsMarkovKernel (splitRowKernel M P A R S D n) := by unfold splitRowKernel; infer_instance

abbrev squareFibre (P R : Finset I) (n : ℕ) :=
  condDistrib id (wholeGroupData M P R n) (M.law (n+2))
abbrev cellLaw (A S : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :=
  groupMarginal M A S n e

end

universe u
variable {I : Type u} [Fintype I] [retained7 : DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def rowPairKernel (A R S D : Finset I) (n : ℕ) :
    Kernel (GroupData M A R n) ((S → A → Arr I M.Y n) × (D → A → Arr I M.Y n)) :=
  condDistrib (fun y => (cells M A S n y,cells M A D n y)) (groupData M A R n) (M.law (n+2))
instance rowPairKernel_markov (A R S D : Finset I) (n : ℕ) :
    IsMarkovKernel (rowPairKernel M A R S D n) := by unfold rowPairKernel; infer_instance

def columnGroupKernel (P S : Finset I) (n : ℕ) :
    Kernel (GroupData M P S n) (S → Arr I M.Y (n+1)) :=
  FiniteKernel.pi (fun j : S => (posterior M P n).comap
    (fun v => (plane (n+1) (Fin.last (n+1)) j v.1, fun p : P => v.2 j p)) (by fun_prop))
instance columnGroupKernel_markov (P S : Finset I) (n : ℕ) :
    IsMarkovKernel (columnGroupKernel M P S n) := by unfold columnGroupKernel; infer_instance

def columnOwnData (P R S : Finset I) (n : ℕ) (u : WholeGroupData M P R n) : GroupData M P S n :=
  (u.1.1,rowRestrict M P S n u.1.2)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_columnOwnData (P R S : Finset I) (n : ℕ) :
    Measurable (columnOwnData M P R S n) := by unfold columnOwnData; fun_prop

end ArrayObjects.Object.Rolled

namespace JoiningOperator
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace

section

variable {U X Y : Type*} [MeasurableSpace U] [MeasurableSpace X] [MeasurableSpace Y]
  (κ : Kernel U (X × Y)) (ν : Measure X) (ρ : Measure Y)

def family (u : U) : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ν := by
  classical
  exact if h : MeasurePreserving Prod.fst (κ u) ν ∧ MeasurePreserving Prod.snd (κ u) ρ
  then operator h.1 h.2 else 0

end


end JoiningOperator

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def columnPairKernel (P A B S : Finset I) (n : ℕ) :
    Kernel (GroupData M P S n) ((S → A → Arr I M.Y n) × (S → B → Arr I M.Y n)) :=
  (columnGroupKernel M P S n).map (fun y => (columnRestrict M A S n y,columnRestrict M B S n y))
instance columnPairKernel_markov (P A B S : Finset I) (n : ℕ) :
    IsMarkovKernel (columnPairKernel M P A B S n) :=
  Kernel.IsMarkovKernel.map _ (by fun_prop)

def rowEdge (A R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2))
    (p : GroupData M A R n) : Lp ℂ 2 (cellLaw M A D n e) →L[ℂ] Lp ℂ 2 (cellLaw M A S n e) :=
  JoiningOperator.family (rowPairKernel M A R S D n)
    (cellLaw M A S n e) (cellLaw M A D n e) p

def columnEdge (P A B S : Finset I) (n : ℕ) (e : Arr I M.U (n+2))
    (p : GroupData M P S n) : Lp ℂ 2 (cellLaw M B S n e) →L[ℂ] Lp ℂ 2 (cellLaw M A S n e) :=
  JoiningOperator.family (columnPairKernel M P A B S n)
    (cellLaw M A S n e) (cellLaw M B S n e) p

end ArrayObjects.Object.Rolled
end

section
open MeasureTheory ProbabilityTheory

namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)


def fibreRowEdge (A R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2))
    (x : R → A → Arr I M.Y n) : Lp ℂ 2 (cellLaw M A D n e) →L[ℂ] Lp ℂ 2 (cellLaw M A S n e) :=
  rowEdge M A R S D n e (e,x)

def fibreColumnEdge (P A B S : Finset I) (n : ℕ) (e : Arr I M.U (n+2))
    (c : S → P → Arr I M.Y n) : Lp ℂ 2 (cellLaw M B S n e) →L[ℂ] Lp ℂ 2 (cellLaw M A S n e) :=
  columnEdge M P A B S n e (e,c)

end ArrayObjects.Object.Rolled
end

section

open MeasureTheory Filter ContinuousLinearMap
open scoped InnerProductSpace Topology

section EssentialKernel
variable {X E H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

def essentialKernel (μ : Measure X) (A : X → E →L[ℂ] H) : Submodule ℂ E where
  carrier := {v | ∀ᵐ x ∂μ, A x v = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change ∀ᵐ x ∂μ, A x (v + w) = 0
    change ∀ᵐ x ∂μ, A x v = 0 at hv
    change ∀ᵐ x ∂μ, A x w = 0 at hw
    filter_upwards [hv, hw] with x hx hy
    simp [map_add, hx, hy]
  smul_mem' := by
    intro c v hv
    change ∀ᵐ x ∂μ, A x (c • v) = 0
    change ∀ᵐ x ∂μ, A x v = 0 at hv
    filter_upwards [hv] with x hx
    simp [hx]

end EssentialKernel

section EssentialRange
variable {X E H J : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

noncomputable def essentialRange (μ : Measure X) (F : X → E →L[ℂ] H) : Submodule ℂ H :=
  (essentialKernel μ (fun x => (F x).adjoint))ᗮ

lemma essentialRange.isClosed (μ : Measure X) (F : X → E →L[ℂ] H) :
    IsClosed (essentialRange μ F : Set H) := Submodule.isClosed_orthogonal _

instance essentialRange.completeSpace (μ : Measure X) (F : X → E →L[ℂ] H) :
    CompleteSpace (essentialRange μ F) := (essentialRange.isClosed μ F).completeSpace_coe

end EssentialRange

end

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
variable {X E H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def compress (A : E →L[ℂ] H) (V : Submodule ℂ E) (W : Submodule ℂ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection] : V →L[ℂ] W :=
  W.orthogonalProjectionOnto ∘L A ∘L V.subtypeL

end

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
variable {X E H J : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

instance submodule_completeSpace_inf (V W : Submodule ℂ H)
    [CompleteSpace V] [CompleteSpace W] : CompleteSpace (V ⊓ W : Submodule ℂ H) :=
by
  have hV : IsClosed (V : Set H) := (completeSpace_coe_iff_isComplete.mp inferInstance).isClosed
  have hW : IsClosed (W : Set H) := (completeSpace_coe_iff_isComplete.mp inferInstance).isClosed
  exact (hV.inter hW).completeSpace_coe

end

section
open MeasureTheory ContinuousLinearMap
variable {X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄]
  (μX : Measure X) (μY : Measure Y) (μC : Measure C) (μD : Measure D)
  (F : X → H₂ →L[ℂ] H₁) (G : Y → H₄ →L[ℂ] H₃)
  (K : C → H₃ →L[ℂ] H₁) (N : D → H₄ →L[ℂ] H₂)

def rectangleSpace₁ := essentialRange μX F ⊓ essentialRange μC K
def rectangleSpace₂ := essentialRange μX (fun x => (F x).adjoint) ⊓ essentialRange μD N
def rectangleSpace₃ := essentialRange μY G ⊓ essentialRange μC (fun c => (K c).adjoint)
def rectangleSpace₄ := essentialRange μY (fun y => (G y).adjoint) ⊓ essentialRange μD (fun d => (N d).adjoint)

instance instCompleteSpaceSubtypeMemSubmoduleComplexRectangleSpace₁ : CompleteSpace (rectangleSpace₁ μX μC F K) := by unfold rectangleSpace₁; infer_instance
instance instCompleteSpaceSubtypeMemSubmoduleComplexRectangleSpace₂ : CompleteSpace (rectangleSpace₂ μX μD F N) := by unfold rectangleSpace₂; infer_instance
instance instCompleteSpaceSubtypeMemSubmoduleComplexRectangleSpace₃ : CompleteSpace (rectangleSpace₃ μY μC G K) := by unfold rectangleSpace₃; infer_instance
instance instCompleteSpaceSubtypeMemSubmoduleComplexRectangleSpace₄ : CompleteSpace (rectangleSpace₄ μY μD G N) := by unfold rectangleSpace₄; infer_instance

def rectangleRestrictF (x : X) : rectangleSpace₂ μX μD F N →L[ℂ] rectangleSpace₁ μX μC F K :=
  compress (F x) _ _
def rectangleRestrictG (y : Y) : rectangleSpace₄ μY μD G N →L[ℂ] rectangleSpace₃ μY μC G K :=
  compress (G y) _ _
def rectangleRestrictK (c : C) : rectangleSpace₃ μY μC G K →L[ℂ] rectangleSpace₁ μX μC F K :=
  compress (K c) _ _
def rectangleRestrictN (d : D) : rectangleSpace₄ μY μD G N →L[ℂ] rectangleSpace₂ μX μD F N :=
  compress (N d) _ _
end

section

structure TriplePartition (I : Type*) [Fintype I] [DecidableEq I] where
  P : Finset I
  A : Finset I
  B : Finset I
  nonemptyP : P.Nonempty
  nonemptyA : A.Nonempty
  nonemptyB : B.Nonempty
  disjointPA : Disjoint P A
  disjointPB : Disjoint P B
  disjointAB : Disjoint A B
  cover : P ∪ A ∪ B = Finset.univ

open MeasureTheory
end

namespace StrongUnitary
open MeasureTheory Filter Topology
open scoped Topology
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SecondCountableTopology E]

def code (U : E ≃ₗᵢ[ℂ] H) : ℕ → H := fun n => U (TopologicalSpace.denseSeq E n)

instance topology : TopologicalSpace (E ≃ₗᵢ[ℂ] H) :=
  .induced code inferInstance

instance measurableSpace : MeasurableSpace (E ≃ₗᵢ[ℂ] H) := borel _
end StrongUnitary

section
open MeasureTheory ContinuousLinearMap
variable {X E H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SecondCountableTopology H]

structure MeasurablePolar (μ : Measure X) (F : X → E →L[ℂ] H) where
  unitary : X → E ≃ₗᵢ[ℂ] H
  measurable : Measurable unitary
  formula : ∀ᵐ x ∂μ, Function.Injective (F x) ∧ DenseRange (F x) ∧
    (unitary x : E →L[ℂ] H) ∘L operatorAbs (F x) = F x

end

section
open MeasureTheory ContinuousLinearMap
variable {Ω X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄] [SecondCountableTopology H₄]

structure MeasurablePolarRectangle
    (μ : Measure Ω) (μX : Measure X) (μY : Measure Y) (μC : Measure C) (μD : Measure D)
    (F : X → H₂ →L[ℂ] H₁) (G : Y → H₄ →L[ℂ] H₃)
    (K : C → H₃ →L[ℂ] H₁) (N : D → H₄ →L[ℂ] H₂)
    (x : Ω → X) (y : Ω → Y) (c : Ω → C) (d : Ω → D) where
  a : MeasurablePolar μX F
  b : MeasurablePolar μY G
  p : MeasurablePolar μC K
  q : MeasurablePolar μD N
  rectangle : ∀ᵐ ω ∂μ, (q.unitary (d ω)).trans (a.unitary (x ω)) =
    (b.unitary (y ω)).trans (p.unitary (c ω))

end

namespace ArrayObjects.Object.Rolled

open ContinuousLinearMap MeasureTheory ProbabilityTheory
open scoped ENNReal

section GroupedPolarData
local instance instFactNeENNRealOfNatTop_3 : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def GroupedPolarData (rows cols : TriplePartition I) (n : ℕ) (e : Arr I M.U (n+2)) :=
  let μX := cellLaw M rows.A cols.P n e
  let μY := cellLaw M rows.B cols.P n e
  let μC := cellLaw M rows.P cols.A n e
  let μD := cellLaw M rows.P cols.B n e
  let F := fibreRowEdge M rows.A cols.P cols.A cols.B n e
  let G := fibreRowEdge M rows.B cols.P cols.A cols.B n e
  let K := fibreColumnEdge M rows.P rows.A rows.B cols.A n e
  let N := fibreColumnEdge M rows.P rows.A rows.B cols.B n e
  MeasurablePolarRectangle (M.ownKernel (n+2) e) μX μY μC μD
    (rectangleRestrictF μX μC μD F K N) (rectangleRestrictG μY μC μD G K N)
    (rectangleRestrictK μX μY μC F G K) (rectangleRestrictN μX μY μD F G N)
    (cells M rows.A cols.P n) (cells M rows.B cols.P n)
    (cells M rows.P cols.A n) (cells M rows.P cols.B n)

end GroupedPolarData


universe u
end ArrayObjects.Object.Rolled

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal


section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def rowActive (A R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :=
  essentialRange (cellLaw M A S n e) (fibreRowEdge M A S R D n e)

def columnActive (P A B R : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :=
  essentialRange (cellLaw M A R n e) (fibreColumnEdge M A P B R n e)

def commonActive (P A B R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :=
  rowActive M P R S D n e ⊓ columnActive M P A B R n e

instance instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleRowActive (A R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    CompleteSpace (rowActive M A R S D n e) := by unfold rowActive; infer_instance
instance instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleColumnActive (P A B R : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    CompleteSpace (columnActive M P A B R n e) := by unfold columnActive; infer_instance
instance instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleCommonActive (P A B R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    CompleteSpace (commonActive M P A B R S D n e) := by
  exact (IsClosed.inter (essentialRange.isClosed (cellLaw M P S n e) (fibreRowEdge M P S R D n e))
    (essentialRange.isClosed (cellLaw M A R n e) (fibreColumnEdge M A P B R n e))).completeSpace_coe

end
universe u

end ArrayObjects.Object.Rolled

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Tensors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal

namespace ArrayObjects.Object.Rolled
local instance instFactNeENNRealOfNatTop_10 : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
end ArrayObjects.Object.Rolled
end


end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_ExactLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal
local instance instMeasurableSpaceCircle : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
universe u
end ArrayObjects.Object.Rolled

section
variable {I : Type*} [Fintype I] [DecidableEq I]

@[ext] structure ComplementSplit (P : Finset I) where
  A : Finset I
  B : Finset I
  nonemptyP : P.Nonempty
  nonemptyA : A.Nonempty
  nonemptyB : B.Nonempty
  disjointPA : Disjoint P A
  disjointPB : Disjoint P B
  disjointAB : Disjoint A B
  cover : P ∪ A ∪ B = Finset.univ

namespace ComplementSplit
variable {P : Finset I}

instance instFinite : Finite (ComplementSplit P) :=
  Finite.of_injective (fun s : ComplementSplit P => (s.A,s.B)) (by
    intro s t h
    exact ComplementSplit.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

end ComplementSplit
end

namespace JoiningOperator
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {Ω Z X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure Ω) (η : Measure Z) [IsFiniteMeasure η]
  (x : Ω → X) (y : Ω → Y) (z : Ω → Z)

def splitExact : Set (Lp ℂ 2 η) := {v | ∃ (f : Z → Circle) (g : X → Circle) (h : Y → Circle)
    (hf : Measurable f) (_ : Measurable g) (_ : Measurable h) (c : ℂ),
    v = c • circleLp η f hf ∧ ∀ᵐ ω ∂μ, f (z ω) = g (x ω) * h (y ω)}

end JoiningOperator

namespace ArrayObjects.Object.Rolled

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def rowSplitExact (P R : Finset I) (s : ComplementSplit R) (n : ℕ) (e : Arr I M.U (n+2)) :=
  JoiningOperator.splitExact (M.ownKernel (n+2) e) (cellLaw M P R n e)
    (cells M P s.A n) (cells M P s.B n) (cells M P R n)
def columnSplitExact (P R : Finset I) (s : ComplementSplit P) (n : ℕ) (e : Arr I M.U (n+2)) :=
  JoiningOperator.splitExact (M.ownKernel (n+2) e) (cellLaw M P R n e)
    (cells M s.A R n) (cells M s.B R n) (cells M P R n)

def allSplitExact (P R : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :=
  {v | (∀ s : ComplementSplit R, v ∈ rowSplitExact M P R s n e) ∧
    (∀ t : ComplementSplit P, v ∈ columnSplitExact M P R t n e)}

def oneColumn (P : Finset I) (n : ℕ) (j : I) (y : Arr I M.Y (n+2)) : P → Arr I M.Y n :=
  fun i => missingRow M n j i y

def oneRow (R : Finset I) (n : ℕ) (i : I) (y : Arr I M.Y (n+2)) : R → Arr I M.Y n :=
  fun j => missingRow M n j i y

omit [DecidableEq I] in
@[fun_prop] lemma measurable_oneColumn (P : Finset I) (n : ℕ) (j : I) : Measurable (oneColumn M P n j) := by
  exact Measurable.of_eval fun _ => measurable_missingRow M _ _ _
omit [DecidableEq I] in
@[fun_prop] lemma measurable_oneRow (R : Finset I) (n : ℕ) (i : I) : Measurable (oneRow M R n i) := by
  exact Measurable.of_eval fun _ => measurable_missingRow M _ _ _

def columnCellLaw (P : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) (j : I) : Measure (P → Arr I M.Y n) :=
  (M.ownKernel (n+1) (plane (n+1) (Fin.last (n+1)) j e)).map (fun y (i : P) => plane n 0 i y)
def rowCellLaw (R : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) (i : I) : Measure (R → Arr I M.Y n) :=
  (M.ownKernel (n+1) (plane (n+1) 0 i e)).map (fun y (j : R) => plane n (Fin.last n) j y)

instance instIsProbabilityMeasureForallSubtypeMemFinsetArrαYColumnCellLaw (P : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) (j : I) : IsProbabilityMeasure (columnCellLaw M P n e j) :=
  (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (by fun_prop)
instance instIsProbabilityMeasureForallSubtypeMemFinsetArrαYRowCellLaw (R : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) (i : I) : IsProbabilityMeasure (rowCellLaw M R n e i) :=
  (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (by fun_prop)

end ArrayObjects.Object.Rolled

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def fullExact (P R : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) : Set (Lp ℂ 2 (cellLaw M P R n e)) :=
  {v | ∃ (f : (R → P → Arr I M.Y n) → Circle) (hf : Measurable f) (d : ℂ),
    v = d • circleLp (cellLaw M P R n e) f hf ∧
    (∃ (a : ↥(Rᶜ) → (P → Arr I M.Y n) → Circle) (c : Circle),
      (∀ i, Measurable (a i)) ∧ ∀ᵐ y ∂M.ownKernel (n+2) e,
        f (cells M P R n y) = c * ∏ i : ↥(Rᶜ), a i (oneColumn M P n i y)) ∧
    (∃ (a : ↥(Pᶜ) → (R → Arr I M.Y n) → Circle) (c : Circle),
      (∀ i, Measurable (a i)) ∧ ∀ᵐ y ∂M.ownKernel (n+2) e,
        f (cells M P R n y) = c * ∏ i : ↥(Pᶜ), a i (oneRow M R n i y))}

end ArrayObjects.Object.Rolled

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u
variable {I : Type u} [Fintype I] [retained10 : DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

abbrev Cell (i : I) := ({i} : Finset I) → ({i} : Finset I) → Arr I M.Y 0

def padCell (i : I) (y : Arr I M.Y 0) : Cell M i := fun _ _ => y
omit [DecidableEq I] in
@[fun_prop] lemma measurable_padCell (i : I) : Measurable (padCell M i) := by
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ => measurable_id

def slotCell (i : I) : Arr I M.Y 1 → Cell M i := padCell M i ∘ plane 0 0 i
include retained10 in
@[fun_prop] lemma measurable_slotCell (i : I) : Measurable (slotCell M i) := by
  let _ := retained10
  exact (measurable_padCell M i).comp (measurable_plane _ _ _)

def slotRest (i : I) (y : Arr I M.Y 1) : ↥(({i} : Finset I)ᶜ) → Arr I M.Y 0 :=
  fun j => plane 0 0 j y
@[fun_prop] lemma measurable_slotRest (i : I) : Measurable (slotRest M i) := by
  exact Measurable.of_eval fun _ => measurable_plane _ _ _

def slotLocal (i : I) : Kernel (Arr I M.U 0) (Cell M i) := (M.ownKernel 0).map (padCell M i)
instance instIsMarkovKernelArrαUOfNatNatCellSlotLocal (i : I) : IsMarkovKernel (slotLocal M i) := Kernel.IsMarkovKernel.map _ (measurable_padCell M i)

def slotActive (i : I) (ν : Measure (Cell M i)) (p : Arr I M.U 1) : Submodule ℂ (Lp ℂ 2 ν) := by
  classical
  exact if h : MeasurePreserving (slotCell M i) (M.ownKernel 1 p) ν then
    (LinearMap.range (JoiningOperator.operator h
      (MeasurePreserving.mk (measurable_slotRest M i) rfl)).toLinearMap).topologicalClosure
  else ⊥

lemma slotActive_closed (i : I) (ν : Measure (Cell M i)) (p : Arr I M.U 1) :
    IsClosed (slotActive M i ν p : Set (Lp ℂ 2 ν)) := by
  unfold slotActive
  split
  · exact Submodule.isClosed_topologicalClosure _
  · exact isClosed_singleton

instance instCompleteSpaceSubtypeAEEqFunCellComplexMemAddSubgroupLpOfNatENNRealSubmoduleSlotActive (i : I) (ν : Measure (Cell M i)) (p : Arr I M.U 1) :
    CompleteSpace (slotActive M i ν p) := (slotActive_closed M i ν p).completeSpace_coe

end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Set
namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def slotTuple (r : I) (y : Arr I M.Y 1) : I → Cell M r :=
  fun j => padCell M r (plane 0 0 j y)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_slotTuple (r : I) : Measurable (slotTuple M r) :=
  Measurable.of_eval fun _ => (measurable_padCell M r).comp (measurable_plane _ _ _)

def slotTupleKernel (r : I) : Kernel (Arr I M.U 1) (I → Cell M r) :=
  (M.ownKernel 1).map (slotTuple M r)
instance instIsMarkovKernelArrαUOfNatNatForallCellSlotTupleKernel (r : I) : IsMarkovKernel (slotTupleKernel M r) :=
  Kernel.IsMarkovKernel.map _ (measurable_slotTuple M r)

def tupleParameter (p : Arr I M.U 1) : I → Arr I M.U 0 := fun j => plane 0 0 j p
omit [DecidableEq I] in
@[fun_prop] lemma measurable_tupleParameter : Measurable (tupleParameter M) :=
  Measurable.of_eval fun _ => measurable_plane _ _ _

end ArrayObjects.Object.Rolled
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set

section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def rawTuple (y : Arr I M.Y 1) : I → Arr I M.Y 0 := fun j => plane 0 0 j y
omit [DecidableEq I] in
@[fun_prop] lemma measurable_rawTuple : Measurable (rawTuple M) :=
  Measurable.of_eval fun _ => measurable_plane _ _ _

def rawTupleKernel : Kernel (Arr I M.U 1) (I → Arr I M.Y 0) := (M.ownKernel 1).map (rawTuple M)
instance instIsMarkovKernelArrαUOfNatNatForallYRawTupleKernel : IsMarkovKernel (rawTupleKernel M) := Kernel.IsMarkovKernel.map _ (measurable_rawTuple M)

end

universe u

end ArrayObjects.Object.Rolled

section
open MeasureTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable (Y : Type*) [MeasurableSpace Y]

def measurableCircleSubgroup : Subgroup (Y → Circle) where
  carrier := {f | Measurable f}
  one_mem' := measurable_const
  mul_mem' := fun hf hg => hf.mul hg
  inv_mem' := fun hf => hf.inv
abbrev MeasurableCircle := measurableCircleSubgroup Y
variable {Y} (μ : Measure Y)

def phaseSubgroup : Subgroup (MeasurableCircle Y) where
  carrier := {f | ∃ c : Circle, (f : Y → Circle) =ᵐ[μ] fun _ => c}
  one_mem' := ⟨1,Filter.Eventually.of_forall fun _ => rfl⟩
  mul_mem' := by
    rintro f g ⟨a,ha⟩ ⟨b,hb⟩
    refine ⟨a*b,?_⟩
    filter_upwards [ha,hb] with y hfy hgy
    exact congrArg₂ (·*·) hfy hgy
  inv_mem' := by
    rintro f ⟨a,ha⟩
    refine ⟨a⁻¹,?_⟩
    filter_upwards [ha] with y hy
    exact congrArg Inv.inv hy
abbrev ProjectiveCircle := MeasurableCircle Y ⧸ phaseSubgroup μ

def projectiveCircle (f : Y → Circle) (hf : Measurable f) : ProjectiveCircle μ :=
  QuotientGroup.mk (⟨f,hf⟩ : MeasurableCircle Y)

end

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)
namespace HilbertCode
variable {κ}
def projective (u : U) (q : HilbertCode κ) : ProjectiveCircle (κ u) :=
  projectiveCircle (κ u) (circleRep q) (measurable_circleRep_fixed q)

end HilbertCode

end

section
open MeasureTheory ProbabilityTheory Set
variable {P U Y I : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

omit [StandardBorelSpace U] in
lemma HilbertCode.distance_self (q : HilbertCode κ) : HilbertCode.distance q q = 0 := by
  rw [←HilbertCode.encode_decode q,HilbertCode.distance_encode,dist_self]

omit [StandardBorelSpace P] [StandardBorelSpace U] in
lemma exactCode_unique_slot (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p))
    {p : P} {a b : I → HilbertCode κ}
    (ha : (p,a) ∈ exactCodeSet κ Λ u) (hb : (p,b) ∈ exactCodeSet κ Λ u)
    (i : I) (hi : a i = b i) : a = b := by
  rcases HilbertCode.exact_codes_dichotomy hk (Λ p) a b
    (fun j => (ha.1 j).trans (hb.1 j).symm) ha.2.1 hb.2.1
    (fun j => by simpa only [ha.1 j] using hm p j) (hind p) ha.2.2 hb.2.2 with h | h
  · exact h
  · have h := h i
    rw [hi,HilbertCode.distance_self] at h
    norm_num at h

def exactMatching (i : I) : P × HilbertCode κ → I → HilbertCode κ :=
  Function.extend (fun t : ExactCodeTuple κ Λ u => (t.1.1,t.1.2 i))
    (fun t => t.1.2) (fun pq j => HilbertCode.encode (u pq.1 j) 0)

end

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

abbrev ExactCodeSlot (p : P) (i : I) := {q : HilbertCode κ //
  ∃ a : I → HilbertCode κ, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q}

end

section
open MeasureTheory ProbabilityTheory
namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

abbrev CellAt (a j : I) := ({j} : Finset I) → ({a} : Finset I) → Arr I M.Y 0

def collapseCell (a j : I) : CellAt M a j ≃ᵐ Arr I M.Y 0 where
  toFun y := y ⟨j,Finset.mem_singleton_self j⟩ ⟨a,Finset.mem_singleton_self a⟩
  invFun y := fun _ _ => y
  left_inv y := by
    funext s t
    have hs : s = ⟨j,Finset.mem_singleton_self j⟩ := Subtype.ext (Finset.mem_singleton.mp s.property)
    have ht : t = ⟨a,Finset.mem_singleton_self a⟩ := Subtype.ext (Finset.mem_singleton.mp t.property)
    subst s; subst t; rfl
  right_inv _ := rfl
  measurable_toFun := (measurable_pi_apply _).comp (measurable_pi_apply _)
  measurable_invFun := Measurable.of_eval fun _ => Measurable.of_eval fun _ => measurable_id

def rawSlotActive (i : I) (ν : Measure (Arr I M.Y 0)) (p : Arr I M.U 1) : Submodule ℂ (Lp ℂ 2 ν) := by
  classical
  exact if h : MeasurePreserving (plane 0 0 i) (M.ownKernel 1 p) ν then
    (LinearMap.range (JoiningOperator.operator h
      (MeasurePreserving.mk (measurable_slotRest M i) rfl)).toLinearMap).topologicalClosure
  else ⊥
lemma rawSlotActive_closed (i : I) (ν : Measure (Arr I M.Y 0)) (p : Arr I M.U 1) :
    IsClosed (rawSlotActive M i ν p : Set (Lp ℂ 2 ν)) := by
  unfold rawSlotActive
  split
  · exact Submodule.isClosed_topologicalClosure _
  · exact isClosed_singleton
instance instCompleteSpaceSubtypeAEEqFunArrαYOfNatNatComplexMemAddSubgroupLpENNRealSubmoduleRawSlotActive (i : I) (ν : Measure (Arr I M.Y 0)) (p : Arr I M.U 1) :
    CompleteSpace (rawSlotActive M i ν p) := (rawSlotActive_closed M i ν p).completeSpace_coe

end ArrayObjects.Object.Rolled
end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace ArrayObjects.Object.Rolled

attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def rawExactCone (i : I) (ν : Measure (Arr I M.Y 0)) [IsFiniteMeasure ν] (p : Arr I M.U 1) :
    Set (Lp ℂ 2 ν) := {v | ∃ (f : I → Arr I M.Y 0 → Circle) (hf : ∀ j, Measurable (f j))
      (c : Circle) (d : ℂ), v = d • circleLp ν (f i) (hf i) ∧
      ∀ᵐ y ∂M.ownKernel 1 p, ∏ j, f j (plane 0 0 j y) = c}

end ArrayObjects.Object.Rolled
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [retained11 : DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def rawLineGraph (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) :
    I → Set (Arr I M.U 1 × HilbertCode (M.ownKernel 0)) := fun i =>
  {pz | ∃ a : I → HilbertCode (M.ownKernel 0),
    (pz.1,a) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) ∧ a i = pz.2}

end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Set
variable {P Ω X Y U : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]
  [retained12 : StandardBorelSpace Ω] [StandardBorelSpace X]
  [StandardBorelSpace Y] [Nonempty Y]
  (Λ : Kernel P Ω) [IsMarkovKernel Λ] (x : Ω → X) (y : Ω → Y)
  (hx : Measurable x) (hy : Measurable y)

def joiningPosterior : Kernel (P × X) Y := (Λ.map (fun ω => (x ω,y ω))).condKernel
instance instIsMarkovKernelProdJoiningPosterior : IsMarkovKernel (joiningPosterior Λ x y) := inferInstanceAs (IsMarkovKernel (Λ.map (fun ω => (x ω,y ω))).condKernel)

variable (κ : Kernel U X) [IsMarkovKernel κ] (u : P → U)
  (f : Y → ℂ) (hf : Measurable f) (B : ℝ) (hB : ∀ z, ‖f z‖ ≤ B)

omit [StandardBorelSpace Ω] in
include hf B hB in
lemma posterior_memLp (p : P) :
    MemLp (fun a => ∫ z, f z ∂joiningPosterior Λ x y (p,a)) 2 (κ (u p)) := by
  refine MemLp.of_bound (by
    exact (hf.stronglyMeasurable.integral_kernel (κ := joiningPosterior Λ x y)).comp_measurable
      measurable_prodMk_left |>.aestronglyMeasurable) B ?_
  exact Filter.Eventually.of_forall fun a => by
    simpa only [probReal_univ,mul_one] using
      (norm_integral_le_of_norm_le_const (μ := joiningPosterior Λ x y (p,a))
        (Filter.Eventually.of_forall hB))

def posteriorVector (p : P) : Lp ℂ 2 (κ (u p)) :=
  (posterior_memLp Λ x y κ u f hf B hB p).toLp _

end

section
open MeasureTheory ProbabilityTheory Set
variable {Y : Type*} [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
lemma hilbertTestFunction_bounded (t : HilbertTestKey Y) :
    ∃ B : ℝ, ∀ y, ‖hilbertTestFunction t y‖ ≤ B := by
  induction t with
  | nil => exact ⟨0,fun _ => by simp [hilbertTestFunction]⟩
  | cons p t ih =>
    obtain ⟨B,hB⟩ := ih
    refine ⟨‖(p.1.1 : ℂ) + p.1.2 * Complex.I‖ + B,fun y => ?_⟩
    change ‖((p.1.1 : ℂ) + p.1.2 * Complex.I) * (p.2.val.indicator (fun _ => (1 : ℂ))) y + hilbertTestFunction t y‖ ≤ _
    apply (norm_add_le _ _).trans
    apply add_le_add _ (hB y)
    by_cases h : y ∈ p.2.val
    · simp only [Set.indicator_of_mem h,mul_one,le_refl]
    · simp only [Set.indicator_of_notMem h,mul_zero,norm_zero]
      exact norm_nonneg _
variable {P Ω X U : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace U] [StandardBorelSpace Ω] [StandardBorelSpace X]
  [StandardBorelSpace Y] [Nonempty Y]
  (Λ : Kernel P Ω) [IsMarkovKernel Λ] (x : Ω → X) (y : Ω → Y)
  (κ : Kernel U X) [IsMarkovKernel κ] (u : P → U)

def posteriorTest (n : ℕ) (p : P) : Lp ℂ 2 (κ (u p)) :=
  posteriorVector Λ x y κ u (hilbertTestFunction (hilbertTestKeys n))
    (hilbertTestFunction_measurable _) (hilbertTestFunction_bounded _).choose
    (hilbertTestFunction_bounded _).choose_spec p

end

section
open MeasureTheory ProbabilityTheory
namespace ArrayObjects.Object.Rolled
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def rawSlotTest (i : I) (n : ℕ) (p : Arr I M.U 1) : Lp ℂ 2 (M.ownKernel 0 (plane 0 0 i p)) :=
  posteriorTest (M.ownKernel 1) (plane 0 0 i) (slotRest M i) (M.ownKernel 0) (plane 0 0 i) n p

def rawSlotTestSpan (i : I) (p : Arr I M.U 1) : Submodule ℂ (Lp ℂ 2 (M.ownKernel 0 (plane 0 0 i p))) :=
  (Submodule.span ℂ (Set.range (fun n => rawSlotTest M i n p))).topologicalClosure

variable {P : Type*} [MeasurableSpace P]

def rawSlotIndicator (i : I) (f : P → Arr I M.Y 0 → Circle)
    (hf : Measurable (Function.uncurry f)) (p : P) (q : Arr I M.U 1) : Bool := by
  classical
  exact decide (circleLp (M.ownKernel 0 (plane 0 0 i q)) (f p)
    (hf.comp (measurable_const.prodMk measurable_id)) ∈ rawSlotTestSpan M i q)

end ArrayObjects.Object.Rolled
end

open MeasureTheory Set

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_FibreMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {U Z : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Z] [StandardBorelSpace Z]

structure BorelFibreEnumeration (S : Set (U × Z)) where
  domain : ℕ → Set U
  section_ : ℕ → U → Z
  measurable_domain : ∀ n, MeasurableSet (domain n)
  measurable_section : ∀ n, Measurable (section_ n)
  mem : ∀ n u, u ∈ domain n → (u,section_ n u) ∈ S
  cover : ∀ u z, (u,z) ∈ S → ∃ n, u ∈ domain n ∧ section_ n u = z
  unique : ∀ u n m, u ∈ domain n → u ∈ domain m → section_ n u = section_ m u → n = m

namespace BorelFibreEnumeration
variable {S : Set (U × Z)} (E : BorelFibreEnumeration S)
def indexDomain : Set (U × ℕ) := {x | x.1 ∈ E.domain x.2}
omit [StandardBorelSpace U] [StandardBorelSpace Z] in
lemma measurable_indexDomain : MeasurableSet E.indexDomain := by
  have he : E.indexDomain = ⋃ n, E.domain n ×ˢ {n} := by
    ext x; simp [indexDomain]
  rw [he]
  exact MeasurableSet.iUnion (fun n => (E.measurable_domain n).prod (measurableSet_singleton n))
instance instStandardBorelSpaceElemProdNatIndexDomain : StandardBorelSpace E.indexDomain := E.measurable_indexDomain.standardBorel

def point (x : E.indexDomain) : U × Z := (x.val.1,E.section_ x.val.2 x.val.1)
omit [StandardBorelSpace U] [StandardBorelSpace Z] in
lemma measurable_point : Measurable E.point := by
  apply measurable_subtype_coe.fst.prodMk
  have h : Measurable (fun x : U × ℕ => E.section_ x.2 x.1) :=
    measurable_from_prod_countable_left (fun n => E.measurable_section n)
  exact h.comp measurable_subtype_coe
omit [StandardBorelSpace U] [StandardBorelSpace Z] in
lemma injective_point : Function.Injective E.point := by
  intro x y h
  have hu : x.val.1 = y.val.1 := congrArg (fun p : U × Z => p.1) h
  have hn : x.val.2 = y.val.2 := E.unique x.val.1 x.val.2 y.val.2 x.property
    (by rw [hu]; exact y.property) (by
      have hh := congrArg (fun p : U × Z => p.2) h
      change E.section_ x.val.2 x.val.1 = E.section_ y.val.2 y.val.1 at hh
      rwa [←hu] at hh)
  exact Subtype.ext (Prod.ext hu hn)
lemma measurableEmbedding_point : MeasurableEmbedding E.point :=
  E.measurable_point.measurableEmbedding E.injective_point

def indexMeasure (ν : Measure U) : Measure E.indexDomain :=
  (ν.prod Measure.count).comap Subtype.val

def measure (ν : Measure U) : Measure (U × Z) := (E.indexMeasure ν).map E.point

lemma lintegral_measure (ν : Measure U) [SigmaFinite ν]
    (F : U × Z → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂E.measure ν = ∫⁻ u, ∑' n, (E.domain n).indicator
      (fun u => F (u,E.section_ n u)) u ∂ν := by
  rw [measure,E.measurableEmbedding_point.lintegral_map]
  change (∫⁻ x : E.indexDomain, F (x.val.1,E.section_ x.val.2 x.val.1)
    ∂(ν.prod Measure.count).comap Subtype.val) = _
  rw [MeasureTheory.lintegral_subtype_comap E.measurable_indexDomain
    (fun x : U × ℕ => F (x.1,E.section_ x.2 x.1))]
  rw [←lintegral_indicator E.measurable_indexDomain]
  have hm : Measurable (fun x : U × ℕ => E.indexDomain.indicator
      (fun x => F (x.1,E.section_ x.2 x.1)) x) := by
    apply Measurable.indicator _ E.measurable_indexDomain
    exact hF.comp (measurable_fst.prodMk
      (measurable_from_prod_countable_left E.measurable_section))
  rw [lintegral_prod _ hm.aemeasurable]
  congr 1
  funext u
  rw [lintegral_count]
  rfl
end BorelFibreEnumeration
end

namespace BorelFibreEnumeration
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {U Z V W : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Z] [StandardBorelSpace Z]
  [MeasurableSpace V] [StandardBorelSpace V]
  [MeasurableSpace W] [StandardBorelSpace W]
  {S : Set (U × Z)} (E : BorelFibreEnumeration S)

def fibreEquiv (u : U) : {n : ℕ // u ∈ E.domain n} ≃ {z : Z // (u,z) ∈ S} := by
  let f : {n : ℕ // u ∈ E.domain n} → {z : Z // (u,z) ∈ S} :=
    fun n => ⟨E.section_ n u,E.mem n u n.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro n m he
    exact Subtype.ext (E.unique u n m n.property m.property (congrArg Subtype.val he))
  · intro z
    obtain ⟨n,hn,he⟩ := E.cover u z.val z.property
    exact ⟨⟨n,hn⟩,Subtype.ext he⟩

omit [StandardBorelSpace U] [StandardBorelSpace Z] in
lemma sum_sections (u : U) (g : U × Z → ℝ≥0∞) :
    ∑' n, (E.domain n).indicator (fun u => g (u,E.section_ n u)) u =
      ∑' z : {z : Z // (u,z) ∈ S}, g (u,z.val) := by
  classical
  have he := (E.fibreEquiv u).tsum_eq (fun z => g (u,z.val))
  change (∑' n : {n : ℕ // u ∈ E.domain n}, g (u,E.section_ n u)) = _ at he
  have hs := tsum_subtype {n : ℕ | u ∈ E.domain n} (fun n => g (u,E.section_ n u))
  simpa only [Set.indicator_apply,Set.mem_ofPred_eq] using hs.symm.trans he

lemma measurePreserving_fibrewise {R : Set (V × W)} (D : BorelFibreEnumeration R)
    (ν : Measure U) [SigmaFinite ν] (ρ : Measure V) [SigmaFinite ρ]
    (t : U → V) (ht : MeasurePreserving t ν ρ)
    (f : U × Z → W) (hf : Measurable f)
    (he : ∀ᵐ u ∂ν, ∃ e : {z : Z // (u,z) ∈ S} ≃ {w : W // (t u,w) ∈ R},
      ∀ z, (e z).val = f (u,z.val)) :
    MeasurePreserving (fun x : U × Z => (t x.1,f x)) (E.measure ν) (D.measure ρ) := by
  have hm : Measurable (fun x : U × Z => (t x.1,f x)) := (ht.measurable.comp measurable_fst).prodMk hf
  refine ⟨hm,?_⟩
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hm]
  have hleft := E.lintegral_measure ν (fun x => F (t x.1,f x)) (hF.comp hm)
  rw [hleft,D.lintegral_measure ρ F hF]
  have hsum : Measurable (fun v => ∑' n, (D.domain n).indicator
      (fun v => F (v,D.section_ n v)) v) := by
    apply Measurable.tsum
    intro n
    exact (hF.comp (measurable_id.prodMk (D.measurable_section n))).indicator (D.measurable_domain n)
  rw [←ht.lintegral_comp hsum]
  apply lintegral_congr_ae
  filter_upwards [he] with u hu
  obtain ⟨e,he⟩ := hu
  rw [E.sum_sections u (fun x => F (t x.1,f x)),D.sum_sections (t u) F]
  have hh := e.tsum_eq (fun w => F (t u,w.val))
  simpa only [he] using hh
end BorelFibreEnumeration

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {P U Y I : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

def exactFibreSlotEquiv (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p))
    (S : Set (U × HilbertCode κ)) (p : P) (i : I)
    (hS : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} =
      {q | (u p i,q) ∈ S}) :
    {a : I → HilbertCode κ // (p,a) ∈ exactCodeSet κ Λ u} ≃
      {q : HilbertCode κ // (u p i,q) ∈ S} := by
  let f : {a : I → HilbertCode κ // (p,a) ∈ exactCodeSet κ Λ u} →
      {q : HilbertCode κ // (u p i,q) ∈ S} := fun a =>
    ⟨a.val i,by exact (Set.ext_iff.mp hS _).mp ⟨a.val,a.property,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b he
    exact Subtype.ext (exactCode_unique_slot κ Λ u hk hm hind a.property b.property i
      (congrArg Subtype.val he))
  · intro q
    obtain ⟨a,ha,he⟩ := (Set.ext_iff.mp hS _).mpr q.property
    exact ⟨⟨a,ha⟩,Subtype.ext he⟩

lemma exactCounting_slot_preserving (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p))
    (S : Set (U × HilbertCode κ)) (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet κ Λ u))
    (π : Measure P) [SigmaFinite π] (ν : Measure U) [SigmaFinite ν]
    (i : I) (hui : MeasurePreserving (fun p => u p i) π ν)
    (hS : ∀ᵐ p ∂π, {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} =
      {q | (u p i,q) ∈ S}) :
    MeasurePreserving (fun x : P × (I → HilbertCode κ) => (u x.1 i,x.2 i))
      (Eπ.measure π) (E.measure ν) := by
  apply Eπ.measurePreserving_fibrewise E π ν (fun p => u p i) hui
    (fun x => x.2 i) ((measurable_pi_apply i).comp measurable_snd)
  filter_upwards [hS] with p hp
  exact ⟨exactFibreSlotEquiv κ Λ u hk hm hind S p i hp,fun _ => rfl⟩
end

section
open MeasureTheory ProbabilityTheory Set
variable {P Q U Y I : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace Q] [StandardBorelSpace Q]
  [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U) (row col : Q → I → P)

def exactSquareSet : Set (Q × (I → I → HilbertCode κ)) :=
  {eq | (∀ a, (row eq.1 a,eq.2 a) ∈ exactCodeSet κ Λ u) ∧
    (∀ s, (col eq.1 s,fun a => eq.2 a s) ∈ exactCodeSet κ Λ u)}

end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

def rawExactSquare : Set (Arr I M.U 2 × (I → I → HilbertCode (M.ownKernel 0))) :=
  exactSquareSet (M.ownKernel 0) Λ (tupleParameter M)
    (fun e i => plane 1 0 i e) (fun e j => plane 1 (Fin.last 1) j e)

lemma rawCounting_coordinate_preserving (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M))) (i : I) :
    MeasurePreserving (fun x : Arr I M.U 1 × (I → HilbertCode (M.ownKernel 0)) =>
      (tupleParameter M x.1 i,x.2 i)) (Eπ.measure (M.parameterLaw 1)) (E.measure (M.parameterLaw 0)) := by
  apply exactCounting_slot_preserving (M.ownKernel 0) Λ (tupleParameter M) hk hm hind S E Eπ _ _ i
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
  exact hS.mono (fun _ hp => hp i)

end ArrayObjects.Object.Rolled

namespace BorelFibreEnumeration

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {P U Z : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U] [MeasurableSpace Z] [StandardBorelSpace Z]
  {S : Set (U × Z)} (E : BorelFibreEnumeration S)

def comapBase (t : P → U) (ht : Measurable t) :
    BorelFibreEnumeration {x : P × Z | (t x.1,x.2) ∈ S} where
  domain n := t ⁻¹' E.domain n
  section_ n := E.section_ n ∘ t
  measurable_domain n := ht (E.measurable_domain n)
  measurable_section n := (E.measurable_section n).comp ht
  mem n p hp := E.mem n (t p) hp
  cover p z hz := E.cover (t p) z hz
  unique p n m hn hm he := E.unique (t p) n m hn hm he

end BorelFibreEnumeration

namespace Kernel
open MeasureTheory ProbabilityTheory
variable {A B C D E F : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace F]

def depMap (κ : ProbabilityTheory.Kernel A B) (f : A × B → C) : ProbabilityTheory.Kernel A C :=
  (ProbabilityTheory.Kernel.id ×ₖ κ).map f

end Kernel

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

abbrev RawLabel := Arr I M.U 0 × HilbertCode (M.ownKernel 0)
abbrev RawLabelTuple := Arr I M.U 1 × (I → HilbertCode (M.ownKernel 0))

def rawLabelSlot (a : I) (x : RawLabelTuple M) : RawLabel M :=
  (tupleParameter M x.1 a,x.2 a)

omit [DecidableEq I] in
lemma measurable_rawLabelSlot (a : I) : Measurable (rawLabelSlot M a) :=
  ((measurable_plane _ _ _).comp measurable_fst).prodMk
    ((measurable_pi_apply a).comp measurable_snd)

def rawMatchedLabel (a b : I) (x : RawLabel M × Arr I M.U 1) : RawLabel M :=
  (tupleParameter M x.2 b,exactMatching (M.ownKernel 0) Λ (tupleParameter M) a (x.2,x.1.2) b)

def rawLabelTransition (a b : I) : Kernel (RawLabel M) (RawLabel M) :=
  Rokhlin.Kernel.depMap ((M.parameterCoordinateKernel a).comap Prod.fst measurable_fst)
    (rawMatchedLabel M Λ a b)

end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Set

namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
abbrev RawLabelSquare := Arr I M.U 2 × (I → I → HilbertCode (M.ownKernel 0))
def rawLabelRow (a : I) (x : RawLabelSquare M) : RawLabelTuple M := (plane 1 0 a x.1,x.2 a)

def rawLabelColumn (s : I) (x : RawLabelSquare M) : RawLabelTuple M :=
  (plane 1 (Fin.last 1) s x.1,fun a => x.2 a s)
end ArrayObjects.Object.Rolled
end

namespace ArrayObjects.Object.Rolled

open ContinuousLinearMap MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace


universe u
variable {I : Type u} [Fintype I] [retained13 : DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

def rawLabelTime (z : RawLabel M) : RawLabel M :=
  (amap M.timeU 0 z.1,HilbertCode.transport (amap M.timeU 0) (amapEquiv M.timeY 0) z.2)
def rawLabelTimeInv (z : RawLabel M) : RawLabel M :=
  (amap M.timeU.symm 0 z.1,HilbertCode.transport (amap M.timeU.symm 0) (amapEquiv M.timeY.symm 0) z.2)
def rawLabelTupleTime (z : RawLabelTuple M) : RawLabelTuple M :=
  (amap M.timeU 1 z.1,fun i => HilbertCode.transport (amap M.timeU 0) (amapEquiv M.timeY 0) (z.2 i))

end ArrayObjects.Object.Rolled

section
open MeasureTheory
abbrev LabelOrbitVector := (ℤ × ℤ) → ℂ

def labelShiftSecond : LabelOrbitVector ≃ᵐ LabelOrbitVector where
  toFun c p := c (p.1,p.2+1)
  invFun c p := c (p.1,p.2-1)
  left_inv c := by funext p; simp
  right_inv c := by funext p; simp
  measurable_toFun := Measurable.of_eval fun p => measurable_pi_apply _
  measurable_invFun := Measurable.of_eval fun p => measurable_pi_apply _

end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_OrbitCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U) (S : Set (U × HilbertCode κ))

def localProjectiveGroup (a : U) : Subgroup (ProjectiveCircle (κ a)) :=
  Subgroup.closure {g | ∃ q, (a,q) ∈ S ∧ HilbertCode.projective a q = g}

end

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
attribute [local instance] Classical.propDecidable
variable {U Y C : Type*} [MeasurableSpace U] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] (κ : Kernel U Y) [IsMarkovKernel κ]
    (S : Set (U × HilbertCode κ))

def localGroupCode (a : U) (g : localProjectiveGroup κ S a) : HilbertCode κ :=
  if h : ∃ q, (a,q) ∈ S ∧ HilbertCode.projective a q = g.val then h.choose
  else HilbertCode.encode a 0

def localGroupBlock (ψ : U × HilbertCode κ → C) (a : U) (g : localProjectiveGroup κ S a) : C :=
  ψ (a,localGroupCode κ S a g)

end

namespace ArrayObjects.Object.Rolled

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators


attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def slotExact (i : I) (ν : Measure (Cell M i)) [IsFiniteMeasure ν] (p : Arr I M.U 1) :
    Set (Lp ℂ 2 ν) := {v | ∃ (f : Cell M i → Circle) (hf : Measurable f) (d : ℂ),
      v = d • circleLp ν f hf ∧ ∃ (a : ↥(({i} : Finset I)ᶜ) → Arr I M.Y 0 → Circle) (c : Circle),
      (∀ j, Measurable (a j)) ∧ ∀ᵐ y ∂M.ownKernel 1 p,
        f (slotCell M i y) = c * ∏ j : ↥(({i} : Finset I)ᶜ), a j (plane 0 0 j y)}

def slotExactSpan (i : I) (ν : Measure (Cell M i)) [IsFiniteMeasure ν] (p : Arr I M.U 1) :
    Submodule ℂ (Lp ℂ 2 ν) := (Submodule.span ℂ (slotExact M i ν p)).topologicalClosure

def unpadCell (i : I) (y : Cell M i) : Arr I M.Y 0 :=
  y ⟨i,Finset.mem_singleton_self i⟩ ⟨i,Finset.mem_singleton_self i⟩
omit [DecidableEq I] in
@[fun_prop] lemma measurable_unpadCell (i : I) : Measurable (unpadCell M i) :=
  (measurable_pi_apply _).comp (measurable_pi_apply _)
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] (κ : Kernel U Y) [IsMarkovKernel κ]

def absoluteCoefficient (f : Y → ℂ) (z : U × HilbertCode κ) : ℝ :=
  ‖∫ y, f y * conj (HilbertCode.circleRep z.2 y : ℂ) ∂κ z.1‖

end

namespace BorelFibreEnumeration
open MeasureTheory Set
open scoped BigOperators

section
attribute [local instance] Classical.propDecidable
variable {U Z W : Type*} [MeasurableSpace U] [MeasurableSpace Z] [MeasurableSpace W]
variable {S : Set (U × Z)} (E : BorelFibreEnumeration S)

def fibreSum (F : U × Z → ℝ) (a : U) : ℝ :=
  ∑' n : ℕ, if a ∈ E.domain n then F (a,E.section_ n a) else 0

variable {R : Set (U × W)} (D : BorelFibreEnumeration R)

variable {C : Type*} [MeasurableSpace C] [MeasurableSingletonClass C]

def restrictLevel (ψ : U × Z → C) (hψ : Measurable ψ) (b : C) :
    BorelFibreEnumeration {z | z ∈ S ∧ ψ z = b} where
  domain n := {a | a ∈ E.domain n ∧ ψ (a,E.section_ n a) = b}
  section_ := E.section_
  measurable_domain n := (E.measurable_domain n).inter
    ((hψ.comp (measurable_id.prodMk (E.measurable_section n))) (measurableSet_singleton b))
  measurable_section := E.measurable_section
  mem n a ha := ⟨E.mem n a ha.1,ha.2⟩
  cover a z hz := by
    obtain ⟨n,hn,he⟩ := E.cover a z hz.1
    exact ⟨n,⟨hn,he ▸ hz.2⟩,he⟩
  unique a n m hn hm he := E.unique a n m hn.1 hm.1 he
end

end BorelFibreEnumeration

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

structure PositiveRawBlock (S : Set (RawLabel M)) (E : BorelFibreEnumeration S)
    (f : Arr I M.Y 0 → ℂ) where
  ψ : RawLabel M → LabelOrbitVector
  measurable_ψ : Measurable ψ
  a₀ : Arr I M.U 0
  b : LabelOrbitVector
  finite_block : {g : localProjectiveGroup (M.ownKernel 0) S a₀ |
    localGroupBlock (M.ownKernel 0) S ψ a₀ g = b}.Finite
  G : localProjectiveGroup (M.ownKernel 0) S a₀ ≃* localProjectiveGroup (M.ownKernel 0) S a₀
  block_shift : ∀ g, localGroupBlock (M.ownKernel 0) S ψ a₀ (G g) =
    labelShiftSecond.symm (localGroupBlock (M.ownKernel 0) S ψ a₀ g)
  identifications : ∀ᵐ a ∂M.parameterLaw 0,
    ∃ J : localProjectiveGroup (M.ownKernel 0) S a₀ ≃* localProjectiveGroup (M.ownKernel 0) S a,
      ∀ g, localGroupBlock (M.ownKernel 0) S ψ a (J g) = localGroupBlock (M.ownKernel 0) S ψ a₀ g
  time_labels : ∀ᵐ a ∂M.parameterLaw 0, ∀ q, (a,q) ∈ S →
    ψ (rawLabelTime M (a,q)) = labelShiftSecond (ψ (a,q))
  positive : 0 < ∫ a, (E.restrictLevel ψ measurable_ψ b).fibreSum
    (absoluteCoefficient (M.ownKernel 0) f) a ∂M.parameterLaw 0

end ArrayObjects.Object.Rolled

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Saturation
attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.columnGroupKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.columnPairKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunArrαYOfNatNatComplexMemAddSubgroupLpENNRealSubmoduleRawSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunCellComplexMemAddSubgroupLpOfNatENNRealSubmoduleSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleColumnActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleCommonActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleRowActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatCellSlotLocal _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallCellSlotTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallYRawTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYColumnCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYRowCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.rowPairKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.splitRowKernel_markov _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Rokhlin

open MeasureTheory ProbabilityTheory
universe u

open MeasureTheory ProbabilityTheory Finset Function Filter Preorder
open scoped ENNReal

namespace SequentialLimit


section

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  [∀ n, StandardBorelSpace (X n)] [∀ n, Nonempty (X n)]
  (μ : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
  (θ : ∀ n, X (n + 1) → X n) (hθ : ∀ n, Measurable (θ n))

noncomputable def step (n : ℕ) : Kernel (X n) (X (n + 1)) :=
  condDistrib id (θ n) (μ (n + 1))

instance step_markov (n : ℕ) : IsMarkovKernel (step μ θ n) := by
  dsimp [step]
  infer_instance

noncomputable def transition (n : ℕ) : Kernel (∀ i : Finset.Iic n, X i) (X (n + 1)) :=
  (step μ θ n).comap (fun x => x ⟨n, by simp⟩) (by fun_prop)

instance transition_markov (n : ℕ) : IsMarkovKernel (transition μ θ n) := by
  dsimp [transition]
  infer_instance

noncomputable def law : Measure (∀ n, X n) := Kernel.trajMeasure (μ 0) (transition μ θ)

instance law_probability : IsProbabilityMeasure (law μ θ) := by
  dsimp [law]
  infer_instance

lemma hasCondDistrib_step (n : ℕ) :
    HasCondDistrib (fun x : ∀ n, X n => x (n + 1)) (fun x => x n)
      (step μ θ n) (law μ θ) := by
  have h : HasCondDistrib (fun x : ∀ n, X n => x (n + 1))
      (frestrictLe n) (transition μ θ n) (law μ θ) :=
    ⟨by fun_prop, Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm⟩
  exact h.comp_right

lemma map_zero : (law μ θ).map (fun x => x 0) = μ 0 := by
  have hrestrict : (law μ θ).map (frestrictLe 0) =
      (μ 0).map (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 => X i)).symm := by
    rw [law, Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
    try rfl
  have h := congrArg (fun ρ => ρ.map (fun x : ∀ i : Finset.Iic 0, X i => x ⟨0, by simp⟩)) hrestrict
  erw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  change (law μ θ).map (fun x => x 0) = (μ 0).map id at h
  simpa only [Measure.map_id] using h

variable (hp : ∀ n, (μ (n + 1)).map (θ n) = μ n)

include hθ hp

lemma map_eval (n : ℕ) : (law μ θ).map (fun x => x n) = μ n := by
  induction n with
  | zero => exact map_zero μ θ
  | succ n ih =>
    have h := congrArg Measure.snd (hasCondDistrib_step μ θ n).map_eq
    rw [Measure.snd_map_prodMk (by fun_prop), Measure.snd_compProd, ih] at h
    rw [← hp n, step, condDistrib_comp_map (hθ n).aemeasurable aemeasurable_id,
      Measure.map_id] at h
    exact h

lemma map_pair (n : ℕ) :
    (law μ θ).map (fun x => (x n, x (n + 1))) =
      (μ (n + 1)).map (fun x => (θ n x, x)) := by
  rw [(hasCondDistrib_step μ θ n).map_eq, map_eval μ θ hθ hp n,
    ← hp n, step, compProd_map_condDistrib aemeasurable_id]
  rfl

lemma ae_compatible (n : ℕ) : ∀ᵐ x ∂law μ θ, θ n (x (n + 1)) = x n := by
  have h : ∀ᵐ p ∂(law μ θ).map (fun x => (x n, x (n + 1))), θ n p.2 = p.1 := by
    rw [map_pair μ θ hθ hp n]
    exact (ae_map_iff (by fun_prop) (measurableSet_eq_fun ((hθ n).comp measurable_snd) measurable_fst)).mpr (Filter.Eventually.of_forall (by simp))
  exact (ae_map_iff (by fun_prop) (measurableSet_eq_fun ((hθ n).comp measurable_snd) measurable_fst)).mp h

lemma ae_all_compatible : ∀ᵐ x ∂law μ θ, ∀ n, θ n (x (n + 1)) = x n := by
  simpa only [ae_all_iff] using fun n => ae_compatible μ θ hθ hp n

end
section


variable {X : ℕ → Type*}
    (θ : ∀ n, X (n + 1) → X n)

def bond {n m : ℕ} (h : n ≤ m) : X m → X n :=
  Nat.leRecOn (C := fun j => X j → X n) h (fun {j} f => f ∘ θ j) id

@[simp] lemma bond_self (n : ℕ) : bond θ (le_refl n) = id := by
  exact Nat.leRecOn_self _

lemma bond_succ {n m : ℕ} (h : n ≤ m) :
    bond θ (h.trans (Nat.le_succ m)) = bond θ h ∘ θ m := by
  exact Nat.leRecOn_succ h _

variable [∀ n, MeasurableSpace (X n)]

lemma measurable_bond (hθ : ∀ n, Measurable (θ n)) {n m : ℕ} (h : n ≤ m) :
    Measurable (bond θ h) := by
  induction m, h using Nat.le_induction with
  | base => simp only [bond_self]; exact measurable_id
  | succ m h ih => rw [bond_succ]; exact ih.comp (hθ m)

omit [∀ n, MeasurableSpace (X n)] in
lemma bond_apply_of_compatible {x : ∀ n, X n}
    (hx : ∀ n, θ n (x (n + 1)) = x n) {n m : ℕ} (h : n ≤ m) :
    bond θ h (x m) = x n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m h ih => rw [bond_succ]; simpa only [Function.comp_apply, hx m] using ih

lemma map_restrict_of_compatible (hθ : ∀ n, Measurable (θ n))
    {ρ : Measure (∀ n, X n)}
    (hc : ∀ᵐ x ∂ρ, ∀ n, θ n (x (n + 1)) = x n)
    (I : Finset ℕ) (m : ℕ) (hm : ∀ i ∈ I, i ≤ m) :
    ρ.map I.restrict = (ρ.map (fun x => x m)).map
      (fun x (i : I) => bond θ (hm i i.2) x) := by
  rw [Measure.map_map (Measurable.of_eval (fun (i : I) =>
    measurable_bond θ hθ (hm i i.2))) (by fun_prop)]
  apply Measure.map_congr
  filter_upwards [hc] with x hx
  funext i
  exact (bond_apply_of_compatible θ hx (hm i i.2)).symm

theorem unique_of_compatible (hθ : ∀ n, Measurable (θ n))
    {ρ σ : Measure (∀ n, X n)} [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (hρ : ∀ᵐ x ∂ρ, ∀ n, θ n (x (n + 1)) = x n)
    (hσ : ∀ᵐ x ∂σ, ∀ n, θ n (x (n + 1)) = x n)
    (hmap : ∀ n, ρ.map (fun x => x n) = σ.map (fun x => x n)) : ρ = σ := by
  let P (I : Finset ℕ) := σ.map I.restrict
  have hP : ∀ I, IsFiniteMeasure (P I) := fun I => by
    dsimp [P]; infer_instance
  let := hP
  have hρP : IsProjectiveLimit ρ P := by
    intro I
    rw [map_restrict_of_compatible θ hθ hρ I (I.sup id)
      (fun i hi => Finset.le_sup (f := id) hi),
      hmap (I.sup id)]
    exact (map_restrict_of_compatible θ hθ hσ I (I.sup id)
      (fun i hi => Finset.le_sup (f := id) hi)).symm
  exact hρP.unique (fun _ => rfl)


end


end SequentialLimit

namespace InverseSystems

section
open Rokhlin.SequentialLimit

variable {X : ℕ → Type*}

abbrev Path (θ : ∀ n, X (n + 1) → X n) :=
  {x : ∀ n, X n // ∀ n, θ n (x (n + 1)) = x n}

def eval (θ : ∀ n, X (n + 1) → X n) (n : ℕ) : Path θ → X n := fun x => x.val n

@[fun_prop] lemma measurable_eval {θ : ∀ n, X (n + 1) → X n}
    [∀ n, MeasurableSpace (X n)] (n : ℕ) : Measurable (eval θ n) :=
  (measurable_pi_apply n).comp measurable_subtype_coe

variable [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)]
  (θ : ∀ n, X (n + 1) → X n) (hθ : ∀ n, Measurable (θ n))

include hθ in
lemma measurableSet_path : MeasurableSet {x : ∀ n, X n | ∀ n, θ n (x (n + 1)) = x n} := by
  simpa only [Set.ofPred_forall, Function.comp_def] using MeasurableSet.iInter (fun n =>
    measurableSet_eq_fun ((hθ n).comp (measurable_pi_apply (n + 1))) (measurable_pi_apply n))

include hθ in
lemma standardBorel_path : StandardBorelSpace (Path θ) :=
  (measurableSet_path θ hθ).standardBorel

variable [∀ n, Nonempty (X n)] (μ : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
  (hp : ∀ n, (μ (n + 1)).map (θ n) = μ n)

noncomputable def law : Measure (Path θ) :=
  (SequentialLimit.law μ θ).comap Subtype.val

include hθ hp in
lemma law_probability : IsProbabilityMeasure (law θ μ) := by
  apply (MeasurableEmbedding.subtype_coe (measurableSet_path θ hθ)).isProbabilityMeasure_comap
  filter_upwards [ae_all_compatible μ θ hθ hp] with x hx
  exact ⟨⟨x, hx⟩, rfl⟩

include hθ hp in
lemma map_val_law : (law θ μ).map Subtype.val = SequentialLimit.law μ θ := by
  exact (map_comap_subtype_coe (measurableSet_path θ hθ)
    (SequentialLimit.law μ θ)).trans
    (Measure.restrict_eq_self_of_ae_mem (ae_all_compatible μ θ hθ hp))

include hθ hp in
lemma map_eval_law (n : ℕ) : (law θ μ).map (eval θ n) = μ n := by
  change (law θ μ).map ((fun x : ∀ n, X n => x n) ∘ Subtype.val) = _
  rw [← Measure.map_map (measurable_pi_apply n) measurable_subtype_coe,
    map_val_law θ hθ μ hp, map_eval μ θ hθ hp]

include hθ hp in
lemma nonempty_path : Nonempty (Path θ) := by
  let := law_probability θ hθ μ hp
  exact nonempty_of_isProbabilityMeasure (law θ μ)

omit [∀ n, Nonempty (X n)] in
include hθ in
lemma unique {ρ σ : Measure (Path θ)} [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (hmap : ∀ n, ρ.map (eval θ n) = σ.map (eval θ n)) : ρ = σ := by
  apply (MeasurableEmbedding.subtype_coe (measurableSet_path θ hθ)).map_injective
  apply unique_of_compatible θ hθ
  · exact (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_path θ hθ)).mpr (Filter.Eventually.of_forall Subtype.property)
  · exact (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_path θ hθ)).mpr (Filter.Eventually.of_forall Subtype.property)
  · intro n
    rw [Measure.map_map (measurable_pi_apply n) measurable_subtype_coe,
      Measure.map_map (measurable_pi_apply n) measurable_subtype_coe]
    exact hmap n

section Map
variable {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)] [∀ n, StandardBorelSpace (Y n)]
    {ψ : ∀ n, Y (n + 1) → Y n}
    (f : ∀ n, X n → Y n)
    (hc : ∀ n x, ψ n (f (n + 1) x) = f n (θ n x))

def map : Path θ → Path ψ := fun x =>
  ⟨fun n => f n (x.val n), fun n => by rw [hc, x.property]⟩

omit [∀ n, StandardBorelSpace (X n)] [∀ n, Nonempty (X n)]
  [∀ n, StandardBorelSpace (Y n)] in
@[fun_prop] lemma measurable_map (hf : ∀ n, Measurable (f n)) : Measurable (map θ f hc) :=
  (Measurable.of_eval (fun n => (hf n).comp (measurable_eval n))).subtype_mk

end Map

variable (T : ∀ n, X n ≃ᵐ X n)
    (hc : ∀ n x, θ n (T (n + 1) x) = T n (θ n x))

def time : Path θ ≃ᵐ Path θ where
  toFun := map θ (fun n => T n) hc
  invFun := map θ (fun n => (T n).symm) (fun n x => by
    apply (T n).injective
    rw [← hc, (T (n + 1)).apply_symm_apply, (T n).apply_symm_apply])
  left_inv x := Subtype.ext (by funext n; exact (T n).symm_apply_apply _)
  right_inv x := Subtype.ext (by funext n; exact (T n).apply_symm_apply _)
  measurable_toFun := (Measurable.of_eval (fun n =>
    (T n).measurable.comp (measurable_eval n))).subtype_mk
  measurable_invFun := (Measurable.of_eval (fun n =>
    (T n).symm.measurable.comp (measurable_eval n))).subtype_mk

end


variable {X : ℕ → Type*} {J : Type*} [∀ n, MeasurableSpace (X n)]
  (θ : ∀ n, X (n + 1) → X n)

def arrayBond (n : ℕ) : (J → X (n + 1)) → (J → X n) := fun y j => θ n (y j)

def transpose : Path (X := fun n => J → X n) (arrayBond θ) ≃ᵐ (J → Path θ) where
  toFun y j := ⟨fun n => y.val n j, fun n => congrFun (y.property n) j⟩
  invFun y := ⟨fun n j => (y j).val n, fun n => funext (fun j => (y j).property n)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := Measurable.of_eval (fun _ =>
    (Measurable.of_eval (fun n => (measurable_pi_apply _).comp
      (measurable_eval n))).subtype_mk)
  measurable_invFun := (Measurable.of_eval (fun n => Measurable.of_eval
    (fun j => (measurable_eval n).comp (measurable_pi_apply j)))).subtype_mk

variable [Countable J] [∀ n, StandardBorelSpace (X n)]
  (hθ : ∀ n, Measurable (θ n))

include hθ in
lemma array_unique {ρ σ : Measure (J → Path θ)} [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (hm : ∀ n, ρ.map (fun y j => eval θ n (y j)) =
      σ.map (fun y j => eval θ n (y j))) : ρ = σ := by
  apply (transpose (J := J) θ).symm.measurableEmbedding.map_injective
  apply unique (X := fun n => J → X n) (arrayBond θ) (fun n => Measurable.of_eval (fun _ =>
    (hθ n).comp (measurable_pi_apply _)))
  intro n
  rw [Measure.map_map (measurable_eval n) (transpose θ).symm.measurable,
    Measure.map_map (measurable_eval n) (transpose θ).symm.measurable]
  exact hm n

variable [∀ n, Nonempty (X n)] (ρ : ∀ n, Measure (J → X n))
  [∀ n, IsProbabilityMeasure (ρ n)]
  (hp : ∀ n, (ρ (n + 1)).map (fun y j => θ n (y j)) = ρ n)

noncomputable def arrayLaw : Measure (J → Path θ) :=
  (law (X := fun n => J → X n) (arrayBond θ) ρ).map (transpose θ)

include hθ hp in
lemma arrayLaw_probability : IsProbabilityMeasure (arrayLaw θ ρ) := by
  let := law_probability (X := fun n => J → X n) (arrayBond θ)
    (fun n => Measurable.of_eval (fun _ => (hθ n).comp (measurable_pi_apply _))) ρ hp
  exact (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (transpose θ).measurable.aemeasurable

include hθ hp in
lemma arrayLaw_map_eval (n : ℕ) :
    (arrayLaw θ ρ).map (fun y j => eval θ n (y j)) = ρ n := by
  have hm : Measurable (fun (y : J → Path θ) j => eval θ n (y j)) :=
    Measurable.of_eval (fun j =>
      (measurable_eval n).comp (measurable_pi_apply j))
  rw [arrayLaw, Measure.map_map hm (transpose θ).measurable]
  change (law (X := fun s => J → X s) (arrayBond θ) ρ).map
    (eval (X := fun s => J → X s) (arrayBond θ) n) = ρ n
  exact map_eval_law (X := fun n => J → X n) (arrayBond θ) (fun n => Measurable.of_eval (fun _ =>
    (hθ n).comp (measurable_pi_apply _))) ρ hp n

variable {K : Type*} [Countable K]

omit [∀ n, Nonempty (X n)] in
include hθ in
lemma array_pi_unique {ρ σ : Measure (K → J → Path θ)}
    [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (hm : ∀ n, ρ.map (fun y k j => eval θ n (y k j)) =
      σ.map (fun y k j => eval θ n (y k j))) : ρ = σ := by
  let e := (MeasurableEquiv.curry K J (Path θ)).symm
  apply e.measurableEmbedding.map_injective
  apply array_unique θ hθ
  intro n
  have hn := congrArg (Measure.map (MeasurableEquiv.curry K J (X n)).symm) (hm n)
  have hd : Measurable (fun (y : K → J → Path θ) k j => eval θ n (y k j)) :=
    Measurable.of_eval (fun k => Measurable.of_eval (fun j =>
      (measurable_eval n).comp ((measurable_pi_apply j).comp (measurable_pi_apply k))))
  have hf : Measurable (fun (y : K × J → Path θ) j => eval θ n (y j)) :=
    Measurable.of_eval (fun j =>
      (measurable_eval n).comp (measurable_pi_apply j))
  rw [Measure.map_map (MeasurableEquiv.curry K J (X n)).symm.measurable hd,
    Measure.map_map (MeasurableEquiv.curry K J (X n)).symm.measurable hd] at hn
  rw [Measure.map_map hf e.measurable, Measure.map_map hf e.measurable]
  exact hn


end InverseSystems

namespace ArrayObjects.Object
open Rokhlin.InverseSystems
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T}

structure Tower (base : InitialLaws I X T) where
  stage : ℕ → Object I base
  step : ∀ n, Extension (stage n) (stage (n + 1))

namespace Tower
variable (D : Tower base)

abbrev yBond (s : ℕ) : (D.stage (s + 1)).Y → (D.stage s).Y := (D.step s).state
abbrev uBond (s : ℕ) : (D.stage (s + 1)).U → (D.stage s).U := (D.step s).parameter

lemma measurable_yBond (s : ℕ) : Measurable (D.yBond s) := (D.step s).measurable_state
lemma measurable_uBond (s : ℕ) : Measurable (D.uBond s) := (D.step s).measurable_parameter

noncomputable abbrev stateSpace : StandardSpace where
  α := Path (X := fun s => (D.stage s).Y) D.yBond
  measurableSpace := inferInstance
  standardBorel := standardBorel_path (X := fun s => (D.stage s).Y) D.yBond D.measurable_yBond
  nonempty := nonempty_path (X := fun s => (D.stage s).Y) D.yBond D.measurable_yBond
    (fun s => (D.stage s).localLaw) (fun s => (D.step s).localLaw_map)

noncomputable abbrev parameterSpace : StandardSpace where
  α := Path (X := fun s => (D.stage s).U) D.uBond
  measurableSpace := inferInstance
  standardBorel := standardBorel_path (X := fun s => (D.stage s).U) D.uBond D.measurable_uBond
  nonempty := nonempty_path (X := fun s => (D.stage s).U) D.uBond D.measurable_uBond
    (fun s => (D.stage s).parameter) (fun s => (D.step s).parameter_map)

def timeState : D.stateSpace ≃ᵐ D.stateSpace :=
  InverseSystems.time (X := fun s => (D.stage s).Y) D.yBond (fun s => (D.stage s).timeY)
    (fun s x => congrFun (D.step s).time_state x)

def timeParameter : D.parameterSpace ≃ᵐ D.parameterSpace :=
  InverseSystems.time (X := fun s => (D.stage s).U) D.uBond (fun s => (D.stage s).timeU)
    (fun s x => congrFun (D.step s).time_parameter x)

abbrev proj (s : ℕ) : D.stateSpace → (D.stage s).Y := InverseSystems.eval (X := fun s => (D.stage s).Y) D.yBond s
abbrev pproj (s : ℕ) : D.parameterSpace → (D.stage s).U := InverseSystems.eval (X := fun s => (D.stage s).U) D.uBond s

@[fun_prop] lemma measurable_proj (s : ℕ) : Measurable (D.proj s) := InverseSystems.measurable_eval s
@[fun_prop] lemma measurable_pproj (s : ℕ) : Measurable (D.pproj s) := InverseSystems.measurable_eval s

def x : D.stateSpace → X := (D.stage 0).x ∘ D.proj 0

def par : D.stateSpace → D.parameterSpace :=
  InverseSystems.map (X := fun s => (D.stage s).Y)
    (Y := fun s => (D.stage s).U) D.yBond (ψ := D.uBond) (fun s => (D.stage s).par)
    (fun s y => (congrFun (D.step s).state_par y).symm)

@[fun_prop] lemma measurable_x : Measurable D.x :=
  (D.stage 0).measurable_x.comp (D.measurable_proj 0)

@[fun_prop] lemma measurable_par : Measurable D.par :=
  InverseSystems.measurable_map (X := fun s => (D.stage s).Y)
    (Y := fun s => (D.stage s).U) (ψ := D.uBond) D.yBond _ _ (fun s => (D.stage s).measurable_par)

lemma time_x : D.x ∘ D.timeState = T ∘ D.x := by
  funext y
  exact congrFun (D.stage 0).time_x (D.proj 0 y)

lemma time_par : D.par ∘ D.timeState = D.timeParameter ∘ D.par := by
  funext y
  apply Subtype.ext
  funext s
  exact congrFun (D.stage s).time_par (D.proj s y)

lemma x_stage (s : ℕ) : (D.stage s).x ∘ D.proj s = D.x := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [← ih]
    funext y
    change (D.stage (s + 1)).x (y.val (s + 1)) = (D.stage s).x (y.val s)
    rw [← y.property s]
    exact (congrFun (D.step s).state_x (y.val (s + 1))).symm

lemma par_stage (s : ℕ) : (D.stage s).par ∘ D.proj s = D.pproj s ∘ D.par := rfl

lemma array_coherent (n s : ℕ) :
    ((D.stage (s + 1)).law n).map (fun y v => D.yBond s (y v)) = (D.stage s).law n :=
  (D.step s).laws n

noncomputable def arrayLaw (n : ℕ) : Measure (Arr I D.stateSpace n) :=
  InverseSystems.arrayLaw (X := fun s => (D.stage s).Y) D.yBond (fun s => (D.stage s).law n)

instance arrayLaw_probability (n : ℕ) : IsProbabilityMeasure (D.arrayLaw n) :=
  InverseSystems.arrayLaw_probability (X := fun s => (D.stage s).Y) D.yBond D.measurable_yBond
    (fun s => (D.stage s).law n) (D.array_coherent n)

lemma array_marginal (n s : ℕ) : (D.arrayLaw n).map (amap (D.proj s) n) =
    (D.stage s).law n :=
  InverseSystems.arrayLaw_map_eval (X := fun s => (D.stage s).Y) D.yBond D.measurable_yBond
    (fun s => (D.stage s).law n) (D.array_coherent n) s

lemma array_over_base (n : ℕ) : (D.arrayLaw n).map (amap D.x n) = base.law n := by
  rw [← (D.stage 0).over_base n, ← D.array_marginal n 0,
    Measure.map_map (measurable_amap (D.stage 0).measurable_x n)
      (measurable_amap (D.measurable_proj 0) n)]
  rfl

lemma array_invariant (n : ℕ) :
    MeasurePreserving (amap D.timeState n) (D.arrayLaw n) (D.arrayLaw n) := by
  refine ⟨measurable_amap D.timeState.measurable n, ?_⟩
  apply InverseSystems.array_unique (X := fun s => (D.stage s).Y) D.yBond D.measurable_yBond
  intro s
  change ((D.arrayLaw n).map (amap D.timeState n)).map (amap (D.proj s) n) =
    (D.arrayLaw n).map (amap (D.proj s) n)
  rw [Measure.map_map (measurable_amap (D.measurable_proj s) n)
    (measurable_amap D.timeState.measurable n)]
  change (D.arrayLaw n).map (amap (D.stage s).timeY n ∘ amap (D.proj s) n) = _
  rw [← Measure.map_map (measurable_amap (D.stage s).timeY.measurable n)
    (measurable_amap (D.measurable_proj s) n), D.array_marginal,
    (D.stage s).invariant n |>.map_eq]

lemma array_consistent (n : ℕ) (a : Fin (n + 1)) (i : I) :
    (D.arrayLaw (n + 1)).map (plane n a i) = D.arrayLaw n := by
  apply InverseSystems.array_unique (X := fun s => (D.stage s).Y) D.yBond D.measurable_yBond
  intro s
  change ((D.arrayLaw (n + 1)).map (plane n a i)).map (amap (D.proj s) n) =
    (D.arrayLaw n).map (amap (D.proj s) n)
  rw [Measure.map_map (measurable_amap (D.measurable_proj s) n) (measurable_plane n a i)]
  change (D.arrayLaw (n + 1)).map (plane n a i ∘ amap (D.proj s) (n + 1)) = _
  rw [← Measure.map_map (measurable_plane n a i)
    (measurable_amap (D.measurable_proj s) (n + 1)), D.array_marginal,
    (D.stage s).consistent, D.array_marginal]

lemma array_proper (n : ℕ) (J : Finset I) (hJ : J ≠ Finset.univ) :
    (D.arrayLaw (n + 1)).map (planes n J) = Measure.pi (fun _ : J => D.arrayLaw n) := by
  apply InverseSystems.array_pi_unique (X := fun s => (D.stage s).Y)
    D.yBond D.measurable_yBond
  intro s
  change ((D.arrayLaw (n + 1)).map (planes n J)).map
    (fun y j => amap (D.proj s) n (y j)) = _
  have hm : Measurable (fun (y : J → Arr I D.stateSpace n) j =>
      amap (D.proj s) n (y j)) := Measurable.of_eval (fun j =>
    (measurable_amap (D.measurable_proj s) n).comp (measurable_pi_apply j))
  rw [Measure.map_map hm (measurable_planes n J)]
  change (D.arrayLaw (n + 1)).map (planes n J ∘ amap (D.proj s) (n + 1)) = _
  rw [← Measure.map_map (measurable_planes n J)
    (measurable_amap (D.measurable_proj s) (n + 1)), D.array_marginal,
    (D.stage s).proper n J hJ]
  change Measure.pi (fun _ : J => (D.stage s).law n) =
    (Measure.pi (fun _ : J => D.arrayLaw n)).map (fun y j => amap (D.proj s) n (y j))
  rw [Measure.pi_map_pi (fun _ => (measurable_amap (D.measurable_proj s) n).aemeasurable)]
  simp only [D.array_marginal]

noncomputable def localLaw : Measure D.stateSpace :=
  (D.arrayLaw 0).map (zeroEquiv I D.stateSpace)

instance localLaw_probability : IsProbabilityMeasure D.localLaw :=
  (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (zeroEquiv I D.stateSpace).measurable.aemeasurable

lemma localLaw_marginal (s : ℕ) : D.localLaw.map (D.proj s) = (D.stage s).localLaw := by
  rw [localLaw, Measure.map_map (D.measurable_proj s) (zeroEquiv I D.stateSpace).measurable]
  change (D.arrayLaw 0).map (zeroEquiv I (D.stage s).Y ∘ amap (D.proj s) 0) = _
  rw [← Measure.map_map (zeroEquiv I (D.stage s).Y).measurable
    (measurable_amap (D.measurable_proj s) 0), D.array_marginal]
  rfl

lemma local_indep_stage (s : ℕ) : IndepFun D.x (D.pproj s ∘ D.par) D.localLaw := by
  have h : IndepFun ((D.stage s).x ∘ D.proj s)
      ((D.stage s).par ∘ D.proj s) D.localLaw := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro A B hA hB
    have he := (D.stage s).local_independent.measure_inter_preimage_eq_mul A B hA hB
    change (D.stage s).localLaw _ = (D.stage s).localLaw _ * (D.stage s).localLaw _ at he
    rw [← D.localLaw_marginal s,
      Measure.map_apply (D.measurable_proj s)
        (((D.stage s).measurable_x hA).inter ((D.stage s).measurable_par hB)),
      Measure.map_apply (D.measurable_proj s) ((D.stage s).measurable_x hA),
      Measure.map_apply (D.measurable_proj s) ((D.stage s).measurable_par hB)] at he
    exact he
  rwa [D.x_stage s, D.par_stage s] at h

lemma parameter_comap :
    MeasurableSpace.comap D.par (inferInstance : MeasurableSpace D.parameterSpace) =
      ⨆ s, MeasurableSpace.comap (D.pproj s ∘ D.par)
        (inferInstance : MeasurableSpace (D.stage s).U) := by
  change MeasurableSpace.comap D.par
    (MeasurableSpace.comap Subtype.val MeasurableSpace.pi) = _
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp]
  rfl

lemma parameter_comap_mono : Monotone (fun s =>
    MeasurableSpace.comap (D.pproj s ∘ D.par)
      (inferInstance : MeasurableSpace (D.stage s).U)) := by
  apply monotone_nat_of_le_succ
  intro s
  have he : D.pproj s ∘ D.par = D.uBond s ∘ (D.pproj (s + 1) ∘ D.par) := by
    funext y
    exact ((D.par y).property s).symm
  rw [he, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (D.measurable_uBond s).comap_le

lemma local_independent : IndepFun D.x D.par D.localLaw := by
  rw [IndepFun_iff_Indep]
  apply Indep.symm
  rw [D.parameter_comap]
  apply indep_iSup_of_monotone
  · intro s
    exact (D.local_indep_stage s).symm
  · intro s
    exact ((D.measurable_pproj s).comp D.measurable_par).comap_le
  · exact D.measurable_x.comap_le
  · exact D.parameter_comap_mono

end Tower
end ArrayObjects.Object

open MeasureTheory Filter
open scoped BigOperators Topology

namespace ConditionalLimits

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (𝒢 : ι → Filtration ℕ ‹MeasurableSpace Ω›)
    (f : ι → Ω → ℝ)

theorem product_identity
    (h : ∀ᶠ n in atTop,
      μ[(fun x => ∏ i, f i x) | ℱ n] =ᵐ[μ]
        (fun x => ∏ i, μ[f i | 𝒢 i n] x)) :
    μ[(fun x => ∏ i, f i x) | ⨆ n, ℱ n] =ᵐ[μ]
      (fun x => ∏ i, μ[f i | ⨆ n, 𝒢 i n] x) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have he : ∀ᵐ x ∂μ, ∀ n, N ≤ n →
      μ[(fun x => ∏ i, f i x) | ℱ n] x = ∏ i, μ[f i | 𝒢 i n] x := by
    rw [ae_all_iff]
    intro n
    by_cases hn : N ≤ n
    · exact (hN n hn).mono (fun _ hx _ => hx)
    · exact Filter.Eventually.of_forall (by simp [hn])
  have hG : ∀ᵐ x ∂μ, ∀ i, Tendsto (fun n => μ[f i | 𝒢 i n] x) atTop
      (𝓝 (μ[f i | ⨆ n, 𝒢 i n] x)) := by
    rw [ae_all_iff]
    exact fun i => tendsto_ae_condExp (ℱ := 𝒢 i) (f i)
  filter_upwards [tendsto_ae_condExp (ℱ := ℱ) (fun x => ∏ i, f i x), hG, he]
    with x hF hG hx
  apply tendsto_nhds_unique hF
  exact (tendsto_finsetProd _ (fun i _ => hG i)).congr'
    (eventually_atTop.mpr ⟨N, fun n hn => (hx n hn).symm⟩)

end ConditionalLimits

namespace ConditionalProducts
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {U Ω ι : Type*} {Y : ι → Type*}
  [MeasurableSpace U] [MeasurableSpace Ω] [Fintype ι]
  [∀ i, MeasurableSpace (Y i)] [∀ i, StandardBorelSpace (Y i)]

lemma kernel_ae_eq_of_boxes (ν : Measure U) [IsFiniteMeasure ν]
    (κ η : Kernel U (∀ i, Y i)) [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : ∀ s : ∀ i, Set (Y i), (∀ i, MeasurableSet (s i)) →
      (fun p => κ p (Set.pi Set.univ s)) =ᵐ[ν] (fun p => η p (Set.pi Set.univ s))) :
    κ =ᵐ[ν] η := by
  apply Kernel.ae_eq_of_compProd_eq
  let D : Set (Set (∀ i, Y i)) :=
    Set.pi Set.univ '' Set.pi Set.univ (fun i => {s : Set (Y i) | MeasurableSet s})
  let C : Set (Set (U × (∀ i, Y i))) :=
    Set.image2 (· ×ˢ ·) {s : Set U | MeasurableSet s} D
  have hgen : MeasurableSpace.generateFrom C = (inferInstance : MeasurableSpace (U × (∀ i, Y i))) :=
    generateFrom_eq_prod MeasurableSpace.generateFrom_measurableSet generateFrom_pi
      isCountablySpanning_measurableSet
      (IsCountablySpanning.pi (fun _ => isCountablySpanning_measurableSet))
  refine Measure.ext_of_generateFrom_of_iUnion C (fun _ => Set.univ) hgen.symm
    (MeasurableSpace.isPiSystem_measurableSet.prod isPiSystem_pi) (by
      exact Set.iUnion_const (s := Set.univ)) ?_
    (fun _ => measure_ne_top _ _) ?_
  · intro _
    refine ⟨Set.univ, MeasurableSet.univ, Set.univ, ?_, by simp⟩
    exact ⟨fun _ => Set.univ, fun _ _ => MeasurableSet.univ, by simp⟩
  · rintro _ ⟨A, hA, _, ⟨s, hs, rfl⟩, rfl⟩
    have hS : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi
      (fun i => hs i (Set.mem_univ i))
    rw [Measure.compProd_apply_prod hA hS, Measure.compProd_apply_prod hA hS]
    exact lintegral_congr_ae ((h s (fun i => hs i (Set.mem_univ i))).filter_mono
      ae_restrict_le)

variable [∀ i, Nonempty (Y i)]

lemma condDistrib_product_of_indicator
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Ω → U) (O : Ω → ∀ i, Y i) (hE : Measurable E) (hO : Measurable O)
    (κ : ∀ i, Kernel U (Y i)) [∀ i, IsMarkovKernel (κ i)]
    (h : ∀ s : ∀ i, Set (Y i), (∀ i, MeasurableSet (s i)) →
      μ⟦O ⁻¹' Set.pi Set.univ s | MeasurableSpace.comap E inferInstance⟧ =ᵐ[μ]
        (fun ω => ∏ i, (κ i (E ω)).real (s i))) :
    condDistrib O E μ =ᵐ[μ.map E] FiniteKernel.pi κ := by
  apply kernel_ae_eq_of_boxes
  intro s hs
  have hS : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
  have he := (condDistrib_ae_eq_condExp (μ := μ) hE hO hS).trans (h s hs)
  apply (ae_map_iff hE.aemeasurable ?_).mpr
  · filter_upwards [he] with ω hω
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    simpa only [Measure.real, FiniteKernel.pi_apply, Measure.pi_pi, ENNReal.toReal_prod]
      using hω
  · exact measurableSet_eq_fun ((condDistrib O E μ).measurable_coe hS)
      ((FiniteKernel.pi κ).measurable_coe hS)

end ConditionalProducts

open MeasureTheory ProbabilityTheory
namespace ConditionalPullback
variable {Ω Z U B : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  [MeasurableSpace U] [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]

lemma indicator (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → Z) (p : Z → U) (o : Z → B)
    (hf : Measurable f) (hp : Measurable p) (ho : Measurable o)
    (S : Set B) (hS : MeasurableSet S) :
    μ⟦(o ∘ f) ⁻¹' S | MeasurableSpace.comap (p ∘ f) inferInstance⟧ =ᵐ[μ]
      ((μ.map f)⟦o ⁻¹' S | MeasurableSpace.comap p inferInstance⟧ ∘ f) := by
  have hk := condDistrib_map (ν := μ) hp.aemeasurable ho.aemeasurable hf.aemeasurable
  have hk' := ae_of_ae_map (hp.comp hf).aemeasurable hk
  have hc := condDistrib_ae_eq_condExp (μ := μ) (hp.comp hf) (ho.comp hf) hS
  have hc' := ae_of_ae_map hf.aemeasurable
    (condDistrib_ae_eq_condExp (μ := μ.map f) hp ho hS)
  filter_upwards [hk', hc, hc'] with ω hω h1 h2
  exact h1.symm.trans ((congrArg (fun ν : Measure B => ν.real S) hω).symm.trans h2)

end ConditionalPullback

namespace ArrayObjects.Object
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T}

lemma indicator_product (M : Object I base) (n : ℕ) (J : Finset I)
    (hJ : J ≠ Finset.univ) (S : J → Set (Arr I M.Y n))
    (hS : ∀ j, MeasurableSet (S j)) :
    (M.law (n + 1))⟦planes n J ⁻¹' Set.pi Set.univ S |
      MeasurableSpace.comap (amap M.par (n + 1)) inferInstance⟧ =ᵐ[M.law (n + 1)]
    (fun y => ∏ j : J, ((M.law (n + 1))⟦plane n (Fin.last n) (j : I) ⁻¹' S j |
      MeasurableSpace.comap (amap M.par n ∘ plane n (Fin.last n) (j : I)) inferInstance⟧) y) := by
  have hk := ae_of_ae_map (measurable_amap M.measurable_par (n + 1)).aemeasurable
    (M.conditional n J hJ)
  have hc := condDistrib_ae_eq_condExp (μ := M.law (n + 1))
    (measurable_amap M.measurable_par (n + 1)) (measurable_planes n J)
    (MeasurableSet.univ_pi hS)
  have hj : ∀ j : J,
      (fun y => (condDistrib (id : Arr I M.Y n → Arr I M.Y n)
        (amap M.par n) (M.law n) (amap M.par n (plane n (Fin.last n) (j : I) y))).real (S j))
        =ᵐ[M.law (n + 1)]
      (M.law (n + 1))⟦plane n (Fin.last n) (j : I) ⁻¹' S j |
        MeasurableSpace.comap (amap M.par n ∘ plane n (Fin.last n) (j : I)) inferInstance⟧ := by
    intro j
    have hlocal := condDistrib_ae_eq_condExp (μ := M.law n)
      (measurable_amap M.measurable_par n) measurable_id (hS j)
    have hpull := Rokhlin.ConditionalPullback.indicator (M.law (n + 1))
      (plane n (Fin.last n) (j : I)) (amap M.par n) id (measurable_plane _ _ _)
      (measurable_amap M.measurable_par n) measurable_id (S j) (hS j)
    rw [M.consistent] at hpull
    have hpres : MeasurePreserving (plane n (Fin.last n) (j : I))
        (M.law (n + 1)) (M.law n) := ⟨measurable_plane _ _ _, M.consistent _ _ _⟩
    exact (hpres.quasiMeasurePreserving.ae_eq_comp hlocal).trans hpull.symm
  have hall := ae_all_iff.mpr hj
  filter_upwards [hk, hc, hall] with y hk hc hj
  rw [← hc, hk]
  simp only [Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro j _
  exact hj j

end ArrayObjects.Object

namespace InverseSystems
variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  (θ : ∀ n, X (n + 1) → X n)
  {Ω J : Type*} (F : Ω → J → Path θ)

lemma comap_array_path :
    MeasurableSpace.comap F (inferInstance : MeasurableSpace (J → Path θ)) =
      ⨆ s, MeasurableSpace.comap (fun ω j => eval θ s (F ω j))
        (inferInstance : MeasurableSpace (J → X s)) := by
  change MeasurableSpace.comap F
    (⨆ j, MeasurableSpace.comap (Function.eval j)
      (MeasurableSpace.comap Subtype.val MeasurableSpace.pi)) = _
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rw [iSup_comm]
  rfl

lemma comap_array_path_mono (hθ : ∀ n, Measurable (θ n)) :
    Monotone (fun s => MeasurableSpace.comap (fun ω j => eval θ s (F ω j))
      (inferInstance : MeasurableSpace (J → X s))) := by
  apply monotone_nat_of_le_succ
  intro s
  have he : (fun ω j => eval θ s (F ω j)) =
      (fun y j => θ s (y j)) ∘ (fun ω j => eval θ (s + 1) (F ω j)) := by
    funext ω j
    exact ((F ω j).property s).symm
  rw [he, ← MeasurableSpace.comap_comp]
  apply MeasurableSpace.comap_mono
  exact (Measurable.of_eval (fun j => (hθ s).comp (measurable_pi_apply j))).comap_le
end InverseSystems

namespace ArrayObjects.Object.Tower

section
open MeasureTheory ProbabilityTheory Rokhlin.InverseSystems Filter
open scoped BigOperators Topology
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T} (D : Tower base)

lemma stage_indicator_product (n : ℕ) (J : Finset I) (hJ : J ≠ Finset.univ)
    (t : ℕ) (S : J → Set (Arr I (D.stage t).Y n))
    (hS : ∀ j, MeasurableSet (S j)) :
    (D.arrayLaw (n + 1))⟦(planes n J ∘ amap (D.proj t) (n + 1)) ⁻¹' Set.pi Set.univ S |
      MeasurableSpace.comap (amap (D.stage t).par (n + 1) ∘ amap (D.proj t) (n + 1))
        inferInstance⟧ =ᵐ[D.arrayLaw (n + 1)]
    (fun y => ∏ j : J, ((D.arrayLaw (n + 1))⟦
      (plane n (Fin.last n) (j : I) ∘ amap (D.proj t) (n + 1)) ⁻¹' S j |
      MeasurableSpace.comap (amap (D.stage t).par n ∘ plane n (Fin.last n) (j : I) ∘
        amap (D.proj t) (n + 1)) inferInstance⟧) y) := by
  have hp : MeasurePreserving (amap (D.proj t) (n + 1))
      (D.arrayLaw (n + 1)) ((D.stage t).law (n + 1)) :=
    ⟨measurable_amap (D.measurable_proj t) _, D.array_marginal _ _⟩
  have hs := hp.quasiMeasurePreserving.ae_eq_comp ((D.stage t).indicator_product n J hJ S hS)
  have hh := Rokhlin.ConditionalPullback.indicator (D.arrayLaw (n + 1))
    (amap (D.proj t) (n + 1)) (amap (D.stage t).par (n + 1)) (planes n J)
    (measurable_amap (D.measurable_proj t) _) (measurable_amap (D.stage t).measurable_par _)
    (measurable_planes n J) (Set.pi Set.univ S) (MeasurableSet.univ_pi hS)
  rw [D.array_marginal] at hh
  have hl := fun j : J => Rokhlin.ConditionalPullback.indicator (D.arrayLaw (n + 1))
    (amap (D.proj t) (n + 1))
    (amap (D.stage t).par n ∘ plane n (Fin.last n) (j : I)) (plane n (Fin.last n) (j : I))
    (measurable_amap (D.measurable_proj t) _)
    ((measurable_amap (D.stage t).measurable_par n).comp (measurable_plane _ _ _))
    (measurable_plane _ _ _) (S j) (hS j)
  simp only [D.array_marginal] at hl
  have hall := ae_all_iff.mpr hl
  filter_upwards [hs, hh, hall] with y hs hh hl
  rw [hh, hs]
  apply Finset.prod_congr rfl
  intro j _
  exact (hl j).symm

def parameterFiltration {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (E : Ω → Arr I D.parameterSpace n) (hE : Measurable E) :
    Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq s := MeasurableSpace.comap (amap (D.pproj s) n ∘ E) inferInstance
  mono' := InverseSystems.comap_array_path_mono (X := fun s => (D.stage s).U) D.uBond E D.measurable_uBond
  le' s := ((measurable_amap (D.measurable_pproj s) n).comp hE).comap_le

lemma parameterFiltration_iSup {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (E : Ω → Arr I D.parameterSpace n) (hE : Measurable E) :
    (⨆ s, D.parameterFiltration n E hE s) = MeasurableSpace.comap E inferInstance :=
  (InverseSystems.comap_array_path (X := fun s => (D.stage s).U) D.uBond E).symm


lemma proj_bond {s t : ℕ} (h : s ≤ t) :
    D.proj s = SequentialLimit.bond (X := fun s => (D.stage s).Y) D.yBond h ∘ D.proj t := by
  funext y
  exact (SequentialLimit.bond_apply_of_compatible (X := fun s => (D.stage s).Y) D.yBond y.property h).symm

lemma indicator_box {Ω ι : Type*} {Z : ι → Type*} [Fintype ι]
    (O : Ω → ∀ j, Z j) (S : ∀ j, Set (Z j)) :
    (O ⁻¹' Set.pi Set.univ S).indicator (fun _ => (1 : ℝ)) =
      (fun y => ∏ j, ((fun y => O y j) ⁻¹' S j).indicator (fun _ => (1 : ℝ)) y) := by
  classical
  funext y
  simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
    forall_true_left]
  rw [Finset.prod_boole]
  simp

lemma limit_indicator_product (n : ℕ) (J : Finset I) (hJ : J ≠ Finset.univ)
    (s : ℕ) (S : J → Set (Arr I (D.stage s).Y n))
    (hS : ∀ j, MeasurableSet (S j)) :
    (D.arrayLaw (n + 1))⟦(planes n J ∘ amap (D.proj s) (n + 1)) ⁻¹' Set.pi Set.univ S |
      MeasurableSpace.comap (amap D.par (n + 1)) inferInstance⟧ =ᵐ[D.arrayLaw (n + 1)]
    (fun y => ∏ j : J, ((D.arrayLaw (n + 1))⟦
      (plane n (Fin.last n) (j : I) ∘ amap (D.proj s) (n + 1)) ⁻¹' S j |
      MeasurableSpace.comap (amap D.par n ∘ plane n (Fin.last n) (j : I)) inferInstance⟧) y) := by
  let ℱ := D.parameterFiltration (n + 1) (amap D.par (n + 1))
    (measurable_amap D.measurable_par (n + 1))
  let 𝒢 := fun j : J => D.parameterFiltration n (amap D.par n ∘ plane n (Fin.last n) (j : I))
    ((measurable_amap D.measurable_par n).comp (measurable_plane _ _ _))
  let f := fun j : J => ((plane n (Fin.last n) (j : I) ∘ amap (D.proj s) (n + 1)) ⁻¹' S j).indicator
    (fun _ => (1 : ℝ))
  have hF : (⨆ t, ℱ t) = MeasurableSpace.comap (amap D.par (n + 1)) inferInstance :=
    D.parameterFiltration_iSup _ _ _
  have hG : ∀ j : J, (⨆ t, 𝒢 j t) =
      MeasurableSpace.comap (amap D.par n ∘ plane n (Fin.last n) (j : I)) inferInstance :=
    fun _ => D.parameterFiltration_iSup _ _ _
  have hx : (fun y => ∏ j, f j y) =
      ((planes n J ∘ amap (D.proj s) (n + 1)) ⁻¹' Set.pi Set.univ S).indicator
        (fun _ => (1 : ℝ)) := (indicator_box _ _).symm
  have hh : ∀ᶠ t in atTop, (D.arrayLaw (n + 1))[(fun y => ∏ j, f j y) | ℱ t] =ᵐ[D.arrayLaw (n + 1)]
      (fun y => ∏ j, (D.arrayLaw (n + 1))[f j | 𝒢 j t] y) := by
    refine eventually_atTop.mpr ⟨s, fun t ht => ?_⟩
    let b := SequentialLimit.bond (X := fun s => (D.stage s).Y) D.yBond ht
    have hb : Measurable b := SequentialLimit.measurable_bond (X := fun s => (D.stage s).Y) D.yBond D.measurable_yBond ht
    let S' : J → Set (Arr I (D.stage t).Y n) := fun j => amap b n ⁻¹' S j
    have hS' : ∀ j, MeasurableSet (S' j) := fun j => (measurable_amap hb n) (hS j)
    have he := D.stage_indicator_product n J hJ t S' hS'
    have ho : (planes n J ∘ amap (D.proj t) (n + 1)) ⁻¹' Set.pi Set.univ S' =
        (planes n J ∘ amap (D.proj s) (n + 1)) ⁻¹' Set.pi Set.univ S := by
      rw [D.proj_bond ht]
      rfl
    have ho' : ∀ j : J,
        (plane n (Fin.last n) (j : I) ∘ amap (D.proj t) (n + 1)) ⁻¹' S' j =
        (plane n (Fin.last n) (j : I) ∘ amap (D.proj s) (n + 1)) ⁻¹' S j := by
      intro j
      rw [D.proj_bond ht]
      rfl
    rw [ho] at he
    simp_rw [ho'] at he
    rw [hx]
    exact he
  have h := Rokhlin.ConditionalLimits.product_identity (D.arrayLaw (n + 1)) ℱ 𝒢 f hh
  rw [hF, hx] at h
  simp only [hG] at h
  exact h


end

open MeasureTheory ProbabilityTheory Rokhlin.InverseSystems
open scoped BigOperators
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T} (D : Tower base)

lemma conditional_observation (n : ℕ) (J : Finset I) (hJ : J ≠ Finset.univ) (s : ℕ) :
    condDistrib (planes n J ∘ amap (D.proj s) (n + 1)) (amap D.par (n + 1))
      (D.arrayLaw (n + 1)) =ᵐ[(D.arrayLaw (n + 1)).map (amap D.par (n + 1))]
    FiniteKernel.pi (fun j : J =>
      (condDistrib (amap (D.proj s) n) (amap D.par n) (D.arrayLaw n)).comap
        (plane n (Fin.last n) (j : I)) (measurable_plane _ _ _)) := by
  apply Rokhlin.ConditionalProducts.condDistrib_product_of_indicator
    (D.arrayLaw (n + 1)) (amap D.par (n + 1))
    (planes n J ∘ amap (D.proj s) (n + 1))
    (measurable_amap D.measurable_par _) ((measurable_planes n J).comp
      (measurable_amap (D.measurable_proj s) _))
  intro S hS
  have h := D.limit_indicator_product n J hJ s S hS
  have hj : ∀ j : J,
      (D.arrayLaw (n + 1))⟦
        (plane n (Fin.last n) (j : I) ∘ amap (D.proj s) (n + 1)) ⁻¹' S j |
        MeasurableSpace.comap (amap D.par n ∘ plane n (Fin.last n) (j : I)) inferInstance⟧
        =ᵐ[D.arrayLaw (n + 1)]
      (fun y => (condDistrib (amap (D.proj s) n) (amap D.par n) (D.arrayLaw n)
        (amap D.par n (plane n (Fin.last n) (j : I) y))).real (S j)) := by
    intro j
    have hpull := Rokhlin.ConditionalPullback.indicator (D.arrayLaw (n + 1))
      (plane n (Fin.last n) (j : I)) (amap D.par n) (amap (D.proj s) n)
      (measurable_plane _ _ _) (measurable_amap D.measurable_par _)
      (measurable_amap (D.measurable_proj s) _) (S j) (hS j)
    rw [D.array_consistent] at hpull
    have hl := condDistrib_ae_eq_condExp (μ := D.arrayLaw n)
      (measurable_amap D.measurable_par _) (measurable_amap (D.measurable_proj s) _) (hS j)
    have hpres : MeasurePreserving (plane n (Fin.last n) (j : I))
        (D.arrayLaw (n + 1)) (D.arrayLaw n) :=
      ⟨measurable_plane _ _ _, D.array_consistent _ _ _⟩
    exact hpull.trans (hpres.quasiMeasurePreserving.ae_eq_comp hl).symm
  have hall := ae_all_iff.mpr hj
  filter_upwards [h, hall] with y h hj
  rw [h]
  apply Finset.prod_congr rfl
  intro j _
  exact hj j

lemma parameter_plane_preserving (n : ℕ) (i : I) :
    MeasurePreserving (plane n (Fin.last n) i)
      ((D.arrayLaw (n + 1)).map (amap D.par (n + 1)))
      ((D.arrayLaw n).map (amap D.par n)) := by
  refine ⟨measurable_plane _ _ _, ?_⟩
  rw [Measure.map_map (measurable_plane _ _ _) (measurable_amap D.measurable_par _),
    plane_amap, ← Measure.map_map (measurable_amap D.measurable_par _)
      (measurable_plane _ _ _), D.array_consistent]

local instance instStandardBorelSpaceαStateSpace : StandardBorelSpace D.stateSpace := D.stateSpace.standardBorel
local instance instNonemptyαStateSpace : Nonempty D.stateSpace := D.stateSpace.nonempty

lemma conditional (n : ℕ) (J : Finset I) (hJ : J ≠ Finset.univ) :
    condDistrib (planes n J) (amap D.par (n + 1)) (D.arrayLaw (n + 1))
      =ᵐ[(D.arrayLaw (n + 1)).map (amap D.par (n + 1))]
    (fun p => Measure.pi (fun j : J =>
      condDistrib (id : Arr I D.stateSpace n → Arr I D.stateSpace n)
        (amap D.par n) (D.arrayLaw n) (plane n (Fin.last n) (j : I) p))) := by
  have hs : ∀ s : ℕ, ∀ᵐ p ∂(D.arrayLaw (n + 1)).map (amap D.par (n + 1)),
      (condDistrib (planes n J) (amap D.par (n + 1)) (D.arrayLaw (n + 1)) p).map
        (fun y (j : J) => amap (D.proj s) n (y j)) =
      (Measure.pi (fun j : J =>
        condDistrib (id : Arr I D.stateSpace n → Arr I D.stateSpace n)
          (amap D.par n) (D.arrayLaw n) (plane n (Fin.last n) (j : I) p))).map
        (fun y (j : J) => amap (D.proj s) n (y j)) := by
    intro s
    have hf : Measurable (fun (y : J → Arr I D.stateSpace n) j => amap (D.proj s) n (y j)) :=
      Measurable.of_eval (fun j => (measurable_amap (D.measurable_proj s) n).comp
        (measurable_pi_apply j))
    have hleft := condDistrib_comp (mβ := inferInstance) (μ := D.arrayLaw (n + 1))
      (amap D.par (n + 1))
      (measurable_planes n J).aemeasurable hf
    have hright : condDistrib (amap (D.proj s) n) (amap D.par n) (D.arrayLaw n)
        =ᵐ[(D.arrayLaw n).map (amap D.par n)]
      (condDistrib (id : Arr I D.stateSpace n → Arr I D.stateSpace n)
        (amap D.par n) (D.arrayLaw n)).map (amap (D.proj s) n) := by
      exact condDistrib_comp (μ := D.arrayLaw n) (amap D.par n)
        (Y := (id : Arr I D.stateSpace n → Arr I D.stateSpace n)) aemeasurable_id
        (measurable_amap (D.measurable_proj s) n)
    have hall : ∀ᵐ p ∂(D.arrayLaw (n + 1)).map (amap D.par (n + 1)), ∀ j : J,
        condDistrib (amap (D.proj s) n) (amap D.par n) (D.arrayLaw n)
          (plane n (Fin.last n) (j : I) p) =
        (condDistrib id (amap D.par n) (D.arrayLaw n)
          (plane n (Fin.last n) (j : I) p)).map (amap (D.proj s) n) := by
      rw [ae_all_iff]
      intro j
      have he := (D.parameter_plane_preserving n (j : I)).quasiMeasurePreserving.ae_eq_comp hright
      filter_upwards [he] with p hp
      simpa only [Function.comp_apply, Kernel.map_apply _ (measurable_amap (D.measurable_proj s) n)] using hp
    filter_upwards [hleft, D.conditional_observation n J hJ s, hall] with p hl ho hr
    have hcomm : (fun (y : J → Arr I D.stateSpace n) (j : J) =>
        amap (D.proj s) n (y j)) ∘ planes n J =
      planes n J ∘ amap (D.proj s) (n + 1) := rfl
    rw [← Kernel.map_apply _ hf, ← hl, hcomm, ho, FiniteKernel.pi_apply,
      Measure.pi_map_pi (fun _ => (measurable_amap (D.measurable_proj s) n).aemeasurable)]
    congr 1
    funext j
    exact hr j
  have hall := ae_all_iff.mpr hs
  filter_upwards [hall] with p hp
  exact InverseSystems.array_pi_unique (X := fun s => (D.stage s).Y)
    D.yBond D.measurable_yBond hp

noncomputable def limit : Object I base where
  Y := D.stateSpace
  U := D.parameterSpace
  timeY := D.timeState
  timeU := D.timeParameter
  x := D.x
  par := D.par
  measurable_x := D.measurable_x
  measurable_par := D.measurable_par
  time_x := D.time_x
  time_par := D.time_par
  law := D.arrayLaw
  probability := D.arrayLaw_probability
  invariant := D.array_invariant
  over_base := D.array_over_base
  consistent := D.array_consistent
  proper := D.array_proper
  conditional := D.conditional
  local_independent := D.local_independent

noncomputable def projection (s : ℕ) : Extension (D.stage s) D.limit where
  state := D.proj s
  parameter := D.pproj s
  measurable_state := D.measurable_proj s
  measurable_parameter := D.measurable_pproj s
  time_state := rfl
  time_parameter := rfl
  state_x := D.x_stage s
  state_par := D.par_stage s
  laws := fun n => D.array_marginal n s


end ArrayObjects.Object.Tower

namespace ArrayObjects.Object
open scoped ENNReal
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T}

structure Test (M : Object I base) where
  level : ℕ
  kind : DataKind I
  vector : Lp ℂ 2 (M.law (level + 1))

namespace Test
variable {M N P : Object I base}

noncomputable def pull (F : Test M) (e : Extension M N) : Test N :=
  ⟨F.level, F.kind, e.pull (F.level + 1) F.vector⟩

noncomputable def energy (F : Test M) : ℝ := ‖M.project F.level F.kind F.vector‖

lemma energy_pull_le (F : Test M) (e : Extension M N) :
    (F.pull e).energy ≤ ‖F.vector‖ := by
  exact (N.project_norm_le _ _ _).trans_eq ((e.pull (F.level + 1)).norm_map F.vector)

lemma exists_near_max (F : Test M) (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : Object I base) (e : Extension M N),
      ∀ (P : Object I base) (f : Extension M P), (F.pull f).energy < (F.pull e).energy + ε := by
  let R : Set ℝ := {r | ∃ (N : Object I base) (e : Extension M N), (F.pull e).energy = r}
  have hR : R.Nonempty := ⟨(F.pull (Extension.refl M)).energy, M, Extension.refl M, rfl⟩
  have hRb : BddAbove R := ⟨‖F.vector‖, by
    rintro r ⟨N, e, rfl⟩
    exact F.energy_pull_le e⟩
  obtain ⟨r, ⟨N, e, hr⟩, hlt⟩ :=
    exists_lt_of_lt_csSup hR (show sSup R - ε < sSup R by linarith)
  refine ⟨N, e, fun P f => ?_⟩
  have hc : (F.pull f).energy ≤ sSup R := le_csSup hRb ⟨P, f, rfl⟩
  linarith

end Test
end ArrayObjects.Object

open MeasureTheory
open scoped ENNReal

namespace ArrayObjects.Object
open scoped ENNReal Topology
open Filter
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T}

namespace Extension
@[ext] lemma ext {M N : Object I base} {e f : Extension M N}
    (hs : e.state = f.state) (hp : e.parameter = f.parameter) : e = f := by
  cases e; cases f; cases hs; cases hp; rfl
end Extension

namespace Saturating

local instance instFactNeENNRealOfNatTop : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

def origin (n : ℕ) : ℕ := (Nat.unpair (Nat.unpair n).1).1
def testIndex (n : ℕ) : ℕ := (Nat.unpair (Nat.unpair n).1).2
@[simp] lemma origin_pair (i j r : ℕ) : origin (Nat.pair (Nat.pair i j) r) = i := by
  simp [origin]
@[simp] lemma testIndex_pair (i j r : ℕ) : testIndex (Nat.pair (Nat.pair i j) r) = j := by
  simp [testIndex]

instance instNonemptyDataKind : Nonempty (DataKind I) := ⟨.parameter⟩
noncomputable def keys : ℕ → ℕ × DataKind I × ℕ :=
  (exists_surjective_nat (ℕ × DataKind I × ℕ)).choose

noncomputable def dense (M : Object I base) (n : ℕ) : ℕ → Lp ℂ 2 (M.law (n + 1)) :=
  TopologicalSpace.denseSeq (Lp ℂ 2 (M.law (n + 1)))

noncomputable def listed (M : Object I base) (j : ℕ) : Test M :=
  let k := keys (I := I) j
  ⟨k.1, k.2.1, dense M k.1 k.2.2⟩

structure Bank where
  obj : Object I base
  tests : ℕ → ℕ → Test obj

namespace Bank
noncomputable def seed (M : Object I base) : Bank (base := base) :=
  ⟨M, fun _ => listed M⟩

noncomputable def focus (b : Bank (base := base)) (n : ℕ) : Test b.obj :=
  b.tests (origin n) (testIndex n)

noncomputable def nextObj (b : Bank (base := base)) (n : ℕ) : Object I base :=
  (b.focus n |>.exists_near_max (1 / ((n : ℝ) + 1)) (by positivity)).choose

noncomputable def nextMap (b : Bank (base := base)) (n : ℕ) : Extension b.obj (b.nextObj n) :=
  (b.focus n |>.exists_near_max (1 / ((n : ℝ) + 1)) (by positivity)).choose_spec.choose

noncomputable def next (b : Bank (base := base)) (n : ℕ) : Bank (base := base) :=
  ⟨b.nextObj n, fun i j => if i = n + 1 then listed (b.nextObj n) j
    else (b.tests i j).pull (b.nextMap n)⟩
end Bank

noncomputable def sequence (M : Object I base) : ℕ → Bank (base := base)
  | 0 => Bank.seed M
  | n + 1 => (sequence M n).next n

noncomputable abbrev tower (M : Object I base) : Tower base where
  stage n := (sequence M n).obj
  step n := (sequence M n).nextMap n

end Saturating
end ArrayObjects.Object

end Rokhlin

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_WeakLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

namespace ArrayObjects

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology


universe u
variable {I : Type u} {X : Type u} [TopologicalSpace X]

def firstDuplicate (T : X ≃ₜ X) (d : I → ℕ) (n : ℕ) : Arr I X n → Arr I X (n+1) :=
  fun y v => (T^[d (v 0)]) (y (fun j => v j.succ))

lemma continuous_firstDuplicate (T : X ≃ₜ X) (d : I → ℕ) (n : ℕ) :
    Continuous (firstDuplicate T d n) :=
  continuous_pi fun _v => (T.continuous.iterate _).comp (continuous_apply _)

lemma continuous_array_amap {Y : Type u} [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) (n : ℕ) : Continuous (amap (I := I) f n) :=
  continuous_pi fun _ => hf.comp (continuous_apply _)

lemma continuous_array_plane (n : ℕ) (a : Fin (n+1)) (i : I) :
    Continuous (plane (Y := X) n a i) := continuous_pi fun _ => continuous_apply _

lemma continuous_array_planes (n : ℕ) (J : Finset I) :
    Continuous (planes (Y := X) n J) := continuous_pi fun _ => continuous_array_plane _ _ _

omit [TopologicalSpace X] in
lemma amap_iterate (f : X → X) (m n : ℕ) :
    amap (I := I) (f^[m]) n = (amap f n)^[m] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ,amap_comp,ih,Function.iterate_succ]

lemma plane_firstDuplicate_zero (T : X ≃ₜ X) (d : I → ℕ) (n : ℕ) (i : I) :
    plane n 0 i ∘ firstDuplicate T d n = amap (T^[d i]) n := by
  funext y v
  simp [plane,firstDuplicate,amap,Fin.insertNth_zero']

lemma plane_firstDuplicate_succ (T : X ≃ₜ X) (d : I → ℕ) (n : ℕ)
    (a : Fin (n+1)) (i : I) :
    plane (n+1) a.succ i ∘ firstDuplicate T d (n+1) =
      firstDuplicate T d n ∘ plane n a i := by
  funext y v
  have hv : v = Fin.cons (v 0) (fun j => v j.succ) := by
    ext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  conv_lhs => simp only [Function.comp_apply,plane,firstDuplicate]
  rw [hv,Fin.insertNth_succ_cons]
  simp only [Fin.cons_zero,Fin.cons_succ]
  rfl

lemma planes_firstDuplicate_succ (T : X ≃ₜ X) (d : I → ℕ) (n : ℕ) (J : Finset I) :
    planes (n+1) J ∘ firstDuplicate T d (n+1) =
      (fun z j => firstDuplicate T d n (z j)) ∘ planes n J := by
  funext y j
  exact congrFun (plane_firstDuplicate_succ T d n (Fin.last n) j) y

section ContinuousPush
variable {A B C : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]

def continuousPush (f : A → B) (hf : Continuous f) (μ : ProbabilityMeasure A) : ProbabilityMeasure B :=
  μ.map hf.measurable.aemeasurable
lemma continuous_continuousPush (f : A → B) (hf : Continuous f) :
    Continuous (continuousPush f hf) := ProbabilityMeasure.continuous_map hf
lemma continuousPush_comp (f : A → B) (hf : Continuous f) (g : B → C) (hg : Continuous g)
    (μ : ProbabilityMeasure A) :
    continuousPush g hg (continuousPush f hf μ) = continuousPush (g ∘ f) (hg.comp hf) μ := by
  apply Subtype.ext
  exact Measure.map_map hg.measurable hf.measurable

lemma continuousPush_pi {J : Type*} [Fintype J] [SecondCountableTopology A] [SecondCountableTopology B] (f : J → A → B)
    (hf : ∀ j, Continuous (f j)) (ν : J → ProbabilityMeasure A) :
    continuousPush (fun z : J → A => fun j => f j (z j))
      (continuous_pi fun j => (hf j).comp (continuous_apply j)) (ProbabilityMeasure.pi ν) =
      ProbabilityMeasure.pi (fun j => continuousPush (f j) (hf j) (ν j)) := by
  apply Subtype.ext
  exact Measure.pi_map_pi (fun j => (hf j).measurable.aemeasurable)
end ContinuousPush

variable [Fintype I] [CompactSpace X] [T2Space X] [SecondCountableTopology X] [MetrizableSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable (T : X ≃ₜ X) (d : ℕ → I → ℕ) (U : Ultrafilter ℕ) (μ : ProbabilityMeasure X)

def weakArrayLaw : (n : ℕ) → ProbabilityMeasure (Arr I X n)
  | 0 => continuousPush (fun x _ => x) (continuous_pi fun _ => continuous_id) μ
  | n+1 => (U.map (fun b => continuousPush (firstDuplicate T (d b) n)
      (continuous_firstDuplicate T (d b) n) (weakArrayLaw n))).lim

omit [MetrizableSpace X] in
lemma weakArrayLaw_tendsto (n : ℕ) :
    Tendsto (fun b => continuousPush (firstDuplicate T (d b) n)
      (continuous_firstDuplicate T (d b) n) (weakArrayLaw T d U μ n)) U
      (𝓝 (weakArrayLaw T d U μ (n+1))) :=
  (U.map _).le_nhds_lim

omit [Fintype I] [CompactSpace X] [T2Space X] [SecondCountableTopology X] [MetrizableSpace X]
  [MeasurableSpace X] [BorelSpace X] in
lemma firstDuplicate_amap (b : ℕ) (n : ℕ) :
    amap T (n+1) ∘ firstDuplicate T (d b) n = firstDuplicate T (d b) n ∘ amap T n := by
  funext y v
  exact Function.Commute.iterate_right (Function.Commute.refl (T : X → X)) _ _

lemma weakArrayLaw_invariant (hμ : MeasurePreserving T μ μ) (n : ℕ) :
    continuousPush (amap T n) (continuous_array_amap T.continuous n) (weakArrayLaw T d U μ n) =
      weakArrayLaw T d U μ n := by
  induction n with
  | zero =>
    apply Subtype.ext
    change (Measure.map (fun x _ => x) μ).map (amap T 0) = Measure.map (fun x _ => x) μ
    rw [Measure.map_map (measurable_amap T.measurable 0) (show Measurable (fun x : X => fun _ : Index I 0 => x) from Measurable.of_eval fun _ => measurable_id)]
    change μ.toMeasure.map ((fun x _ => x) ∘ T) = _
    rw [←Measure.map_map (show Measurable (fun x : X => fun _ : Index I 0 => x) from Measurable.of_eval fun _ => measurable_id) T.measurable,hμ.map_eq]
  | succ n ih =>
    have h := (continuous_continuousPush (amap T (n+1)) (continuous_array_amap T.continuous _)).tendsto
      (weakArrayLaw T d U μ (n+1)) |>.comp (weakArrayLaw_tendsto T d U μ n)
    have he (b : ℕ) : continuousPush (amap T (n+1)) (continuous_array_amap T.continuous _)
        (continuousPush (firstDuplicate T (d b) n) (continuous_firstDuplicate T (d b) n)
          (weakArrayLaw T d U μ n)) =
        continuousPush (firstDuplicate T (d b) n) (continuous_firstDuplicate T (d b) n)
          (weakArrayLaw T d U μ n) := by
      simp only [continuousPush_comp, firstDuplicate_amap]
      rw [←continuousPush_comp (amap T n) (continuous_array_amap T.continuous n)
        (firstDuplicate T (d b) n) (continuous_firstDuplicate T (d b) n),ih]
    exact tendsto_nhds_unique h ((weakArrayLaw_tendsto T d U μ n).congr fun b => (he b).symm)

lemma weakArrayLaw_iterate_invariant (hμ : MeasurePreserving T μ μ) (n m : ℕ) :
    continuousPush (amap (T^[m]) n) (continuous_array_amap (T.continuous.iterate m) n)
      (weakArrayLaw T d U μ n) = weakArrayLaw T d U μ n := by
  apply Subtype.ext
  have h : MeasurePreserving (amap (I := I) T n) (weakArrayLaw T d U μ n : Measure (Arr I X n)) (weakArrayLaw T d U μ n : Measure (Arr I X n)) :=
    ⟨(continuous_array_amap T.continuous n).measurable,
      congrArg Subtype.val (weakArrayLaw_invariant T d U μ hμ n)⟩
  change (weakArrayLaw T d U μ n : Measure (Arr I X n)).map (amap (T^[m]) n) = _
  rw [amap_iterate]
  exact (h.iterate m).map_eq

lemma weakArrayLaw_consistent (hμ : MeasurePreserving T μ μ) (n : ℕ)
    (a : Fin (n+1)) (i : I) :
    continuousPush (plane n a i) (continuous_array_plane n a i) (weakArrayLaw T d U μ (n+1)) =
      weakArrayLaw T d U μ n := by
  induction n with
  | zero =>
    have h := (continuous_continuousPush (plane 0 a i) (continuous_array_plane 0 a i)).tendsto
      (weakArrayLaw T d U μ 1) |>.comp (weakArrayLaw_tendsto T d U μ 0)
    have he (b : ℕ) : continuousPush (plane 0 a i) (continuous_array_plane 0 a i)
        (continuousPush (firstDuplicate T (d b) 0) (continuous_firstDuplicate T (d b) 0)
          (weakArrayLaw T d U μ 0)) = weakArrayLaw T d U μ 0 := by
      have ha : a = 0 := by apply Fin.ext; omega
      subst a
      simpa only [continuousPush_comp,plane_firstDuplicate_zero] using
        weakArrayLaw_iterate_invariant T d U μ hμ 0 (d b i)
    exact tendsto_nhds_unique h (tendsto_const_nhds.congr fun b => (he b).symm)
  | succ n ih =>
    induction a using Fin.cases with
    | zero =>
      have h := (continuous_continuousPush (plane (n+1) 0 i) (continuous_array_plane _ _ _)).tendsto
        (weakArrayLaw T d U μ (n+2)) |>.comp (weakArrayLaw_tendsto T d U μ (n+1))
      have he (b : ℕ) : continuousPush (plane (n+1) 0 i) (continuous_array_plane _ _ _)
          (continuousPush (firstDuplicate T (d b) (n+1)) (continuous_firstDuplicate T (d b) (n+1))
            (weakArrayLaw T d U μ (n+1))) = weakArrayLaw T d U μ (n+1) := by
        simpa only [continuousPush_comp,plane_firstDuplicate_zero] using
          weakArrayLaw_iterate_invariant T d U μ hμ (n+1) (d b i)
      exact tendsto_nhds_unique h (tendsto_const_nhds.congr fun b => (he b).symm)
    | succ a =>
      have h := (continuous_continuousPush (plane (n+1) a.succ i) (continuous_array_plane _ _ _)).tendsto
        (weakArrayLaw T d U μ (n+2)) |>.comp (weakArrayLaw_tendsto T d U μ (n+1))
      have he (b : ℕ) : continuousPush (plane (n+1) a.succ i) (continuous_array_plane _ _ _)
          (continuousPush (firstDuplicate T (d b) (n+1)) (continuous_firstDuplicate T (d b) (n+1))
            (weakArrayLaw T d U μ (n+1))) =
          continuousPush (firstDuplicate T (d b) n) (continuous_firstDuplicate T (d b) n)
            (weakArrayLaw T d U μ n) := by
        simp only [continuousPush_comp,plane_firstDuplicate_succ]
        rw [←continuousPush_comp (plane n a i) (continuous_array_plane n a i)
          (firstDuplicate T (d b) n) (continuous_firstDuplicate T (d b) n),ih a]
      exact tendsto_nhds_unique h ((weakArrayLaw_tendsto T d U μ n).congr fun b => (he b).symm)

lemma weakArrayLaw_proper
    (hproper : ∀ J : Finset I, J ≠ Finset.univ →
      Tendsto (fun b => continuousPush (planes 0 J) (continuous_array_planes 0 J)
        (continuousPush (firstDuplicate T (d b) 0) (continuous_firstDuplicate T (d b) 0)
          (weakArrayLaw T d U μ 0))) U
        (𝓝 (ProbabilityMeasure.pi (fun _ : J => weakArrayLaw T d U μ 0))))
    (n : ℕ) (J : Finset I) (hJ : J ≠ Finset.univ) :
    continuousPush (planes n J) (continuous_array_planes n J) (weakArrayLaw T d U μ (n+1)) =
      ProbabilityMeasure.pi (fun _ : J => weakArrayLaw T d U μ n) := by
  induction n with
  | zero =>
    exact tendsto_nhds_unique
      ((continuous_continuousPush (planes 0 J) (continuous_array_planes 0 J)).tendsto
        _ |>.comp (weakArrayLaw_tendsto T d U μ 0)) (hproper J hJ)
  | succ n ih =>
    have h := (continuous_continuousPush (planes (n+1) J) (continuous_array_planes _ _)).tendsto
      (weakArrayLaw T d U μ (n+2)) |>.comp (weakArrayLaw_tendsto T d U μ (n+1))
    have he (b : ℕ) : continuousPush (planes (n+1) J) (continuous_array_planes _ _)
        (continuousPush (firstDuplicate T (d b) (n+1)) (continuous_firstDuplicate T (d b) (n+1))
          (weakArrayLaw T d U μ (n+1))) =
        ProbabilityMeasure.pi (fun _ : J => continuousPush (firstDuplicate T (d b) n)
          (continuous_firstDuplicate T (d b) n) (weakArrayLaw T d U μ n)) := by
      simp only [continuousPush_comp,planes_firstDuplicate_succ]
      rw [←continuousPush_comp (planes n J) (continuous_array_planes n J)
        (fun z j => firstDuplicate T (d b) n (z j))
        (continuous_pi fun j => (continuous_firstDuplicate T (d b) n).comp (continuous_apply j)),ih]
      exact continuousPush_pi _ (fun _ => continuous_firstDuplicate T (d b) n) _
    have hp := (ProbabilityMeasure.continuous_pi (α := fun _ : J => Arr I X (n+1))).tendsto
      (fun _ : J => weakArrayLaw T d U μ (n+1)) |>.comp
        (tendsto_pi_nhds.mpr (fun _ : J => weakArrayLaw_tendsto T d U μ n))
    exact tendsto_nhds_unique h (hp.congr fun b => (he b).symm)

end ArrayObjects

section
open MeasureTheory Filter Set
open scoped Topology BigOperators
variable {I X : Type*} [Fintype I] [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]

lemma probability_pi_tendsto_of_rectangles (ρ : ℕ → ProbabilityMeasure (I → X))
    (μ : I → ProbabilityMeasure X)
    (h : ∀ s : I → Set X, (∀ i, MeasurableSet (s i)) →
      Tendsto (fun n => (ρ n : Measure (I → X)) (Set.pi Set.univ s)) atTop
        (𝓝 (∏ i, (μ i : Measure X) (s i)))) :
    Tendsto ρ atTop (𝓝 (ProbabilityMeasure.pi μ)) := by
  apply isPiSystem_pi.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro _ ⟨s,hs,rfl⟩
    exact MeasurableSet.univ_pi fun i => hs i (mem_univ i)
  · intro u hu x hx
    obtain ⟨s,hs,hsub⟩ := isOpen_pi_iff'.mp hu x hx
    refine ⟨Set.pi Set.univ s,⟨s,fun i _ => (hs i).1.measurableSet,rfl⟩,?_,hsub⟩
    exact set_pi_mem_nhds Set.finite_univ fun i _ => (hs i).1.mem_nhds (hs i).2
  · rintro _ ⟨s,hs,rfl⟩
    have hh := h s (fun i => hs i (mem_univ i))
    have he : (∏ i, (μ i : Measure X) (s i)) =
        (ProbabilityMeasure.pi μ : Measure (I → X)) (Set.pi Set.univ s) := by
      exact (Measure.pi_pi _ _).symm
    rw [he] at hh
    exact (ENNReal.tendsto_toNNReal (measure_ne_top _ _)).comp hh
end

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped Topology BigOperators
namespace ArrayObjects
universe u
variable {I : Type u} [Fintype I] [retained15 : DecidableEq I]
    {X : StandardSpace.{u}} [TopologicalSpace X] [retained16 : CompactSpace X] [retained17 : T2Space X]
    [SecondCountableTopology X] [retained18 : MetrizableSpace X] [BorelSpace X]
    (T : X ≃ₜ X) (d : ℕ → I → ℕ) (μ : ProbabilityMeasure X)

include retained15 retained16 retained17 retained18 in
lemma weakArrayLaw_proper_input
    (hrect : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set X,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun b => (μ : Measure X) (⋂ j : J, (T^[d b j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, (μ : Measure X) (s j))))
    (J : Finset I) (hJ : J ≠ Finset.univ) :
    Tendsto (fun b => continuousPush (planes 0 J) (continuous_array_planes 0 J)
      (continuousPush (firstDuplicate T (d b) 0) (continuous_firstDuplicate T (d b) 0)
        (weakArrayLaw T d (Ultrafilter.of atTop) μ 0))) (↑(Ultrafilter.of (atTop : Filter ℕ)))
      (𝓝 (ProbabilityMeasure.pi (fun _ : J => weakArrayLaw T d (Ultrafilter.of atTop) μ 0))) := by
  let _ := retained15
  let _ := retained16
  let _ := retained17
  let _ := retained18
  let ρ : ℕ → ProbabilityMeasure (J → X) := fun b =>
    continuousPush (fun x j => (T^[d b j]) x)
      (continuous_pi fun j => T.continuous.iterate (d b j)) μ
  have hρ : Tendsto ρ atTop (𝓝 (ProbabilityMeasure.pi (fun _ : J => μ))) := by
    apply Rokhlin.probability_pi_tendsto_of_rectangles
    intro s hs
    convert hrect J hJ s hs using 1
    all_goals try with_reducible_and_instances rfl
    ext b
    change ((μ : Measure X).map (fun x => fun j : J => (T^[d b j]) x)) (Set.pi Set.univ s) = _
    rw [Measure.map_apply (show Measurable (fun x : X => fun j : J => (T^[d b j]) x) from
      (continuous_pi fun j : J => T.continuous.iterate (d b j)).measurable)
      (MeasurableSet.univ_pi hs)]
    congr 1
    ext x
    simp
  have hpush := (continuous_continuousPush
    (fun z : J → X => fun j : J => fun _ : Index I 0 => z j)
    (continuous_pi fun j => continuous_pi fun _ => continuous_apply j)).tendsto
      (ProbabilityMeasure.pi (fun _ : J => μ)) |>.comp hρ
  have he : continuousPush (fun z : J → X => fun j : J => fun _ : Index I 0 => z j)
      (continuous_pi fun j => continuous_pi fun _ => continuous_apply j)
      (ProbabilityMeasure.pi (fun _ : J => μ)) =
      ProbabilityMeasure.pi (fun _ : J => weakArrayLaw T d (Ultrafilter.of atTop) μ 0) := by
    exact continuousPush_pi (fun _ : J => fun x : X => fun _ : Index I 0 => x)
      (fun _ => continuous_pi fun _ => continuous_id) (fun _ => μ)
  rw [he] at hpush
  have he' (b : ℕ) : continuousPush
      (fun z : J → X => fun j : J => fun _ : Index I 0 => z j)
      (continuous_pi fun j => continuous_pi fun _ => continuous_apply j) (ρ b) =
      continuousPush (planes 0 J) (continuous_array_planes 0 J)
        (continuousPush (firstDuplicate T (d b) 0) (continuous_firstDuplicate T (d b) 0)
          (weakArrayLaw T d (Ultrafilter.of atTop) μ 0)) := by
    simp only [ρ,weakArrayLaw,continuousPush_comp]
    rfl
  exact (hpush.congr he').mono_left (Ultrafilter.of_le atTop)

end ArrayObjects

end Rokhlin

end

end OAI
end


