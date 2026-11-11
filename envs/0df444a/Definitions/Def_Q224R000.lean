-- Prove2me | Definitions.Def_Q224R000
-- name    : Q224R000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T15:10:15.476173+00:00
-- url     : https://prove2.me/theorems/864ea47f-0a05-4de5-afc3-47cb46d0f88a
-- title:
--   Definitions bundle Q224R000 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 85 declarations of OpenAI's Lean: 17 definitions, 1 inductive type or structure, 4 instances and 63 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.Program`, `OAI.MetricKMedianRecovery.RefinedRecovery.CheckedInput.checked`, `OAI.MetricKMedianRecovery.RefinedRecovery.CheckedInput.distance`, `OAI.MetricKMedianRecovery.RefinedRecovery.CheckedInput.fallback`, `OAI.MetricKMedianRecovery.RefinedRecovery.CheckedInput.mask`, `OAI.MetricKMedianRecovery.RefinedRecovery.CheckedInput.metricTest`, `OAI.MetricKMedianRecovery.RefinedRecovery.CheckedInput.n`, `OAI.MetricKMedianRecovery.RefinedRecovery.CheckedInput.normalized`, `OAI.MetricKMedianRecovery.RefinedRecovery.CheckedInput.ofValid`, `OAI.MetricKMedianRecovery.RefinedRecovery.CheckedInput.parseProgram`, `OAI.MetricKMedianRecovery.RefinedRecovery.CheckedInput.program`, `OAI.MetricKMedianRecovery.RefinedRecovery.CheckedInput.rows`, `OAI.MetricKMedianRecovery.RefinedRecovery.CheckedInput.valid`, `OAI.MetricKMedianRecovery.RefinedRecovery.CompanionThresholdInput`, `OAI.MetricKMedianRecovery.RefinedRecovery.Input.asInstance`, `OAI.MetricKMedianRecovery.RefinedRecovery.metricLengthPolynomial`, `OAI.MetricKMedianRecovery.RefinedRecovery.refinedRecoveryClaim`, `OAI.circleMeasurableSpace`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedianRecovery_Machines_Program`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/Program.lean), [`KMedianRecovery_Refined_CheckedInput`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Refined/CheckedInput.lean), [`KMedianRecovery_Refined_ConditionalRecovery`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Refined/ConditionalRecovery.lean), [`KMedianRecovery_Refined_Model`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Refined/Model.lean), [`KMedianRecovery_Refined_ThresholdInput`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Refined/ThresholdInput.lean), [`KMedianRecovery_Refined_Work`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Refined/Work.lean), [`KMedian_Binary_BooleanPolynomial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Binary/BooleanPolynomial.lean).
--
--   **Imports.** It imports the published bundles `Def_KMedianRefinedRecovery` and `Def_MetricKMedian`; the bundle `OAIQ035K061` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q224R002`; the statements `OAI_MetricKMedianRecovery_RefinedRecovery_metric_length_bound`, `OAI.MetricKMedianRecovery.RefinedRecovery.metric_length_bound_s35`, `OAI_MetricKMedianRecovery_RefinedRecovery_refined_recovery_conditional` and `OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery_conditional_s35`; the proofs of `OAI_MetricKMedianRecovery_RefinedRecovery_metric_length_bound`, `OAI.MetricKMedianRecovery.RefinedRecovery.metric_length_bound_s35`, `OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery` and `OAI_MetricKMedian_main_finite_work`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K061

section
-- module Solutions.Q224_RR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.Q224_RR.KMedianRecovery_Machines_Program
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

structure Program where
  K : Type
  [kDecidableEq : DecidableEq K]
  [kFinite : Fintype K]
  input : K
  output : K
  Label : Type
  [labelFinite : Fintype Label]
  main : Label
  State : Type
  [stateFinite : Fintype State]
  initial : State
  code : Label → TM2.Stmt (fun _ : K => Bool) Label State

attribute [instance] Program.kDecidableEq Program.kFinite Program.labelFinite Program.stateFinite

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q224_RR.KMedian_Binary_BooleanPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Turing Polynomial

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
variable {f : α → β} {g : β → γ}

 theorem finite_work (P : PolyProgram ea eb f) (k : P.stock.tm.K) : Finite (P.stock.tm.Γ k) :=
  inferInstanceAs (Finite Bool)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.Q224_RR.KMedianRecovery_Refined_CheckedInput
attribute [-simp] _root_.OAI.MetricKMedian.Instance.restrict_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RefinedRecovery.CheckedInput

open MetricKMedian MetricKMedian.Binary MetricKMedian.Binary.Automatic
open MetricKMedian.Binary.Automatic.Poly
open MetricKMedian.InstanceProgram (Raw view)
open MetricKMedian.SparseGraph.ListOperation (Row Table setView)

def n (x : Raw) : ℕ := x.1.2.length
def distance (x : Raw) (i j : ℕ) : ℚ := (x.2.2[i]?.getD [])[j]?.getD 0
def mask (x : Row) (m : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => x[i.val]?.getD false)
def rows (x : Raw) : List ℕ := List.range (n x)

def metricTest (x : Raw) : Bool :=
  ((rows x).map (fun i => ((rows x).map (fun j =>
    decide (0 ≤ distance x i j) &&
    (decide (distance x i j = 0) == decide (i = j)) &&
    decide (distance x i j = distance x j i) &&
    (((rows x).map (fun k =>
      decide (distance x i k ≤ distance x i j + distance x j k))).all id))).all id)).all id

def valid (x : Raw) : Bool :=
  decide (0 < x.2.1) && decide (x.2.1 ≤ (x.1.2.filter id).length) && metricTest x

@[fun_prop] theorem distance_poly : Poly (fun x : Raw × (ℕ × ℕ) =>
    distance x.1 x.2.1 x.2.2) := by
  unfold distance
  fun_prop

@[fun_prop] theorem rows_poly : Poly rows := by
  exact list_indices.comp (show Poly (fun x : Raw => x.1.2) by fun_prop)

@[fun_prop] theorem bool_beq_poly : Poly (fun x : Bool × Bool => x.1 == x.2) := by
  have he : (fun x : Bool × Bool => x.1 == x.2) =
      (fun x => if x.1 then x.2 else !x.2) := by
    funext x
    rcases x with ⟨a, b⟩
    cases a <;> cases b <;> rfl
  rw [he]
  fun_prop

@[fun_prop] theorem valid_poly : Poly valid := by
  unfold valid metricTest
  fun_prop

lemma mask_card (r : Row) : (mask r r.length).card = (r.filter id).length := by
  have he : List.ofFn (fun i : Fin r.length => r[i.val]?.getD false) = r := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp
  have hc := MetricKMedian.EncodingLists.length_filter_ofFn
    (fun i : Fin r.length => r[i.val]?.getD false) id
  rw [he] at hc
  exact hc.symm

lemma metricTest_spec {x : Raw} (h : metricTest x = true) (i j : Fin (n x)) :
    0 ≤ distance x i j ∧
    (distance x i j = 0 ↔ i = j) ∧
    distance x i j = distance x j i ∧
    ∀ k : Fin (n x), distance x i k ≤ distance x i j + distance x j k := by
  simp only [metricTest, List.all_map, List.all_eq_true, rows, List.mem_range,
    Function.comp_apply, id_eq, Bool.and_eq_true_iff, beq_iff_eq, decide_eq_true_iff] at h
  obtain ⟨⟨⟨h₀, h₁⟩, h₂⟩, h₃⟩ := h i i.isLt j j.isLt
  refine ⟨h₀, ?_, h₂, fun k => h₃ k k.isLt⟩
  simpa only [decide_eq_decide, Fin.ext_iff] using h₁

def ofValid (x : Raw) (h : valid x = true) : Instance where
  n := n x
  distance i j := distance x i j
  clients := mask x.1.1 (n x)
  facilities := mask x.1.2 (n x)
  k := x.2.1
  distance_nonneg i j := (metricTest_spec (Bool.and_eq_true_iff.mp h).2 i j).1
  distance_eq_zero i j := (metricTest_spec (Bool.and_eq_true_iff.mp h).2 i j).2.1
  distance_symm i j := (metricTest_spec (Bool.and_eq_true_iff.mp h).2 i j).2.2.1
  distance_triangle i j k := (metricTest_spec (Bool.and_eq_true_iff.mp h).2 i j).2.2.2 k
  k_pos := of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1
  k_le := by
    rw [n, mask_card]
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2

def fallback : Instance where
  n := 1
  distance _ _ := 0
  clients := ∅
  facilities := Finset.univ
  k := 1
  distance_nonneg _ _ := le_rfl
  distance_eq_zero i j := ⟨fun _ => Subsingleton.elim i j, fun _ => rfl⟩
  distance_symm _ _ := rfl
  distance_triangle _ _ _ := by norm_num
  k_pos := le_rfl
  k_le := by simp

def checked (x : Raw) : Instance := if h : valid x = true then ofValid x h else fallback

def normalized (x : Raw) : Raw :=
  (((rows x).map (fun i => x.1.1[i]?.getD false), x.1.2),
    (x.2.1, (rows x).map (fun i => (rows x).map (fun j => distance x i j))))

@[fun_prop] theorem normalized_poly : Poly normalized := by
  unfold normalized
  fun_prop

lemma mask_view (r : Row) (m : ℕ) :
    setView (mask r m) = (List.range m).map (fun i => r[i]?.getD false) := by
  apply List.ext_getElem
  · simp [setView]
  · intro i h₁ h₂
    simp [setView, mask]

lemma range_map {α : Type*} (m : ℕ) (f : ℕ → α) :
    (List.range m).map f = List.ofFn (fun i : Fin m => f i.val) := by
  apply List.ext_getElem <;> simp

lemma normalized_view (x : Raw) (h : valid x = true) : normalized x = view (ofValid x h) := by
  simp only [normalized, view, ofValid, mask_view, rows, n]
  have hr : (List.range x.1.2.length).map (fun i => x.1.2[i]?.getD false) = x.1.2 := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp [h₂]
  rw [hr]
  simp only [range_map]

noncomputable def program : PolyProgram enc InstanceProgram.encode checked := by
  let p := (MetricKMedian.Binary.Automatic.Poly.ite valid_poly normalized_poly
    (MetricKMedian.Binary.Automatic.Poly.const (α := Raw) (view fallback))).program
  exact p.recode id (fun _ => rfl) (fun x => by
    change enc (if valid x = true then normalized x else view fallback) = enc (view (checked x))
    by_cases h : valid x = true
    · simp only [checked, ite_eq_left h, dite_eq_left h]
      exact congrArg enc (normalized_view x h)
    · simp only [checked, ite_eq_right h, dite_eq_right h])

noncomputable def parseProgram : PolyProgram id InstanceProgram.encode
    (fun xs => checked (InputParser.raw xs)) :=
  (BooleanLists.packProgram.comp InputParser.rawProgram).comp program

end MetricKMedianRecovery.RefinedRecovery.CheckedInput

end OAI
end

section
-- module Solutions.Q224_RR.KMedianRecovery_Refined_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized metric inputs, hidden comparison certificates, and the refined recovery claim. -/

namespace MetricKMedianRecovery.RefinedRecovery

def refinedRecoveryClaim : Prop :=
  ∀ (bound : Polynomial ℕ) (ε L₀ : ℝ) (μ : ℚ),
    0 < ε → 0 < L₀ → 0 < μ → μ ≤ 1/4 → (μ : ℝ) ≤ ε/12 →
    ∃ A : BinaryRandomizedAlgorithm,
      PolynomialWork A bound ∧
      ∀ I : Input, I.Bounded bound → ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
        (∀ s : Seed A I ζ, I.metric.Feasible (output A I ζ s)) ∧
        (∀ C : Certificate I μ L₀,
          1 - ζ ≤ successProbability A I ζ
            ((1 + 2 / Real.exp 1 + ε) * (I.metric.cost C.centers : ℝ)))

end MetricKMedianRecovery.RefinedRecovery

end OAI
end

section
-- module Solutions.Q224_RR.KMedianRecovery_Refined_ThresholdInput
attribute [-instance] _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RefinedRecovery

namespace Input

abbrev asInstance (I : Input) : MetricKMedian.Instance where
  n := I.metric.pointCount
  distance := I.metric.distance
  clients := I.metric.clients
  facilities := I.metric.facilities
  k := I.metric.budget
  distance_nonneg := I.metric.distance_nonneg
  distance_eq_zero i j := by
    constructor
    · intro h
      by_contra hn
      exact (ne_of_gt (I.positive i j hn)) h
    · rintro rfl
      exact I.metric.distance_self i
  distance_symm := I.metric.distance_symm
  distance_triangle := I.metric.distance_triangle
  k_pos := I.metric.budget_pos
  k_le := I.anchor_card.symm.trans_le (Finset.card_le_card I.anchor_subset)

end Input

end MetricKMedianRecovery.RefinedRecovery

end OAI
end

section
-- module Solutions.Q224_RR.KMedianRecovery_Refined_Work
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RefinedRecovery

noncomputable def metricLengthPolynomial (b : Polynomial ℕ) : Polynomial ℕ :=
  6*(Polynomial.X+1) + Polynomial.X^2*(2*b+7)

end MetricKMedianRecovery.RefinedRecovery

end OAI
end

section
-- module Solutions.Q224_RR.KMedianRecovery_Refined_ConditionalRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RefinedRecovery

open MetricKMedian.Binary

def CompanionThresholdInput : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ f : MetricKMedian.Instance → List Bool,
    Nonempty (PolyProgram MetricKMedian.InstanceProgram.encode id f) ∧
    ∀ I, MetricKMedian.Correct ε I (f I)

end MetricKMedianRecovery.RefinedRecovery

end OAI
end


