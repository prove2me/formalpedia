-- Prove2me | Definitions.Def_OAIQ12Ed000
-- name    : OAIQ12Ed000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T11:19:36.48872+00:00
-- url     : https://prove2.me/theorems/d5dab5c5-59f2-4fbc-a544-8fe785e6b694
-- title:
--   Definitions bundle OAIQ12Ed000 of the split of OpenAI, Edit Distance in l1: Matching Bounds up to Constants in the Exponent
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.edit_distance_main`, carved from OpenAI's openai/math development (OpenAI, *Edit Distance in l1: Matching Bounds up to Constants in the Exponent*, OpenAI Math Release, September 27, 2026, result family 99, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 315 declarations of OpenAI's Lean: 108 definitions, 2 inductive types or structures, 4 instances and 201 theorems. The definitions and types are `OAI.EditAverage.avg`, `OAI.EditCode.BlockPair`, `OAI.EditCode.BlockSpan`, `OAI.EditCode.Charge`, `OAI.EditCode.Gap`, `OAI.EditCode.Missing`, `OAI.EditCode.bit`, `OAI.EditCode.block`, `OAI.EditCode.encode`, `OAI.EditCode.labels`, `OAI.EditCode.padded`, `OAI.EditCode.width`, `OAI.EditCutHash.coin`, `OAI.EditCutHash.count`, `OAI.EditCutHash.distance`, `OAI.EditCutHash.histogramDistance`, `OAI.EditCutHash.hit`, `OAI.EditCutHash.key`, `OAI.EditCutHash.meanHistogram`, `OAI.EditCutHash.probability`, `OAI.EditCutHash.rate`, `OAI.EditCutHash.sep`, `OAI.EditCutModel.Model`, `OAI.EditCutModel.Model.dist`, `OAI.EditCutModel.Model.histogram`, `OAI.EditCutModel.Model.pullback`, `OAI.EditCutModel.Model.scale`, `OAI.EditCutModel.Model.total`, `OAI.EditCutModel.Model.vector`, `OAI.EditCutModel.countNat`, `OAI.EditCutModel.sep`, `OAI.EditCuts.RealL1`, `OAI.EditCuts.cut`, `OAI.EditDepth.depth`, `OAI.EditDepth.radius`, `OAI.EditDistortion.coordinateEmbedding`, `OAI.EditDistortion.cost`, `OAI.EditDistortion.indel`, `OAI.EditFamily.Family`, `OAI.EditFamily.ProductState` and 70 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/EditDistance, in whole or in part: `EditApproximation_Definitions`, `EditDistance_BinaryCode`, `EditDistance_BinaryEmbedding`, `EditDistance_BlockAlignment`, `EditDistance_CutModels`, `EditDistance_CutRealization`, `EditDistance_Cuts`, `EditDistance_DelimiterAlignment`, `EditDistance_DepthInversion`, `EditDistance_DirectSums`, `EditDistance_Distortion`, `EditDistance_Families`, `EditDistance_FamilyRecursion`, `EditDistance_FiniteLower`, `EditDistance_FourierAverages`, `EditDistance_FourierCharacters`, `EditDistance_HashCuts`, `EditDistance_Histograms`, `EditDistance_LowerDistortion`, `EditDistance_LowerParameters`, `EditDistance_MeanHistograms`, `EditDistance_Metric`, `EditDistance_PrimeCharacters`, `EditDistance_PrimeDisplacement`, `EditDistance_PrimePeriods`, `EditDistance_PrimePool`, `EditDistance_RecursiveControl`, `EditDistance_RecursiveWords`, `EditDistance_RowAlignment`, `EditDistance_RowConstruction`, `EditDistance_RowSeparation`, `EditDistance_Slots`, `EditDistance_UpperBase`, `EditDistance_UpperParameters`, `EditDistance_UpperRecursion`, `EditDistance_WindowRecursion`, `EditDistance_Windows`.
--
--   **Imports.** It imports the published bundle `Def_EditDistance`.
--
--   **Imported by** (directly, in this split): the proof of `OAI.edit_distance_main`.
-- source:
--   OpenAI, Edit Distance in l1: Matching Bounds up to Constants in the Exponent, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 99; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Edit-Distance-in-l1-Matching-Bounds-up-to-Constants-in-the-Exponent-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/EditDistance at commit adc7f12

import Mathlib
import Definitions.Def_EditDistance

section
-- module Solutions.OAIQ12_ED.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditApproximation_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A uniform almost-linear approximation scheme for edit distance.
The statement retains the concrete binary algorithm and its exact resource accounting. -/

section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8
namespace OAI.EditDistortion
variable {Alpha : Type u} {s : Bool}

noncomputable def cost (s : Bool) (x y : List Alpha) : ℕ := sInf {n | Script s n x y}


end OAI.EditDistortion
end
end

section
-- module Solutions.OAIQ12_ED.EditDistance_Metric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Unrestricted edit scripts, metric inequalities, and common subsequences
-/

namespace EditDistortion

universe u v
noncomputable def indel {Alpha : Type u} (x y : List Alpha) : ℕ :=
  sInf {n | Script false n x y}

variable {Alpha : Type u} {Beta : Type v} {s : Bool}

namespace Step

theorem symm {x y : List Alpha} (h : Step s x y) : Step s y x := by
  cases h with
  | insert p q a => exact .delete p q a
  | delete p q a => exact .insert p q a
  | substitute hs p q a b => exact .substitute hs p q b a

theorem map (f : Alpha → Beta) {x y : List Alpha} (h : Step s x y) :
    Step s (x.map f) (y.map f) := by
  cases h with
  | insert p q a => simpa using Step.insert (substitutions := s) (p.map f) (q.map f) (f a)
  | delete p q a => simpa using Step.delete (substitutions := s) (p.map f) (q.map f) (f a)
  | substitute hs p q a b =>
    simpa using Step.substitute hs (p.map f) (q.map f) (f a) (f b)

theorem append_left (p : List Alpha) {x y : List Alpha} (h : Step s x y) :
    Step s (p ++ x) (p ++ y) := by
  cases h with
  | insert q r a => simpa only [List.append_assoc] using Step.insert (substitutions := s) (p ++ q) r a
  | delete q r a => simpa only [List.append_assoc] using Step.delete (substitutions := s) (p ++ q) r a
  | substitute hs q r a b =>
    simpa only [List.append_assoc] using Step.substitute hs (p ++ q) r a b

theorem append_right (q : List Alpha) {x y : List Alpha} (h : Step s x y) :
    Step s (x ++ q) (y ++ q) := by
  cases h with
  | insert p r a =>
    simpa only [List.append_assoc, List.cons_append] using
      Step.insert (substitutions := s) p (r ++ q) a
  | delete p r a =>
    simpa only [List.append_assoc, List.cons_append] using
      Step.delete (substitutions := s) p (r ++ q) a
  | substitute hs p r a b =>
    simpa only [List.append_assoc, List.cons_append] using Step.substitute hs p (r ++ q) a b

end Step

namespace Script

theorem trans {m n : ℕ} {x y z : List Alpha}
    (h : Script s m x y) (k : Script s n y z) : Script s (m + n) x z := by
  induction h with
  | nil => simpa using k
  | @cons l x w y e h ih =>
    simpa only [Nat.add_right_comm] using Script.cons e (ih k)

theorem single {x y : List Alpha} (h : Step s x y) : Script s 1 x y :=
  .cons h (.nil y)

theorem symm {n : ℕ} {x y : List Alpha} (h : Script s n x y) : Script s n y x := by
  induction h with
  | nil x => exact .nil x
  | cons e h ih => exact ih.trans (single e.symm)

theorem map (f : Alpha → Beta) {n : ℕ} {x y : List Alpha} (h : Script s n x y) :
    Script s n (x.map f) (y.map f) := by
  induction h with
  | nil x => exact .nil _
  | cons e h ih => exact .cons (e.map f) ih

theorem append_left (p : List Alpha) {n : ℕ} {x y : List Alpha} (h : Script s n x y) :
    Script s n (p ++ x) (p ++ y) := by
  induction h with
  | nil x => exact .nil _
  | cons e h ih => exact .cons (e.append_left p) ih

theorem append_right (q : List Alpha) {n : ℕ} {x y : List Alpha} (h : Script s n x y) :
    Script s n (x ++ q) (y ++ q) := by
  induction h with
  | nil x => exact .nil _
  | cons e h ih => exact .cons (e.append_right q) ih

theorem to_nil (x : List Alpha) : Script s x.length x [] := by
  induction x with
  | nil => exact .nil []
  | cons a x ih => exact .cons (.delete [] x a) ih

theorem exists_script (x y : List Alpha) : ∃ n, Script s n x y :=
  ⟨x.length + y.length, (to_nil x).trans (to_nil y).symm⟩

theorem eq_of_zero {x y : List Alpha} (h : Script s 0 x y) : x = y := by
  cases h
  rfl

end Script



theorem cost_le {n : ℕ} {x y : List Alpha} (h : Script s n x y) : cost s x y ≤ n :=
  Nat.sInf_le h

theorem cost_spec (x y : List Alpha) : Script s (cost s x y) x y :=
  Nat.sInf_mem (Script.exists_script x y)

theorem cost_refl (x : List Alpha) : cost s x x = 0 :=
  Nat.eq_zero_of_le_zero (cost_le (.nil x))

theorem cost_eq_zero_iff {x y : List Alpha} : cost s x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hc := cost_spec (s := s) x y
    rw [h] at hc
    exact hc.eq_of_zero
  · rintro rfl
    exact cost_refl _

theorem cost_map_le (f : Alpha → Beta) (x y : List Alpha) :
    cost s (x.map f) (y.map f) ≤ cost s x y :=
  cost_le ((cost_spec x y).map f)

end EditDistortion

namespace EditDistortion

universe u v
variable {Alpha : Type u} {Beta : Type v} {s : Bool}

theorem cost_map_eq_of_leftInverse (f : Alpha → Beta) (g : Beta → Alpha)
    (h : Function.LeftInverse g f) (x y : List Alpha) :
    cost s (x.map f) (y.map f) = cost s x y := by
  apply Nat.le_antisymm (cost_map_le f x y)
  have H := cost_map_le (s := s) g (x.map f) (y.map f)
  simpa only [List.map_map, h.comp_eq_id, List.map_id] using H

theorem cost_append_le (x y u v : List Alpha) :
    cost s (x ++ u) (y ++ v) ≤ cost s x y + cost s u v :=
  cost_le (((cost_spec x y).append_right u).trans ((cost_spec u v).append_left y))

theorem Script.of_sublist {x y : List Alpha} (h : x.Sublist y) :
    Script false (y.length - x.length) y x := by
  induction h with
  | slnil => exact .nil []
  | @cons x y a h ih =>
    have hl := h.length_le
    simpa only [List.length_cons, Nat.succ_sub hl, Nat.succ_eq_add_one, List.nil_append] using
      Script.cons (.delete [] y a) ih
  | @cons_cons x y a h ih =>
    simpa only [List.length_cons, Nat.add_sub_add_right, List.singleton_append] using
      ih.append_left [a]

theorem indel_le_matching_loss {x y z : List Alpha} (hx : z.Sublist x) (hy : z.Sublist y) :
    indel x y ≤ x.length + y.length - 2 * z.length := by
  have hs := (Script.of_sublist hx).trans (Script.of_sublist hy).symm
  have hx' := hx.length_le
  have hy' := hy.length_le
  have heq : x.length - z.length + (y.length - z.length) =
      x.length + y.length - 2 * z.length := by omega
  rw [heq] at hs
  exact cost_le hs

end EditDistortion

namespace EditDistortion

universe u
variable {Alpha : Type u}

theorem sublist_erase_one {z p q : List Alpha} {a : Alpha}
    (h : z.Sublist (p ++ a :: q)) :
    ∃ z' : List Alpha, z'.Sublist z ∧ z'.Sublist (p ++ q) ∧ z.length ≤ z'.length + 1 := by
  obtain ⟨z₁, z₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp h
  rcases List.sublist_cons_iff.mp h₂ with h₂ | ⟨r, rfl, hr⟩
  · exact ⟨z₁ ++ z₂, .refl _, h₁.append h₂, by omega⟩
  · refine ⟨z₁ ++ r, (List.Sublist.refl z₁).append ((List.Sublist.refl r).cons a),
      h₁.append hr, ?_⟩
    simp only [List.length_append, List.length_cons]
    omega

theorem Script.common_sublist {n : ℕ} {x y : List Alpha} (h : Script false n x y) :
    ∃ z : List Alpha, z.Sublist x ∧ z.Sublist y ∧ x.length + y.length ≤ n + 2 * z.length := by
  induction h with
  | nil x => exact ⟨x, .refl _, .refl _, by omega⟩
  | @cons n x v y e h ih =>
    obtain ⟨z, hzx, hzy, hz⟩ := ih
    cases e with
    | insert p q a =>
      obtain ⟨z', hz'z, hz'x, hz'L⟩ := sublist_erase_one hzx
      refine ⟨z', hz'x, hz'z.trans hzy, ?_⟩
      simp only [List.length_append, List.length_cons] at hz ⊢
      omega
    | delete p q a =>
      refine ⟨z, hzx.middle a, hzy, ?_⟩
      simp only [List.length_append, List.length_cons] at hz ⊢
      omega
    | substitute hf => cases hf

theorem indel_matching (x y : List Alpha) :
    ∃ z : List Alpha, z.Sublist x ∧ z.Sublist y ∧
      indel x y = x.length + y.length - 2 * z.length := by
  obtain ⟨z, hx, hy, hz⟩ := (cost_spec (s := false) x y).common_sublist
  refine ⟨z, hx, hy, Nat.le_antisymm (indel_le_matching_loss hx hy) ?_⟩
  change x.length + y.length - 2 * z.length ≤ cost false x y
  omega

end EditDistortion

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_DelimiterAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Increasing matchings through binary delimiter blocks
-/

namespace EditCode
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section Matching
variable {k w n U V : ℕ} {f g : Fin k → ℕ}

def BlockSpan (f g : Fin k → ℕ) (w i : ℕ) : Prop :=
  ∃ t : ℕ, ∀ r : ℕ, r < w → ∃ a : Fin k, f a = w * i + r ∧ g a = t + r

def Missing (f : Fin k → ℕ) (w i : ℕ) : Prop :=
  ∃ r : ℕ, r < w ∧ ∀ a : Fin k, f a ≠ w * i + r

def Gap (f g : Fin k → ℕ) (w i : ℕ) : Prop :=
  ∃ (r : ℕ) (a b : Fin k), r + 1 < w ∧ f a = w * i + r ∧
    f b = w * i + (r+1) ∧ g a + 1 < g b

def Charge (f g : Fin k → ℕ) (w i : ℕ) : ℕ ⊕ ℕ → Prop
  | Sum.inl x => w * i ≤ x ∧ x < w * i + w ∧ ∀ a : Fin k, f a ≠ x
  | Sum.inr x => (∀ a : Fin k, g a ≠ x) ∧ ∃ a b : Fin k,
      w * i ≤ f a ∧ f a < w * i + w ∧ w * i ≤ f b ∧ f b < w * i + w ∧
        g a < x ∧ x < g b

end Matching
end EditCode

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_BinaryCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Binary delimiter codes and padding
-/

namespace EditCode
open EditDistortion
variable {A : Type*} {t : ℕ}

def width (t : ℕ) : ℕ := 2 * t + 3

def bit (label : A → Fin t → Bool) (a : A) (r : ℕ) : Bool :=
  if r < 2 then true else
    if h : r % 2 = 1 ∧ r / 2 - 1 < t then label a ⟨r / 2 - 1,h.2⟩ else false

def block (label : A → Fin t → Bool) (a : A) : List Bool :=
  List.ofFn (fun r : Fin (width t) => bit label a r)

def encode (label : A → Fin t → Bool) (x : List A) : List Bool := x.flatMap (block label)

def padded (label : A → Fin t → Bool) (x : List A) (r : ℕ) : List Bool :=
  encode label x ++ List.replicate r false

@[simp] lemma block_length (label : A → Fin t → Bool) (a : A) :
    (block label a).length = width t := List.length_ofFn

@[simp] lemma width_pos : 0 < width t := by unfold width; omega

@[simp] lemma encode_length (label : A → Fin t → Bool) (x : List A) :
    (encode label x).length = width t * x.length := by
  induction x with
  | nil => simp [encode]
  | cons a x ih => simp_all [encode, Nat.mul_add, Nat.add_comm]

@[simp] lemma padded_length (label : A → Fin t → Bool) (x : List A) (r : ℕ) :
    (padded label x r).length = width t * x.length + r := by simp [padded]

@[simp] lemma bit_zero (label : A → Fin t → Bool) (a : A) : bit label a 0 = true := by simp [bit]
@[simp] lemma bit_one (label : A → Fin t → Bool) (a : A) : bit label a 1 = true := by simp [bit]

end EditCode

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_RowAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Charging arbitrary alignments across rows and markers
-/

namespace EditRows
open scoped BigOperators

def payload (B i : ℕ) : Finset ℕ := Finset.Ico (2 * B * i) (2 * B * i + B)
def marker (B i : ℕ) : Finset ℕ := Finset.Ico (2 * B * i + B) (2 * B * i + 2 * B)

lemma mem_payload {B i x : ℕ} : x ∈ payload B i ↔ 2 * B * i ≤ x ∧ x < 2 * B * i + B := by
  simp [payload]

lemma mem_marker {B i x : ℕ} : x ∈ marker B i ↔
    2 * B * i + B ≤ x ∧ x < 2 * B * i + 2 * B := by
  simp [marker]

lemma card_payload (B i : ℕ) : (payload B i).card = B := by simp [payload]
lemma card_marker (B i : ℕ) : (marker B i).card = B := by simp [marker]; omega

lemma payload_before {B i j x y : ℕ} (hij : i < j)
    (hx : x ∈ payload B i) (hy : y ∈ payload B j) : x < y := by
  have hx := mem_payload.mp hx
  have hy := mem_payload.mp hy
  have h : 2 * B * (i + 1) ≤ 2 * B * j := Nat.mul_le_mul_left _ hij
  nlinarith

lemma marker_disjoint {B i j : ℕ} (h : i ≠ j) : Disjoint (marker B i) (marker B j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hx := mem_marker.mp hx
  have hy := mem_marker.mp hy
  rcases lt_or_gt_of_ne h with h | h
  · have h' : 2 * B * (i + 1) ≤ 2 * B * j := Nat.mul_le_mul_left _ h
    nlinarith
  · have h' : 2 * B * (j + 1) ≤ 2 * B * i := Nat.mul_le_mul_left _ h
    nlinarith

lemma payload_disjoint {B i j : ℕ} (h : i ≠ j) : Disjoint (payload B i) (payload B j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne h with h | h
  · exact (Nat.lt_irrefl x) (payload_before h hx hy)
  · exact (Nat.lt_irrefl x) (payload_before h hy hx)

lemma payload_subset_range {B L i : ℕ} (hi : i < L) :
    payload B i ⊆ Finset.range (2 * B * L) := by
  intro x hx
  have hx := mem_payload.mp hx
  have h : 2 * B * (i + 1) ≤ 2 * B * L := Nat.mul_le_mul_left _ hi
  simp only [Finset.mem_range]
  nlinarith

lemma marker_subset_range {B L i : ℕ} (hi : i < L) :
    marker B i ⊆ Finset.range (2 * B * L) := by
  intro x hx
  have hx := mem_marker.mp hx
  have h : 2 * B * (i + 1) ≤ 2 * B * L := Nat.mul_le_mul_left _ hi
  simp only [Finset.mem_range]
  nlinarith

lemma payload_index {B : ℕ} (hB : 0 < B) {i x : ℕ} (hx : x ∈ payload B i) :
    x / (2 * B) = i := by
  have hx := mem_payload.mp hx
  apply Nat.div_eq_of_lt_le <;> nlinarith

lemma payload_of_mod {B x : ℕ} (hx : x % (2 * B) < B) :
    x ∈ payload B (x / (2 * B)) := by
  rw [mem_payload]
  have h := Nat.mod_add_div x (2 * B)
  constructor <;> omega

lemma marker_between {B i a b : ℕ} (ha : a ∈ payload B i)
    (hb : i < b / (2 * B)) {x : ℕ} (hx : x ∈ marker B i) : a < x ∧ x < b := by
  have ha := mem_payload.mp ha
  have hx := mem_marker.mp hx
  have h : 2 * B * (i + 1) ≤ 2 * B * (b / (2 * B)) := Nat.mul_le_mul_left _ hb
  have hd := Nat.div_mul_le_self b (2 * B)
  constructor <;> nlinarith

lemma marker_not_payload {B i x : ℕ} (hB : 0 < B) (hx : x ∈ marker B i) :
    ¬ x % (2 * B) < B := by
  intro hp
  have h := payload_of_mod hp
  have hm := mem_marker.mp hx
  have hd : x / (2 * B) = i := by
    apply Nat.div_eq_of_lt_le <;> nlinarith
  rw [hd] at h
  have h := mem_payload.mp h
  omega

section Matching
variable {k B L : ℕ} {f g : Fin k → ℕ}
variable (hf : StrictMono f) (hg : StrictMono g)
include hf hg

def rowMatches (f : Fin k → ℕ) (B i : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun a => f a ∈ payload B i)

def Cross (f g : Fin k → ℕ) (B i : ℕ) : Prop :=
  ∃ a b : Fin k, f a ∈ payload B i ∧ f b ∈ payload B i ∧
    g a / (2 * B) < g b / (2 * B)

lemma crossing_marker_unmatched (hB : 0 < B)
    (hclean : ∀ a : Fin k, ∀ i : ℕ, f a ∈ payload B i → g a % (2 * B) < B)
    {i : ℕ} {a b : Fin k} (ha : f a ∈ payload B i) (hb : f b ∈ payload B i)
    (hab : g a / (2 * B) < g b / (2 * B)) :
    Disjoint (marker B (g a / (2 * B))) (Finset.univ.image g) := by
  apply Finset.disjoint_left.mpr
  intro x hx hxm
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hxm
  obtain ⟨hac, hcb⟩ := marker_between (payload_of_mod (hclean a i ha)) hab hx
  have hac' : a < c := hg.lt_iff_lt.mp hac
  have hcb' : c < b := hg.lt_iff_lt.mp hcb
  have hfa := hf hac'
  have hfb := hf hcb'
  have hc : f c ∈ payload B i := by
    have ha := mem_payload.mp ha
    have hb := mem_payload.mp hb
    rw [mem_payload]
    omega
  exact marker_not_payload hB hx (hclean c i hc)

lemma crossing_marker_distinct {i j : ℕ} (hij : i ≠ j) {a b c d : Fin k}
    (ha : f a ∈ payload B i) (hb : f b ∈ payload B i)
    (hc : f c ∈ payload B j) (hd : f d ∈ payload B j)
    (hab : g a / (2 * B) < g b / (2 * B))
    (hcd : g c / (2 * B) < g d / (2 * B)) :
    g a / (2 * B) ≠ g c / (2 * B) := by
  intro heq
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hbc : b < c := hf.lt_iff_lt.mp (payload_before hij hb hc)
    have hbc' := hg hbc
    have hbc'' : g b / (2 * B) ≤ g c / (2 * B) := Nat.div_le_div_right (Nat.le_of_lt hbc')
    omega
  · have hda : d < a := hf.lt_iff_lt.mp (payload_before hji hd ha)
    have hda' := hg hda
    have hda'' : g d / (2 * B) ≤ g a / (2 * B) := Nat.div_le_div_right (Nat.le_of_lt hda')
    omega

end Matching
end EditRows

namespace EditRows
open scoped BigOperators

lemma sum_cards_le {I X : Type*} [Fintype I] [DecidableEq X]
    (S : I → Finset X) (U : Finset X)
    (hdisj : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hsub : ∀ i, S i ⊆ U) : ∑ i, (S i).card ≤ U.card := by
  classical
  have hd : (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint S :=
    fun i _ j _ hij => hdisj hij
  rw [← Finset.card_biUnion hd]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨i, _, hx⟩ := Finset.mem_biUnion.mp hx
  exact hsub i hx

lemma noncross_loss {k B i t : ℕ} {f g : Fin k → ℕ}
    (hclean : ∀ a : Fin k, f a ∈ payload B i → g a % (2 * B) < B)
    (hcross : ¬ Cross f g B i) (ht : t ≤ B)
    (hlocal : ∀ j : ℕ,
      t + ((rowMatches f B i).filter (fun a => g a ∈ payload B j)).card ≤ B) :
    t + (rowMatches f B i).card ≤ B := by
  classical
  by_cases hne : (rowMatches f B i).Nonempty
  · obtain ⟨a, ha⟩ := hne
    have ha' : f a ∈ payload B i := (Finset.mem_filter.mp ha).2
    have heq : (rowMatches f B i).filter (fun b => g b ∈ payload B (g a / (2 * B))) =
        rowMatches f B i := by
      apply Finset.filter_eq_self.mpr
      intro b hb
      have hb' : f b ∈ payload B i := (Finset.mem_filter.mp hb).2
      have hab : g b / (2 * B) = g a / (2 * B) := by
        by_contra hn
        rcases lt_or_gt_of_ne hn with h | h
        · exact hcross ⟨b, a, hb', ha', h⟩
        · exact hcross ⟨a, b, ha', hb', h⟩
      simpa only [hab] using payload_of_mod (hclean b hb')
    simpa only [heq] using hlocal (g a / (2 * B))
  · have hnil : rowMatches f B i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simpa only [hnil, Finset.card_empty, Nat.add_zero] using ht

lemma source_loss_card {k B i : ℕ} {f : Fin k → ℕ} (hf : Function.Injective f) :
    (payload B i \ Finset.univ.image f).card = B - (rowMatches f B i).card := by
  classical
  have himg : (rowMatches f B i).image f = Finset.univ.image f ∩ payload B i := by
    ext x
    simp only [rowMatches, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_inter]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, rfl⟩, ha⟩
    · rintro ⟨⟨a, rfl⟩, ha⟩
      exact ⟨a, ha, rfl⟩
  rw [Finset.card_sdiff, ← himg, card_payload, Finset.card_image_of_injective _ hf]

lemma unmatched_card {k N : ℕ} {f : Fin k → ℕ} (hf : Function.Injective f)
    (hb : ∀ a, f a < N) :
    (Finset.range N \ Finset.univ.image f).card = N - k := by
  have hsub : Finset.univ.image f ⊆ Finset.range N := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hb a)
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_range,
    Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]

theorem matching_loss {k B L t : ℕ} {f g : Fin k → ℕ}
    (hf : StrictMono f) (hg : StrictMono g) (hB : 0 < B)
    (hfb : ∀ a, f a < 2 * B * L) (hgb : ∀ a, g a < 2 * B * L)
    (hclean : ∀ a : Fin k, ∀ i : ℕ, f a ∈ payload B i → g a % (2 * B) < B)
    (ht : t ≤ B)
    (hlocal : ∀ i : Fin L, ∀ j : ℕ,
      t + ((rowMatches f B i).filter (fun a => g a ∈ payload B j)).card ≤ B) :
    L * t ≤ 2 * (2 * B * L - k) := by
  classical
  let C : Finset (Fin L) := Finset.univ.filter (fun i => Cross f g B i)
  have hex : ∀ i : C, ∃ a b : Fin k, f a ∈ payload B i.val ∧
      f b ∈ payload B i.val ∧ g a / (2 * B) < g b / (2 * B) := by
    intro i
    exact (Finset.mem_filter.mp i.property).2
  choose a b ha hb hab using hex
  let S (i : Fin L) : Finset ℕ :=
    if i ∈ C then ∅ else payload B i \ Finset.univ.image f
  let T (i : Fin L) : Finset ℕ :=
    if h : i ∈ C then marker B (g (a ⟨i, h⟩) / (2 * B)) else ∅
  have hsdisj : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    dsimp [S]
    split_ifs with hi hj <;> try simp
    exact (payload_disjoint (Fin.val_ne_of_ne hij)).mono Finset.sdiff_subset Finset.sdiff_subset
  have htdisj : Pairwise (fun i j => Disjoint (T i) (T j)) := by
    intro i j hij
    dsimp [T]
    split_ifs with hi hj <;> try simp
    apply marker_disjoint
    exact crossing_marker_distinct hf hg (Fin.val_ne_of_ne hij)
      (ha ⟨i, hi⟩) (hb ⟨i, hi⟩) (ha ⟨j, hj⟩) (hb ⟨j, hj⟩)
      (hab ⟨i, hi⟩) (hab ⟨j, hj⟩)
  have hssub : ∀ i, S i ⊆ Finset.range (2 * B * L) \ Finset.univ.image f := by
    intro i x hx
    dsimp [S] at hx
    split_ifs at hx with hi
    · simp at hx
    · obtain ⟨hp, hn⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨payload_subset_range i.isLt hp, hn⟩
  have htsub : ∀ i, T i ⊆ Finset.range (2 * B * L) \ Finset.univ.image g := by
    intro i x hx
    dsimp [T] at hx
    split_ifs at hx with hi
    · have hd := crossing_marker_unmatched hf hg hB hclean
        (ha ⟨i, hi⟩) (hb ⟨i, hi⟩) (hab ⟨i, hi⟩)
      have hi' : g (a ⟨i, hi⟩) / (2 * B) < L :=
        (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [Nat.mul_comm] using hgb (a ⟨i, hi⟩))
      exact Finset.mem_sdiff.mpr ⟨marker_subset_range hi' hx, Finset.disjoint_left.mp hd hx⟩
    · simp at hx
  have hsc := sum_cards_le S _ hsdisj hssub
  have htc := sum_cards_le T _ htdisj htsub
  rw [unmatched_card hf.injective hfb] at hsc
  rw [unmatched_card hg.injective hgb] at htc
  have heach : ∀ i : Fin L, t ≤ (S i).card + (T i).card := by
    intro i
    dsimp [S, T]
    split_ifs with hi
    · simpa only [Finset.card_empty, card_marker, Nat.zero_add] using ht
    · simp only [Finset.card_empty, Nat.add_zero, source_loss_card hf.injective]
      have hn : ¬ Cross f g B i := by
        simpa only [C, Finset.mem_filter, Finset.mem_univ, true_and] using hi
      have h := noncross_loss (fun a ha => hclean a i ha) hn ht (hlocal i)
      omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hsum
  omega

end EditRows

namespace EditRows

theorem matching_loss_real {k B L : ℕ} {t : ℝ} {f g : Fin k → ℕ}
    (hf : StrictMono f) (hg : StrictMono g) (hB : 0 < B)
    (hfb : ∀ a, f a < 2 * B * L) (hgb : ∀ a, g a < 2 * B * L)
    (hclean : ∀ a : Fin k, ∀ i : ℕ, f a ∈ payload B i → g a % (2 * B) < B)
    (ht : t ≤ B)
    (hlocal : ∀ i : Fin L, ∀ j : ℕ,
      t + (((rowMatches f B i).filter (fun a => g a ∈ payload B j)).card : ℝ) ≤ B) :
    (L : ℝ) * t ≤ 2 * ((2 * B * L - k : ℕ) : ℝ) := by
  classical
  by_cases ht0 : 0 ≤ t
  · have hceil : ∀ i : Fin L, ∀ j : ℕ,
        ⌈t⌉₊ + ((rowMatches f B i).filter (fun a => g a ∈ payload B j)).card ≤ B := by
      intro i j
      rw [← Nat.ceil_add_natCast ht0]
      exact Nat.ceil_le.mpr (hlocal i j)
    have h := matching_loss hf hg hB hfb hgb hclean (Nat.ceil_le.mpr ht) hceil
    have h' : (L : ℝ) * (⌈t⌉₊ : ℝ) ≤ 2 * ((2 * B * L - k : ℕ) : ℝ) := by
      exact_mod_cast h
    exact (mul_le_mul_of_nonneg_left (Nat.le_ceil t) (Nat.cast_nonneg L)).trans h'
  · exact (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg L) (le_of_not_ge ht0)).trans
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))

end EditRows

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_RowSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Payload restrictions and fresh-marker row separation
-/

namespace EditDistortion

lemma sublist_ofFn_comp {A : Type*} {m n : ℕ} (x : Fin n → A) (f : Fin m ↪o Fin n) :
    (List.ofFn (fun i => x (f i))).Sublist (List.ofFn x) := by
  apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
  refine ⟨((Fin.castOrderIso (List.length_ofFn (f := fun i => x (f i)))).toOrderEmbedding.trans f).trans
    (Fin.castOrderIso (List.length_ofFn (f := x)).symm).toOrderEmbedding, ?_⟩
  intro i
  simp only [List.get_ofFn]
  rfl

lemma indel_le_of_matching {A : Type*} {m n k : ℕ} (x : Fin m → A) (y : Fin n → A)
    (f : Fin k ↪o Fin m) (g : Fin k ↪o Fin n) (heq : ∀ i, x (f i) = y (g i)) :
    indel (List.ofFn x) (List.ofFn y) ≤ m + n - 2 * k := by
  have hx := sublist_ofFn_comp x f
  have hy := sublist_ofFn_comp y g
  have hz : (fun i => x (f i)) = (fun i => y (g i)) := funext heq
  rw [← hz] at hy
  simpa only [List.length_ofFn] using indel_le_matching_loss hx hy

end EditDistortion

namespace EditRows

lemma payload_mod {B i x : ℕ} (hB : 0 < B) (hx : x ∈ payload B i) :
    x % (2 * B) < B := by
  have hd := payload_index hB hx
  have hx := mem_payload.mp hx
  have hm := Nat.mod_add_div x (2 * B)
  rw [hd] at hm
  omega

def rowValue {A : Type*} {L B : ℕ} (P : Fin L → Fin B → A)
    (x : Fin (2 * B * L)) : Option A :=
  if h : x.val % (2 * B) < B then
    some (P ⟨x.val / (2 * B), (Nat.div_lt_iff_lt_mul (by omega)).mpr
      (by simpa only [Nat.mul_comm] using x.isLt)⟩ ⟨x.val % (2 * B), h⟩)
  else none

def rowWord {A : Type*} {L B : ℕ} (P : Fin L → Fin B → A) : List (Option A) :=
  List.ofFn (rowValue P)

@[simp] lemma rowWord_length {A : Type*} {L B : ℕ} (P : Fin L → Fin B → A) :
    (rowWord P).length = 2 * B * L := by simp [rowWord]

lemma rowValue_ne_none {A : Type*} {L B : ℕ} (P : Fin L → Fin B → A)
    (x : Fin (2 * B * L)) : rowValue P x ≠ none ↔ x.val % (2 * B) < B := by
  unfold rowValue
  split_ifs <;> simp_all

def payloadOffset {B i x : ℕ} (h : x ∈ payload B i) : Fin B :=
  ⟨x - 2 * B * i, by have h := mem_payload.mp h; omega⟩

lemma rowValue_payload {A : Type*} {L B : ℕ} (hB : 0 < B) (P : Fin L → Fin B → A)
    (i : Fin L) (x : Fin (2 * B * L)) (hx : x.val ∈ payload B i) :
    rowValue P x = some (P i (payloadOffset hx)) := by
  have hd := payload_index hB hx
  have hm := payload_mod hB hx
  rw [rowValue, dite_eq_left hm]
  congr 2
  · exact Fin.ext hd
  · apply Fin.ext
    change x.val % (2 * B) = x.val - 2 * B * i.val
    have hh := Nat.mod_add_div x.val (2 * B)
    rw [hd] at hh
    omega

end EditRows

namespace EditRows

lemma local_matching_bound {A : Type*} {k L B : ℕ} {t : ℝ}
    (P Q : Fin L → Fin B → A) (hB : 0 < B)
    (f g : Fin k → Fin (2 * B * L))
    (hf : StrictMono (fun a => (f a).val)) (hg : StrictMono (fun a => (g a).val))
    (heq : ∀ a, rowValue P (f a) = rowValue Q (g a))
    (ht : t ≤ B)
    (hsep : ∀ i j : Fin L, 2 * t ≤
      (EditDistortion.indel (List.ofFn (P i)) (List.ofFn (Q j)) : ℝ))
    (i : Fin L) (j : ℕ) :
    t + (((rowMatches (fun a => (f a).val) B i).filter
      (fun a => (g a).val ∈ payload B j)).card : ℝ) ≤ B := by
  classical
  let K := (rowMatches (fun a => (f a).val) B i).filter
    (fun a => (g a).val ∈ payload B j)
  change t + (K.card : ℝ) ≤ B
  by_cases hj : j < L
  · let e : Fin K.card ↪o Fin k := K.orderEmbOfFin rfl
    have hp : ∀ r : Fin K.card,
        (f (e r)).val ∈ payload B i ∧ (g (e r)).val ∈ payload B j := by
      intro r
      have h := K.orderEmbOfFin_mem rfl r
      exact ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2,
        (Finset.mem_filter.mp h).2⟩
    let ff : Fin K.card → Fin B := fun r => payloadOffset (hp r).1
    let gg : Fin K.card → Fin B := fun r => payloadOffset (hp r).2
    have hff : StrictMono ff := by
      intro r s hrs
      have h := hf (e.strictMono hrs)
      change (f (e r)).val < (f (e s)).val at h
      have hr := mem_payload.mp (hp r).1
      have hs := mem_payload.mp (hp s).1
      change (f (e r)).val - 2 * B * i.val < (f (e s)).val - 2 * B * i.val
      omega
    have hgg : StrictMono gg := by
      intro r s hrs
      have h := hg (e.strictMono hrs)
      change (g (e r)).val < (g (e s)).val at h
      have hr := mem_payload.mp (hp r).2
      have hs := mem_payload.mp (hp s).2
      change (g (e r)).val - 2 * B * j < (g (e s)).val - 2 * B * j
      omega
    have he : ∀ r, P i (ff r) = Q ⟨j, hj⟩ (gg r) := by
      intro r
      have h := heq (e r)
      rw [rowValue_payload hB P i (f (e r)) (hp r).1,
        rowValue_payload hB Q ⟨j, hj⟩ (g (e r)) (hp r).2] at h
      exact Option.some.inj h
    have hcost := EditDistortion.indel_le_of_matching (P i) (Q ⟨j, hj⟩)
      (OrderEmbedding.ofStrictMono ff hff) (OrderEmbedding.ofStrictMono gg hgg) he
    have hk : K.card ≤ B := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective ff hff.injective
    have hcost' : (EditDistortion.indel (List.ofFn (P i)) (List.ofFn (Q ⟨j, hj⟩)) : ℝ) ≤
        ((B + B - 2 * K.card : ℕ) : ℝ) := by exact_mod_cast hcost
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_mul] at hcost'
    norm_num at hcost'
    have hsep' := hsep i ⟨j, hj⟩
    linarith
  · have hnil : K = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have h := mem_payload.mp (Finset.mem_filter.mp ha).2
      have hg' := (g a).isLt
      have hh : 2 * B * L ≤ 2 * B * j := Nat.mul_le_mul_left _ (by omega)
      omega
    simpa only [hnil, Finset.card_empty, Nat.cast_zero, add_zero] using ht

theorem indel_row_separation {A : Type*} {L B : ℕ} {t : ℝ}
    (P Q : Fin L → Fin B → A) (hB : 0 < B) (ht : t ≤ B)
    (hsep : ∀ i j : Fin L, 2 * t ≤
      (EditDistortion.indel (List.ofFn (P i)) (List.ofFn (Q j)) : ℝ)) :
    (L : ℝ) * t ≤ (EditDistortion.indel (rowWord P) (rowWord Q) : ℝ) := by
  classical
  obtain ⟨z, hx, hy, hcost⟩ := EditDistortion.indel_matching (rowWord P) (rowWord Q)
  obtain ⟨f₀, hf₀⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hx
  obtain ⟨g₀, hg₀⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hy
  let f : Fin z.length ↪o Fin (2 * B * L) :=
    f₀.trans (Fin.castOrderIso (rowWord_length P)).toOrderEmbedding
  let g : Fin z.length ↪o Fin (2 * B * L) :=
    g₀.trans (Fin.castOrderIso (rowWord_length Q)).toOrderEmbedding
  have hf : StrictMono (fun a => (f a).val) := fun _ _ h => f.strictMono h
  have hg : StrictMono (fun a => (g a).val) := fun _ _ h => g.strictMono h
  have heq : ∀ a, rowValue P (f a) = rowValue Q (g a) := by
    intro a
    have h := (hf₀ a).symm.trans (hg₀ a)
    simpa only [rowWord, List.get_ofFn] using! h
  have hclean : ∀ a : Fin z.length, ∀ i : ℕ,
      (f a).val ∈ payload B i → (g a).val % (2 * B) < B := by
    intro a i ha
    apply (rowValue_ne_none Q (g a)).mp
    rw [← heq a]
    exact (rowValue_ne_none P (f a)).mpr (payload_mod hB ha)
  have hbound := matching_loss_real hf hg hB (fun a => (f a).isLt)
    (fun a => (g a).isLt) hclean ht (local_matching_bound P Q hB f g hf hg heq ht hsep)
  have hk : z.length ≤ 2 * B * L := by simpa only [rowWord_length] using hx.length_le
  have he : 2 * (2 * B * L - z.length) =
      (rowWord P).length + (rowWord Q).length - 2 * z.length := by
    rw [rowWord_length, rowWord_length]
    omega
  rw [hcost, ← he, Nat.cast_mul, Nat.cast_ofNat]
  exact hbound

end EditRows

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_BlockAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Contraction of arbitrary bit alignments to letter blocks
-/

namespace EditCode
open EditDistortion
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type*} {t k : ℕ}

def BlockPair (f g : Fin k → ℕ) (w i j : ℕ) : Prop :=
  ∀ r : ℕ, r < w → ∃ a : Fin k, f a = w*i+r ∧ g a = w*j+r

end EditCode

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_BinaryEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed-length binary embeddings with unrestricted edit distance
-/

namespace EditCode
variable (A : Type*) [Fintype A]

noncomputable def labels : A ↪ (Fin (Nat.clog 2 (Fintype.card A)) → Bool) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by
    simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool] using
      Nat.le_pow_clog (by norm_num : 1 < 2) (Fintype.card A)))

end EditCode

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_HashCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite cut hashes and averaged separation
-/

namespace EditCutHash
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

noncomputable def sep {X : Type*} (x y : X) : ℝ := if x = y then 0 else 1
@[simp] lemma sep_self {X : Type*} (x : X) : sep x x = 0 := by simp [sep]

section Hash
variable {I X : Type*} [Fintype I]

noncomputable def distance (w : I → ℝ) (c : I → X → Bool) (x y : X) : ℝ :=
  ∑ i, w i * sep (c i x) (c i y)

noncomputable def coin (w : I → ℝ) (a : ℝ) (i : I) (b : Bool) : ℝ :=
  if b then 1-Real.exp (-a*w i) else Real.exp (-a*w i)

noncomputable def probability (w : I → ℝ) (a : ℝ) (h : I → Bool) : ℝ :=
  ∏ i, coin w a i (h i)

def key (c : I → X → Bool) (h : I → Bool) (x : X) : I → Bool :=
  fun i => h i && c i x

lemma probability_nonneg {w : I → ℝ} (hw : ∀ i, 0 ≤ w i) {a : ℝ} (ha : 0 ≤ a)
    (h : I → Bool) : 0 ≤ probability w a h := by
  apply prod_nonneg
  intro i _
  unfold coin
  split
  · have hb : Real.exp (-a*w i) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hw i])
    linarith
  · exact (Real.exp_pos _).le

end Hash
end EditCutHash

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_Histograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Hash separation and finite histogram inequalities
-/

namespace EditCutHash
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

section Histogram
variable {J K : Type*} [Fintype J] [Fintype K]

noncomputable def hit (a b : K) : ℝ := if a = b then 1 else 0
omit [Fintype K] in
@[simp] lemma hit_self (a : K) : hit a a = 1 := by simp [hit]

noncomputable def count (f : J → K) (z : K) : ℝ := ∑ j, hit (f j) z
noncomputable def histogramDistance (f g : J → K) : ℝ := ∑ z, |count f z-count g z|

end Histogram
end EditCutHash

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_MeanHistograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean histograms as finite cut distances
-/

namespace EditCutHash
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

section MeanHistogram
variable {I J X : Type*} [Fintype I] [Fintype J]

noncomputable def meanHistogram (w : I → ℝ) (a : ℝ) (c : I → X → Bool) (f g : J → X) : ℝ :=
  ∑ h : I → Bool, probability w a h * histogramDistance (fun j => key c h (f j)) (fun j => key c h (g j))

noncomputable def rate (s : ℕ) : ℝ := Real.log (2*(s : ℝ)^2)/(s : ℝ)

lemma rate_nonneg {s : ℕ} (hs : 0 < s) : 0 ≤ rate s := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  apply div_nonneg (Real.log_nonneg (by nlinarith)) (by positivity)

end MeanHistogram
end EditCutHash

namespace EditCutHash
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

@[simp] lemma meanHistogram_self {I J X : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (a : ℝ) (c : I → X → Bool) (f : J → X) :
    meanHistogram w a c f f = 0 := by
  simp [meanHistogram,histogramDistance]

end EditCutHash

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_CutModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite weighted cuts and histogram lifts
-/

namespace EditCutModel

universe u v

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

noncomputable def sep (a b : Bool) : ℝ := if a = b then 0 else 1

structure Model (X : Type u) where
  Index : Type
  finiteIndex : Fintype Index
  weight : Index → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  cut : Index → X → Bool

attribute [instance] Model.finiteIndex

noncomputable def Model.dist {X : Type u} (M : Model X) (x y : X) : ℝ :=
  ∑ i, M.weight i * sep (M.cut i x) (M.cut i y)

@[simp] lemma Model.dist_self {X : Type u} (M : Model X) (x : X) : M.dist x x = 0 := by
  simp [Model.dist,sep]

noncomputable def Model.pullback {X : Type u} {Y : Type v} (M : Model X) (f : Y → X) : Model Y where
  Index := M.Index
  finiteIndex := M.finiteIndex
  weight := M.weight
  nonneg := M.nonneg
  cut i y := M.cut i (f y)

noncomputable def Model.scale {X : Type u} (M : Model X) (a : ℝ) (ha : 0 ≤ a) : Model X where
  Index := M.Index
  finiteIndex := M.finiteIndex
  weight i := a*M.weight i
  nonneg i := mul_nonneg ha (M.nonneg i)
  cut := M.cut

noncomputable def Model.total {X : Type u} {J : Type} [Fintype J] (M : J → Model X) : Model X where
  Index := (j : J) × (M j).Index
  finiteIndex := inferInstance
  weight i := (M i.1).weight i.2
  nonneg i := (M i.1).nonneg i.2
  cut i x := (M i.1).cut i.2 x

end EditCutModel

namespace EditCutModel
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

noncomputable def countNat {J K : Type*} [Fintype J] (f : J → K) (z : K) : ℕ :=
  (univ.filter (fun j => f j = z)).card

noncomputable def Model.histogram {X : Type*} (M : Model X) (s : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    Model (Fin s → X) where
  Index := (M.Index → Bool) × (M.Index → Bool) × Fin s
  finiteIndex := inferInstance
  weight i := EditCutHash.probability M.weight a i.1
  nonneg i := EditCutHash.probability_nonneg M.nonneg ha i.1
  cut i f := decide (i.2.2.val < countNat (fun j : Fin s => EditCutHash.key M.cut i.1 (f j)) i.2.1)

end EditCutModel

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_Cuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite scalar and absolutely summable cut decompositions
-/

namespace EditCuts
open scoped BigOperators
open Finset

lemma top_clipping_distance (a b x y : ℝ) (hba : b < a)
    (hx : x = a ∨ x ≤ b) (hy : y = a ∨ y ≤ b) :
    |x - y| = |min x b - min y b| +
      (a - b) * |(if x = a then (1 : ℝ) else 0) - (if y = a then (1 : ℝ) else 0)| := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · subst x; subst y; simp
  · subst x
    have hya : y < a := hy.trans_lt hba
    simp [min_eq_right hba.le, min_eq_left hy, hya.ne,
      abs_of_nonneg (sub_nonneg.mpr hya.le), abs_of_nonneg (sub_nonneg.mpr hy)]
  · subst y
    have hxa : x < a := hx.trans_lt hba
    simp [min_eq_right hba.le, min_eq_left hx, hxa.ne,
      abs_of_nonpos (sub_nonpos.mpr hxa.le), abs_of_nonpos (sub_nonpos.mpr hx)]
  · have hxa : x < a := hx.trans_lt hba
    have hya : y < a := hy.trans_lt hba
    simp [min_eq_left hx, min_eq_left hy, hxa.ne, hya.ne]

section Finite
variable {X : Type*} [Fintype X] [DecidableEq X]

def cut (A : Finset X) (x : X) : ℝ := if x ∈ A then 1 else 0

theorem scalar_decomposition_aux (s : Finset ℝ) :
    ∀ (f : X → ℝ), (∀ x, f x ∈ s) →
      ∃ w : Finset X → ℝ, (∀ A, 0 ≤ w A) ∧
        ∀ x y, |f x - f y| = ∑ A : Finset X, w A * |cut A x - cut A y| := by
  classical
  induction s using Finset.induction_on_max with
  | empty =>
    intro f hf
    refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
    intro x
    simpa using hf x
  | insert a s hmax ih =>
    intro f hf
    by_cases hse : s = ∅
    · have hfconst (x : X) : f x = a := by simpa [hse] using hf x
      refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
      intro x y
      simp [hfconst]
    have hsn : s.Nonempty := nonempty_iff_ne_empty.mpr hse
    let b : ℝ := s.max' hsn
    have hb : b ∈ s := max'_mem s hsn
    have hba : b < a := hmax b hb
    have hfb (x : X) (hx : f x ≠ a) : f x ≤ b := by
      exact le_max' s (f x) ((mem_insert.mp (hf x)).resolve_left hx)
    let f' : X → ℝ := fun x => min (f x) b
    have hf' (x : X) : f' x ∈ s := by
      by_cases hx : f x = a
      · simpa only [f', hx, min_eq_right hba.le] using hb
      · simpa only [f', min_eq_left (hfb x hx)] using
          ((mem_insert.mp (hf x)).resolve_left hx)
    obtain ⟨w, hw, hwd⟩ := ih f' hf'
    let A : Finset X := univ.filter (fun x => f x = a)
    have hcut (x : X) : cut A x = if f x = a then 1 else 0 := by simp [cut, A]
    have hcase (x : X) : f x = a ∨ f x ≤ b := by
      by_cases hx : f x = a
      · exact Or.inl hx
      · exact Or.inr (hfb x hx)
    have heq (x y : X) : |f x - f y| = |f' x - f' y| +
        (a - b) * |cut A x - cut A y| := by
      simpa only [f', hcut] using top_clipping_distance a b (f x) (f y) hba (hcase x) (hcase y)
    refine ⟨fun B => w B + if B = A then a - b else 0, ?_, ?_⟩
    · intro B
      apply add_nonneg (hw B)
      split_ifs
      · exact sub_nonneg.mpr hba.le
      · exact le_rfl
    · intro x y
      rw [heq, hwd]
      simp only [add_mul, sum_add_distrib, ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]

theorem scalar_decomposition (f : X → ℝ) :
    ∃ w : Finset X → ℝ, (∀ A, 0 ≤ w A) ∧
      ∀ x y, |f x - f y| = ∑ A : Finset X, w A * |cut A x - cut A y| :=
  scalar_decomposition_aux (univ.image f) f (fun x => mem_image.mpr ⟨x, mem_univ x, rfl⟩)

end Finite
end EditCuts

namespace EditCuts
open scoped BigOperators
open Finset

abbrev RealL1 := lp (fun _ : ℕ => ℝ) 1

lemma l1_norm (f : RealL1) : ‖f‖ = ∑' n, |f n| := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal) f

lemma l1_summable (f : RealL1) : Summable (fun n => |f n|) := by
  simpa using (lp.memℓp f).summable (by norm_num : 0 < (1 : ENNReal).toReal)

lemma l1_norm_sub (f g : RealL1) : ‖f - g‖ = ∑' n, |f n - g n| :=
  l1_norm (f - g)

section Finite
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] in
lemma cut_empty (x : X) : cut ∅ x = 0 := by simp [cut]
lemma cut_univ (x : X) : cut univ x = 1 := by simp [cut]

theorem scalar_decomposition_nontrivial (f : X → ℝ) :
    ∃ w : Finset X → ℝ, (∀ A, 0 ≤ w A) ∧ w ∅ = 0 ∧ w univ = 0 ∧
      ∀ x y, |f x - f y| = ∑ A : Finset X, w A * |cut A x - cut A y| := by
  classical
  obtain ⟨w, hw, hd⟩ := scalar_decomposition f
  refine ⟨fun A => if A = ∅ ∨ A = univ then 0 else w A, ?_, by simp, by simp, ?_⟩
  · intro A
    dsimp only
    split_ifs <;> simp_all
  · intro x y
    rw [hd]
    apply sum_congr rfl
    intro A _
    by_cases hac : A = ∅ ∨ A = univ
    · rcases hac with rfl | rfl <;> simp [cut_empty, cut_univ]
    · simp [hac]

lemma weight_le_distance (f : X → ℝ) (w : Finset X → ℝ)
    (hw : ∀ A, 0 ≤ w A)
    (hd : ∀ x y, |f x - f y| = ∑ A : Finset X, w A * |cut A x - cut A y|)
    (A : Finset X) (x y : X) (hx : x ∈ A) (hy : y ∉ A) :
    w A ≤ |f x - f y| := by
  rw [hd]
  calc
    w A = w A * |cut A x - cut A y| := by simp [cut, hx, hy]
    _ ≤ _ := single_le_sum (fun B _ => mul_nonneg (hw B) (abs_nonneg (cut B x - cut B y))) (mem_univ A)

theorem l1_decomposition (H : X → RealL1) :
    ∃ c : Finset X → ℝ, (∀ A, 0 ≤ c A) ∧ c ∅ = 0 ∧ c univ = 0 ∧
      ∀ x y, ‖H x - H y‖ = ∑ A : Finset X, c A * |cut A x - cut A y| := by
  classical
  choose w hw he hu hd using fun n => scalar_decomposition_nontrivial (fun x => H x n)
  have hs (A : Finset X) : Summable (fun n => w n A) := by
    by_cases ha : A = ∅ ∨ A = univ
    · rcases ha with rfl | rfl <;> simpa only [he, hu] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr (not_or.mp ha).1
    obtain ⟨y, hy⟩ : ∃ y, y ∉ A := by
      by_contra! hn
      exact (not_or.mp ha).2 (eq_univ_iff_forall.mpr hn)
    exact Summable.of_nonneg_of_le (fun n => hw n A)
      (fun n => weight_le_distance _ _ (hw n) (hd n) A x y hx hy)
      (l1_summable (H x - H y))
  refine ⟨fun A => ∑' n, w n A, fun A => tsum_nonneg (fun n => hw n A),
    by simp [he], by simp [hu], ?_⟩
  intro x y
  rw [l1_norm_sub]
  simp_rw [hd]
  rw [Summable.tsum_finsetSum]
  · apply sum_congr rfl
    intro A _
    exact (hs A).tsum_mul_right _
  · intro A _
    exact (hs A).mul_right _

end Finite
end EditCuts

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_FourierCharacters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite Fourier inversion, Parseval, and character displacement
-/

namespace EditFourier
open scoped BigOperators
open Finset

section FiniteRing
variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

noncomputable def transform (ψ : AddChar R ℂ) (F : R → ℂ) (k : R) : ℂ :=
  ∑ t : R, ψ (-(t * k)) * F t

theorem transform_twice (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (F : R → ℂ) :
    transform ψ (transform ψ F) = fun j => (Fintype.card R : ℂ) * F (-j) := by
  funext j
  simp only [transform, mul_sum, ← mul_assoc, ← AddChar.map_add_eq_mul, ← neg_add,
    mul_comm _ j, ← add_mul]
  rw [sum_comm]
  simp only [← sum_mul, ← neg_mul]
  have h1 (t : R) : ∑ i, ψ (t * i) = if t = 0 then (Fintype.card R : ℂ) else 0 := by
    simpa only [mul_comm, Nat.cast_ite, Nat.cast_zero] using AddChar.sum_mulShift t hψ
  have h2 (x j : R) : -(j + x) = 0 ↔ x = -j := by
    rw [neg_add, add_comm, add_eq_zero_iff_neg_eq, neg_neg]
  simp only [h1, h2, ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]

omit [DecidableEq R] in
theorem transform_sub (ψ : AddChar R ℂ) (F G : R → ℂ) :
    transform ψ (F - G) = transform ψ F - transform ψ G := by
  funext k
  simp only [transform, Pi.sub_apply, mul_sub, sum_sub_distrib]

omit [DecidableEq R] in
theorem transform_shift (ψ : AddChar R ℂ) (F : R → ℂ) (l k : R) :
    transform ψ (fun t => F (t + l)) k = ψ (l * k) * transform ψ F k := by
  classical
  calc
    _ = ∑ t : R, ψ (-((t - l) * k)) * F t := by
      apply Fintype.sum_equiv (Equiv.addRight l)
      intro t
      simp
    _ = ψ (l * k) * transform ψ F k := by
      rw [transform, mul_sum]
      apply sum_congr rfl
      intro t _
      rw [sub_mul, neg_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring

omit [DecidableEq R] in
theorem transform_pairing (ψ : AddChar R ℂ) (F G : R → ℂ) :
    ∑ k, transform ψ F k * G k = ∑ t, F t * transform ψ G t := by
  simp only [transform, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  apply sum_congr rfl
  intro k _
  rw [mul_comm k t]
  ring

omit [DecidableEq R] in
theorem transform_conj (ψ : AddChar R ℂ) (F : R → ℂ) (k : R) :
    transform ψ (fun t => (starRingEnd ℂ) (F t)) k =
      (starRingEnd ℂ) (transform ψ F (-k)) := by
  simp only [transform, map_sum, map_mul]
  apply sum_congr rfl
  intro t _
  rw [← AddChar.map_neg_eq_conj]
  congr 2
  ring

theorem parseval (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (F : R → ℂ) :
    ∑ k, ‖transform ψ F k‖ ^ 2 = (Fintype.card R : ℝ) * ∑ t, ‖F t‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq]
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.mul_conj]
  rw [transform_pairing]
  simp only [transform_conj, transform_twice ψ hψ F, neg_neg, map_mul,
    map_natCast, Finset.mul_sum]
  apply sum_congr rfl
  intro t _
  ring

theorem displacement (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (F : R → ℂ) (l : R) :
    (Fintype.card R : ℝ) * ∑ t, ‖F (t + l) - F t‖ ^ 2 =
      ∑ k, ‖transform ψ F k‖ ^ 2 * ‖ψ (l * k) - 1‖ ^ 2 := by
  rw [← parseval ψ hψ (fun t => F (t + l) - F t)]
  have ht : transform ψ (fun t => F (t + l) - F t) =
      fun k => (ψ (l * k) - 1) * transform ψ F k := by
    rw [show (fun t => F (t + l) - F t) = (fun t => F (t + l)) - F from rfl,
      transform_sub]
    funext k
    simp only [Pi.sub_apply, transform_shift]
    ring
  rw [ht]
  apply sum_congr rfl
  intro k _
  rw [norm_mul, mul_pow, mul_comm]

noncomputable def fourier (ψ : AddChar R ℂ) (F : R → ℂ) (k : R) : ℂ :=
  transform ψ F k / (Fintype.card R : ℂ)

theorem displacement_normalized (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (F : R → ℂ) (l : R) :
    (∑ t, ‖F (t + l) - F t‖ ^ 2) / (Fintype.card R : ℝ) =
      ∑ k, ‖fourier ψ F k‖ ^ 2 * ‖ψ (l * k) - 1‖ ^ 2 := by
  have hn : (Fintype.card R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [fourier, norm_div, Complex.norm_natCast, div_pow, div_mul_eq_mul_div,
    ← sum_div]
  apply (eq_div_iff (pow_ne_zero 2 hn)).mpr
  rw [← displacement ψ hψ F l]
  field_simp

end FiniteRing

section ProductCharacter
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {A : J → Type*} [∀ j, CommRing (A j)]

noncomputable def productCharacter (ψ : ∀ j, AddChar (A j) ℂ) :
    AddChar (∀ j, A j) ℂ where
  toFun x := ∏ j, ψ j (x j)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by simp [AddChar.map_add_eq_mul, prod_mul_distrib]

theorem productCharacter_single (ψ : ∀ j, AddChar (A j) ℂ)
    (a : ∀ j, A j) (j : J) (x : A j) :
    (productCharacter ψ) (a * Pi.single j x) = ψ j (a j * x) := by
  change ∏ i, ψ i (a i * Pi.single j x i) = _
  rw [prod_eq_single j]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · simp

theorem productCharacter_primitive (ψ : ∀ j, AddChar (A j) ℂ)
    (hψ : ∀ j, (ψ j).IsPrimitive) : (productCharacter ψ).IsPrimitive := by
  intro a ha h
  apply ha
  funext j
  by_contra hj
  apply hψ j hj
  ext x
  have hx := DFunLike.congr_fun h (Pi.single j x)
  simpa only [AddChar.mulShift_apply, productCharacter_single, AddChar.one_apply] using hx

noncomputable def torusCharacter (p : J → ℕ) [∀ j, NeZero (p j)] :
    AddChar (∀ j, ZMod (p j)) ℂ :=
  productCharacter (fun j => ZMod.stdAddChar (N := p j))

theorem torusCharacter_primitive (p : J → ℕ) [∀ j, NeZero (p j)] :
    (torusCharacter p).IsPrimitive :=
  productCharacter_primitive _ (fun j => ZMod.isPrimitive_stdAddChar (p j))

end ProductCharacter
end EditFourier

namespace EditFourier
open scoped BigOperators
open Finset

theorem norm_pow_sub_one_le (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    ‖z ^ n - 1‖ ≤ (n : ℝ) * ‖z - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      ‖z ^ (n + 1) - 1‖ = ‖z * (z ^ n - 1) + (z - 1)‖ := by
        congr 1
        rw [pow_succ']
        ring
      _ ≤ ‖z * (z ^ n - 1)‖ + ‖z - 1‖ := norm_add_le _ _
      _ = ‖z ^ n - 1‖ + ‖z - 1‖ := by rw [norm_mul, hz, one_mul]
      _ ≤ (n : ℝ) * ‖z - 1‖ + ‖z - 1‖ := add_le_add ih le_rfl
      _ = ((n + 1 : ℕ) : ℝ) * ‖z - 1‖ := by push_cast; ring

theorem root_separation (z : ℂ) (hz : ‖z‖ = 1) (hne : z ≠ 1)
    (q : ℕ) (hq : 0 < q) (hpow : z ^ q = 1) :
    2 ≤ (q : ℝ) * ‖z - 1‖ := by
  have hs : ∑ i ∈ range q, z ^ i = 0 := by
    apply eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero.mpr hne.symm)
    rw [mul_neg_geom_sum, hpow, sub_self]
  have heq : (q : ℝ) = ‖∑ i ∈ range q, (1 - z ^ i)‖ := by
    simp [sum_sub_distrib, hs]
  have hbound : (q : ℝ) ≤ (∑ i ∈ range q, (i : ℝ)) * ‖z - 1‖ := by
    rw [heq]
    calc
      _ ≤ ∑ i ∈ range q, ‖1 - z ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range q, (i : ℝ) * ‖z - 1‖ := by
        apply sum_le_sum
        intro i _
        rw [norm_sub_rev]
        exact norm_pow_sub_one_le z hz i
      _ = _ := by rw [sum_mul]
  have hid : (∑ i ∈ range q, (i : ℝ)) * 2 = (q : ℝ) * ((q : ℝ) - 1) := by
    have ht := congrArg (fun a : ℕ => (a : ℝ)) (sum_range_id_mul_two q)
    push_cast [Nat.cast_sub (Nat.succ_le_of_lt hq)] at ht
    exact ht
  have hnn := norm_nonneg (z - 1)
  have hm := congrArg (fun x : ℝ => x * ‖z - 1‖) hid
  have hp : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hh : (q : ℝ) * 2 ≤ (q : ℝ) * ((q : ℝ) * ‖z - 1‖) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ hp).mp hh

end EditFourier

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_PrimeCharacters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coprime roots and prime-product Fourier multipliers
-/

namespace EditFourier
open scoped BigOperators
open Finset

section CoprimeRoots
variable {J : Type*} [DecidableEq J]

omit [DecidableEq J] in

theorem prod_roots_pow (s : Finset J) (p : J → ℕ) (z : J → ℂ)
    (hz : ∀ j ∈ s, z j ^ p j = 1) (q : ℕ) (hq : ∀ j ∈ s, p j ∣ q) :
    (∏ j ∈ s, z j) ^ q = 1 := by
  rw [← prod_pow]
  apply prod_eq_one
  intro j hj
  obtain ⟨m, hm⟩ := hq j hj
  rw [hm, pow_mul, hz j hj, one_pow]

theorem coprime_roots_nontrivial (s : Finset J) (p : J → ℕ) (z : J → ℂ)
    (hcop : (s : Set J).Pairwise (fun i j => (p i).Coprime (p j)))
    (hz : ∀ j ∈ s, z j ^ p j = 1) (i : J) (hi : i ∈ s) (hne : z i ≠ 1) :
    (∏ j ∈ s, z j) ≠ 1 := by
  intro h
  let q := ∏ j ∈ s.erase i, p j
  have hq : ∀ j ∈ s.erase i, p j ∣ q := fun j hj => dvd_prod_of_mem p hj
  have hpow := prod_roots_pow (s.erase i) p z
    (fun j hj => hz j (mem_of_mem_erase hj)) q hq
  have hp : z i ^ q = 1 := by
    have hh := congrArg (fun a : ℂ => a ^ q) h
    rw [← mul_prod_erase s z hi, mul_pow, hpow, mul_one, one_pow] at hh
    exact hh
  have hc : (p i).Coprime q := Nat.Coprime.prod_right fun j hj =>
    hcop hi (mem_of_mem_erase hj) (ne_of_mem_erase hj).symm
  exact hne ((pow_eq_one_iff_of_coprime hc).mp ⟨hz i hi, hp⟩)

theorem coprime_root_separation (s : Finset J) (p : J → ℕ) (z : J → ℂ)
    (hpos : ∀ j ∈ s, 0 < p j)
    (hcop : (s : Set J).Pairwise (fun i j => (p i).Coprime (p j)))
    (hz : ∀ j ∈ s, z j ^ p j = 1) (hnorm : ∀ j ∈ s, ‖z j‖ = 1)
    (i : J) (hi : i ∈ s) (hne : z i ≠ 1) :
    2 ≤ ((∏ j ∈ s, p j : ℕ) : ℝ) * ‖(∏ j ∈ s, z j) - 1‖ := by
  apply root_separation
  · rw [norm_prod]
    exact prod_eq_one hnorm
  · exact coprime_roots_nontrivial s p z hcop hz i hi hne
  · exact prod_pos hpos
  · apply prod_roots_pow s p z hz
    exact fun j hj => dvd_prod_of_mem p hj

end CoprimeRoots
end EditFourier

namespace EditFourier
open scoped BigOperators
open Finset

lemma norm_sub_one_sq_of_norm_one (z : ℂ) (hz : ‖z‖ = 1) :
    ‖z - 1‖ ^ 2 = 2 - 2 * z.re := by
  have hh : z.re * z.re + z.im * z.im = 1 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hz
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h
    simpa only [one_pow] using h
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  nlinarith

lemma character_multiplier_four {R : Type*} [AddCommGroup R] [Finite R]
    (ψ : AddChar R ℂ) (a : R) : ‖ψ a - 1‖ ^ 2 ≤ 4 := by
  have hb : ‖ψ a - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖ψ a‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [ψ.norm_apply, norm_one]; norm_num
  nlinarith [norm_nonneg (ψ a - 1)]

lemma average_character_multiplier {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (a : R) :
    (∑ x : R, ‖ψ (a * x) - 1‖ ^ 2) / (Fintype.card R : ℝ) =
      if a = 0 then 0 else 2 := by
  by_cases ha : a = 0
  · simp [ha]
  have hs : ∑ x : R, ψ (a * x) = 0 := by
    simpa only [ha, ite_false, Nat.cast_zero, mul_comm] using AddChar.sum_mulShift a hψ
  have hr : ∑ x : R, (ψ (a * x)).re = 0 := by rw [← Complex.re_sum, hs]; rfl
  simp_rw [norm_sub_one_sq_of_norm_one _ (ψ.norm_apply _)]
  rw [sum_sub_distrib, ← mul_sum, hr, mul_zero, sub_zero]
  simp only [sum_const, card_univ, nsmul_eq_mul, ha, ite_false]
  field_simp

lemma std_character_pow (p : ℕ) [NeZero p] (a : ZMod p) :
    (ZMod.stdAddChar a) ^ p = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  simp

end EditFourier

namespace EditFourier
open scoped BigOperators
open Finset

section PrimeProduct
variable {J : Type*} [Fintype J] [DecidableEq J]
variable (p : J → ℕ) [∀ j, NeZero (p j)]

theorem multiplier_comparison
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (B : ℝ) (hB : 1 ≤ B) (hpB : ∀ j, (p j : ℝ) ≤ B)
    (h : ℕ) (hh : 0 < h) (lam : ∀ j, ZMod (p j)) (i : J) (u : ZMod (p i)) :
    ‖ZMod.stdAddChar (lam i * u) - 1‖ ^ 2 ≤
      B ^ (2 * h) * ‖torusCharacter p lam - 1‖ ^ 2 +
        (2 / (h : ℝ)) * ∑ j, (if lam j = 0 then (0 : ℝ) else 2) := by
  have hSim : 0 ≤ B ^ (2 * h) * ‖torusCharacter p lam - 1‖ ^ 2 := by positivity
  have hCoord : 0 ≤ (2 / (h : ℝ)) * ∑ j, (if lam j = 0 then (0 : ℝ) else 2) := by
    apply mul_nonneg (by positivity)
    apply sum_nonneg
    intro j _
    split_ifs <;> norm_num
  by_cases hi : lam i = 0
  · simpa only [hi, zero_mul, AddChar.map_zero_eq_one, sub_self, norm_zero, zero_pow
      (by omega : 2 ≠ 0)] using add_nonneg hSim hCoord
  have hleft := character_multiplier_four (ZMod.stdAddChar (N := p i)) (lam i * u)
  let s : Finset J := univ.filter (fun j => lam j ≠ 0)
  have his : i ∈ s := by simp [s, hi]
  by_cases hs : s.card < h
  · have hroot := coprime_root_separation s p (fun j => ZMod.stdAddChar (lam j))
      (fun j _ => NeZero.pos (p j))
      (fun _ _ _ _ hij => hcop hij)
      (fun j _ => std_character_pow (p j) (lam j))
      (fun j _ => (ZMod.stdAddChar (N := p j)).norm_apply (lam j)) i his
      (by
        intro heq
        apply hi
        exact ZMod.injective_stdAddChar (heq.trans (AddChar.map_zero_eq_one _).symm))
    have heq : (∏ j ∈ s, ZMod.stdAddChar (lam j)) = torusCharacter p lam := by
      change (∏ j ∈ s, ZMod.stdAddChar (lam j)) = ∏ j, ZMod.stdAddChar (lam j)
      apply prod_subset (filter_subset _ _)
      intro j _ hj
      have hjz : lam j = 0 := by simpa [s] using hj
      simp [hjz]
    rw [heq] at hroot
    have hprod : ((∏ j ∈ s, p j : ℕ) : ℝ) ≤ B ^ h := by
      calc
        _ = ∏ j ∈ s, (p j : ℝ) := by norm_cast
        _ ≤ ∏ _j ∈ s, B := prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun j _ => hpB j)
        _ = B ^ s.card := by rw [prod_const]
        _ ≤ B ^ h := pow_le_pow_right₀ hB hs.le
    have htwo : 2 ≤ B ^ h * ‖torusCharacter p lam - 1‖ :=
      hroot.trans (mul_le_mul_of_nonneg_right hprod (norm_nonneg _))
    have hfour : 4 ≤ B ^ (2 * h) * ‖torusCharacter p lam - 1‖ ^ 2 := by
      have hsq : 4 ≤ (B ^ h * ‖torusCharacter p lam - 1‖) ^ 2 := by nlinarith
      simpa only [mul_pow, ← pow_mul, Nat.mul_comm h 2] using hsq
    linarith
  · have hcard : (h : ℝ) ≤ s.card := by exact_mod_cast Nat.le_of_not_gt hs
    have hsum : (∑ j, (if lam j = 0 then (0 : ℝ) else 2)) = (s.card : ℝ) * 2 := by
      calc
        _ = ∑ _j ∈ s, (2 : ℝ) := by simp only [s, sum_filter, ite_not]
        _ = _ := by simp
    rw [hsum]
    have hfour : 4 ≤ 2 / (h : ℝ) * ((s.card : ℝ) * 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (Nat.cast_pos.mpr hh)]
      linarith
    linarith

end PrimeProduct
end EditFourier

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_FourierAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform averages and quadratic displacement on finite groups
-/

namespace EditFourier
open scoped BigOperators
open Finset

noncomputable def quadraticVariation {R : Type*} [AddCommGroup R] [Fintype R]
    (F : R → ℂ) (l : R) : ℝ :=
  (∑ t, ‖F (t + l) - F t‖ ^ 2) / (Fintype.card R : ℝ)

section Torus
variable {J : Type*} [Fintype J] [DecidableEq J]
variable (p : J → ℕ) [∀ j, NeZero (p j)]

lemma torus_variation_single (F : (∀ j, ZMod (p j)) → ℂ) (i : J) (u : ZMod (p i)) :
    quadraticVariation F (Pi.single i u) =
      ∑ lam, ‖fourier (torusCharacter p) F lam‖ ^ 2 *
        ‖ZMod.stdAddChar (lam i * u) - 1‖ ^ 2 := by
  rw [quadraticVariation, displacement_normalized _ (torusCharacter_primitive p)]
  apply sum_congr rfl
  intro lam _
  rw [mul_comm (Pi.single i u) lam]
  rw [show torusCharacter p (lam * Pi.single i u) = ZMod.stdAddChar (lam i * u) from
    productCharacter_single (fun j => ZMod.stdAddChar (N := p j)) lam i u]

lemma torus_variation_average (F : (∀ j, ZMod (p j)) → ℂ) (i : J) :
    (∑ u : ZMod (p i), quadraticVariation F (Pi.single i u)) /
        (Fintype.card (ZMod (p i)) : ℝ) =
      ∑ lam, ‖fourier (torusCharacter p) F lam‖ ^ 2 *
        (if lam i = 0 then (0 : ℝ) else 2) := by
  simp_rw [torus_variation_single p F i]
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro lam _
  rw [← mul_sum, mul_div_assoc, average_character_multiplier _ (ZMod.isPrimitive_stdAddChar _)]

theorem torus_quadratic_comparison
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (B : ℝ) (hB : 1 ≤ B) (hpB : ∀ j, (p j : ℝ) ≤ B)
    (h : ℕ) (hh : 0 < h) (F : (∀ j, ZMod (p j)) → ℂ) (i : J) (u : ZMod (p i)) :
    quadraticVariation F (Pi.single i u) ≤
      B ^ (2 * h) * quadraticVariation F 1 + (2 / (h : ℝ)) *
        ∑ j, (∑ a : ZMod (p j), quadraticVariation F (Pi.single j a)) /
          (Fintype.card (ZMod (p j)) : ℝ) := by
  rw [torus_variation_single p]
  calc
    _ ≤ ∑ lam, ‖fourier (torusCharacter p) F lam‖ ^ 2 *
        (B ^ (2 * h) * ‖torusCharacter p lam - 1‖ ^ 2 +
          (2 / (h : ℝ)) * ∑ j, (if lam j = 0 then (0 : ℝ) else 2)) := by
      apply sum_le_sum
      intro lam _
      exact mul_le_mul_of_nonneg_left
        (multiplier_comparison p hcop B hB hpB h hh lam i u) (sq_nonneg _)
    _ = _ := by
      simp_rw [torus_variation_average p, quadraticVariation,
        displacement_normalized _ (torusCharacter_primitive p), one_mul,
        mul_add, sum_add_distrib]
      congr 1
      · simp_rw [mul_left_comm _ (B ^ (2 * h)), ← mul_sum]
      · simp_rw [mul_left_comm _ (2 / (h : ℝ)), ← mul_sum, mul_sum]
        rw [sum_comm]

end Torus
end EditFourier

namespace EditAverage
open scoped BigOperators
open Finset

noncomputable def avg {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card X : ℝ)

lemma avg_mono {X : Type*} [Fintype X] {f g : X → ℝ} (hf : ∀ x, f x ≤ g x) :
    avg f ≤ avg g := div_le_div_of_nonneg_right (sum_le_sum (fun x _ => hf x)) (Nat.cast_nonneg _)

lemma avg_const {X : Type*} [Fintype X] [Nonempty X] (c : ℝ) :
    avg (fun _ : X => c) = c := by
  simp [avg, Fintype.card_ne_zero]

lemma avg_add {X : Type*} [Fintype X] (f g : X → ℝ) :
    avg (f + g) = avg f + avg g := by simp only [avg, Pi.add_apply, sum_add_distrib, add_div]

lemma avg_mul {X : Type*} [Fintype X] (c : ℝ) (f : X → ℝ) :
    avg (fun x => c * f x) = c * avg f := by rw [avg, ← mul_sum, mul_div_assoc]; rfl

lemma avg_sum {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y → ℝ) :
    avg (fun x => ∑ y, f x y) = ∑ y, avg (fun x => f x y) := by
  simp only [avg, ← sum_div]
  rw [sum_comm]

lemma avg_comm {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y → ℝ) :
    avg (fun x => avg (f x)) = avg (fun y => avg (fun x => f x y)) := by
  simp only [avg, ← sum_div, div_div]
  rw [sum_comm, mul_comm]

lemma avg_equiv {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (f : Y → ℝ) :
    avg (fun x => f (e x)) = avg f := by
  rw [avg, avg, Fintype.card_congr e, Equiv.sum_comp]

lemma avg_shift {G : Type*} [AddGroup G] [Fintype G] (f : G → ℝ) (g : G) :
    avg (fun z => f (z + g)) = avg f := avg_equiv (Equiv.addRight g) f

end EditAverage

namespace EditFourier
open scoped BigOperators
open Finset EditAverage

section Group
variable {G R : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup R] [Fintype R]

lemma quadraticVariation_eq_avg (F : G → ℂ) (l : G) :
    quadraticVariation F l = avg (fun t => ‖F (t + l) - F t‖ ^ 2) := rfl

lemma quadraticVariation_pullback_average (φ : R →+ G) (F : G → ℂ) (l : R) :
    avg (fun c : G => quadraticVariation (fun t : R => F (c + φ t)) l) =
      quadraticVariation F (φ l) := by
  simp_rw [quadraticVariation_eq_avg, map_add, ← add_assoc]
  rw [avg_comm]
  have hshift (t : R) :
      avg (fun c : G => ‖F (c + φ t + φ l) - F (c + φ t)‖ ^ 2) =
        avg (fun c : G => ‖F (c + φ l) - F c‖ ^ 2) :=
    avg_shift (fun c : G => ‖F (c + φ l) - F c‖ ^ 2) (φ t)
  simp_rw [hshift]
  exact avg_const _

end Group

section TorusGroup
variable {J : Type*} [Fintype J] [DecidableEq J]
variable (p : J → ℕ) [∀ j, NeZero (p j)]
variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem group_quadratic_comparison
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (B : ℝ) (hB : 1 ≤ B) (hpB : ∀ j, (p j : ℝ) ≤ B)
    (h : ℕ) (hh : 0 < h) (φ : (∀ j, ZMod (p j)) →+ G)
    (F : G → ℂ) (i : J) (u : ZMod (p i)) :
    quadraticVariation F (φ (Pi.single i u)) ≤
      B ^ (2 * h) * quadraticVariation F (φ 1) + (2 / (h : ℝ)) *
        ∑ j, avg (fun a : ZMod (p j) => quadraticVariation F (φ (Pi.single j a))) := by
  have hpoint (c : G) := torus_quadratic_comparison p hcop B hB hpB h hh
    (fun t => F (c + φ t)) i u
  have havg := avg_mono hpoint
  change avg (fun c : G => quadraticVariation (fun t => F (c + φ t)) (Pi.single i u)) ≤
    avg (fun c : G => B ^ (2 * h) * quadraticVariation (fun t => F (c + φ t)) 1 +
      (2 / (h : ℝ)) * ∑ j, avg (fun a : ZMod (p j) =>
        quadraticVariation (fun t => F (c + φ t)) (Pi.single j a))) at havg
  rw [show (fun c : G => B ^ (2 * h) * quadraticVariation (fun t => F (c + φ t)) 1 +
      (2 / (h : ℝ)) * ∑ j, avg (fun a : ZMod (p j) =>
        quadraticVariation (fun t => F (c + φ t)) (Pi.single j a))) =
    (fun c => B ^ (2 * h) * quadraticVariation (fun t => F (c + φ t)) 1) +
    (fun c => (2 / (h : ℝ)) * ∑ j, avg (fun a : ZMod (p j) =>
        quadraticVariation (fun t => F (c + φ t)) (Pi.single j a))) from rfl,
    avg_add] at havg
  simp_rw [avg_mul, avg_sum, avg_comm (fun c a =>
    quadraticVariation (fun t => F (c + φ t)) (Pi.single _ a)),
    quadraticVariation_pullback_average] at havg
  exact havg

end TorusGroup
end EditFourier

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_PrimeDisplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Prime-product displacement for absolutely summable maps
-/

namespace EditFourier
open scoped BigOperators
open Finset EditAverage

noncomputable def variation {G E : Type*} [AddCommGroup G] [Fintype G]
    [NormedAddCommGroup E] (H : G → E) (l : G) : ℝ :=
  avg (fun z => ‖H (z + l) - H z‖)

section CutTransport
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma quadraticVariation_cut (A : Finset G) (l : G) :
    quadraticVariation (fun z => (EditCuts.cut A z : ℂ)) l =
      variation (EditCuts.cut A) l := by
  unfold quadraticVariation variation avg
  congr 1
  apply sum_congr rfl
  intro z _
  by_cases hz : z ∈ A <;> by_cases hzl : z + l ∈ A <;>
    simp [EditCuts.cut, hz, hzl]

lemma variation_cut_decomposition (H : G → EditCuts.RealL1) (c : Finset G → ℝ)
    (hd : ∀ x y, ‖H x - H y‖ = ∑ A : Finset G, c A * |EditCuts.cut A x - EditCuts.cut A y|)
    (l : G) : variation H l = ∑ A : Finset G, c A * variation (EditCuts.cut A) l := by
  simp_rw [variation, hd, avg_sum, avg_mul, Real.norm_eq_abs]

end CutTransport

section PrimeProductL1
variable {J : Type*} [Fintype J] [DecidableEq J]
variable (p : J → ℕ) [∀ j, NeZero (p j)]
variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem prime_product_displacement
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (B : ℝ) (hB : 1 ≤ B) (hpB : ∀ j, (p j : ℝ) ≤ B)
    (h : ℕ) (hh : 0 < h) (φ : (∀ j, ZMod (p j)) →+ G)
    (H : G → EditCuts.RealL1) (i : J) (u : ZMod (p i)) :
    variation H (φ (Pi.single i u)) ≤
      B ^ (2 * h) * variation H (φ 1) + (2 / (h : ℝ)) *
        ∑ j, avg (fun a : ZMod (p j) => variation H (φ (Pi.single j a))) := by
  classical
  have hcut (A : Finset G) :
      variation (EditCuts.cut A) (φ (Pi.single i u)) ≤
        B ^ (2 * h) * variation (EditCuts.cut A) (φ 1) + (2 / (h : ℝ)) *
          ∑ j, avg (fun a : ZMod (p j) => variation (EditCuts.cut A) (φ (Pi.single j a))) := by
    simpa only [quadraticVariation_cut] using group_quadratic_comparison p hcop B hB hpB h hh φ
      (fun z => (EditCuts.cut A z : ℂ)) i u
  obtain ⟨c, hc, _, _, hd⟩ := EditCuts.l1_decomposition H
  simp_rw [variation_cut_decomposition H c hd]
  calc
    _ ≤ ∑ A : Finset G, c A *
        (B ^ (2 * h) * variation (EditCuts.cut A) (φ 1) + (2 / (h : ℝ)) *
          ∑ j, avg (fun a : ZMod (p j) => variation (EditCuts.cut A) (φ (Pi.single j a)))) := by
      apply sum_le_sum
      intro A _
      exact mul_le_mul_of_nonneg_left (hcut A) (hc A)
    _ = _ := by
      simp_rw [mul_add, sum_add_distrib, avg_sum, avg_mul]
      congr 1
      · simp_rw [mul_left_comm _ (B ^ (2 * h)), ← mul_sum]
      · simp_rw [mul_left_comm _ (2 / (h : ℝ)), ← mul_sum, mul_sum]
        rw [sum_comm]

end PrimeProductL1
end EditFourier

namespace EditFourier
open scoped BigOperators
open Finset EditAverage

def torsionHom {G : Type*} [AddCommGroup G] (p : ℕ) (v : G) (hv : p • v = 0) :
    ZMod p →+ G :=
  ZMod.lift p ⟨{ toFun := fun z : ℤ => z • v
                 map_zero' := zero_zsmul v
                 map_add' := fun x y => add_zsmul v x y }, by simpa using hv⟩

lemma torsionHom_natCast {G : Type*} [AddCommGroup G] (p : ℕ) (v : G) (hv : p • v = 0)
    (a : ℕ) : torsionHom p v hv (a : ZMod p) = a • v := by
  simpa [torsionHom] using ZMod.lift_coe p
    (⟨{ toFun := fun z : ℤ => z • v
        map_zero' := zero_zsmul v
        map_add' := fun x y => add_zsmul v x y }, by simpa using hv⟩) (a : ℤ)

lemma torsionHom_apply {G : Type*} [AddCommGroup G] (p : ℕ) [NeZero p]
    (v : G) (hv : p • v = 0) (a : ZMod p) : torsionHom p v hv a = a.val • v := by
  rw [← torsionHom_natCast p v hv a.val, ZMod.natCast_zmod_val]

section Vectors
variable {J G : Type*} [Fintype J] [DecidableEq J] [AddCommGroup G]
variable (p : J → ℕ) (v : J → G) (hv : ∀ j, p j • v j = 0)

def vectorHom : (∀ j, ZMod (p j)) →+ G where
  toFun a := ∑ j, torsionHom (p j) (v j) (hv j) (a j)
  map_zero' := by simp
  map_add' a b := by simp [map_add, Finset.sum_add_distrib]

lemma vectorHom_single (i : J) (a : ZMod (p i)) :
    vectorHom p v hv (Pi.single i a) = torsionHom (p i) (v i) (hv i) a := by
  classical
  simp only [vectorHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

omit [DecidableEq J] in
lemma vectorHom_one : vectorHom p v hv 1 = ∑ j, v j := by
  change (∑ j, torsionHom (p j) (v j) (hv j) 1) = _
  apply Finset.sum_congr rfl
  intro j _
  simpa using torsionHom_natCast (p j) (v j) (hv j) 1

variable [Fintype G] [∀ j, NeZero (p j)]

include hv

theorem vector_displacement
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (B : ℝ) (hB : 1 ≤ B) (hpB : ∀ j, (p j : ℝ) ≤ B)
    (h : ℕ) (hh : 0 < h) (H : G → EditCuts.RealL1) (i : J) (u : ZMod (p i)) :
    variation H (u.val • v i) ≤ B ^ (2 * h) * variation H (∑ j, v j) +
      (2 / (h : ℝ)) * ∑ j, avg (fun a : ZMod (p j) => variation H (a.val • v j)) := by
  simpa only [vectorHom_single, vectorHom_one, torsionHom_apply] using
    prime_product_displacement p hcop B hB hpB h hh (vectorHom p v hv) H i u

theorem prime_vector_displacement (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (P : ℝ) (hP : 1 ≤ 2 * P) (hpP : ∀ j, (p j : ℝ) ≤ 2 * P)
    (h : ℕ) (hh : 0 < h) (H : G → EditCuts.RealL1) (i : J) (u : ZMod (p i)) :
    variation H (u.val • v i) ≤ (2 * P) ^ (2 * h) * variation H (∑ j, v j) +
      (2 / (h : ℝ)) * ∑ j, avg (fun a : ZMod (p j) => variation H (a.val • v j)) := by
  apply vector_displacement p v hv (fun i j hij => ?_) (2 * P) hP hpP h hh H i u
  exact (hp i).coprime_iff_not_dvd.mpr (fun hd =>
    hij (hinj ((Nat.dvd_prime (hp j)).mp hd |>.resolve_left (hp i).ne_one)))

end Vectors
end EditFourier

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_DirectSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weighted direct sums and normalized slice maps
-/

namespace EditL1
open scoped BigOperators

abbrev L1 := lp (fun _ : ℕ => ℝ) 1
abbrev L1On (I : Type*) := lp (fun _ : I => ℝ) 1

lemma norm_eq_tsum {I : Type*} (f : L1On I) : ‖f‖ = ∑' i, |f i| := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal) f

lemma summable_abs {I : Type*} (f : L1On I) : Summable (fun i => |f i|) := by
  simpa using (lp.memℓp f).summable (by norm_num : 0 < (1 : ENNReal).toReal)

noncomputable def reindex {I J : Type*} (e : I ≃ J) (f : L1On I) : L1On J :=
  ⟨fun j => f (e.symm j), memℓp_gen (by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs, Function.comp_def] using!
      (e.symm.summable_iff).mpr (summable_abs f))⟩

lemma reindex_apply {I J : Type*} (e : I ≃ J) (f : L1On I) (j : J) :
    reindex e f j = f (e.symm j) := rfl

lemma reindex_norm {I J : Type*} (e : I ≃ J) (f : L1On I) :
    ‖reindex e f‖ = ‖f‖ := by
  simp_rw [norm_eq_tsum, reindex_apply]
  exact e.symm.tsum_eq (fun i => |f i|)

lemma reindex_sub {I J : Type*} (e : I ≃ J) (f g : L1On I) :
    reindex e (f - g) = reindex e f - reindex e g := by
  ext j
  rfl

section FiniteSum
variable {I : Type*} [Fintype I]

lemma family_summable (f : I → L1) : Summable (fun a : I × ℕ => |f a.1 a.2|) :=
  (summable_prod_of_nonneg (fun _ => abs_nonneg _)).mpr
    ⟨fun i => summable_abs (f i), (hasSum_fintype _).summable⟩

noncomputable def familyLp (f : I → L1) : L1On (I × ℕ) :=
  ⟨fun a => f a.1 a.2, memℓp_gen (by simpa using family_summable f)⟩

lemma familyLp_norm (f : I → L1) : ‖familyLp f‖ = ∑ i, ‖f i‖ := by
  rw [norm_eq_tsum]
  change (∑' a : I × ℕ, |f a.1 a.2|) = _
  rw [(family_summable f).tsum_prod, tsum_fintype]
  exact Finset.sum_congr rfl (fun i _ => (norm_eq_tsum (f i)).symm)

lemma familyLp_sub (f g : I → L1) : familyLp (f - g) = familyLp f - familyLp g := by
  ext ⟨i, n⟩
  rfl

variable [Nonempty I]

noncomputable def indexEquiv : (I × ℕ) ≃ ℕ := Classical.choice inferInstance

noncomputable def pack (f : I → L1) : L1 := reindex indexEquiv (familyLp f)

lemma pack_norm (f : I → L1) : ‖pack f‖ = ∑ i, ‖f i‖ := by
  rw [pack, reindex_norm, familyLp_norm]

lemma pack_sub (f g : I → L1) : pack (f - g) = pack f - pack g := by
  rw [pack, familyLp_sub, reindex_sub]
  rfl

lemma pack_distance (f g : I → L1) : ‖pack f - pack g‖ = ∑ i, ‖f i - g i‖ := by
  rw [← pack_sub, pack_norm]
  rfl

lemma weighted_pack_distance (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (f g : I → L1) :
    ‖pack (fun i => w i • f i) - pack (fun i => w i • g i)‖ =
      ∑ i, w i * ‖f i - g i‖ := by
  rw [pack_distance]
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i)]

end FiniteSum
end EditL1

namespace EditAverage
lemma avg_prod {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y → ℝ) :
    avg (fun z : X × Y => f z.1 z.2) = avg (fun x => avg (f x)) := by
  simp only [avg, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type, ← Finset.sum_div,
    div_div]
  rw [mul_comm]
end EditAverage

namespace EditSlices
open scoped BigOperators
open EditAverage EditFourier

variable {J : Type*} [Fintype J] [DecidableEq J]
variable (G : J → Type*) [∀ j, AddCommGroup (G j)] [∀ j, Fintype (G j)]

omit [Fintype J] [∀ j, Fintype (G j)] in
lemma split_add_single (i : J) (x u : G i) (y : ∀ j : {j // j ≠ i}, G j) :
    (Equiv.piSplitAt i G).symm (x + u, y) =
      (Equiv.piSplitAt i G).symm (x, y) + Pi.single i u := by
  ext j
  by_cases h : j = i
  · subst j
    simp [Equiv.piSplitAt]
  · simp [Equiv.piSplitAt, h]

noncomputable def slice (H : (∀ j, G j) → EditL1.L1) (i : J) (ω : ℝ) : G i → EditL1.L1 :=
  fun x => EditL1.pack (fun y : (∀ j : {j // j ≠ i}, G j) =>
    (1 / (ω * Fintype.card (∀ j : {j // j ≠ i}, G j))) •
      H ((Equiv.piSplitAt i G).symm (x,y)))

lemma variation_slice (H : (∀ j, G j) → EditL1.L1) (i : J) (ω : ℝ) (hω : 0 < ω)
    (u : G i) : variation (slice G H i ω) u = variation H (Pi.single i u) / ω := by
  let Y := ∀ j : {j // j ≠ i}, G j
  let E := Equiv.piSplitAt i G
  have hY : 0 < (Fintype.card Y : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hweight : 0 ≤ 1 / (ω * (Fintype.card Y : ℝ)) := by positivity
  have hd (x : G i) :
      ‖slice G H i ω (x + u) - slice G H i ω x‖ =
        (1 / ω) * avg (fun y : Y => ‖H (E.symm (x,y) + Pi.single i u) - H (E.symm (x,y))‖) := by
    rw [slice, slice, EditL1.weighted_pack_distance (fun _ => _) (fun _ => hweight)]
    simp_rw [split_add_single]
    rw [← Finset.mul_sum, avg]
    dsimp [E, Y]
    ring
  have he : variation H (Pi.single i u) =
      avg (fun x : G i => avg (fun y : Y =>
        ‖H (E.symm (x,y) + Pi.single i u) - H (E.symm (x,y))‖)) := by
    rw [← avg_prod]
    exact (avg_equiv E.symm (fun z => ‖H (z + Pi.single i u) - H z‖)).symm
  change avg (fun x => ‖slice G H i ω (x + u) - slice G H i ω x‖) = _
  simp_rw [hd]
  rw [avg_mul, ← he]
  ring

end EditSlices

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_CutRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Realization of all finite-cut distances by one summable vector map
-/

namespace EditCutModel
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

noncomputable def Model.vector {X : Type*} (M : Model X) (x : X) : EditL1.L1 :=
  EditL1.pack (fun j : Option M.Index => match j with
    | none => 0
    | some i => lp.single (E := fun _ : ℕ => ℝ) 1 0 (if M.cut i x then M.weight i else 0))

end EditCutModel

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_PrimePeriods
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Prime divisibility and distinct phase periods
-/

namespace EditPhase
open scoped BigOperators

lemma few_divisors {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) (hp : Pairwise (fun i j => (p i).Coprime (p j)))
    {P r n : ℕ} (hP : 1 ≤ P) (hpP : ∀ j, P ≤ p j)
    (hn : 0 < n) (hnr : n < P ^ r) :
    (Finset.univ.filter (fun j => p j ∣ n)).card < r := by
  let S := Finset.univ.filter (fun j => p j ∣ n)
  have hdiv : (∏ j ∈ S, p j) ∣ n := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro i hi j hj hij
      exact Nat.coprime_iff_isRelPrime.mp (hp hij)
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
  have hlow : P ^ S.card ≤ ∏ j ∈ S, p j :=
    Finset.pow_card_le_prod S p P (fun j _ => hpP j)
  have hle : P ^ S.card ≤ n := hlow.trans (Nat.le_of_dvd hn hdiv)
  by_contra h
  have hcard : r ≤ S.card := Nat.le_of_not_gt h
  have hpow := pow_le_pow_right' hP hcard
  exact (not_lt_of_ge (hpow.trans hle)) hnr

lemma few_prime_divisors {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    {P r n : ℕ} (hP : 1 ≤ P) (hpP : ∀ j, P ≤ p j)
    (hn : 0 < n) (hnr : n < P ^ r) :
    (Finset.univ.filter (fun j => p j ∣ n)).card < r := by
  apply few_divisors p (fun i j hij => ?_) hP hpP hn hnr
  exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hinj h))

lemma many_nondivisors_except {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    {P r n : ℕ} (hP : 1 ≤ P) (hpP : ∀ j, P ≤ p j)
    (hn : 0 < n) (hnr : n < P ^ r) (i : J) :
    Fintype.card J - r ≤
      (Finset.univ.filter (fun j => j ≠ i ∧ ¬p j ∣ n)).card := by
  have hbad := few_prime_divisors p hp hinj hP hpP hn hnr
  have hsum : (Finset.univ.filter (fun j : J => p j ∣ n)).card +
      (Finset.univ.filter (fun j : J => ¬p j ∣ n)).card = Fintype.card J := by
    exact Finset.card_filter_add_card_filter_not _
  have hins : (Finset.univ.filter (fun j : J => ¬p j ∣ n)) ⊆
      insert i (Finset.univ.filter (fun j => j ≠ i ∧ ¬p j ∣ n)) := by
    intro j hj
    by_cases hji : j = i
    · simp [hji]
    · simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨hji, (Finset.mem_filter.mp hj).2⟩
  have hcard := Finset.card_le_card hins
  have hle := Finset.card_insert_le i (Finset.univ.filter (fun j => j ≠ i ∧ ¬p j ∣ n))
  omega

lemma many_nonzero_phases {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    {P r : ℕ} (hP : 1 ≤ P) (hpP : ∀ j, P ≤ p j)
    {q : ℤ} (hq : q ≠ 0) (hqr : q.natAbs < P ^ r) (i : J) :
    Fintype.card J - r ≤
      (Finset.univ.filter (fun j => j ≠ i ∧ ¬(p j : ℤ) ∣ q)).card := by
  simpa only [Int.natCast_dvd] using
    many_nondivisors_except p hp hinj hP hpP (Int.natAbs_pos.mpr hq) hqr i

end EditPhase

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_Families
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite word families with averaged displacement control
-/

namespace EditFamily
open scoped BigOperators
open EditDistortion EditAverage EditFourier

structure Family (p n A : ℕ) (α Q : ℝ) where
  State : Type
  [group : AddCommGroup State]
  [finite : Fintype State]
  v : State
  annihilate : p • v = 0
  word : State → Fin n → Fin A
  steps : List (State × ℝ)
  positive : ∀ e r, (e,r) ∈ steps → 0 < r
  cheap : ∀ e r, (e,r) ∈ steps → ∀ z,
    (indel (List.ofFn (word z)) (List.ofFn (word (z + e))) : ℝ) ≤ n * r
  far : ∀ z u, 0 < u → u < p →
    (n : ℝ) * α ≤ (indel (List.ofFn (word z)) (List.ofFn (word (z + u • v))) : ℝ)
  control : ∀ H : State → L1,
    (∀ e r, (e,r) ∈ steps → variation H e ≤ r) →
    ∀ u, 0 < u → u < p → variation H (u • v) ≤ Q

attribute [instance] Family.group Family.finite

lemma indel_singletons_le {A : Type*} (a b : A) : indel [a] [b] ≤ 2 := by
  exact cost_le ((Script.to_nil [a]).trans (Script.to_nil [b]).symm)

noncomputable def base {p A : ℕ} (hp : p.Prime) (hA : p ≤ A) : Family p 1 A 1 2 := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  let W : ZMod p → Fin 1 → Fin A := fun z _ => ⟨z.val, lt_of_lt_of_le (ZMod.val_lt z) hA⟩
  let S : List (ZMod p × ℝ) :=
    ((Finset.univ.filter (fun e : ZMod p => e ≠ 0)).toList).map (fun e => (e,2))
  have memS (e : ZMod p) (r : ℝ) : (e,r) ∈ S ↔ e ≠ 0 ∧ r = 2 := by
    simp [S, eq_comm]
  have phase (u : ℕ) (hu : 0 < u) (hup : u < p) : u • (1 : ZMod p) ≠ 0 := by
    simp only [nsmul_eq_mul, mul_one, Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hu hup
  refine { State := ZMod p
           group := inferInstance
           finite := inferInstance
           v := 1
           annihilate := ?_
           word := W
           steps := S
           positive := ?_
           cheap := ?_
           far := ?_
           control := ?_ }
  · simp [nsmul_eq_mul]
  · intro e r hr
    rw [(memS e r).mp hr |>.2]
    norm_num
  · intro e r hr z
    rw [(memS e r).mp hr |>.2]
    simpa [List.ofFn_succ, W] using
      (show (indel [W z 0] [W (z+e) 0] : ℝ) ≤ 2 from by exact_mod_cast indel_singletons_le _ _)
  · intro z u hu hup
    have hne : List.ofFn (W z) ≠ List.ofFn (W (z + u • (1 : ZMod p))) := by
      intro he
      have hx : W z 0 = W (z + u • (1 : ZMod p)) 0 := by
        simpa [List.ofFn_succ] using he
      have hz : z = z + u • (1 : ZMod p) := by
        apply ZMod.val_injective
        exact congrArg Fin.val hx
      exact phase u hu hup (add_eq_left.mp hz.symm)
    have hpos : 0 < indel (List.ofFn (W z)) (List.ofFn (W (z + u • (1 : ZMod p)))) :=
      Nat.pos_of_ne_zero (fun hh => hne ((cost_eq_zero_iff (s := false)).mp hh))
    have hlow : (1 : ℝ) ≤ indel (List.ofFn (W z)) (List.ofFn (W (z + u • (1 : ZMod p)))) := by
      exact_mod_cast hpos
    simpa using hlow
  · intro H hH u hu hup
    exact hH _ 2 ((memS _ _).mpr ⟨phase u hu hup, rfl⟩)

end EditFamily

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_Slots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Position-tagged concatenation and repeated slots
-/

namespace EditSlots
open scoped BigOperators

variable {I A : Type*} [DecidableEq I]

def project (i : I) (x : I × A) : Option A := if i = x.1 then some x.2 else none

lemma project_map (i j : I) (x : List A) :
    (x.map (Prod.mk j)).filterMap (project i) = if i = j then x else [] := by
  by_cases h : i = j <;> simp [List.filterMap_map, project, h, Function.comp_def]

def tagged (l : List I) (P : I → List A) : List (I × A) :=
  l.flatMap (fun i => (P i).map (Prod.mk i))

lemma project_tagged (l : List I) (hl : l.Nodup) (P : I → List A) (i : I) :
    (tagged l P).filterMap (project i) = if i ∈ l then P i else [] := by
  induction l with
  | nil => simp [tagged]
  | cons j l ih =>
    obtain ⟨hjl, hl⟩ := List.nodup_cons.mp hl
    simp only [tagged, List.flatMap_cons, List.filterMap_append, project_map]
    change (if i = j then P j else []) ++ (tagged l P).filterMap (project i) = _
    rw [ih hl]
    by_cases h : i = j
    · subst i
      simp [hjl]
    · simp [h]

lemma project_length_partition [Fintype I] (z : List (I × A)) :
    ∑ i, (z.filterMap (project i)).length = z.length := by
  induction z with
  | nil => simp
  | cons a z ih =>
    have hh (i : I) : ((a :: z).filterMap (project i)).length =
        (z.filterMap (project i)).length + if i = a.1 then 1 else 0 := by
      by_cases h : i = a.1 <;> simp [project, h]
    simp_rw [hh]
    rw [Finset.sum_add_distrib, ih]
    simp

omit [DecidableEq I] in
lemma tagged_length (l : List I) (P : I → List A) :
    (tagged l P).length = (l.map (fun i => (P i).length)).sum := by
  induction l with
  | nil => simp [tagged]
  | cons a l ih => simp_all [tagged]

theorem sum_indel_le_tagged [Fintype I] (l : List I) (hl : l.Nodup)
    (hfull : ∀ i : I, i ∈ l) (P Q : I → List A) :
    (∑ i, (EditDistortion.indel (P i) (Q i) : ℝ)) ≤
      (EditDistortion.indel (tagged l P) (tagged l Q) : ℝ) := by
  classical
  obtain ⟨z, hzP, hzQ, hz⟩ := EditDistortion.indel_matching (tagged l P) (tagged l Q)
  have hsubP : ∀ i, (z.filterMap (project i)).Sublist (P i) := by
    intro i
    simpa only [project_tagged l hl P i, ite_eq_left (hfull i)] using hzP.filterMap (project i)
  have hsubQ : ∀ i, (z.filterMap (project i)).Sublist (Q i) := by
    intro i
    simpa only [project_tagged l hl Q i, ite_eq_left (hfull i)] using hzQ.filterMap (project i)
  have hp (i : I) : (EditDistortion.indel (P i) (Q i) : ℝ) ≤
      ((P i).length : ℝ) + (Q i).length - 2 * (z.filterMap (project i)).length := by
    have hh := EditDistortion.indel_le_matching_loss (hsubP i) (hsubQ i)
    have h₁ := (hsubP i).length_le
    have h₂ := (hsubQ i).length_le
    have hh' : (EditDistortion.indel (P i) (Q i) : ℝ) ≤
        (((P i).length + (Q i).length - 2 * (z.filterMap (project i)).length : ℕ) : ℝ) := by
      exact_mod_cast hh
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hh'
    exact hh'
  have hlen (R : I → List A) : (tagged l R).length = ∑ i, (R i).length := by
    have hp := project_length_partition (tagged l R)
    simpa only [project_tagged l hl R, ite_eq_left (hfull _)] using hp.symm
  have hpart : (∑ i, ((z.filterMap (project i)).length : ℝ)) = z.length := by
    exact_mod_cast project_length_partition z
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hpart] at hsum
  have hz₁ := hzP.length_le
  have hz₂ := hzQ.length_le
  rw [hz, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    hlen P, hlen Q, Nat.cast_sum, Nat.cast_sum]
  exact hsum

end EditSlots

namespace EditSlots
open scoped BigOperators

lemma cost_tagged_le {I A : Type*} (l : List I) (P Q : I → List A) (s : Bool) :
    EditDistortion.cost s (tagged l P) (tagged l Q) ≤
      (l.map (fun i => EditDistortion.cost s (P i) (Q i))).sum := by
  induction l with
  | nil => exact le_of_eq (EditDistortion.cost_refl [])
  | cons i l ih =>
      have ha := EditDistortion.cost_append_le (s := s)
        ((P i).map (Prod.mk i)) ((Q i).map (Prod.mk i)) (tagged l P) (tagged l Q)
      have hm := EditDistortion.cost_map_le (s := s) (Prod.mk i) (P i) (Q i)
      exact ha.trans (by simpa only [List.map_cons, List.sum_cons] using Nat.add_le_add hm ih)

def fixedFn {A : Type*} {n : ℕ} (l : List A) (h : l.length = n) : Fin n → A :=
  fun i => l.get (Fin.cast h.symm i)

@[simp] lemma ofFn_fixedFn {A : Type*} {n : ℕ} (l : List A) (h : l.length = n) :
    List.ofFn (fixedFn l h) = l := by
  subst n
  exact List.ofFn_get l

section Repeated
variable {J : Type*} [Fintype J] [DecidableEq J] (i : J)

abbrev Slots := Fin (Fintype.card J) ⊕ {j : J // j ≠ i}

def component : Slots i → J
  | Sum.inl _ => i
  | Sum.inr j => j.val

lemma slots_card : Fintype.card (Slots i) = 2 * Fintype.card J - 1 := by
  have hb : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨i⟩
  simp only [Slots, Fintype.card_sum, Fintype.card_fin, Fintype.card_subtype_compl,
    Fintype.card_unique]
  omega

noncomputable def enumeration : List (Slots i) :=
  List.ofFn (Fintype.equivFin (Slots i)).symm

lemma enumeration_nodup : (enumeration i).Nodup :=
  List.nodup_ofFn_ofInjective (Fintype.equivFin (Slots i)).symm.injective

lemma enumeration_full (r : Slots i) : r ∈ enumeration i := by
  simp only [enumeration, List.mem_ofFn]
  exact ⟨(Fintype.equivFin (Slots i)) r, (Fintype.equivFin (Slots i)).symm_apply_apply r⟩

lemma sum_slots (f : J → ℝ) :
    (∑ r : Slots i, f (component i r)) =
      (Fintype.card J : ℝ) * f i + ∑ j : {j : J // j ≠ i}, f j := by
  simp [Fintype.sum_sum_type, component]

def multiplicity (j : J) : ℕ := if j = i then Fintype.card J else 1

lemma sum_slots_delta (j : J) (a : ℝ) :
    (∑ r : Slots i, if component i r = j then a else 0) = multiplicity i j * a := by
  rw [sum_slots i (fun k => if k = j then a else 0)]
  by_cases h : j = i
  · subst j
    have hz : (∑ x : {j : J // j ≠ i}, if x.val = i then a else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      simp [x.property]
    simp [hz, multiplicity]
  · have hs : (∑ x : {j : J // j ≠ i}, if x.val = j then a else 0) = a := by
      rw [Finset.sum_eq_single ⟨j,h⟩]
      · simp
      · intro x _ hx
        have hx' : x.val ≠ j := fun he => hx (Subtype.ext he)
        simp [hx']
      · simp
    simp [hs, Ne.symm h, multiplicity, h]

lemma sum_multiplicity : (∑ j : J, (multiplicity i j : ℝ)) = 2 * Fintype.card J - 1 := by
  have he (j : J) : (multiplicity i j : ℝ) =
      1 + if j = i then (Fintype.card J : ℝ) - 1 else 0 := by
    by_cases h : j = i <;> simp [multiplicity, h]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

end Repeated
end EditSlots

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_RecursiveControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Averaged displacement control for recursive word families
-/

namespace EditFamily
open scoped BigOperators
open EditDistortion EditAverage EditFourier EditSlots

section InductiveControl
variable {J : Type} [Fintype J] [DecidableEq J] (i : J)

noncomputable def weight (j : J) : ℝ := (EditSlots.multiplicity i j : ℝ) / (2 * (2 * Fintype.card J - 1))

lemma weight_pos (j : J) : 0 < weight i j := by
  have hb : 0 < (Fintype.card J : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  have hb' : (1 : ℝ) ≤ Fintype.card J := by
    exact_mod_cast (show 1 ≤ Fintype.card J by exact Fintype.card_pos_iff.mpr ⟨i⟩)
  have hc : 0 < (EditSlots.multiplicity i j : ℝ) := by
    by_cases hj : j = i <;> simp [EditSlots.multiplicity, hj, hb]
  exact div_pos hc (by linarith)

lemma sum_weight : (∑ j : J, weight i j) = 1 / 2 := by
  have hb : (1 : ℝ) ≤ Fintype.card J := by
    exact_mod_cast (show 1 ≤ Fintype.card J by exact Fintype.card_pos_iff.mpr ⟨i⟩)
  simp only [weight, ← Finset.sum_div, sum_multiplicity]
  field_simp [show (2 * (Fintype.card J : ℝ) - 1) ≠ 0 by linarith]

variable {p : J → ℕ} {m A : ℕ} {α Q : ℝ}
variable (F : ∀ j, Family (p j) m A α Q)

abbrev ProductState := ∀ j, (F j).State

def lift (j : J) (e : (F j).State) : ProductState F := Pi.single j e

def allPhase : ProductState F := fun j => (F j).v

lemma sum_lift_vectors : (∑ j, lift F j (F j).v) = allPhase F := by
  ext j
  simp [lift, allPhase]

omit [Fintype J] in
lemma lift_nsmul (j : J) (u : ℕ) (e : (F j).State) :
    lift F j (u • e) = u • lift F j e := by
  ext k
  by_cases hk : k = j
  · subst k; simp [lift]
  · simp [lift, hk]

lemma variation_zero (H : ProductState F → L1) : variation H 0 = 0 := by
  simp [variation, avg]

lemma component_control (hQ : 0 ≤ Q) (H : ProductState F → L1)
    (hh : ∀ j e r, (e,r) ∈ (F j).steps →
      variation H (lift F j e) ≤ weight i j * r)
    (j : J) (a : ℕ) (ha : a < p j) :
    variation H (a • lift F j (F j).v) ≤ weight i j * Q := by
  by_cases ha0 : a = 0
  · simp only [ha0, zero_nsmul, variation_zero]
    exact mul_nonneg (weight_pos i j).le hQ
  let T := EditSlices.slice (fun j => (F j).State) H j (weight i j)
  have hT : ∀ e r, (e,r) ∈ (F j).steps → variation T e ≤ r := by
    intro e r her
    rw [EditSlices.variation_slice _ H j _ (weight_pos i j)]
    apply (div_le_iff₀ (weight_pos i j)).mpr
    simpa only [lift, mul_comm] using hh j e r her
  have hC := (F j).control T hT a (Nat.pos_of_ne_zero ha0) ha
  rw [EditSlices.variation_slice _ H j _ (weight_pos i j)] at hC
  have hC' := (div_le_iff₀ (weight_pos i j)).mp hC
  change variation H (lift F j (a • (F j).v)) ≤ Q * weight i j at hC'
  rw [lift_nsmul] at hC'
  simpa only [mul_comm] using hC'

theorem successor_control
    (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (P : ℝ) (hP : 1 ≤ 2 * P) (hpP : ∀ j, (p j : ℝ) ≤ 2 * P)
    (h : ℕ) (hh : 0 < h) (L : ℕ) (hQ : 0 ≤ Q)
    (H : ProductState F → L1) (hτ : variation H (allPhase F) ≤ 2 / L)
    (hlift : ∀ j e r, (e,r) ∈ (F j).steps →
      variation H (lift F j e) ≤ weight i j * r)
    (u : ℕ) (hu : u < p i) :
    variation H (u • lift F i (F i).v) ≤
      2 * (2 * P) ^ (2 * h) / L + Q / h := by
  let (j : J) : NeZero (p j) := ⟨(hp j).ne_zero⟩
  have hv (j : J) : p j • lift F j (F j).v = 0 := by
    rw [← lift_nsmul, (F j).annihilate]
    simp [lift]
  have hc := prime_vector_displacement p (fun j => lift F j (F j).v) hv hp hinj
    P hP hpP h hh H i (u : ZMod (p i))
  rw [ZMod.val_natCast_of_lt hu, sum_lift_vectors] at hc
  have hb (j : J) : avg (fun a : ZMod (p j) => variation H (a.val • lift F j (F j).v)) ≤
      weight i j * Q := by
    rw [← avg_const (X := ZMod (p j)) (weight i j * Q)]
    exact avg_mono (fun a => component_control i F hQ H hlift j a.val (ZMod.val_lt a))
  calc
    _ ≤ (2 * P) ^ (2 * h) * variation H (allPhase F) +
        (2 / (h : ℝ)) * ∑ j, avg (fun a : ZMod (p j) =>
          variation H (a.val • lift F j (F j).v)) := hc
    _ ≤ (2 * P) ^ (2 * h) * (2 / (L : ℝ)) +
        (2 / (h : ℝ)) * ∑ j, weight i j * Q := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hτ (pow_nonneg (by linarith) _)
      · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hb j)) (by positivity)
    _ = _ := by rw [← Finset.sum_mul, sum_weight]; ring

end InductiveControl
end EditFamily

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_RowConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Row concatenation and cyclic phase shifts
-/

namespace EditRows

lemma rowValue_offset {A : Type*} {L B : ℕ} (hB : 0 < B)
    (P : Fin L → Fin B → A) (i : Fin L) (j : Fin (2 * B)) :
    rowValue P ⟨2 * B * i.val + j.val, by nlinarith [i.isLt, j.isLt]⟩ =
      if h : j.val < B then some (P i ⟨j.val, h⟩) else none := by
  have hdiv : (2 * B * i.val + j.val) / (2 * B) = i.val := by
    simp [Nat.mul_add_div (by omega : 0 < 2 * B), Nat.div_eq_of_lt j.isLt]
  have hmod : (2 * B * i.val + j.val) % (2 * B) = j.val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  unfold rowValue
  simp only [hmod, hdiv]

lemma chunk_ofFn {A : Type*} {B : ℕ} (P : Fin B → A) :
    (List.ofFn (fun j : Fin (2 * B) =>
      if h : j.val < B then some (P ⟨j.val, h⟩) else none)) =
      (List.ofFn P).map some ++ List.replicate B none := by
  rw [show 2 * B = B + B by omega]
  rw [List.ofFn_add]
  congr 1
  · rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    simp [i.isLt]
  · have he : (fun i : Fin B => if h : (Fin.natAdd B i).val < B then
        some (P ⟨(Fin.natAdd B i).val, h⟩) else none) = (fun _ => (none : Option A)) := by
      funext i
      simp
    simp only [he, List.ofFn_const]

lemma rowWord_flatten {A : Type*} {L B : ℕ} (hB : 0 < B) (P : Fin L → Fin B → A) :
    rowWord P = (List.ofFn (fun i : Fin L =>
      (List.ofFn (P i)).map some ++ List.replicate B none)).flatten := by
  rw [rowWord, List.ofFn_mul']
  congr 1
  apply congrArg List.ofFn
  funext i
  simp_rw [rowValue_offset hB]
  exact chunk_ofFn (P i)

lemma indel_flatten_le {A : Type*} (x y : List (List A)) (hlen : x.length = y.length) :
    EditDistortion.indel x.flatten y.flatten ≤
      ((x.zip y).map (fun z => EditDistortion.indel z.1 z.2)).sum := by
  induction x generalizing y with
  | nil =>
      have hy : y = [] := List.length_eq_zero_iff.mp hlen.symm
      subst y
      exact le_of_eq (EditDistortion.cost_refl (s := false) [])
  | cons a x ih =>
      cases y with
      | nil => simp at hlen
      | cons b y =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          have hh := EditDistortion.cost_append_le (s := false) a b x.flatten y.flatten
          exact hh.trans (by simpa only [List.zip_cons_cons, List.map_cons, List.sum_cons] using! Nat.add_le_add_left (ih y hlen) (EditDistortion.indel a b))

lemma zip_ofFn {A C : Type*} {n : ℕ} (f : Fin n → A) (g : Fin n → C) :
    (List.ofFn f).zip (List.ofFn g) = List.ofFn (fun i => (f i, g i)) := by
  simp only [List.ofFn_eq_map, List.zip_map']

lemma indel_rowWord_le {A : Type*} {L B : ℕ} (hB : 0 < B)
    (P Q : Fin L → Fin B → A) :
    EditDistortion.indel (rowWord P) (rowWord Q) ≤
      ∑ i, EditDistortion.indel (List.ofFn (P i)) (List.ofFn (Q i)) := by
  classical
  rw [rowWord_flatten hB P, rowWord_flatten hB Q]
  have h := indel_flatten_le
    (List.ofFn (fun i : Fin L => (List.ofFn (P i)).map some ++ List.replicate B none))
    (List.ofFn (fun i : Fin L => (List.ofFn (Q i)).map some ++ List.replicate B none)) (by simp)
  apply h.trans
  rw [zip_ofFn, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_le_sum
  intro i _
  have ha := EditDistortion.cost_append_le (s := false)
    ((List.ofFn (P i)).map some) ((List.ofFn (Q i)).map some)
    (List.replicate B none) (List.replicate B none)
  have hb := EditDistortion.cost_map_le (s := false) some (List.ofFn (P i)) (List.ofFn (Q i))
  simpa only [EditDistortion.cost_refl, Nat.add_zero] using! ha.trans (Nat.add_le_add_right hb _)

end EditRows

namespace EditRows

lemma indel_shift_flatten {A : Type*} {n R : ℕ} (P Q : Fin (n+1) → List A)
    (hfront : (P 0).length ≤ R) (hback : (Q (Fin.last n)).length ≤ R)
    (halign : ∀ i : Fin n, Q i.castSucc = P i.succ) :
    EditDistortion.indel (List.ofFn P).flatten (List.ofFn Q).flatten ≤ 2 * R := by
  have hp : (List.ofFn P).flatten = P 0 ++ (List.ofFn (fun i : Fin n => P i.succ)).flatten := by
    rw [List.ofFn_succ, List.flatten_cons]
  have hq : (List.ofFn Q).flatten =
      (List.ofFn (fun i : Fin n => Q i.castSucc)).flatten ++ Q (Fin.last n) := by
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simp
  rw [hp, hq]
  simp_rw [halign]
  let m := (List.ofFn (fun i : Fin n => P i.succ)).flatten
  have h₁ : EditDistortion.Script false (P 0).length (P 0 ++ m) m := by
    simpa using (EditDistortion.Script.to_nil (s := false) (P 0)).append_right m
  have h₂ : EditDistortion.Script false (Q (Fin.last n)).length m (m ++ Q (Fin.last n)) := by
    simpa using (EditDistortion.Script.to_nil (s := false) (Q (Fin.last n))).symm.append_left m
  exact (EditDistortion.cost_le (h₁.trans h₂)).trans (by omega)

lemma indel_row_shift {A : Type*} {L B : ℕ} (hL : 0 < L) (hB : 0 < B)
    (P Q : Fin L → Fin B → A)
    (halign : ∀ (i j : Fin L), j.val = i.val + 1 → Q i = P j) :
    EditDistortion.indel (rowWord P) (rowWord Q) ≤ 4 * B := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL)
  rw [rowWord_flatten hB P, rowWord_flatten hB Q]
  have h := indel_shift_flatten (R := 2 * B)
    (fun i => (List.ofFn (P i)).map some ++ List.replicate B none)
    (fun i => (List.ofFn (Q i)).map some ++ List.replicate B none)
    (by simp; omega) (by simp; omega) (fun i => by rw [halign i.castSucc i.succ (by simp)])
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  omega

end EditRows

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_RecursiveWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recursive payloads, markers, symbol codes, and word separation
-/

namespace EditFamily
open scoped BigOperators
open EditDistortion EditAverage EditFourier EditSlots

lemma torsionHom_intCast {G : Type*} [AddCommGroup G] (p : ℕ) (v : G) (hv : p • v = 0)
    (a : ℤ) : torsionHom p v hv (a : ZMod p) = a • v := by
  simp [torsionHom]

lemma Family.far_int {p m A : ℕ} {α Q : ℝ} (F : Family p m A α Q)
    (hp : 0 < p) (z : F.State) (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) :
    (m : ℝ) * α ≤ (indel (List.ofFn (F.word z)) (List.ofFn (F.word (z + a • F.v))) : ℝ) := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  let x : ZMod p := a
  have hx : x ≠ 0 := fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  have hv : x.val • F.v = a • F.v := by
    rw [← torsionHom_apply p F.v F.annihilate x]
    exact torsionHom_intCast p F.v F.annihilate a
  rw [← hv]
  exact F.far z x.val (Nat.pos_of_ne_zero (fun h => hx ((ZMod.val_eq_zero x).mp h))) (ZMod.val_lt x)

section Words
variable {J : Type} [Fintype J] [DecidableEq J] (i : J)
variable {p : J → ℕ} {m A : ℕ} {α Q : ℝ}
variable (F : ∀ j, Family (p j) m A α Q)

noncomputable def payloadList (z : ProductState F) (row : ℕ) : List (Slots i × Fin A) :=
  tagged (enumeration i) (fun r => List.ofFn ((F (component i r)).word
    (z (component i r) + row • (F (component i r)).v)))

lemma payload_length (z : ProductState F) (row : ℕ) :
    (payloadList i F z row).length = (2 * Fintype.card J - 1) * m := by
  rw [payloadList, tagged_length, enumeration, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, List.length_ofFn, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, slots_card, Nat.cast_id]

noncomputable def payloadFn (z : ProductState F) (row : ℕ) :
    Fin ((2 * Fintype.card J - 1) * m) → (Slots i × Fin A) :=
  fixedFn (payloadList i F z row) (payload_length i F z row)

@[simp] lemma ofFn_payloadFn (z : ProductState F) (row : ℕ) :
    List.ofFn (payloadFn i F z row) = payloadList i F z row := ofFn_fixedFn _ _

noncomputable def rawWord (L : ℕ) (z : ProductState F) : List (Option (Slots i × Fin A)) :=
  EditRows.rowWord (fun row : Fin L => payloadFn i F z row.val)

@[simp] lemma rawWord_length (L : ℕ) (z : ProductState F) :
    (rawWord i F L z).length = 2 * ((2 * Fintype.card J - 1) * m) * L :=
  EditRows.rowWord_length _

omit [Fintype J] in
lemma shift_state (z : ProductState F) (u row row' : ℕ) (j : J) :
    (z + u • lift F i (F i).v) j + row' • (F j).v =
      (z j + row • (F j).v) +
        ((row' : ℤ) - (row : ℤ) + if j = i then (u : ℤ) else 0) • (F j).v := by
  by_cases hj : j = i
  · subst j
    simp only [Pi.add_apply, Pi.smul_apply, lift, Pi.single_eq_same]
    simp [add_zsmul, sub_zsmul]
    abel
  · simp only [Pi.add_apply, Pi.smul_apply, lift, Pi.single_eq_of_ne hj, smul_zero,
      ite_eq_right hj, add_zero, sub_zsmul, natCast_zsmul]
    abel

noncomputable def componentDistance (z z' : ProductState F) (row row' : ℕ) (j : J) : ℝ :=
  indel (List.ofFn ((F j).word (z j + row • (F j).v)))
    (List.ofFn ((F j).word (z' j + row' • (F j).v)))

omit [Fintype J] [DecidableEq J] in
lemma componentDistance_nonneg (z z' : ProductState F) (row row' : ℕ) (j : J) :
    0 ≤ componentDistance F z z' row row' j := Nat.cast_nonneg _

lemma payload_distance_ge_sum (z z' : ProductState F) (row row' : ℕ) :
    (∑ r : Slots i, componentDistance F z z' row row' (component i r)) ≤
      (indel (payloadList i F z row) (payloadList i F z' row') : ℝ) := by
  exact sum_indel_le_tagged (enumeration i) (enumeration_nodup i) (enumeration_full i) _ _

omit [Fintype J] in
lemma componentDistance_far (hp : ∀ j, (p j).Prime)
    (z : ProductState F) (u row row' : ℕ) (j : J)
    (ha : ¬ (p j : ℤ) ∣ ((row' : ℤ) - (row : ℤ) + if j = i then (u : ℤ) else 0)) :
    (m : ℝ) * α ≤ componentDistance F z (z + u • lift F i (F i).v) row row' j := by
  unfold componentDistance
  rw [shift_state]
  exact (F j).far_int (hp j).pos _ _ ha

lemma payload_separation
    (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (P : ℕ) (hP : 1 ≤ P) (hpP : ∀ j, P ≤ p j) (hα : 0 ≤ α)
    (z : ProductState F) (u : ℕ) (hu0 : 0 < u) (hu : u < p i)
    (row row' : ℕ) (hr : row < P ^ (Fintype.card J / 2))
    (hr' : row' < P ^ (Fintype.card J / 2)) :
    α * Fintype.card J * m / 3 ≤
      (indel (payloadList i F z row)
        (payloadList i F (z + u • lift F i (F i).v) row') : ℝ) := by
  let D := componentDistance F z (z + u • lift F i (F i).v) row row'
  have hDn (j : J) : 0 ≤ D j := componentDistance_nonneg F _ _ _ _ j
  have hsum := payload_distance_ge_sum i F z (z + u • lift F i (F i).v) row row'
  rw [sum_slots] at hsum
  change (Fintype.card J : ℝ) * D i + ∑ j : {j : J // j ≠ i}, D j ≤ _ at hsum
  have hma : 0 ≤ (m : ℝ) * α := mul_nonneg (Nat.cast_nonneg _) hα
  have hrest : 0 ≤ ∑ j : {j : J // j ≠ i}, D j := Finset.sum_nonneg (fun j _ => hDn j)
  by_cases hphase : ¬(p i : ℤ) ∣ ((row' : ℤ) - row + u)
  · have hf : (m : ℝ) * α ≤ D i := by
      exact componentDistance_far i F hp z u row row' i (by simpa using hphase)
    have hmul := mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg (Fintype.card J) : (0 : ℝ) ≤ _)
    have hbma : 0 ≤ (Fintype.card J : ℝ) * ((m : ℝ) * α) := mul_nonneg (Nat.cast_nonneg _) hma
    nlinarith
  · push Not at hphase
    let q : ℤ := (row' : ℤ) - row
    have hq : q ≠ 0 := by
      intro hq
      have hd : (p i : ℤ) ∣ (u : ℤ) := by simpa [q, hq] using hphase
      have hd' : p i ∣ u := by exact_mod_cast hd
      exact Nat.not_dvd_of_pos_of_lt hu0 hu hd'
    have hqr : q.natAbs < P ^ (Fintype.card J / 2) := by
      apply Int.ofNat_lt.mp
      rw [Int.natCast_natAbs]
      apply abs_lt.mpr
      dsimp [q]
      have hrZ : (row : ℤ) < (P : ℤ) ^ (Fintype.card J / 2) := by exact_mod_cast hr
      have hrZ' : (row' : ℤ) < (P : ℤ) ^ (Fintype.card J / 2) := by exact_mod_cast hr'
      constructor <;> omega
    let S := Finset.univ.filter (fun j => j ≠ i ∧ ¬(p j : ℤ) ∣ q)
    have hc : Fintype.card J - Fintype.card J / 2 ≤ S.card :=
      EditPhase.many_nonzero_phases p hp hinj hP hpP hq hqr i
    have hbc : (Fintype.card J : ℝ) / 3 ≤ (S.card : ℝ) := by
      have hn : Fintype.card J ≤ 3 * (Fintype.card J - Fintype.card J / 2) := by omega
      have hn' : (Fintype.card J : ℝ) ≤ 3 * ((Fintype.card J - Fintype.card J / 2 : ℕ) : ℝ) := by
        exact_mod_cast hn
      have hc' : ((Fintype.card J - Fintype.card J / 2 : ℕ) : ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast hc
      linarith
    have hS : (S.card : ℝ) * ((m : ℝ) * α) ≤ ∑ j ∈ S, D j := by
      calc
        _ = ∑ _j ∈ S, (m : ℝ) * α := by simp
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨hji, hdiv⟩ := (Finset.mem_filter.mp hj).2
          exact componentDistance_far i F hp z u row row' j (by simpa [hji, q] using hdiv)
    have hsub : S ⊆ Finset.univ.erase i := by
      intro j hj
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact (Finset.mem_filter.mp hj).2.1
    have hSrest : ∑ j ∈ S, D j ≤ ∑ j : {j : J // j ≠ i}, D j := by
      rw [← Finset.sum_subtype (Finset.univ.erase i) (by simp) D]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hDn j)
    have hbound := mul_le_mul_of_nonneg_right hbc hma
    have hdi : 0 ≤ (Fintype.card J : ℝ) * D i := mul_nonneg (Nat.cast_nonneg _) (hDn i)
    nlinarith

theorem rawWord_far
    (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (P : ℕ) (hP : 1 ≤ P) (hpP : ∀ j, P ≤ p j) (hm : 0 < m)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (z : ProductState F) (u : ℕ) (hu0 : 0 < u) (hu : u < p i) :
    (2 * ((2 * Fintype.card J - 1) * m) * P ^ (Fintype.card J / 2) : ℕ) * (α / 24) ≤
      (indel (rawWord i F (P ^ (Fintype.card J / 2)) z)
        (rawWord i F (P ^ (Fintype.card J / 2)) (z + u • lift F i (F i).v)) : ℝ) := by
  have hb : 1 ≤ Fintype.card J := Fintype.card_pos_iff.mpr ⟨i⟩
  have hB : 0 < (2 * Fintype.card J - 1) * m := Nat.mul_pos (by omega) hm
  have hbR : (1 : ℝ) ≤ Fintype.card J := by exact_mod_cast hb
  have hcast : ((2 * Fintype.card J - 1 : ℕ) : ℝ) = 2 * (Fintype.card J : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have htB : α * Fintype.card J * m / 6 ≤ (((2 * Fintype.card J - 1) * m : ℕ) : ℝ) := by
    rw [Nat.cast_mul, hcast]
    have ha := mul_le_mul_of_nonneg_right hα1 (Nat.cast_nonneg (Fintype.card J) : (0 : ℝ) ≤ _)
    have ha' := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg m : (0 : ℝ) ≤ _)
    nlinarith [Nat.cast_nonneg m (α := ℝ)]
  have h := EditRows.indel_row_separation
    (fun r : Fin (P ^ (Fintype.card J / 2)) => payloadFn i F z r.val)
    (fun r : Fin (P ^ (Fintype.card J / 2)) => payloadFn i F (z + u • lift F i (F i).v) r.val)
    hB htB (by
      intro r r'
      rw [ofFn_payloadFn, ofFn_payloadFn]
      convert payload_separation i F hp hinj P hP hpP hα0 z u hu0 hu r r' r.isLt r'.isLt using 1
      all_goals try with_reducible_and_instances rfl
      ring)
  change (P ^ (Fintype.card J / 2) : ℕ) * (α * Fintype.card J * m / 6) ≤ _ at h
  apply le_trans _ h
  simp only [Nat.cast_mul, Nat.cast_ofNat, hcast]
  have ha : 0 ≤ α * m * (P ^ (Fintype.card J / 2) : ℕ) := by positivity
  nlinarith

lemma payload_distance_le_sum (z z' : ProductState F) (row : ℕ) :
    (indel (payloadList i F z row) (payloadList i F z' row) : ℝ) ≤
      ∑ r : Slots i, componentDistance F z z' row row (component i r) := by
  have h := cost_tagged_le (enumeration i)
    (fun r => List.ofFn ((F (component i r)).word (z (component i r) + row • (F (component i r)).v)))
    (fun r => List.ofFn ((F (component i r)).word (z' (component i r) + row • (F (component i r)).v))) false
  change indel (payloadList i F z row) (payloadList i F z' row) ≤ _ at h
  rw [enumeration, List.map_ofFn, List.sum_ofFn] at h
  have h' := Nat.cast_le (α := ℝ).mpr h
  rw [Nat.cast_sum] at h'
  change (indel (payloadList i F z row) (payloadList i F z' row) : ℝ) ≤
    ∑ x : Fin (Fintype.card (Slots i)), componentDistance F z z' row row
      (component i ((Fintype.equivFin (Slots i)).symm x)) at h'
  rw [(Fintype.equivFin (Slots i)).symm.sum_comp
    (fun r => componentDistance F z z' row row (component i r))] at h'
  exact h'

omit [Fintype J] in
lemma componentDistance_lift (j : J) (e : (F j).State) (r : ℝ)
    (her : (e,r) ∈ (F j).steps) (z : ProductState F) (row : ℕ) (k : J) :
    componentDistance F z (z + lift F j e) row row k ≤ if k = j then m * r else 0 := by
  by_cases hk : k = j
  · subst k
    have he : (z + lift F j e) j + row • (F j).v = (z j + row • (F j).v) + e := by
      simp [lift, add_right_comm]
    unfold componentDistance
    rw [he, ite_eq_left rfl]
    exact (F j).cheap e r her (z j + row • (F j).v)
  · have he : (z + lift F j e) k + row • (F k).v = z k + row • (F k).v := by
      simp [lift, hk]
    simp only [componentDistance, he, ite_eq_right hk]
    change (cost false _ _ : ℝ) ≤ 0
    simp only [cost_refl, Nat.cast_zero, le_refl]

lemma payload_cheap_lift (j : J) (e : (F j).State) (r : ℝ)
    (her : (e,r) ∈ (F j).steps) (z : ProductState F) (row : ℕ) :
    (indel (payloadList i F z row) (payloadList i F (z + lift F j e) row) : ℝ) ≤
      multiplicity i j * m * r := by
  calc
    _ ≤ ∑ s : Slots i, componentDistance F z (z + lift F j e) row row (component i s) :=
      payload_distance_le_sum i F z (z + lift F j e) row
    _ ≤ ∑ s : Slots i, if component i s = j then (m : ℝ) * r else 0 := by
      apply Finset.sum_le_sum
      intro s _
      exact componentDistance_lift F j e r her z row (component i s)
    _ = _ := by rw [sum_slots_delta]; ring

lemma rawWord_cheap_lift (hm : 0 < m) (L : ℕ)
    (j : J) (e : (F j).State) (r : ℝ) (her : (e,r) ∈ (F j).steps) (z : ProductState F) :
    (indel (rawWord i F L z) (rawWord i F L (z + lift F j e)) : ℝ) ≤
      (2 * ((2 * Fintype.card J - 1) * m) * L : ℕ) * (weight i j * r) := by
  have hb : 1 ≤ Fintype.card J := Fintype.card_pos_iff.mpr ⟨i⟩
  have hB : 0 < (2 * Fintype.card J - 1) * m := Nat.mul_pos (by omega) hm
  have hbR : (1 : ℝ) ≤ Fintype.card J := by exact_mod_cast hb
  have hcast : ((2 * Fintype.card J - 1 : ℕ) : ℝ) = 2 * (Fintype.card J : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have h := EditRows.indel_rowWord_le hB
    (fun row : Fin L => payloadFn i F z row.val)
    (fun row : Fin L => payloadFn i F (z + lift F j e) row.val)
  have h' := Nat.cast_le (α := ℝ).mpr h
  change (indel (rawWord i F L z) (rawWord i F L (z + lift F j e)) : ℝ) ≤ _ at h'
  rw [Nat.cast_sum] at h'
  simp only [ofFn_payloadFn] at h'
  calc
    _ ≤ ∑ row : Fin L, (indel (payloadList i F z row.val)
        (payloadList i F (z + lift F j e) row.val) : ℝ) := h'
    _ ≤ ∑ _row : Fin L, (multiplicity i j : ℝ) * m * r :=
      Finset.sum_le_sum (fun row _ => payload_cheap_lift i F j e r her z row.val)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        weight, Nat.cast_mul, Nat.cast_ofNat, hcast]
      field_simp [show (2 * (Fintype.card J : ℝ) - 1) ≠ 0 by linarith]

lemma payload_allPhase (z : ProductState F) (row : ℕ) :
    payloadList i F (z + allPhase F) row = payloadList i F z (row+1) := by
  unfold payloadList
  congr 1
  funext s
  congr 2
  simp only [Pi.add_apply, allPhase, add_nsmul, one_nsmul]
  abel

lemma rawWord_cheap_phase (hm : 0 < m) (L : ℕ) (hL : 0 < L) (z : ProductState F) :
    (indel (rawWord i F L z) (rawWord i F L (z + allPhase F)) : ℝ) ≤
      (2 * ((2 * Fintype.card J - 1) * m) * L : ℕ) * (2 / (L : ℝ)) := by
  have hb : 1 ≤ Fintype.card J := Fintype.card_pos_iff.mpr ⟨i⟩
  have hB : 0 < (2 * Fintype.card J - 1) * m := Nat.mul_pos (by omega) hm
  have h := EditRows.indel_row_shift hL hB
    (fun row : Fin L => payloadFn i F z row.val)
    (fun row : Fin L => payloadFn i F (z + allPhase F) row.val) (by
      intro a b hab
      apply List.ofFn_injective
      rw [ofFn_payloadFn, ofFn_payloadFn, payload_allPhase, hab])
  have h' := Nat.cast_le (α := ℝ).mpr h
  change (indel (rawWord i F L z) (rawWord i F L (z + allPhase F)) : ℝ) ≤ _ at h'
  convert h' using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  field_simp
  ring

noncomputable def symbolCode : Option (Slots i × Fin A) ≃
    Fin (1 + (2 * Fintype.card J - 1) * A) :=
  (Fintype.equivFin _).trans (finCongr (by
    rw [Fintype.card_option, Fintype.card_prod, slots_card, Fintype.card_fin]
    omega))

noncomputable def nextWord (L : ℕ) (z : ProductState F) :
    Fin (2 * ((2 * Fintype.card J - 1) * m) * L) →
      Fin (1 + (2 * Fintype.card J - 1) * A) :=
  fixedFn ((rawWord i F L z).map (symbolCode (A := A) i)) (by simp)

@[simp] lemma ofFn_nextWord (L : ℕ) (z : ProductState F) :
    List.ofFn (nextWord i F L z) = (rawWord i F L z).map (symbolCode (A := A) i) :=
  ofFn_fixedFn _ _

lemma nextWord_distance (L : ℕ) (z z' : ProductState F) :
    indel (List.ofFn (nextWord i F L z)) (List.ofFn (nextWord i F L z')) =
      indel (rawWord i F L z) (rawWord i F L z') := by
  rw [ofFn_nextWord, ofFn_nextWord]
  exact cost_map_eq_of_leftInverse (s := false) (symbolCode (A := A) i)
    (symbolCode (A := A) i).symm (symbolCode (A := A) i).left_inv _ _

noncomputable def nextSteps (L : ℕ) : List (ProductState F × ℝ) :=
  (allPhase F, 2 / (L : ℝ)) :: (Finset.univ.toList.flatMap (fun j =>
    (F j).steps.map (fun er => (lift F j er.1, weight i j * er.2))))

lemma mem_nextSteps (L : ℕ) (e : ProductState F) (r : ℝ) :
    (e,r) ∈ nextSteps i F L ↔
      (e = allPhase F ∧ r = 2 / (L : ℝ)) ∨
      ∃ (j : J) (e' : (F j).State) (r' : ℝ), (e',r') ∈ (F j).steps ∧
        e = lift F j e' ∧ r = weight i j * r' := by
  simp only [nextSteps, List.mem_cons, Prod.mk.injEq, List.mem_flatMap,
    Finset.mem_toList, Finset.mem_univ, true_and, List.mem_map]
  constructor
  · rintro (h | ⟨j, ⟨e',r'⟩, hmem, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j,e',r',hmem,h.1.symm,h.2.symm⟩
  · rintro (h | ⟨j,e',r',hmem,he,hr⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j,(e',r'),hmem,he.symm,hr.symm⟩

noncomputable def successor
    (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (P : ℕ) (hP : 1 ≤ P) (hpLow : ∀ j, P ≤ p j) (hpHigh : ∀ j, p j ≤ 2 * P)
    (hm : 0 < m) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hQ : 0 ≤ Q)
    (h : ℕ) (hh : 0 < h) :
    Family (p i) (2 * ((2 * Fintype.card J - 1) * m) * P ^ (Fintype.card J / 2))
      (1 + (2 * Fintype.card J - 1) * A) (α / 24)
      (2 * (2 * (P : ℝ)) ^ (2 * h) / (P ^ (Fintype.card J / 2) : ℕ) + Q / h) := by
  classical
  let L := P ^ (Fintype.card J / 2)
  have hL : 0 < L := pow_pos (by omega) _
  refine { State := ProductState F
           group := inferInstance
           finite := inferInstance
           v := lift F i (F i).v
           annihilate := ?_
           word := nextWord i F L
           steps := nextSteps i F L
           positive := ?_
           cheap := ?_
           far := ?_
           control := ?_ }
  · rw [← lift_nsmul, (F i).annihilate]
    simp [lift]
  · intro e r her
    rcases (mem_nextSteps i F L e r).mp her with ⟨rfl,rfl⟩ | ⟨j,e',r',hmem,rfl,rfl⟩
    · exact div_pos (by norm_num) (by exact_mod_cast hL)
    · exact mul_pos (weight_pos i j) ((F j).positive e' r' hmem)
  · intro e r her z
    rw [nextWord_distance]
    rcases (mem_nextSteps i F L e r).mp her with ⟨rfl,rfl⟩ | ⟨j,e',r',hmem,rfl,rfl⟩
    · exact rawWord_cheap_phase i F hm L hL z
    · exact rawWord_cheap_lift i F hm L j e' r' hmem z
  · intro z u hu0 hu
    rw [nextWord_distance]
    exact rawWord_far i F hp hinj P hP hpLow hm hα0 hα1 z u hu0 hu
  · intro H hb u _hu0 hu
    apply successor_control i F hp hinj P (by exact_mod_cast (show 1 ≤ 2 * P by omega))
      (fun j => by exact_mod_cast hpHigh j) h hh L hQ H
    · exact hb _ _ ((mem_nextSteps i F L _ _).mpr (Or.inl ⟨rfl,rfl⟩))
    · intro j e r hmem
      exact hb _ _ ((mem_nextSteps i F L _ _).mpr (Or.inr ⟨j,e,r,hmem,rfl,rfl⟩))
    · exact hu

end Words
end EditFamily

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_FamilyRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Length, alphabet, and distortion recurrences for word families
-/

namespace EditFamily
open scoped BigOperators

def familyLength (b P s : ℕ) : ℕ := (2 * (2 * b - 1) * P ^ (b / 2)) ^ s

def familyAlphabet (b P : ℕ) : ℕ → ℕ
  | 0 => 2 * P
  | s+1 => 1 + (2 * b - 1) * familyAlphabet b P s

noncomputable def familyAlpha (s : ℕ) : ℝ := (24 : ℝ)⁻¹ ^ s

noncomputable def familyBudget (b P h : ℕ) : ℕ → ℝ
  | 0 => 2
  | s+1 => 2 * (2 * (P : ℝ)) ^ (2 * h) / (P ^ (b / 2) : ℕ) + familyBudget b P h s / h

lemma familyLength_pos {b P : ℕ} (hb : 0 < b) (hP : 0 < P) (s : ℕ) :
    0 < familyLength b P s := by
  unfold familyLength
  exact pow_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (pow_pos hP _)) _

lemma familyAlpha_pos (s : ℕ) : 0 < familyAlpha s := by
  unfold familyAlpha
  positivity

lemma familyAlpha_le_one (s : ℕ) : familyAlpha s ≤ 1 := by
  unfold familyAlpha
  exact pow_le_one₀ (by norm_num) (by norm_num)

lemma familyBudget_nonneg (b P h s : ℕ) : 0 ≤ familyBudget b P h s := by
  induction s with
  | zero => norm_num [familyBudget]
  | succ s ih =>
      exact add_nonneg (by positivity) (div_nonneg ih (Nat.cast_nonneg _))

noncomputable def recursive {J : Type} [Fintype J] [DecidableEq J]
    (p : J → ℕ) (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (P : ℕ) (hP : 1 ≤ P) (hpLow : ∀ j, P ≤ p j) (hpHigh : ∀ j, p j ≤ 2 * P)
    (h : ℕ) (hh : 0 < h) : (s : ℕ) → (j : J) →
    Family (p j) (familyLength (Fintype.card J) P s) (familyAlphabet (Fintype.card J) P s)
      (familyAlpha s) (familyBudget (Fintype.card J) P h s)
  | 0, j => base (hp j) (hpHigh j)
  | s+1, j => by
      let F := recursive p hp hinj P hP hpLow hpHigh h hh s
      have hn : familyLength (Fintype.card J) P (s+1) =
          2 * ((2 * Fintype.card J - 1) * familyLength (Fintype.card J) P s) *
            P ^ (Fintype.card J / 2) := by
        simp only [familyLength, pow_succ]
        ring
      have ha : familyAlpha (s+1) = familyAlpha s / 24 := by
        simp only [familyAlpha, pow_succ, div_eq_mul_inv]
      rw [hn, familyAlphabet, ha, familyBudget]
      exact successor j F hp hinj P hP hpLow hpHigh
        (familyLength_pos (Fintype.card_pos_iff.mpr ⟨j⟩) (by omega) s)
        (familyAlpha_pos s).le (familyAlpha_le_one s)
        (familyBudget_nonneg _ _ _ _) h hh

end EditFamily

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_PrimePool
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite pools of distinct primes from central binomial estimates
-/

namespace EditPrimes
open scoped BigOperators
open Nat Finset

def pool (n : ℕ) : Finset ℕ := (Finset.Ioc n (2*n)).filter Nat.Prime

end EditPrimes

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_LowerParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recursive parameter bounds and exponential lower scales
-/

namespace EditParameters
open EditFamily

def b (k : ℕ) := 100*k
def P (k : ℕ) := (b k)^2
def h (k : ℕ) := 10*k
noncomputable def eta (k : ℕ) : ℝ := 2 * (2 * (P k : ℝ)) ^ (2 * h k) / ((P k) ^ (b k / 2) : ℕ)

def codeBits (k : ℕ) := Nat.clog 2 (familyAlphabet (b k) (P k) k)
def codeWidth (k : ℕ) := 2*codeBits k+3
def encodedLength (k : ℕ) := codeWidth k * familyLength (b k) (P k) k

noncomputable def lowerRatio (k : ℕ) : ℝ := ((h k : ℝ)/24)^k/(16*(codeWidth k : ℝ))

end EditParameters

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_DepthInversion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Inverting recursive depth for all sufficiently large lengths
-/

namespace EditDepth
open Filter

noncomputable def radius (t : ℝ) := Real.sqrt (t / Real.log t)
noncomputable def depth (t : ℝ) : ℕ := ⌊radius t / 100⌋₊

end EditDepth

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_Distortion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Distance-ratio extrema and finite-dimensional embeddings
-/

namespace EditDistortion
universe u v

noncomputable def coordinateEmbedding (X : Type u) [Fintype X] : X ↪ L1 := by
  classical
  let e : X ↪ ℕ := (Fintype.equivFin X).toEmbedding.trans ⟨Fin.val,Fin.val_injective⟩
  refine ⟨fun x => lp.single 1 (e x) (1 : ℝ), ?_⟩
  intro x y h
  by_contra hxy
  have hne : e x ≠ e y := fun h => hxy (e.injective h)
  have he := congrArg (fun f : L1 => f (e x)) h
  simp only [lp.single_apply_self,lp.single_apply_ne (E := fun _ : ℕ => ℝ) 1 (e y) (1 : ℝ) hne] at he
  norm_num at he

end EditDistortion

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_LowerDistortion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Distortion lower bounds from separated finite word families
-/

namespace EditLower
open EditDistortion EditFamily EditCode EditAverage EditFourier

variable {p n A t : ℕ} {α Q : ℝ} (F : Family p n A α Q)
  (label : Fin A ↪ (Fin t → Bool))

def codeWord (z : F.State) : List Bool := encode label (List.ofFn (F.word z))
def codeSet : Set (List Bool) := Set.range (codeWord F label)
def codePoint (z : F.State) : codeSet F label := ⟨codeWord F label z,⟨z,rfl⟩⟩

end EditLower

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_FiniteLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite nonempty binary witnesses of a common length
-/

namespace EditLower
open EditDistortion EditFamily EditCode EditParameters

noncomputable def binaryLabels (k : ℕ) : Fin (familyAlphabet (b k) (P k) k) ↪ (Fin (codeBits k) → Bool) := by
  simpa only [codeBits,Fintype.card_fin] using labels (Fin (familyAlphabet (b k) (P k) k))

end EditLower

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_Windows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Padded windows and insertion-deletion matching inequalities
-/

namespace EditWindow
open EditDistortion

variable {A : Type*}

def window (x : List A) (start len : ℕ) : List (Option A) :=
  List.ofFn (fun i : Fin len => x[start+i.val]?)

@[simp] lemma window_length (x : List A) (start len : ℕ) : (window x start len).length = len :=
  List.length_ofFn

end EditWindow

namespace EditWindow
open EditDistortion
variable {A : Type*}

def segment (x : ℕ → A) (start len : ℕ) : List A :=
  List.ofFn (fun i : Fin len => x (start+i.val))

@[simp] lemma segment_length (x : ℕ → A) (start len : ℕ) :
    (segment x start len).length = len := List.length_ofFn

end EditWindow

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_WindowRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic-window recursion and insertion bounds
-/

namespace EditUpper
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset EditDistortion EditWindow EditCutModel

variable {A : Type*}

def samples (x : List A) (start l s : ℕ) : Fin s → List (Option A) :=
  fun i => window x (start+i.val) (l-s+1)

noncomputable def piece (M : Model (List (Option A))) (x y : List A) (start l s : ℕ) : ℝ :=
  EditCutHash.meanHistogram M.weight (EditCutHash.rate s) M.cut
    (samples x start l s) (samples y start l s)

noncomputable def lift (M : Model (List (Option A))) (b l : ℕ) : Model (List A) :=
  (Model.total (fun j : Fin b × Fin (Nat.log 2 l+1) =>
    (M.histogram (2^j.2.val) (EditCutHash.rate (2^j.2.val))
      (EditCutHash.rate_nonneg (pow_pos (by omega) _))).pullback
        (fun x => samples x (j.1.val*l) l (2^j.2.val)))).scale 16 (by norm_num)

end EditUpper

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_UpperBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Base finite-cut embedding for short words
-/

namespace EditUpper
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset EditDistortion EditWindow EditCutModel
variable {A : Type*} [Fintype A]

noncomputable def firstKey (x : List A) : Fin (Fintype.card (Option A)) :=
  Fintype.equivFin (Option A) (x[0]?)

noncomputable def base : Model (List A) where
  Index := Fin (Fintype.card (Option A))
  finiteIndex := inferInstance
  weight _ := 1
  nonneg _ := by norm_num
  cut i x := decide (firstKey x = i)

end EditUpper

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_UpperRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform finite-cut embeddings at recursive capacities
-/

namespace EditUpper

universe u

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset EditDistortion EditWindow EditCutModel

noncomputable def growth (b N : ℕ) : ℝ := 1024*(1+(N : ℝ)*Real.log (b : ℝ))^2

end EditUpper

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_UpperParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Branching and depth choices at every sufficiently large length
-/

namespace EditUpperParameters
open Filter

noncomputable def peak (t : ℝ) : ℝ := Real.sqrt (t*Real.log t)
noncomputable def level (t : ℝ) : ℕ := ⌊EditDepth.radius t⌋₊
noncomputable def branching (t : ℝ) : ℕ := ⌈Real.exp (2*peak t)⌉₊

end EditUpperParameters

end OAI
end


