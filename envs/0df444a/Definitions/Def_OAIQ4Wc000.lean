-- Prove2me | Definitions.Def_OAIQ4Wc000
-- name    : OAIQ4Wc000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T00:18:26.217236+00:00
-- url     : https://prove2.me/theorems/a9208b1e-cd3d-455b-b10e-112558ac24f2
-- title:
--   Definitions bundle OAIQ4Wc000 of the split of OpenAI, Witnessed symmetric choice is strictly stronger than choiceless polynomial time with counting
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WitnessedChoice.main`, carved from OpenAI's openai/math development (OpenAI, *Witnessed symmetric choice is strictly stronger than choiceless polynomial time with counting*, OpenAI Math Release, September 24, 2026, result family 243, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1004 declarations of OpenAI's Lean: 503 definitions, 25 inductive types or structures, 22 instances and 454 theorems. The definitions and types are `OAI.WitnessedChoice.AnchoredTree.Eligible`, `OAI.WitnessedChoice.AnchoredTree.Resolving`, `OAI.WitnessedChoice.AnchoredTree.key`, `OAI.WitnessedChoice.AnchoredTree.parent`, `OAI.WitnessedChoice.AnchoredTree.rooted`, `OAI.WitnessedChoice.BGS.AdmissibleTrace`, `OAI.WitnessedChoice.BGS.BFS.Item`, `OAI.WitnessedChoice.BGS.BFS.closure`, `OAI.WitnessedChoice.BGS.BFS.good`, `OAI.WitnessedChoice.BGS.BFS.update`, `OAI.WitnessedChoice.BGS.CPTFormula`, `OAI.WitnessedChoice.BGS.CPTFormula.letIn`, `OAI.WitnessedChoice.BGS.CPTFormula.quoted`, `OAI.WitnessedChoice.BGS.CPTFormula.value`, `OAI.WitnessedChoice.BGS.CPTTerm`, `OAI.WitnessedChoice.BGS.CPTTerm.comprehend`, `OAI.WitnessedChoice.BGS.CPTTerm.distance`, `OAI.WitnessedChoice.BGS.CPTTerm.iterate`, `OAI.WitnessedChoice.BGS.CPTTerm.letIn`, `OAI.WitnessedChoice.BGS.CPTTerm.map`, `OAI.WitnessedChoice.BGS.CPTTerm.normalizeCandidates`, `OAI.WitnessedChoice.BGS.CPTTerm.normalizeRelations`, `OAI.WitnessedChoice.BGS.CPTTerm.quoted`, `OAI.WitnessedChoice.BGS.CPTTerm.rename`, `OAI.WitnessedChoice.BGS.CPTTerm.up`, `OAI.WitnessedChoice.BGS.CPTTerm.value`, `OAI.WitnessedChoice.BGS.ClosedGuardedProgram`, `OAI.WitnessedChoice.BGS.ClosedGuardedProgram.formula`, `OAI.WitnessedChoice.BGS.ClosedGuardedProgram.parameterTerm`, `OAI.WitnessedChoice.BGS.ClosedGuardedProgram.sentence`, `OAI.WitnessedChoice.BGS.ClosedTrace`, `OAI.WitnessedChoice.BGS.FiniteIteration.run`, `OAI.WitnessedChoice.BGS.Formula.allIn`, `OAI.WitnessedChoice.BGS.Formula.existsIn`, `OAI.WitnessedChoice.BGS.Formula.letIn`, `OAI.WitnessedChoice.BGS.Formula.mem`, `OAI.WitnessedChoice.BGS.Formula.truth`, `OAI.WitnessedChoice.BGS.Formula.up`, `OAI.WitnessedChoice.BGS.FunctionalOnto`, `OAI.WitnessedChoice.BGS.GuardedProgram` and 488 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `WitnessedChoice_AnchoredTree`, `WitnessedChoice_ChoiceSeparation`, `WitnessedChoice_ChoiceTrace`, `WitnessedChoice_Counting`, `WitnessedChoice_CountingTransfer`, `WitnessedChoice_CycleTranslation`, `WitnessedChoice_EncodedCounting`, `WitnessedChoice_EvaluationTrace`, `WitnessedChoice_FormTransfer`, `WitnessedChoice_GridAction`, `WitnessedChoice_GridGeometry`, `WitnessedChoice_GuardedProgram`, `WitnessedChoice_Hereditary`, `WitnessedChoice_Homogeneity`, `WitnessedChoice_Machines`, `WitnessedChoice_Model`, `WitnessedChoice_QuotedSyntax`, `WitnessedChoice_SupportGrid`, `WitnessedChoice_SupportedForms`, `WitnessedChoice_Syntax`, `WitnessedChoice_TermGraphs`, `WitnessedChoice_TraceGraphs`, `WitnessedChoice_TreeCorrection`, `WitnessedChoice_TreeElimination`.
--
--   **Imports.** It imports the published bundle `Def_WitnessedChoice`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ4Wc002`; the statements `OAI.WitnessedSeparation.Grid.QuotedGrid.cycleRelations_negative`, `OAI.WitnessedSeparation.Grid.QuotedGrid.formula_value`, `OAI.WitnessedSeparation.Grid.QuotedGrid.fundamentalPool_in_cycles`, `OAI.WitnessedSeparation.Grid.QuotedGrid.selection_candidates` and `OAI.WitnessedSeparation.Grid.QuotedGrid.selection_transitive`; the proofs of `OAI.WitnessedChoice.main`, `OAI.WitnessedSeparation.Grid.QuotedGrid.cycleRelations_negative`, `OAI.WitnessedSeparation.Grid.QuotedGrid.formula_value`, `OAI.WitnessedSeparation.Grid.QuotedGrid.fundamentalPool_in_cycles`, `OAI.WitnessedSeparation.Grid.QuotedGrid.selection_candidates` and `OAI.WitnessedSeparation.Grid.QuotedGrid.selection_transitive`.
-- source:
--   OpenAI, Witnessed symmetric choice is strictly stronger than choiceless polynomial time with counting, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 243; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Witnessed-symmetric-choice-is-strictly-stronger-than-choiceless-polynomial-time-with-counting-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_WitnessedChoice

section
-- module Solutions.OAIQ4_WC.Compat
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
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
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
-- module Solutions.OAIQ4_WC.WitnessedChoice_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

namespace WitnessedSeparation.Hereditary

noncomputable section

variable {A : Type u} {B : Type v}

@[simp] theorem mk_eq_mk {l r : Lists A} : mk l = mk r ↔ Lists.Equiv l r :=
  Quotient.eq

attribute [local instance] OAI.WitnessedSeparation.Hereditary.instDecidableEqHF
theorem mem_rawElements (a l : Lists A) : mk a ∈ rawElements l ↔ a ∈ l := by
  classical
  rcases l with ⟨(_ | _), l⟩
  · cases l
    change mk a ∈ (∅ : Finset (HF A)) ↔ False
    simp
  · change mk a ∈ (Lists'.toList l).toFinset.image mk ↔ a ∈ l
    simp only [Finset.mem_image, List.mem_toFinset, Lists'.mem_def, mk_eq_mk]
    constructor
    · rintro ⟨a',ha',heq⟩
      exact ⟨a',ha',heq.symm⟩
    · rintro ⟨a',ha',heq⟩
      exact ⟨a',ha',heq.symm⟩

@[simp] theorem mem_mk (a l : Lists A) : mk a ∈ mk l ↔ a ∈ l := mem_rawElements a l

theorem rawRank_lt_of_mem {b : Bool} (l : Lists' A b) (a : Lists A)
    (ha : a ∈ l.toList) : rawRank a < rawRank' l := by
  induction l with
  | atom => simp at ha
  | nil => simp at ha
  | cons' c l ihc ihl =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · exact lt_of_lt_of_le (ihl ha) (le_max_right _ _)

theorem rawRank_congr {l r : Lists A} (h : Lists.Equiv l r) : rawRank l = rawRank r := by
  induction h using Lists.Equiv.rec
      (motive_2 := fun l r _ => rawRank' l ≤ rawRank' r) with
  | refl => rfl
  | antisymm hl hr ihl ihr => exact Nat.le_antisymm ihl ihr
  | nil => exact Nat.zero_le _
  | @cons a a' l r heq hmem hsub iheq ihsub =>
    change max (rawRank a + 1) (rawRank' l) ≤ rawRank' r
    refine max_le ?_ ihsub
    rw [iheq]
    exact rawRank_lt_of_mem r a' hmem

theorem rank_lt_of_mem {x y : HF A} (h : x ∈ y) : rank x < rank y := by
  induction y using Quotient.inductionOn with
  | _ l =>
    induction x using Quotient.inductionOn with
    | _ a =>
      have h' := (mem_mk a l).mp h
      rcases l with ⟨(_ | _), l⟩
      · exact False.elim h'
      · obtain ⟨a',ha',heq⟩ := h'
        change rawRank a < rawRank' l
        rw [rawRank_congr heq]
        exact rawRank_lt_of_mem l a' ha'

theorem toList_rawMap' (f : A → B) {b : Bool} (l : Lists' A b) :
    (rawMap' f l).toList = l.toList.map (rawMap f) := by
  induction l with
  | atom => rfl
  | nil => rfl
  | cons' a l iha ihl => simp only [rawMap', Lists'.toList, ihl]; rfl

@[simp] theorem map_mk (f : A → B) (l : Lists A) : map f (mk l) = mk (rawMap f l) := rfl

@[simp] theorem rawMap_id : ∀ l : Lists A, rawMap id l = l := by
  rintro ⟨b,l⟩
  have h : rawMap' id l = l := by
    induction l with
    | atom => rfl
    | nil => rfl
    | cons' a l iha ihl => simp only [rawMap', iha,ihl]
  exact congrArg (Sigma.mk b) h

@[simp] theorem map_id (x : HF A) : map id x = x := by
  induction x using Quotient.inductionOn with
  | _ l =>
    change map id (mk l) = mk l
    rw [map_mk, rawMap_id]

theorem rawMap_comp {C : Type w} (g : B → C) (f : A → B) (l : Lists A) :
    rawMap g (rawMap f l) = rawMap (g ∘ f) l := by
  rcases l with ⟨b,l⟩
  have h : rawMap' g (rawMap' f l) = rawMap' (g ∘ f) l := by
    induction l with
    | atom => rfl
    | nil => rfl
    | cons' a l iha ihl => simp only [rawMap', iha,ihl]
  exact congrArg (Sigma.mk b) h

@[simp] theorem map_comp {C : Type w} (g : B → C) (f : A → B) (x : HF A) :
    map g (map f x) = map (g ∘ f) x := by
  induction x using Quotient.inductionOn with
  | _ l =>
    change map g (map f (mk l)) = map (g ∘ f) (mk l)
    simp only [map_mk,rawMap_comp]

end

end WitnessedSeparation.Hereditary

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

attribute [instance] FiniteInput.finite

end

end WitnessedChoice.BGS

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_Hereditary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

namespace WitnessedSeparation.Hereditary

noncomputable section

variable {A : Type u} {B : Type v}

attribute [local instance] instDecidableEqHF

@[simp] theorem mk_out (x : HF A) : mk (Quotient.out x) = x := Quotient.out_eq x

@[simp] theorem isSet_mk (l : Lists A) : isSet (mk l) = l.1 := rfl

@[simp] theorem isSet_atom (a : A) : isSet (atom a) = false := rfl

@[simp] theorem elements_mk (l : Lists A) : elements (mk l) = rawElements l := rfl

@[simp] theorem elements_atom (a : A) : elements (atom a) = ∅ := by
  classical
  change rawElements (Lists.atom a) = ∅
  simp [rawElements, Lists.toList]

@[simp] theorem not_mem_atom (x : HF A) (a : A) : ¬ x ∈ atom a := by
  change ¬ x ∈ elements (atom a)
  simp

theorem atom_injective : Function.Injective (atom : A → HF A) := by
  intro a b h
  have h' := Lists.equiv_atom.mp (mk_eq_mk.mp h)
  cases h'
  rfl

@[simp] theorem isSet_ofFinset (s : Finset (HF A)) : isSet (ofFinset s) = true := rfl

@[simp] theorem elements_ofFinset (s : Finset (HF A)) : elements (ofFinset s) = s := by
  classical
  ext x
  simp only [ofFinset, elements_mk, rawElements, Lists.to_ofList, Finset.mem_image,
    List.mem_toFinset]
  simp only [List.mem_map, Finset.mem_toList]
  constructor
  · rintro ⟨l, ⟨y,hy,rfl⟩,h⟩
    rw [mk_out] at h
    exact h ▸ hy
  · intro hx
    exact ⟨Quotient.out x, ⟨x,hx,rfl⟩, mk_out x⟩

@[simp] theorem mem_ofFinset (x : HF A) (s : Finset (HF A)) : x ∈ ofFinset s ↔ x ∈ s := by
  change x ∈ elements (ofFinset s) ↔ x ∈ s
  rw [elements_ofFinset]

theorem ext_sets {x y : HF A} (hx : isSet x = true) (hy : isSet y = true)
    (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y := by
  induction x using Quotient.inductionOn with
  | _ l =>
    induction y using Quotient.inductionOn with
    | _ r =>
      rcases l with ⟨(_ | _), l⟩ <;> (try cases hx)
      rcases r with ⟨(_ | _), r⟩ <;> (try cases hy)
      apply mk_eq_mk.mpr
      apply Lists.Equiv.antisymm
      · apply Lists'.subset_def.mpr
        intro a ha
        apply (mem_mk a (Lists.of' r)).mp
        apply (h (mk a)).mp
        exact (mem_mk a (Lists.of' l)).mpr ⟨a,ha,Lists.Equiv.refl a⟩
      · apply Lists'.subset_def.mpr
        intro a ha
        apply (mem_mk a (Lists.of' l)).mp
        apply (h (mk a)).mpr
        exact (mem_mk a (Lists.of' r)).mpr ⟨a,ha,Lists.Equiv.refl a⟩

theorem ofFinset_elements {x : HF A} (hx : isSet x = true) : ofFinset (elements x) = x := by
  apply ext_sets (isSet_ofFinset _) hx
  intro z
  rw [mem_ofFinset]
  rfl

theorem atom_or_set (x : HF A) : (∃ a, x = atom a) ∨ x = ofFinset (elements x) := by
  induction x using Quotient.inductionOn with
  | _ l =>
    rcases l with ⟨(_ | _), l⟩
    · cases l with
      | atom a => exact Or.inl ⟨a,rfl⟩
    · exact Or.inr (ofFinset_elements rfl).symm

@[simp] theorem rank_mk (l : Lists A) : rank (mk l) = rawRank l := rfl

@[simp] theorem rank_atom (a : A) : rank (atom a) = 0 := rfl

@[simp] theorem map_atom (f : A → B) (a : A) : map f (atom a) = atom (f a) := rfl

@[simp] theorem isSet_map (f : A → B) (x : HF A) : isSet (map f x) = isSet x := by
  induction x using Quotient.inductionOn with
  | _ l => rfl

theorem elements_map (f : A → B) (x : HF A) :
    elements (map f x) = (elements x).image (map f) := by
  classical
  induction x using Quotient.inductionOn with
  | _ l =>
    change (rawMap f l).toList.toFinset.image mk =
      (l.toList.toFinset.image mk).image (map f)
    rw [Finset.image_image]
    have ht : (rawMap f l).toList = l.toList.map (rawMap f) := toList_rawMap' f l.2
    rw [ht]
    ext z
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨b,⟨a,ha,rfl⟩,h⟩
      exact ⟨a,ha,h⟩
    · rintro ⟨a,ha,h⟩
      exact ⟨rawMap f a,⟨a,ha,rfl⟩,h⟩

@[simp] theorem map_ofFinset (f : A → B) (s : Finset (HF A)) :
    map f (ofFinset s) = ofFinset (s.image (map f)) := by
  classical
  apply ext_sets (by simp) (by simp)
  intro z
  change z ∈ elements (map f (ofFinset s)) ↔ z ∈ elements (ofFinset (s.image (map f)))
  rw [elements_map, elements_ofFinset, elements_ofFinset]

def mapEquiv (e : A ≃ B) : HF A ≃ HF B where
  toFun := map e
  invFun := map e.symm
  left_inv x := by
    rw [map_comp]
    have h : (e.symm : B → A) ∘ (e : A → B) = id := by funext a; simp
    rw [h,map_id]
  right_inv x := by
    rw [map_comp]
    have h : (e : A → B) ∘ (e.symm : B → A) = id := by funext a; simp
    rw [h,map_id]

@[simp] theorem smul_atom {G : Type w} [Group G] [MulAction G A] (g : G) (a : A) :
    g • atom a = atom (g • a) := rfl

@[simp] theorem smul_ofFinset {G : Type w} [Group G] [MulAction G A] (g : G) (s : Finset (HF A)) :
    g • ofFinset s = ofFinset (s.image (fun x => g • x)) := map_ofFinset _ _

def Supports {G : Type w} [Group G] [MulAction G A] {k : ℕ}
    (alpha : Fin k → A) (x : HF A) : Prop :=
  ∀ g : G, (∀ i, g • alpha i = alpha i) → g • x = x

def Supported {G : Type w} [Group G] [MulAction G A] (s : ℕ) (x : HF A) : Prop :=
  ∃ alpha : Fin s → A, Supports (G := G) alpha x

def HereditarilySupported {G : Type w} [Group G] [MulAction G A] (s : ℕ) (x : HF A) : Prop :=
  ∀ y, Relation.ReflTransGen (fun a b : HF A => a ∈ b) y x → Supported (G := G) s y

end



noncomputable section

open Classical Finset

variable {A : Type u} {B : Type v}

@[simp] theorem ofFinset_inj {s t : Finset (HF A)} : ofFinset s = ofFinset t ↔ s = t :=
  ⟨fun h => by simpa using congrArg elements h,fun h => congrArg ofFinset h⟩

@[simp] theorem mem_singleton (x a : HF A) : x ∈ singleton a ↔ x = a := by simp [singleton]

@[simp] theorem mem_double (x a b : HF A) : x ∈ double a b ↔ x = a ∨ x = b := by simp [double]

@[simp] theorem singleton_inj {a b : HF A} : singleton a = singleton b ↔ a = b := by simp [singleton]

@[simp] theorem map_singleton (f : A → B) (a : HF A) : map f (singleton a) = singleton (map f a) := by simp [singleton]

@[simp] theorem map_double (f : A → B) (a b : HF A) : map f (double a b) = double (map f a) (map f b) := by
  simp only [double,map_ofFinset,image_insert,image_singleton]
  apply ofFinset_inj.mpr
  ext x
  simp

@[simp] theorem map_pair (f : A → B) (a b : HF A) : map f (pair a b) = pair (map f a) (map f b) := by simp [pair]

theorem pair_injective {a b c d : HF A} (h : pair a b = pair c d) : a = c ∧ b = d := by
  have first (a b : HF A) : ∀ u ∈ pair a b, a ∈ u := by
    intro u hu
    rcases (mem_double _ _ _).mp hu with rfl|rfl <;> simp
  have hac : a = c := by
    have hm : singleton c ∈ pair a b := by rw [h]; simp [pair]
    exact (mem_singleton _ _).mp (first a b _ hm)
  subst c
  have union (a b x : HF A) : (∃ u ∈ pair a b, x ∈ u) ↔ x = a ∨ x = b := by
    simp only [pair,mem_double]
    aesop
  have hb : b = a ∨ b = d := by
    apply (union a d b).mp
    rw [← h]
    exact (union a b b).mpr (Or.inr rfl)
  have hd : d = a ∨ d = b := by
    apply (union a b d).mp
    rw [h]
    exact (union a d d).mpr (Or.inr rfl)
  exact ⟨rfl,by rcases hb with hba|hbd; rcases hd with hda|hdb <;> simp_all; exact hbd⟩

@[simp] theorem pair_eq_pair {a b c d : HF A} : pair a b = pair c d ↔ a = c ∧ b = d :=
  ⟨pair_injective,fun ⟨h,h'⟩ => by rw [h,h']⟩

@[simp] theorem ordinal_isSet (i : ℕ) : isSet (ordinal (A := A) i) = true := by cases i <;> simp [ordinal]

theorem mem_ordinal (x : HF A) (i : ℕ) : x ∈ ordinal i ↔ ∃ k < i, x = ordinal k := by
  induction i with
  | zero => simp [ordinal]
  | succ i ih =>
    change x ∈ ofFinset (insert (ordinal i) (elements (ordinal i))) ↔ _
    simp only [mem_ofFinset,mem_insert]
    change x = ordinal i ∨ x ∈ ordinal i ↔ _
    rw [ih]
    constructor
    · rintro (rfl|⟨k,hk,rfl⟩)
      · exact ⟨i,by omega,rfl⟩
      · exact ⟨k,by omega,rfl⟩
    · rintro ⟨k,hk,rfl⟩
      by_cases hki : k = i
      · exact Or.inl (congrArg ordinal hki)
      · exact Or.inr ⟨k,by omega,rfl⟩

theorem ordinal_injective : Function.Injective (ordinal (A := A)) := by
  intro i j hij
  by_contra hn
  rcases lt_or_gt_of_ne hn with h|h
  · have hm := (mem_ordinal (ordinal (A := A) i) j).mpr ⟨i,h,rfl⟩
    rw [hij] at hm
    exact (Nat.lt_irrefl _) (rank_lt_of_mem hm)
  · have hm := (mem_ordinal (ordinal (A := A) j) i).mpr ⟨j,h,rfl⟩
    rw [hij] at hm
    exact (Nat.lt_irrefl _) (rank_lt_of_mem hm)

@[simp] theorem map_ordinal (f : A → B) (i : ℕ) : map f (ordinal i) = ordinal i := by
  induction i with
  | zero => simp [ordinal]
  | succ i ih =>
    simp only [ordinal,map_ofFinset,image_insert,ih]
    rw [← elements_map,ih]
    apply ofFinset_inj.mpr
    ext x
    simp

end

end WitnessedSeparation.Hereditary

namespace WitnessedSeparation.Hereditary

noncomputable section

open Classical Finset

variable {A : Type u} {B : Type v}

attribute [local instance] instDecidableEqHF_1

@[simp] lemma mem_closure_self (x : HF A) : x ∈ closure x := by rw [closure]; simp

lemma closure_member_subset {x y : HF A} (h : y ∈ x) : closure y ⊆ closure x := by
  nth_rw 2 [closure]
  intro z hz
  simp only [mem_insert,mem_biUnion,mem_attach,true_and,Subtype.exists]
  exact Or.inr ⟨y,h,hz⟩

lemma mem_closure_iff (x y : HF A) : x ∈ closure y ↔
    Relation.ReflTransGen (fun a b : HF A => a ∈ b) x y := by
  constructor
  · intro h
    induction y using (measure rank).wf.induction with
    | h y ih =>
      rw [closure] at h
      rcases mem_insert.mp h with rfl | hm
      · exact .refl
      · obtain ⟨z,hz,hxz⟩ := mem_biUnion.mp hm
        exact (ih z.val (rank_lt_of_mem z.property) hxz).tail z.property
  · intro h
    induction h with
    | refl => exact mem_closure_self _
    | tail hab hbc ih => exact closure_member_subset hbc ih

lemma closure_transitive {x y z : HF A} (hxy : y ∈ closure x) (hyz : z ∈ y) :
    z ∈ closure x := by
  apply (mem_closure_iff z x).mpr
  exact (Relation.ReflTransGen.single (r := fun a b : HF A => a ∈ b) hyz).trans ((mem_closure_iff y x).mp hxy)

end

end WitnessedSeparation.Hereditary

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_SupportGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type}

theorem iterationLoop_total (p : ℕ) (step : HF A → Result (HF A))
    (ht : ∀ x, ∃ y, step x = some y) (fuel : ℕ) (x : HF A) :
    ∃ y, iterationLoop p step fuel x = some y := by
  induction fuel generalizing x with
  | zero => exact ⟨emptyHF, rfl⟩
  | succ fuel ih =>
    rw [iterationLoop]
    split_ifs with hb
    · obtain ⟨y, hy⟩ := ht x
      rw [hy, Option.bind_some]
      split_ifs
      · exact ⟨x, rfl⟩
      · exact ih y
    · exact ⟨emptyHF, rfl⟩

theorem ordinaryIteration_total (p : ℕ) (step : HF A → Result (HF A))
    (ht : ∀ x, ∃ y, step x = some y) : ∃ y, ordinaryIteration p step = some y :=
  iterationLoop_total p step ht _ _

theorem collect_total (r : HF A) (guard : HF A → Result Bool) (body : HF A → Result (HF A))
    (hg : ∀ x ∈ elements r, ∃ b, guard x = some b)
    (hb : ∀ x ∈ elements r, guard x = some true → ∃ y, body x = some y) :
    ∃ y, collect r guard body = some y := by
  have hg' : ∀ x ∈ elements r, (guard x).isSome := by
    intro x hx
    obtain ⟨b, hb⟩ := hg x hx
    simp [hb]
  have hb' : ∀ x ∈ elements r, guard x = some true → (body x).isSome := by
    intro x hx htrue
    obtain ⟨b, hb⟩ := hb x hx htrue
    simp [hb]
  unfold collect
  rw [ite_eq_left ⟨hg', hb'⟩]
  exact ⟨_, rfl⟩

mutual
  theorem Term.total [Fintype A] (S : Input A) (p : Polynomial ℝ) {n : ℕ}
      (t : Term n) (h : t.wscCount = 0) (env : Fin n → HF A) :
      ∃ x, t.eval S p env = some x := by
    cases t with
    | var i => exact ⟨env i, rfl⟩
    | empty => exact ⟨emptyHF, rfl⟩
    | atoms => exact ⟨_, rfl⟩
    | pair a b =>
      simp only [Term.wscCount, Nat.add_eq_zero_iff] at h
      obtain ⟨x, hx⟩ := a.total S p h.1 env
      obtain ⟨y, hy⟩ := b.total S p h.2 env
      exact ⟨double x y, by simp [Term.eval, lift₂, hx, hy]⟩
    | union a =>
      obtain ⟨x, hx⟩ := a.total S p h env
      exact ⟨unionHF x, by simp [Term.eval, hx]⟩
    | unique a =>
      obtain ⟨x, hx⟩ := a.total S p h env
      exact ⟨uniqueHF x, by simp [Term.eval, hx]⟩
    | card a =>
      obtain ⟨x, hx⟩ := a.total S p h env
      exact ⟨cardHF x, by simp [Term.eval, hx]⟩
    | comprehend body range guard =>
      simp only [Term.wscCount, Nat.add_eq_zero_iff] at h
      obtain ⟨r, hr⟩ := range.total S p h.1.2 env
      simp only [Term.eval, hr, Option.bind_some]
      apply collect_total
      · exact fun x _ => guard.total S p h.2 (Fin.cons x env)
      · exact fun x _ _ => body.total S p h.1.1 (Fin.cons x env)
    | iterate step =>
      exact ordinaryIteration_total _ _ (fun x => step.total S p h (Fin.cons x env))
  theorem Formula.total [Fintype A] (S : Input A) (p : Polynomial ℝ) {n : ℕ}
      (f : Formula n) (h : f.wscCount = 0) (env : Fin n → HF A) :
      ∃ b, f.eval S p env = some b := by
    cases f with
    | equal a b =>
      simp only [Formula.wscCount, Nat.add_eq_zero_iff] at h
      obtain ⟨x, hx⟩ := a.total S p h.1 env
      obtain ⟨y, hy⟩ := b.total S p h.2 env
      exact ⟨decide (x = y), by simp [Formula.eval, lift₂, hx, hy]⟩
    | input r a b =>
      simp only [Formula.wscCount, Nat.add_eq_zero_iff] at h
      obtain ⟨x, hx⟩ := a.total S p h.1 env
      obtain ⟨y, hy⟩ := b.total S p h.2 env
      exact ⟨inputHF S r x y, by simp [Formula.eval, lift₂, hx, hy]⟩
    | neg a =>
      obtain ⟨x, hx⟩ := a.total S p h env
      exact ⟨!x, by simp [Formula.eval, hx]⟩
    | and a b =>
      simp only [Formula.wscCount, Nat.add_eq_zero_iff] at h
      obtain ⟨x, hx⟩ := a.total S p h.1 env
      obtain ⟨y, hy⟩ := b.total S p h.2 env
      exact ⟨x && y, by simp [Formula.eval, lift₂, hx, hy]⟩
    | or a b =>
      simp only [Formula.wscCount, Nat.add_eq_zero_iff] at h
      obtain ⟨x, hx⟩ := a.total S p h.1 env
      obtain ⟨y, hy⟩ := b.total S p h.2 env
      exact ⟨x || y, by simp [Formula.eval, lift₂, hx, hy]⟩
    | wsc step choice witness output =>
      simp only [Formula.wscCount] at h
      omega
end

end

end WitnessedChoice.BGS

namespace WitnessedSeparation

namespace Support

abbrev Scalar := ZMod 3

abbrev Plane := Scalar × Scalar

def omega (u v : Plane) : Scalar := u.1 * v.2 - u.2 * v.1

@[simp] theorem omega_self (u : Plane) : omega u u = 0 := by simp [omega, mul_comm]

@[simp] theorem omega_zero_left (u : Plane) : omega 0 u = 0 := by simp [omega]

@[simp] theorem omega_zero_right (u : Plane) : omega u 0 = 0 := by simp [omega]

@[simp] theorem omega_add_left (u v w : Plane) :
    omega (u + v) w = omega u w + omega v w := by simp [omega]; ring

@[simp] theorem omega_add_right (u v w : Plane) :
    omega u (v + w) = omega u v + omega u w := by simp [omega]; ring

@[simp] theorem omega_neg_left (u v : Plane) : omega (-u) v = -omega u v := by
  simp [omega]; ring

@[simp] theorem omega_neg_right (u v : Plane) : omega u (-v) = -omega u v := by
  simp [omega]; ring

@[simp] theorem omega_smul_left (a : Scalar) (u v : Plane) :
    omega (a • u) v = a * omega u v := by simp [omega]; ring

@[simp] theorem omega_smul_right (a : Scalar) (u v : Plane) :
    omega u (a • v) = a * omega u v := by simp [omega]; ring

variable {F K : Type} [Fintype F] [AddCommGroup K] [Module Scalar K]

def correction (cycle : F → K) (a b : F → Plane) : K :=
  (2 : Scalar) • ∑ f, omega (a f) (b f) • cycle f

@[simp] theorem correction_self (cycle : F → K) (a : F → Plane) :
    correction cycle a a = 0 := by simp [correction]

@[simp] theorem correction_zero_left (cycle : F → K) (a : F → Plane) :
    correction cycle 0 a = 0 := by simp [correction]

@[simp] theorem correction_zero_right (cycle : F → K) (a : F → Plane) :
    correction cycle a 0 = 0 := by simp [correction]

@[simp] theorem correction_add_left (cycle : F → K) (a b c : F → Plane) :
    correction cycle (a + b) c = correction cycle a c + correction cycle b c := by
  simp [correction, add_smul, Finset.sum_add_distrib, smul_add]

@[simp] theorem correction_add_right (cycle : F → K) (a b c : F → Plane) :
    correction cycle a (b + c) = correction cycle a b + correction cycle a c := by
  simp [correction, add_smul, Finset.sum_add_distrib, smul_add]

@[simp] theorem correction_neg_left (cycle : F → K) (a b : F → Plane) :
    correction cycle (-a) b = -correction cycle a b := by
  simp [correction, Finset.sum_neg_distrib]

@[simp] theorem correction_neg_right (cycle : F → K) (a b : F → Plane) :
    correction cycle a (-b) = -correction cycle a b := by
  simp [correction, Finset.sum_neg_distrib]

@[ext]
structure H (cycle : F → K) where
  face : F → Plane
  flow : K

namespace H

variable (cycle : F → K)

instance instOne : One (H cycle) := ⟨⟨0, 0⟩⟩

instance instMul : Mul (H cycle) := ⟨fun x y =>
  ⟨x.face + y.face, x.flow + y.flow + correction cycle x.face y.face⟩⟩

instance instInv : Inv (H cycle) := ⟨fun x => ⟨-x.face, -x.flow⟩⟩

omit [Fintype F] [Module Scalar K] in
@[simp] theorem one_face : (1 : H cycle).face = 0 := rfl

omit [Fintype F] [Module Scalar K] in
@[simp] theorem one_flow : (1 : H cycle).flow = 0 := rfl

@[simp] theorem mul_face (x y : H cycle) : (x * y).face = x.face + y.face := rfl

@[simp] theorem mul_flow (x y : H cycle) :
    (x * y).flow = x.flow + y.flow + correction cycle x.face y.face := rfl

omit [Fintype F] [Module Scalar K] in
@[simp] theorem inv_face (x : H cycle) : x⁻¹.face = -x.face := rfl

omit [Fintype F] [Module Scalar K] in
@[simp] theorem inv_flow (x : H cycle) : x⁻¹.flow = -x.flow := rfl

instance instGroup : Group (H cycle) := Group.ofLeftAxioms
  (by intro x y z; ext <;> simp [add_assoc] ; abel)
  (by intro x; ext <;> simp)
  (by intro x; ext <;> simp)

def central (k : K) : H cycle := ⟨0,k⟩

@[simp] theorem central_mul (k l : K) : central cycle k * central cycle l = central cycle (k+l) := by
  ext <;> simp [central]

omit [Fintype F] [Module Scalar K] in
@[simp] theorem central_zero : central cycle (0 : K) = 1 := rfl

omit [Fintype F] [Module Scalar K] in
@[simp] theorem central_neg (k : K) : central cycle (-k) = (central cycle k)⁻¹ := by
  apply H.ext <;> simp [central]

def projectedAddSubgroup (S : Subgroup (H cycle)) : AddSubgroup (F → Plane) where
  carrier := {a | ∃ h ∈ S, h.face = a}
  zero_mem' := ⟨1, S.one_mem, rfl⟩
  add_mem' := by
    rintro a b ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x*y, S.mul_mem hx hy, rfl⟩
  neg_mem' := by
    rintro a ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, S.inv_mem hx, rfl⟩

def centralAddSubgroup (S : Subgroup (H cycle)) : AddSubgroup K where
  carrier := {k | central cycle k ∈ S}
  zero_mem' := S.one_mem
  add_mem' := by
    intro k l hk hl
    change central cycle (k+l) ∈ S
    simpa only [← central_mul] using S.mul_mem hk hl
  neg_mem' := by
    intro k hk
    change central cycle (-k) ∈ S
    simpa only [central_neg] using S.inv_mem hk

def projected (S : Subgroup (H cycle)) : Submodule Scalar (F → Plane) :=
  AddSubgroup.toZModSubmodule 3 (projectedAddSubgroup cycle S)

def centralPart (S : Subgroup (H cycle)) : Submodule Scalar K :=
  AddSubgroup.toZModSubmodule 3 (centralAddSubgroup cycle S)

@[simp] theorem mem_projected (S : Subgroup (H cycle)) (a : F → Plane) :
    a ∈ projected cycle S ↔ ∃ h ∈ S, h.face = a := Iff.rfl

@[simp] theorem mem_centralPart (S : Subgroup (H cycle)) (k : K) :
    k ∈ centralPart cycle S ↔ central cycle k ∈ S := Iff.rfl

def productEquiv : H cycle ≃ (F → Plane) × K where
  toFun x := (x.face,x.flow)
  invFun x := ⟨x.1,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instFinite [Finite K] : Finite (H cycle) :=
  Finite.of_equiv ((F → Plane) × K) (productEquiv cycle).symm

noncomputable def projectedLift (S : Subgroup (H cycle)) (a : projected cycle S) : H cycle :=
  Classical.choose a.property

theorem projectedLift_mem (S : Subgroup (H cycle)) (a : projected cycle S) :
    projectedLift cycle S a ∈ S := (Classical.choose_spec a.property).1

@[simp] theorem projectedLift_face (S : Subgroup (H cycle)) (a : projected cycle S) :
    (projectedLift cycle S a).face = a.val := (Classical.choose_spec a.property).2

theorem mul_inv_of_face_eq (x y : H cycle) (h : x.face = y.face) :
    x * y⁻¹ = central cycle (x.flow - y.flow) := by
  apply H.ext
  · simp [h, central]
  · simp [central, h, sub_eq_add_neg]

noncomputable def subgroupEquiv (S : Subgroup (H cycle)) :
    S ≃ projected cycle S × centralPart cycle S where
  toFun x := by
    let a : projected cycle S := ⟨x.val.face, x.val, x.property, rfl⟩
    refine (a, ⟨x.val.flow - (projectedLift cycle S a).flow, ?_⟩)
    rw [mem_centralPart, ← mul_inv_of_face_eq cycle x.val (projectedLift cycle S a)]
    · exact S.mul_mem x.property (S.inv_mem (projectedLift_mem cycle S a))
    · exact (projectedLift_face cycle S a).symm
  invFun p := ⟨central cycle p.2.val * projectedLift cycle S p.1,
    S.mul_mem ((mem_centralPart cycle S p.2.val).mp p.2.property) (projectedLift_mem cycle S p.1)⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply H.ext
    · simp [central]
    · simp [central]
  right_inv := by
    rintro ⟨a,k⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [central]
    · apply Subtype.ext
      let a' : projected cycle S := ⟨(central cycle k.val * projectedLift cycle S a).face,
        central cycle k.val * projectedLift cycle S a,
        S.mul_mem ((mem_centralPart cycle S k.val).mp k.property) (projectedLift_mem cycle S a), rfl⟩
      have h : a' = a := by
        apply Subtype.ext
        simp [a', central]
      change (central cycle k.val * projectedLift cycle S a).flow -
        (projectedLift cycle S a').flow = k.val
      rw [h]
      simp [central]

end H

def diagonalForm (weight : F → Scalar) : LinearMap.BilinForm Scalar (F → Plane) where
  toFun a := {
    toFun := fun b => ∑ f, weight f * omega (a f) (b f)
    map_add' := by intro b c; simp [mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro r b
      simp only [Pi.smul_apply, omega_smul_right, smul_eq_mul, RingHom.id_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      ring }
  map_add' := by
    intro a b
    ext c
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro r a
    ext b
    simp only [Pi.smul_apply, omega_smul_left, LinearMap.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    change (∑ f, weight f * (r * omega (a f) (b f))) =
      r * (∑ f, weight f * omega (a f) (b f))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    ring

@[simp] theorem diagonalForm_apply (weight : F → Scalar) (a b : F → Plane) :
    diagonalForm weight a b = ∑ f, weight f * omega (a f) (b f) := rfl

theorem mem_diagonalForm_ker (weight : F → Scalar) (a : F → Plane) :
    a ∈ (diagonalForm weight).ker ↔ ∀ f, weight f ≠ 0 → a f = 0 := by
  classical
  constructor
  · intro ha f hf
    have hzero : ∀ b, diagonalForm weight a b = 0 := by
      intro b
      exact LinearMap.congr_fun (LinearMap.mem_ker.mp ha) b
    have heval (b : Plane) : diagonalForm weight a (Pi.single f b) =
        weight f * omega (a f) b := by
      rw [diagonalForm_apply, Finset.sum_eq_single f]
      · simp
      · intro g _ hg
        simp [hg]
      · simp
    have hfst := hzero (Pi.single f (0,1))
    have hsnd := hzero (Pi.single f (1,0))
    simp only [heval, omega, mul_one, mul_zero, sub_zero, zero_sub, mul_neg, neg_eq_zero] at hfst hsnd
    apply Prod.ext
    · exact (mul_eq_zero.mp hfst).resolve_left hf
    · exact (mul_eq_zero.mp hsnd).resolve_left hf
  · intro ha
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro b
    change (∑ f, weight f * omega (a f) (b f)) = 0
    apply Finset.sum_eq_zero
    intro f _
    by_cases hf : weight f = 0
    · simp [hf]
    · simp [ha f hf]

noncomputable def diagonalKerEquiv (weight : F → Scalar) :
    (diagonalForm weight).ker ≃ₗ[Scalar] ({f : F // weight f = 0} → Plane) where
  toFun a f := a.val f.val
  invFun b := by
    classical
    refine ⟨fun f => if hf : weight f = 0 then b ⟨f,hf⟩ else 0, ?_⟩
    rw [mem_diagonalForm_ker]
    intro f hf
    simp [hf]
  left_inv := by
    intro a
    apply Subtype.ext
    funext f
    dsimp
    split_ifs with hf
    · rfl
    · exact ((mem_diagonalForm_ker weight a.val).mp a.property f hf).symm
  right_inv := by intro b; funext f; simp [f.property]
  map_add' := by intro a b; rfl
  map_smul' := by intro r a; rfl

end Support

end WitnessedSeparation

namespace WitnessedSeparation.Grid

abbrev Scalar := ZMod 3

abbrev Vertex (n : ℕ) := Fin (n+1) × Fin (n+1) × Fin (n+1)

abbrev EdgeX (n : ℕ) := Fin n × Fin (n+1) × Fin (n+1)

abbrev EdgeY (n : ℕ) := Fin (n+1) × Fin n × Fin (n+1)

abbrev EdgeZ (n : ℕ) := Fin (n+1) × Fin (n+1) × Fin n

abbrev Edge (n : ℕ) := EdgeX n ⊕ EdgeY n ⊕ EdgeZ n

abbrev FaceXY (n : ℕ) := Fin n × Fin n × Fin (n+1)

abbrev FaceXZ (n : ℕ) := Fin n × Fin (n+1) × Fin n

abbrev FaceYZ (n : ℕ) := Fin (n+1) × Fin n × Fin n

abbrev Face (n : ℕ) := FaceXY n ⊕ FaceXZ n ⊕ FaceYZ n

variable {n : ℕ}

def ex (i : Fin n) (j k : Fin (n+1)) : Edge n := .inl (i,j,k)

def ey (i : Fin (n+1)) (j : Fin n) (k : Fin (n+1)) : Edge n := .inr (.inl (i,j,k))

def ez (i j : Fin (n+1)) (k : Fin n) : Edge n := .inr (.inr (i,j,k))

def tail : Edge n → Vertex n
  | .inl (i,j,k) => (i.castSucc,j,k)
  | .inr (.inl (i,j,k)) => (i,j.castSucc,k)
  | .inr (.inr (i,j,k)) => (i,j,k.castSucc)

def head : Edge n → Vertex n
  | .inl (i,j,k) => (i.succ,j,k)
  | .inr (.inl (i,j,k)) => (i,j.succ,k)
  | .inr (.inr (i,j,k)) => (i,j,k.succ)

noncomputable def boundary : (Edge n → Scalar) →ₗ[Scalar] (Vertex n → Scalar) where
  toFun z := ∑ e, z e • (Pi.single (head e) (1 : Scalar) - Pi.single (tail e) 1)
  map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [smul_smul, Finset.smul_sum]

@[simp] theorem boundary_single (e : Edge n) (z : Scalar) :
    boundary (Pi.single e z) = Pi.single (head e) z - Pi.single (tail e) z := by
  classical
  change (∑ x, (Pi.single e z : Edge n → Scalar) x •
    (Pi.single (head x) 1 - Pi.single (tail x) 1)) = _
  rw [Finset.sum_eq_single e]
  · simp [smul_sub, ← Pi.single_smul]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

def cycle : Face n → Edge n → Scalar
  | .inl (i,j,k) => Pi.single (ex i j.castSucc k) 1 + Pi.single (ey i.succ j k) 1 -
      Pi.single (ex i j.succ k) 1 - Pi.single (ey i.castSucc j k) 1
  | .inr (.inl (i,j,k)) => Pi.single (ex i j k.castSucc) 1 + Pi.single (ez i.succ j k) 1 -
      Pi.single (ex i j k.succ) 1 - Pi.single (ez i.castSucc j k) 1
  | .inr (.inr (i,j,k)) => Pi.single (ey i j k.castSucc) 1 + Pi.single (ez i j.succ k) 1 -
      Pi.single (ey i j k.succ) 1 - Pi.single (ez i j.castSucc k) 1

@[simp] theorem boundary_cycle (f : Face n) : boundary (cycle f) = 0 := by
  rcases f with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals
    simp only [cycle, map_sub, map_add, boundary_single, head, tail, ex, ey, ez]
    abel

def gradient (φ : Vertex n → Scalar) (e : Edge n) : Scalar := φ (head e) - φ (tail e)

def curl (l : Edge n → Scalar) (f : Face n) : Scalar := ∑ e, cycle f e * l e

@[simp] theorem curl_sub (l r : Edge n → Scalar) (f : Face n) :
    curl (l-r) f = curl l f - curl r f := by
  simp [curl, mul_sub, Finset.sum_sub_distrib]

def prefixSum (l : Fin n → Scalar) (i : Fin (n+1)) : Scalar :=
  ∑ a : Fin n, if a.val < i.val then l a else 0

@[simp] theorem prefix_zero (l : Fin n → Scalar) : prefixSum l 0 = 0 := by simp [prefixSum]

def phi1 (l : Edge n → Scalar) (v : Vertex n) : Scalar :=
  prefixSum (fun a => l (ex a v.2.1 v.2.2)) v.1

def residual1 (l : Edge n → Scalar) : Edge n → Scalar := l - gradient (phi1 l)

def phi2 (l : Edge n → Scalar) (i0 : Fin (n+1)) (v : Vertex n) : Scalar :=
  prefixSum (fun b => residual1 l (ey i0 b v.2.2)) v.2.1

def residual2 (l : Edge n → Scalar) (i0 : Fin (n+1)) : Edge n → Scalar :=
  residual1 l - gradient (phi2 l i0)

def phi3 (l : Edge n → Scalar) (i0 : Fin (n+1)) (v : Vertex n) : Scalar :=
  prefixSum (fun c => residual2 l i0 (ez i0 0 c)) v.2.2

def residual (l : Edge n → Scalar) (i0 : Fin (n+1)) : Edge n → Scalar :=
  residual2 l i0 - gradient (phi3 l i0)

def nonzeroSet {ι : Type*} [Fintype ι] (f : ι → Scalar) : Finset ι :=
  Finset.univ.filter (fun i => f i ≠ 0)

@[simp] theorem mem_nonzeroSet {ι : Type*} [Fintype ι] (f : ι → Scalar) (i : ι) :
    i ∈ nonzeroSet f ↔ f i ≠ 0 := by simp [nonzeroSet]

def badXY (l : Edge n → Scalar) : Finset (FaceXY n) :=
  nonzeroSet (fun f => curl l (.inl f))

def badXZ (l : Edge n → Scalar) : Finset (FaceXZ n) :=
  nonzeroSet (fun f => curl l (.inr (.inl f)))

def badYZ (l : Edge n → Scalar) : Finset (FaceYZ n) :=
  nonzeroSet (fun f => curl l (.inr (.inr f)))

def badSlice (l : Edge n → Scalar) (i : Fin (n+1)) : Finset (Fin n × Fin n) :=
  nonzeroSet (fun f => curl l (.inr (.inr (i,f))))

end WitnessedSeparation.Grid

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_GridAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WitnessedSeparation.Grid

noncomputable section

open Support

def pairing {ι : Type*} [Fintype ι] (l : ι → Scalar) : (ι → Scalar) →ₗ[Scalar] Scalar where
  toFun z := ∑ e, l e * z e
  map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem pairing_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : ι → Scalar) (e : ι) (z : Scalar) : pairing l (Pi.single e z) = l e * z := by
  classical
  change (∑ j, l j * (Pi.single e z : ι → Scalar) j) = _
  simp only [Pi.single_apply, mul_ite, mul_zero]
  simp

variable {n : ℕ}

abbrev FlowSpace (n : ℕ) := (boundary (n := n)).ker

def flowCycle (f : Face n) : FlowSpace n := ⟨cycle f, boundary_cycle f⟩

abbrev BoxGroup (n : ℕ) := Support.H (flowCycle (n := n))

def faceCodim (S : Subgroup (BoxGroup n)) : ℕ :=
  Module.finrank Scalar (Face n → Support.Plane) -
    Module.finrank Scalar (Support.H.projected flowCycle S)

def flowCodim (S : Subgroup (BoxGroup n)) : ℕ :=
  Module.finrank Scalar (FlowSpace n) -
    Module.finrank Scalar (Support.H.centralPart flowCycle S)

end



open Support

variable {n : ℕ}

theorem sum_subtype_zero {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (p : ι → Prop) [DecidablePred p] (f : ι → M) (h : ∀ i, ¬ p i → f i = 0) :
    (∑ i : {x // p x}, f i.val) = ∑ i, f i := by
  have hz : (∑ i : {x // ¬ p x}, f i.val) = 0 :=
    Finset.sum_eq_zero (fun i _ => h i.val i.property)
  simpa only [hz,add_zero] using Fintype.sum_subtype_add_sum_subtype p f

abbrev EdgeFaces (e : Edge n) := {f : Face n // cycle f e ≠ 0}

def localCycle (e : Edge n) (f : EdgeFaces e) : Scalar := cycle f.val e

abbrev LocalGroup (e : Edge n) := Support.H (localCycle e)

noncomputable def restrictGroup (e : Edge n) : BoxGroup n →* LocalGroup e where
  toFun g := ⟨fun f => g.face f.val, g.flow.val e⟩
  map_one' := rfl
  map_mul' := by
    intro g h
    apply Support.H.ext
    · rfl
    · simp only [Support.H.mul_flow, Submodule.coe_add, Pi.add_apply]
      congr 1
      simp only [Support.correction, Submodule.coe_smul, Submodule.coe_sum,
        Pi.smul_apply, Finset.sum_apply, smul_eq_mul, flowCycle, localCycle]
      congr 1
      exact (sum_subtype_zero _ _ (fun f hf => by simp_all)).symm

@[simp] theorem restrictGroup_face (g : BoxGroup n) (e : Edge n) (f : EdgeFaces e) :
    (restrictGroup e g).face f = g.face f.val := rfl

@[simp] theorem restrictGroup_flow (g : BoxGroup n) (e : Edge n) :
    (restrictGroup e g).flow = g.flow.val e := rfl

def incident (v : Vertex n) (e : Edge n) : Prop := head e = v ∨ tail e = v

instance instDecidableRelVertexEdgeIncident : DecidableRel (incident (n := n)) := fun v e =>
  inferInstanceAs (Decidable (head e = v ∨ tail e = v))

abbrev IncidentEdges (v : Vertex n) := {e : Edge n // incident v e}

noncomputable def epsilon (v : Vertex n) (e : Edge n) : Scalar :=
  (if head e = v then 1 else 0) - (if tail e = v then 1 else 0)

theorem boundary_eval (z : Edge n → Scalar) (v : Vertex n) :
    boundary z v = ∑ e, epsilon v e * z e := by
  classical
  simp only [boundary, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro e _
  simp [epsilon, Pi.single_apply, eq_comm, mul_comm]

theorem epsilon_eq_zero (v : Vertex n) (e : Edge n) (h : ¬ incident v e) :
    epsilon v e = 0 := by
  classical
  simp only [incident, not_or] at h
  simp [epsilon,h.1,h.2]

theorem sum_incident (z : Edge n → Scalar) (v : Vertex n) :
    (∑ e : IncidentEdges v, epsilon v e.val * z e.val) = boundary z v := by
  classical
  rw [boundary_eval]
  exact sum_subtype_zero (incident v) (fun e => epsilon v e * z e)
    (fun e he => by rw [epsilon_eq_zero v e he,zero_mul])

abbrev LocalStates (v : Vertex n) := (e : IncidentEdges v) → LocalGroup e.val

def Compatible {v : Vertex n} (s : LocalStates v) : Prop :=
  ∀ (e e' : IncidentEdges v) (f : Face n) (h : cycle f e.val ≠ 0)
    (h' : cycle f e'.val ≠ 0),
    (s e).face ⟨f,h⟩ = (s e').face ⟨f,h'⟩

theorem compatible_iff_extend {v : Vertex n} (s : LocalStates v) :
    Compatible s ↔ ∃ u : Face n → Plane,
      ∀ (e : IncidentEdges v) (f : EdgeFaces e.val), (s e).face f = u f.val := by
  classical
  constructor
  · intro h
    let u (f : Face n) : Plane := if hh : ∃ e : IncidentEdges v, cycle f e.val ≠ 0
      then (s hh.choose).face ⟨f,hh.choose_spec⟩ else 0
    refine ⟨u,?_⟩
    intro e f
    have hh : ∃ e : IncidentEdges v, cycle f.val e.val ≠ 0 := ⟨e,f.property⟩
    simp only [u,dite_eq_left hh]
    exact h e hh.choose f.val f.property hh.choose_spec
  · rintro ⟨u,h⟩ e e' f hf hf'
    rw [h e ⟨f,hf⟩, h e' ⟨f,hf'⟩]

noncomputable def divergence {v : Vertex n} (s : LocalStates v) : Scalar :=
  ∑ e : IncidentEdges v, epsilon v e.val * (s e).flow

structure Configuration (b : Vertex n → Scalar) (v : Vertex n) where
  state : LocalStates v
  compatible : Compatible state
  charge : divergence state = b v

@[ext] theorem Configuration.ext {b : Vertex n → Scalar} {v : Vertex n}
    {s t : Configuration b v} (h : ∀ e, s.state e = t.state e) : s = t := by
  cases s; cases t
  congr
  exact funext h

noncomputable def actState {v : Vertex n} (g : BoxGroup n) (s : LocalStates v) :
    LocalStates v := fun e => restrictGroup e.val g * s e

theorem actState_compatible {v : Vertex n} (g : BoxGroup n) (s : LocalStates v)
    (hs : Compatible s) : Compatible (actState g s) := by
  intro e e' f hf hf'
  simp only [actState, Support.H.mul_face, Pi.add_apply, restrictGroup_face]
  rw [hs e e' f hf hf']

theorem actState_divergence {v : Vertex n} (g : BoxGroup n) (s : LocalStates v)
    (hs : Compatible s) : divergence (actState g s) = divergence s := by
  classical
  obtain ⟨u,hu⟩ := (compatible_iff_extend s).mp hs
  have hc (e : IncidentEdges v) : Support.correction (localCycle e.val)
      (restrictGroup e.val g).face (s e).face =
        (Support.correction flowCycle g.face u).val e.val := by
    have heq : (s e).face = fun f : EdgeFaces e.val => u f.val := funext (hu e)
    rw [heq]
    simp only [Support.correction, Submodule.coe_smul, Submodule.coe_sum,
      Pi.smul_apply, Finset.sum_apply, smul_eq_mul, flowCycle, localCycle,
      restrictGroup_face]
    congr 1
    exact sum_subtype_zero (fun f : Face n => cycle f e.val ≠ 0)
      (fun f => omega (g.face f) (u f) * cycle f e.val)
      (fun f hf => by push Not at hf; simp only [hf,mul_zero])
  simp only [divergence, actState, Support.H.mul_flow, restrictGroup_flow,
    mul_add, Finset.sum_add_distrib]
  simp_rw [hc]
  rw [sum_incident, sum_incident]
  have hg := congrFun g.flow.property v
  have hb := congrFun (Support.correction flowCycle g.face u).property v
  simp only [Pi.zero_apply] at hg hb
  simp [hg,hb]

noncomputable def actConfiguration {b : Vertex n → Scalar} {v : Vertex n}
    (g : BoxGroup n) (s : Configuration b v) : Configuration b v where
  state := actState g s.state
  compatible := actState_compatible g s.state s.compatible
  charge := by rw [actState_divergence g s.state s.compatible, s.charge]

noncomputable instance instMulActionBoxGroupConfiguration {b : Vertex n → Scalar} {v : Vertex n} :
    MulAction (BoxGroup n) (Configuration b v) where
  smul := actConfiguration
  one_smul s := by
    apply Configuration.ext
    intro e
    change restrictGroup e.val (1 : BoxGroup n) * s.state e = s.state e
    simp only [map_one,one_mul]
  mul_smul g h s := by
    apply Configuration.ext
    intro e
    change restrictGroup e.val (g*h) * s.state e =
      restrictGroup e.val g * (restrictGroup e.val h * s.state e)
    simp only [map_mul,mul_assoc]

abbrev Atom (b : Vertex n → Scalar) := (Σ e : Edge n, LocalGroup e) ⊕
  (Σ v : Vertex n, Configuration b v)

noncomputable def actAtom {b : Vertex n → Scalar} (g : BoxGroup n) : Atom b → Atom b
  | .inl ⟨e,s⟩ => .inl ⟨e, restrictGroup e g * s⟩
  | .inr ⟨v,s⟩ => .inr ⟨v,g • s⟩

noncomputable instance instMulActionBoxGroupAtom {b : Vertex n → Scalar} : MulAction (BoxGroup n) (Atom b) where
  smul := actAtom
  one_smul x := by
    change actAtom 1 x = x
    cases x with
    | inl x => rcases x with ⟨e,s⟩; simp only [actAtom,map_one,one_mul]
    | inr x => rcases x with ⟨v,s⟩; simp only [actAtom,one_smul]
  mul_smul g h x := by
    change actAtom (g*h) x = actAtom g (actAtom h x)
    cases x with
    | inl x => rcases x with ⟨e,s⟩; simp only [actAtom,map_mul,mul_assoc]
    | inr x => rcases x with ⟨v,s⟩; simp only [actAtom,mul_smul]

end WitnessedSeparation.Grid

namespace WitnessedSeparation.Grid

open Support

variable {n : ℕ} {b : Vertex n → Scalar}

instance instFiniteConfiguration {v : Vertex n} : Finite (Configuration b v) :=
  Finite.of_injective (fun s : Configuration b v => s.state)
    (fun _s _t h => Configuration.ext (fun e => congrFun h e))

noncomputable instance instFintypeConfiguration {v : Vertex n} : Fintype (Configuration b v) := Fintype.ofFinite _

inductive AtomRelation (b : Vertex n → Scalar) : Symbol → Atom b → Atom b → Prop
  | ed (e : Edge n) (s : LocalGroup e) :
      AtomRelation b .Ed (.inl ⟨e,s⟩) (.inl ⟨e,s⟩)
  | cf (v : Vertex n) (s : Configuration b v) :
      AtomRelation b .Cf (.inr ⟨v,s⟩) (.inr ⟨v,s⟩)
  | eb (e : Edge n) (s t : LocalGroup e) :
      AtomRelation b .EB (.inl ⟨e,s⟩) (.inl ⟨e,t⟩)
  | vb (v : Vertex n) (s t : Configuration b v) :
      AtomRelation b .VB (.inr ⟨v,s⟩) (.inr ⟨v,t⟩)
  | inc (v : Vertex n) (s : Configuration b v) (e : IncidentEdges v) :
      AtomRelation b .I (.inr ⟨v,s⟩) (.inl ⟨e.val,s.state e⟩)
  | z (e : Edge n) (s t : LocalGroup e) (δ : Scalar) (h : (s⁻¹*t).flow = δ) :
      AtomRelation b (.Z δ) (.inl ⟨e,s⟩) (.inl ⟨e,t⟩)

theorem AtomRelation.map (g : BoxGroup n) {r : Symbol} {x y : Atom b}
    (h : AtomRelation b r x y) : AtomRelation b r (g • x) (g • y) := by
  cases h with
  | ed e s => exact .ed e _
  | cf v s => exact .cf v _
  | eb e s t => exact .eb e _ _
  | vb v s t => exact .vb v _ _
  | inc v s e => exact .inc v (g • s) e
  | z e s t δ h =>
    apply AtomRelation.z
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using h

theorem AtomRelation.map_iff (g : BoxGroup n) (r : Symbol) (x y : Atom b) :
    AtomRelation b r (g • x) (g • y) ↔ AtomRelation b r x y := by
  constructor
  · intro h
    simpa only [inv_smul_smul] using h.map g⁻¹
  · exact fun h => h.map g

noncomputable def atomInput (b : Vertex n → Scalar) : Input (Atom b) :=
  ⟨fun r x y => @decide (AtomRelation b r x y) (Classical.propDecidable _)⟩

end WitnessedSeparation.Grid

namespace WitnessedSeparation.Grid

variable {n : ℕ}

theorem head_ne_tail (e : Edge n) : head e ≠ tail e := by
  rcases e with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals simp only [head,tail]
  · intro h
    have hu := congrArg (fun v : Vertex n => v.1.val) h
    simp only [Fin.val_succ,Fin.val_castSucc] at hu
    omega
  · intro h
    have hu := congrArg (fun v : Vertex n => v.2.1.val) h
    simp only [Fin.val_succ,Fin.val_castSucc] at hu
    omega
  · intro h
    have hu := congrArg (fun v : Vertex n => v.2.2.val) h
    simp only [Fin.val_succ,Fin.val_castSucc] at hu
    omega

def edgeAxis : Edge n → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

theorem exists_head_or_tail (hn : 1 ≤ n) (v : Vertex n) :
    ∃ e : Edge n, head e = v ∨ tail e = v := by
  rcases v with ⟨i,j,k⟩
  by_cases hi : i.val = 0
  · refine ⟨ex ⟨0,by omega⟩ j k, Or.inr ?_⟩
    simp only [ex,tail,Prod.mk.injEq, and_true]
    apply Fin.ext
    exact hi.symm
  · refine ⟨ex ⟨i.val-1,by omega⟩ j k, Or.inl ?_⟩
    simp only [ex,head,Prod.mk.injEq,and_true]
    apply Fin.ext
    simp only [Fin.val_succ]
    omega

end WitnessedSeparation.Grid

namespace WitnessedSeparation.Grid

noncomputable instance instFintypeLocalGroup {n : ℕ} (e : Edge n) : Fintype (LocalGroup e) := Fintype.ofFinite _

noncomputable instance instFintypeAtom {n : ℕ} {b : Vertex n → Scalar} : Fintype (Atom b) := Fintype.ofFinite _

end WitnessedSeparation.Grid


namespace WitnessedSeparation

namespace Input

variable {A B : Type} [Fintype A] [Fintype B]

structure Iso (S : Input A) (T : Input B) extends A ≃ B where
  rel_eq : ∀ r x y, T.rel r (toEquiv x) (toEquiv y) = S.rel r x y

end Input

end WitnessedSeparation



namespace WitnessedSeparation.Grid

open Support

variable {n : ℕ} {b : Vertex n → Scalar}

noncomputable def actionIso (g : BoxGroup n) : (atomInput b).Iso (atomInput b) where
  toFun x := g • x
  invFun x := g⁻¹ • x
  left_inv := inv_smul_smul g
  right_inv := smul_inv_smul g
  rel_eq := by
    intro r x y
    exact congrArg (fun p => @decide p (Classical.propDecidable p))
      (propext (AtomRelation.map_iff g r x y))

def zeroEdgeAtom (b : Vertex n → Scalar) (e : Edge n) : Atom b := .inl ⟨e,1⟩

@[simp] theorem central_fix_zeroEdgeAtom_iff (k : FlowSpace n) (e : Edge n) :
    Support.H.central flowCycle k • zeroEdgeAtom b e = zeroEdgeAtom b e ↔ k.val e = 0 := by
  change (Sum.inl ⟨e,restrictGroup e (Support.H.central flowCycle k) * 1⟩ : Atom b) =
    (Sum.inl ⟨e,(1 : LocalGroup e)⟩ : Atom b) ↔ _
  simp only [mul_one, Sum.inl.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  constructor
  · intro h
    exact congrArg Support.H.flow h
  · intro h
    apply Support.H.ext
    · rfl
    · exact h

abbrev CentralGroup (n : ℕ) := Multiplicative (FlowSpace n)

def centralHom : CentralGroup n →* BoxGroup n where
  toFun k := Support.H.central flowCycle k.toAdd
  map_one' := rfl
  map_mul' k l := (Support.H.central_mul flowCycle k.toAdd l.toAdd).symm

noncomputable instance instMulActionCentralGroupAtom : MulAction (CentralGroup n) (Atom b) :=
  MulAction.compHom _ centralHom

@[simp] theorem central_smul_atom (k : CentralGroup n) (x : Atom b) :
    k • x = Support.H.central flowCycle k.toAdd • x := rfl

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Grid

noncomputable section

open Support

variable {n : ℕ} {b : Vertex n → Scalar}

@[simp] theorem atomInput_rel_true (r : Symbol) (x y : Atom b) :
    (atomInput b).rel r x y = true ↔ AtomRelation b r x y := by
  simp [atomInput]

@[simp] theorem epsilon_head (e : Edge n) : epsilon (head e) e = 1 := by
  simp [epsilon,Ne.symm (head_ne_tail e)]

@[simp] theorem epsilon_tail (e : Edge n) : epsilon (tail e) e = -1 := by
  simp [epsilon,head_ne_tail e]

theorem epsilon_sq (v : Vertex n) (e : IncidentEdges v) : epsilon v e.val ^ 2 = 1 := by
  rcases e with ⟨e,he⟩
  rcases he with h | h
  · subst v; simp
  · subst v; simp

def someConfiguration (hn : 1 ≤ n) (b : Vertex n → Scalar) (v : Vertex n) : Configuration b v := by
  classical
  let e : IncidentEdges v := ⟨(exists_head_or_tail hn v).choose,(exists_head_or_tail hn v).choose_spec⟩
  let states : LocalStates v := fun f => ⟨0,if f = e then epsilon v e.val * b v else 0⟩
  refine ⟨states,?_,?_⟩
  · intro f f' d hd hd'
    rfl
  · dsimp [divergence,states]
    simp only [mul_ite,mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ e]
    simp only [Finset.mem_univ,ite_true]
    rw [← mul_assoc,← pow_two,epsilon_sq,one_mul]

end

end WitnessedSeparation.Grid

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_Counting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical Support

variable {n : ℕ} {b b' b'' : Vertex n → Scalar}

def shiftLocal (e : Edge n) (z : Scalar) (s : LocalGroup e) : LocalGroup e :=
  Support.H.central (localCycle e) z * s

@[simp] theorem shiftLocal_face (e : Edge n) (z : Scalar) (s : LocalGroup e) :
    (shiftLocal e z s).face = s.face := by
  simp [shiftLocal,Support.H.mul_face,Support.H.central]

@[simp] theorem shiftLocal_flow (e : Edge n) (z : Scalar) (s : LocalGroup e) :
    (shiftLocal e z s).flow = z+s.flow := by
  simp [shiftLocal,Support.H.mul_flow,Support.H.central,Support.correction]

@[simp] theorem shiftLocal_zero (e : Edge n) (s : LocalGroup e) : shiftLocal e 0 s = s := by
  ext <;> simp

@[simp] theorem shiftLocal_add (e : Edge n) (z w : Scalar) (s : LocalGroup e) :
    shiftLocal e z (shiftLocal e w s) = shiftLocal e (z+w) s := by
  ext <;> simp [add_assoc]

def localShiftEquiv (e : Edge n) (z : Scalar) : LocalGroup e ≃ LocalGroup e where
  toFun := shiftLocal e z
  invFun := shiftLocal e (-z)
  left_inv := by intro s; simp
  right_inv := by intro s; simp

def shiftStates {v : Vertex n} (t : Edge n → Scalar) (s : LocalStates v) : LocalStates v :=
  fun e => shiftLocal e.val (t e.val) (s e)

theorem shiftStates_compatible {v : Vertex n} (t : Edge n → Scalar) (s : LocalStates v)
    (hs : Compatible s) : Compatible (shiftStates t s) := by
  intro e e' f hf hf'
  simpa only [shiftStates,shiftLocal_face] using hs e e' f hf hf'

theorem shiftStates_divergence {v : Vertex n} (t : Edge n → Scalar) (s : LocalStates v) :
    divergence (shiftStates t s) = boundary t v + divergence s := by
  simp only [divergence,shiftStates,shiftLocal_flow,mul_add,Finset.sum_add_distrib,sum_incident]

def Configuration.shift {v : Vertex n} (s : Configuration b v) (t : Edge n → Scalar)
    (h : boundary t v = b' v - b v) : Configuration b' v where
  state := shiftStates t s.state
  compatible := shiftStates_compatible t s.state s.compatible
  charge := by rw [shiftStates_divergence,s.charge,h]; abel

@[simp] theorem Configuration.shift_state {v : Vertex n} (s : Configuration b v)
    (t : Edge n → Scalar) (h : boundary t v = b' v - b v) (e : IncidentEdges v) :
    (s.shift t h).state e = shiftLocal e.val (t e.val) (s.state e) := rfl

def configShiftEquiv (v : Vertex n) (t : Edge n → Scalar)
    (h : boundary t v = b' v - b v) : Configuration b v ≃ Configuration b' v where
  toFun s := s.shift t h
  invFun s := s.shift (-t) (by simp only [map_neg,Pi.neg_apply,h]; abel)
  left_inv s := by apply Configuration.ext; intro e; simp
  right_inv s := by apply Configuration.ext; intro e; simp

inductive AtomShift (t : Edge n → Scalar) : Atom b → Atom b' → Prop
  | edge (e : Edge n) (s : LocalGroup e) :
      AtomShift t (.inl ⟨e,s⟩) (.inl ⟨e,shiftLocal e (t e) s⟩)
  | config (v : Vertex n) (s : Configuration b v) (h : boundary t v = b' v - b v) :
      AtomShift t (.inr ⟨v,s⟩) (.inr ⟨v,s.shift t h⟩)

def blockShiftEquiv (te : Edge n → Edge n → Scalar) (tv : Vertex n → Edge n → Scalar)
    (hv : ∀ v, boundary (tv v) v = b' v - b v) : Atom b ≃ Atom b' :=
  Equiv.sumCongr (Equiv.sigmaCongrRight fun e => localShiftEquiv e (te e e))
    (Equiv.sigmaCongrRight fun v => configShiftEquiv v (tv v) (hv v))

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Counting

noncomputable section

variable {R I A B : Type*}

structure Structure (R : Type*) (A : Type*) where
  rel : R → A → A → Prop

inductive Formula (R I : Type*)
  | falsum
  | equal (x y : I)
  | relation (r : R) (x y : I)
  | neg (φ : Formula R I)
  | and (φ ψ : Formula R I)
  | ex (x : I) (φ : Formula R I)
  | exact (x : I) (n : ℕ) (φ : Formula R I)
  deriving DecidableEq

namespace Formula

variable [DecidableEq I]

def free : Formula R I → Finset I
  | .falsum => ∅
  | .equal x y => {x,y}
  | .relation _ x y => {x,y}
  | .neg φ => φ.free
  | .and φ ψ => φ.free ∪ ψ.free
  | .ex x φ => φ.free.erase x
  | .exact x _ φ => φ.free.erase x

def eval (S : Structure R A) : Formula R I → (I → A) → Prop
  | .falsum, _ => False
  | .equal x y, v => v x = v y
  | .relation r x y, v => S.rel r (v x) (v y)
  | .neg φ, v => ¬ φ.eval S v
  | .and φ ψ, v => φ.eval S v ∧ ψ.eval S v
  | .ex x φ, v => ∃ a, φ.eval S (Function.update v x a)
  | .exact x n φ, v => Nonempty ({a : A // φ.eval S (Function.update v x a)} ≃ Fin n)

theorem eval_congr (S : Structure R A) (φ : Formula R I) {v w : I → A}
    (h : ∀ i ∈ φ.free, v i = w i) : φ.eval S v ↔ φ.eval S w := by
  induction φ generalizing v w with
  | falsum => rfl
  | equal x y => simp only [eval,h x (by simp [free]),h y (by simp [free])]
  | relation r x y => simp only [eval,h x (by simp [free]),h y (by simp [free])]
  | neg φ ih => exact not_congr (ih h)
  | and φ ψ ihφ ihψ =>
    apply and_congr
    · exact ihφ (fun i hi => h i (Finset.mem_union_left _ hi))
    · exact ihψ (fun i hi => h i (Finset.mem_union_right _ hi))
  | ex x φ ih =>
    apply exists_congr
    intro a
    apply ih
    intro i hi
    by_cases heq : i = x
    · subst i; simp
    · simp only [Function.update_of_ne heq]
      exact h i (Finset.mem_erase.mpr ⟨heq,hi⟩)
  | exact x n φ ih =>
    have heq : ∀ a, φ.eval S (Function.update v x a) ↔ φ.eval S (Function.update w x a) := by
      intro a
      apply ih
      intro i hi
      by_cases heq : i = x
      · subst i; simp
      · simp only [Function.update_of_ne heq]
        exact h i (Finset.mem_erase.mpr ⟨heq,hi⟩)
    let e := Equiv.subtypeEquivRight heq
    exact ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩, fun ⟨f⟩ => ⟨e.trans f⟩⟩

theorem eval_of_bijectionSystem (S : Structure R A) (T : Structure R B)
    (E : (I → A) → (I → B) → Prop)
    (hequal : ∀ v w, E v w → ∀ i j, (v i = v j ↔ w i = w j))
    (hrel : ∀ v w, E v w → ∀ r i j, S.rel r (v i) (v j) ↔ T.rel r (w i) (w j))
    (hext : ∀ v w, E v w → ∀ i, ∃ e : A ≃ B,
      ∀ a, E (Function.update v i a) (Function.update w i (e a)))
    (φ : Formula R I) : ∀ v w, E v w → (φ.eval S v ↔ φ.eval T w) := by
  induction φ with
  | falsum => intro v w h; rfl
  | equal i j => intro v w h; exact hequal v w h i j
  | relation r i j => intro v w h; exact hrel v w h r i j
  | neg φ ih => intro v w h; exact not_congr (ih v w h)
  | and φ ψ ihφ ihψ => intro v w h; exact and_congr (ihφ v w h) (ihψ v w h)
  | ex i φ ih =>
    intro v w h
    obtain ⟨e,he⟩ := hext v w h i
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨e a,(ih _ _ (he a)).mp ha⟩
    · rintro ⟨b,hb⟩
      obtain ⟨a,rfl⟩ := e.surjective b
      exact ⟨a,(ih _ _ (he a)).mpr hb⟩
  | exact i n φ ih =>
    intro v w h
    obtain ⟨e,he⟩ := hext v w h i
    let f : {a : A // φ.eval S (Function.update v i a)} ≃
        {b : B // φ.eval T (Function.update w i b)} :=
      e.subtypeEquiv (fun a => ih _ _ (he a))
    exact ⟨fun ⟨g⟩ => ⟨f.symm.trans g⟩, fun ⟨g⟩ => ⟨f.trans g⟩⟩

def conjoin : List (Formula R I) → Formula R I
  | [] => .neg .falsum
  | φ :: l => .and φ (conjoin l)

@[simp] theorem eval_conjoin (S : Structure R A) (l : List (Formula R I)) (v : I → A) :
    (conjoin l).eval S v ↔ ∀ φ ∈ l, φ.eval S v := by
  induction l with
  | nil => simp [conjoin,eval]
  | cons φ l ih => simp [conjoin,eval,ih]

end Formula

variable [DecidableEq I]

def typeOf (S : Structure R A) (names : Finset I) (v : I → A) : Set (Formula R I) :=
  {φ | φ.free ⊆ names ∧ φ.eval S v}

theorem typeOf_eq_iff (S : Structure R A) (T : Structure R B) (names : Finset I)
    (v : I → A) (w : I → B) : typeOf S names v = typeOf T names w ↔
      ∀ φ : Formula R I, φ.free ⊆ names → (φ.eval S v ↔ φ.eval T w) := by
  constructor
  · intro h φ hφ
    have heq := Set.ext_iff.mp h φ
    simpa only [typeOf,Set.mem_ofPred_eq,hφ,true_and] using heq
  · intro h
    ext φ
    exact and_congr_right (h φ)

end





noncomputable section

variable {R I A B : Type*} [DecidableEq I]

namespace Formula

def rename (e : I ≃ I) : Formula R I → Formula R I
  | .falsum => .falsum
  | .equal i j => .equal (e i) (e j)
  | .relation r i j => .relation r (e i) (e j)
  | .neg φ => .neg (φ.rename e)
  | .and φ ψ => .and (φ.rename e) (ψ.rename e)
  | .ex i φ => .ex (e i) (φ.rename e)
  | .exact i n φ => .exact (e i) n (φ.rename e)

@[simp] theorem free_rename (e : I ≃ I) (φ : Formula R I) :
    (φ.rename e).free = φ.free.map e.toEmbedding := by
  induction φ with
  | falsum => simp [rename, free]
  | equal i j => simp [rename, free]
  | relation r i j => simp [rename, free]
  | neg φ ih => simpa [rename, free] using ih
  | and φ ψ ihφ ihψ => simp [rename, free, ihφ, ihψ, Finset.map_union]
  | ex i φ ih => simp [rename, free, ih, Finset.map_erase]
  | exact i n φ ih => simp [rename, free, ih, Finset.map_erase]

@[simp] theorem eval_rename (S : Structure R A) (e : I ≃ I) (φ : Formula R I)
    (v : I → A) : (φ.rename e).eval S v ↔ φ.eval S (v ∘ e) := by
  induction φ generalizing v with
  | falsum => rfl
  | equal i j => rfl
  | relation r i j => rfl
  | neg φ ih => exact not_congr (ih v)
  | and φ ψ ihφ ihψ => exact and_congr (ihφ v) (ihψ v)
  | ex i φ ih =>
    simp only [rename,eval]
    apply exists_congr
    intro a
    rw [ih,Function.update_comp_eq_of_injective _ e.injective]
  | exact i n φ ih =>
    have h (a : A) : (φ.rename e).eval S (Function.update v (e i) a) ↔
        φ.eval S (Function.update (v ∘ e) i a) := by
      rw [ih,Function.update_comp_eq_of_injective _ e.injective]
    let f := Equiv.subtypeEquivRight h
    exact ⟨fun ⟨g⟩ => ⟨f.symm.trans g⟩, fun ⟨g⟩ => ⟨f.trans g⟩⟩

end Formula

theorem typeOf_congr (S : Structure R A) (names : Finset I) {v w : I → A}
    (h : ∀ i ∈ names, v i = w i) : typeOf S names v = typeOf S names w := by
  apply (typeOf_eq_iff _ _ _ _ _).mpr
  intro φ hf
  exact φ.eval_congr S (fun i hi => h i (hf hi))

section Tuple

variable {J J' : Type*} [Fintype J] [Fintype J']

def tupleNames (e : J ↪ I) : Finset I := Finset.univ.map e

omit [DecidableEq I] in
@[simp] theorem mem_tupleNames (e : J ↪ I) (i : I) :
    i ∈ tupleNames e ↔ ∃ j, e j = i := by simp [tupleNames]

def tupleAssignment [Nonempty A] (e : J ↪ I) (a : J → A) (i : I) : A :=
  if h : ∃ j, e j = i then a (Classical.choose h) else Classical.choice inferInstance

@[simp] theorem tupleAssignment_apply [Nonempty A] (e : J ↪ I) (a : J → A) (j : J) :
    tupleAssignment e a (e j) = a j := by
  classical
  rw [tupleAssignment,dite_eq_left ⟨j,rfl⟩]
  congr 1
  exact e.injective (Classical.choose_spec (show ∃ k, e k = e j from ⟨j,rfl⟩))

def tupleType [Nonempty A] (S : Structure R A) (e : J ↪ I) (a : J → A) :
    Set (Formula R I) := typeOf S (tupleNames e) (tupleAssignment e a)

theorem tupleType_assignment [Nonempty A] (S : Structure R A) (e : J ↪ I)
    (a : J → A) (v : I → A) (h : ∀ j, v (e j) = a j) :
    tupleType S e a = typeOf S (tupleNames e) v := by
  apply typeOf_congr
  intro i hi
  obtain ⟨j,rfl⟩ := (mem_tupleNames e i).mp hi
  rw [tupleAssignment_apply,h]

end Tuple

theorem eval_iso (S : Structure R A) (T : Structure R B) (e : A ≃ B)
    (he : ∀ r a b, S.rel r a b ↔ T.rel r (e a) (e b))
    (φ : Formula R I) (v : I → A) : φ.eval S v ↔ φ.eval T (e ∘ v) := by
  apply φ.eval_of_bijectionSystem S T (fun v w => ∀ i, w i = e (v i))
  · intro v w h i j
    rw [h i,h j]
    exact e.injective.eq_iff.symm
  · intro v w h r i j
    rw [h i,h j]
    exact he r (v i) (v j)
  · intro v w h i
    refine ⟨e,fun a j => ?_⟩
    by_cases hij : j = i
    · subst j; simp
    · simp only [Function.update_of_ne hij,h j]
  · intro i; rfl

theorem tupleType_iso {J : Type*} [Fintype J] [Nonempty A] [Nonempty B]
    (S : Structure R A) (T : Structure R B) (names : J ↪ I) (e : A ≃ B)
    (he : ∀ r a b, S.rel r a b ↔ T.rel r (e a) (e b)) (a : J → A) :
    tupleType S names a = tupleType T names (e ∘ a) := by
  rw [tupleType_assignment T names (e ∘ a) (e ∘ tupleAssignment names a)
    (fun j => by simp)]
  apply (typeOf_eq_iff _ _ _ _ _).mpr
  intro φ hφ
  exact eval_iso S T e he φ _

end

end WitnessedSeparation.Counting



namespace WitnessedSeparation.Grid

noncomputable section

open Classical Finset

variable {n : ℕ} {b b' : Vertex n → Scalar}

abbrev ClassLabel (n : ℕ) :=
  (Σ e : Edge n, EdgeFaces e → Support.Plane) ⊕
  (Σ v : Vertex n, (e : IncidentEdges v) → EdgeFaces e.val → Support.Plane)

instance instFintypeClassLabel : Fintype (ClassLabel n) := by
  letI : ∀ v : Vertex n, Finite ((e : IncidentEdges v) → EdgeFaces e.val → Support.Plane) :=
    fun v => inferInstance
  exact Fintype.ofFinite _

def classLabel : Atom b → ClassLabel n
  | .inl ⟨e,s⟩ => .inl ⟨e,s.face⟩
  | .inr ⟨v,s⟩ => .inr ⟨v,fun e => (s.state e).face⟩

def classIndex (x : Atom b) : Fin (Fintype.card (ClassLabel n)) :=
  Fintype.equivFin (ClassLabel n) (classLabel x)

inductive AnalysisSymbol
  | input (s : Symbol)
  | preorder
  | raw (δ : Scalar)
  deriving DecidableEq, Fintype

def rawDifference (b : Vertex n → Scalar) (δ : Scalar) : Atom b → Atom b → Prop
  | .inl ⟨e,s⟩, .inl ⟨f,t⟩ => e = f ∧ t.flow - s.flow = δ
  | _, _ => False

def analysisStructure (b : Vertex n → Scalar) : Counting.Structure AnalysisSymbol (Atom b) where
  rel r x y := match r with
    | .input s => AtomRelation b s x y
    | .preorder => classIndex x ≤ classIndex y
    | .raw δ => rawDifference b δ x y

@[simp] theorem classLabel_shiftLocal (e : Edge n) (s : LocalGroup e) (t : Scalar) :
    classLabel (b := b') (.inl ⟨e,shiftLocal e t s⟩) = classLabel (b := b) (.inl ⟨e,s⟩) := by
  simp [classLabel]

@[simp] theorem classLabel_shiftConfig (v : Vertex n) (s : Configuration b v)
    (t : Edge n → Scalar) (h : boundary t v = b' v-b v) :
    classLabel (.inr ⟨v,s.shift t h⟩) = classLabel (.inr ⟨v,s⟩) := by
  simp [classLabel]

def predecessors (x : Atom b) : Finset (Atom b) := univ.filter fun y => classIndex y < classIndex x

def classFormula {I : Type*} (x y : I) (h : ℕ) : Counting.Formula AnalysisSymbol I :=
  .exact y h (.and (.relation .preorder y x) (.neg (.relation .preorder x y)))

end





noncomputable section

open Classical Finset

variable {n : ℕ} {b b' : Vertex n → Scalar}

abbrev Block (n : ℕ) := Edge n ⊕ Vertex n

def atomBlock : Atom b → Block n
  | .inl ⟨e,_⟩ => .inl e
  | .inr ⟨v,_⟩ => .inr v

def blockEdges : Block n → Finset (Edge n)
  | .inl e => {e}
  | .inr v => univ.filter (incident v)

def touch (x : Atom b) : Finset (Edge n) := blockEdges (atomBlock x)

theorem touch_shift {t : Edge n → Scalar} {x : Atom b} {y : Atom b'}
    (h : AtomShift t x y) : touch x = touch y := by cases h <;> rfl

def touches {I : Type*} [DecidableEq I] (names : Finset I) (v : I → Atom b) : Finset (Edge n) :=
  names.biUnion (fun i => touch (v i))

end





noncomputable section

open Classical Finset

variable {n : ℕ} {b : Vertex n → Scalar}

def HasState (x : Atom b) (e : Edge n) (s : LocalGroup e) : Prop :=
  x = .inl ⟨e,s⟩ ∨ AtomRelation b .I x (.inl ⟨e,s⟩)

@[simp] theorem hasState_edge (f : Edge n) (s : LocalGroup f) (e : Edge n) (t : LocalGroup e) :
    HasState (b := b) (.inl ⟨f,s⟩) e t ↔ (⟨f,s⟩ : Σ e, LocalGroup e) = ⟨e,t⟩ := by
  constructor
  · rintro (h | h)
    · exact Sum.inl.inj h
    · cases h
  · exact fun h => Or.inl (congrArg Sum.inl h)

@[simp] theorem hasState_config (v : Vertex n) (s : Configuration b v)
    (e : Edge n) (t : LocalGroup e) :
    HasState (.inr ⟨v,s⟩) e t ↔ ∃ h : incident v e, s.state ⟨e,h⟩ = t := by
  constructor
  · rintro (h | h)
    · cases h
    · cases h with
      | inc v s e => exact ⟨e.property,rfl⟩
  · rintro ⟨h,rfl⟩
    exact Or.inr (.inc v s ⟨e,h⟩)

def stateAt (x : Atom b) (e : Edge n) (he : e ∈ touch x) : LocalGroup e := by
  cases x with
  | inl x =>
    rcases x with ⟨f,s⟩
    have hh : e = f := by simpa [touch,atomBlock,blockEdges] using he
    subst e
    exact s
  | inr x =>
    rcases x with ⟨v,s⟩
    exact s.state ⟨e,by simpa [touch,atomBlock,blockEdges] using he⟩

@[simp] theorem stateAt_edge (e : Edge n) (s : LocalGroup e)
    (he : e ∈ touch (b := b) (.inl ⟨e,s⟩)) : stateAt (.inl ⟨e,s⟩) e he = s := by
  simp [stateAt]

@[simp] theorem stateAt_config (v : Vertex n) (s : Configuration b v) (e : IncidentEdges v)
    (he : e.val ∈ touch (.inr ⟨v,s⟩)) : stateAt (.inr ⟨v,s⟩) e.val he = s.state e := rfl

abbrev Occurrences {J : Type*} (a : J → Atom b) := Σ j : J, {e : Edge n // e ∈ touch (a j)}

def occurrenceAtom {J : Type*} (a : J → Atom b) (o : Occurrences a) : Atom b :=
  .inl ⟨o.2.val,stateAt (a o.1) o.2.val o.2.property⟩

def Augment {J : Type*} (a : J → Atom b) : J ⊕ Occurrences a → Atom b :=
  Sum.elim a (occurrenceAtom a)

structure SameDiagram {J : Type*} (a a' : J → Atom b) : Prop where
  classes : ∀ j, classLabel (a j) = classLabel (a' j)
  equal : ∀ i j, a i = a j ↔ a' i = a' j
  relation : ∀ r i j, (analysisStructure b).rel r (a i) (a j) ↔
    (analysisStructure b).rel r (a' i) (a' j)

end





end WitnessedSeparation.Grid

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_Homogeneity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical Finset

variable {n : ℕ} {b : Vertex n → Scalar}

variable {J : Type*} [Fintype J]

def namesBelow {P : Type*} [Fintype P] {M : ℕ} (h : Fintype.card P < M) : P ↪ Fin M :=
  (Fintype.equivFin P).toEmbedding.trans (Fin.castLEEmb h.le)

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Projection

open Finset

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

def ind {α : Type*} [DecidableEq α] (S : Finset α) (a : α) : ℕ :=
  if a ∈ S then 1 else 0

end WitnessedSeparation.Projection



namespace WitnessedSeparation.BoxLines

open Finset

variable {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}

def projection (R : Finset (Fin (n+1) × J)) : Finset J := R.image Prod.snd

def fullLines (R : Finset (Fin (n+1) × J)) : Finset J :=
  univ.filter fun j => ∀ i, (i,j) ∈ R

def edgeBoundary (R : Finset (Fin (n+1) × J)) : Finset (Fin n × J) :=
  univ.filter fun p => ¬ ((p.1.castSucc,p.2) ∈ R ↔ (p.1.succ,p.2) ∈ R)

end WitnessedSeparation.BoxLines



namespace WitnessedSeparation.Grid

open Finset

variable {n : ℕ}

def edgeBoundary (R : Finset (Vertex n)) : Finset (Edge n) :=
  univ.filter fun e => ¬(tail e ∈ R ↔ head e ∈ R)

def swapXY (v : Vertex n) : Vertex n := (v.2.1,v.1,v.2.2)

def moveZ (v : Vertex n) : Vertex n := (v.2.2,v.1,v.2.1)

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Grid

noncomputable def boxConstant : ℝ := 1 - (2:ℝ)^(-(1:ℝ)/3)

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Flows

noncomputable section

open Classical

abbrev Scalar := ZMod 3

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def incidence (tail head : E → V) : (E → Scalar) →ₗ[Scalar] (V → Scalar) where
  toFun t := ∑ e, t e • (Pi.single (head e) 1 - Pi.single (tail e) 1)
  map_add' := by intros; simp [add_smul,Finset.sum_add_distrib]
  map_smul' := by intros; simp [smul_smul,Finset.smul_sum]

omit [Fintype V] in
@[simp] theorem incidence_single (tail head : E → V) (e : E) (z : Scalar) :
    incidence tail head (Pi.single e z) = Pi.single (head e) z - Pi.single (tail e) z := by
  change (∑ x, (Pi.single e z : E → Scalar) x •
    (Pi.single (head x) 1 - Pi.single (tail x) 1)) = _
  rw [Finset.sum_eq_single e]
  · simp [smul_sub,←Pi.single_smul]
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp

def edgeRelation (tail head : E → V) (T : Finset E) (x y : V) : Prop :=
  ∃ e, e ∉ T ∧ tail e = x ∧ head e = y

def connected (tail head : E → V) (T : Finset E) : Setoid V :=
  Relation.EqvGen.setoid (edgeRelation tail head T)

abbrev Component (tail head : E → V) (T : Finset E) := Quotient (connected tail head T)

def component (tail head : E → V) (T : Finset E) (v : V) : Finset V :=
  Finset.univ.filter fun w => (connected tail head T).r v w

variable (tail head : E → V) (T : Finset E)

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
@[simp] theorem mem_component (v w : V) : w ∈ component tail head T v ↔
    (connected tail head T).r v w := by simp [component]

end





noncomputable section

open Classical Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (tail head : E → V) (T : Finset E)

instance instFintypeComponent : Fintype (Component tail head T) := Fintype.ofFinite _

def cell (c : Component tail head T) : Finset V := component tail head T c.out

def quotientMap (v : V) : Component tail head T := Quotient.mk (connected tail head T) v

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
@[simp] theorem mem_cell (c : Component tail head T) (v : V) :
    v ∈ cell tail head T c ↔ quotientMap tail head T v = c := by
  rw [cell,mem_component]
  constructor
  · intro h
    exact (Quotient.sound h).symm.trans (Quotient.out_eq c)
  · intro h
    exact Quotient.exact ((Quotient.out_eq c).trans h.symm)

def edgeBoundary (U : Finset V) : Finset E := univ.filter fun e => ¬(tail e ∈ U ↔ head e ∈ U)

end

end WitnessedSeparation.Flows



namespace WitnessedSeparation.Flows

noncomputable section

open Classical Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (tail head : E → V)

def IsGiant (T : Finset E) (v : V) : Prop :=
  Fintype.card V < 2*(component tail head T v).card

end

end WitnessedSeparation.Flows



end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_SupportedForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical Finset

variable {n M : ℕ} {b b' : Vertex n → Scalar}

def GiantBound (n M : ℕ) : Prop :=
  ((12*(M:ℝ))/boxConstant)^((3:ℝ)/2) < ((n+1)^3:ℕ)

def CompatibleAssignment {I : Type*} [DecidableEq I] (names : Finset I)
    (a : I → Atom b) (a' : I → Atom b') : Prop :=
  ∃ t : Edge n → Scalar, ∃ w : Vertex n,
    Flows.IsGiant tail head (touches names a) w ∧ boundary t = b'-b-Pi.single w 1 ∧
    ∀ i ∈ names, AtomShift t (a i) (a' i)

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Forms

noncomputable section

open Classical

open Counting Hereditary

variable {R I J A B : Type*}

inductive Form (J L : Type*)
  | atom (j : J)
  | set (n : ℕ) (child : Fin n → Form J L) (label : Fin n → L)

namespace Form

variable [Fintype I] [Fintype J] [DecidableEq I]

variable [Fintype A] [Nonempty A]

def value (S : Structure R A) (e : J ⊕ J ↪ I) :
    Form J (Set (Formula R I)) → (J → A) → HF A
  | .atom j, a => Hereditary.atom (a j)
  | .set _n child label, a => Hereditary.ofFinset
      (Finset.univ.biUnion fun i =>
        (Finset.univ.filter fun b : J → A =>
          tupleType S e (Sum.elim b a) = label i).image (value S e (child i)))

omit [Fintype I] in
@[simp] theorem value_atom (S : Structure R A) (e : J ⊕ J ↪ I) (j : J) (a : J → A) :
    value S e (.atom j) a = Hereditary.atom (a j) := rfl

omit [Fintype I] in
@[simp] theorem value_set_isSet (S : Structure R A) (e : J ⊕ J ↪ I)
    (n : ℕ) (child : Fin n → Form J (Set (Formula R I))) (label : Fin n → Set (Formula R I))
    (a : J → A) : isSet (value S e (.set n child label) a) = true := rfl

omit [Fintype I] in
@[simp] theorem mem_value_set (S : Structure R A) (e : J ⊕ J ↪ I)
    (n : ℕ) (child : Fin n → Form J (Set (Formula R I))) (label : Fin n → Set (Formula R I))
    (a : J → A) (x : HF A) :
    x ∈ value S e (.set n child label) a ↔
      ∃ i b, tupleType S e (Sum.elim b a) = label i ∧ value S e (child i) b = x := by
  classical
  simp only [value,mem_ofFinset,Finset.mem_biUnion,Finset.mem_univ,true_and,
    Finset.mem_image,Finset.mem_filter,true_and]

omit [Fintype I] in

theorem value_iso [Fintype B] [Nonempty B]
    (S : Structure R A) (T : Structure R B) (e : J ⊕ J ↪ I) (f : A ≃ B)
    (hf : ∀ r a b, S.rel r a b ↔ T.rel r (f a) (f b))
    (φ : Form J (Set (Formula R I))) (a : J → A) :
    Hereditary.map f (value S e φ a) = value T e φ (f ∘ a) := by
  induction φ generalizing a with
  | atom j => rfl
  | set n child label ih =>
    apply Hereditary.ext_sets (by simp [value]) (by simp)
    intro x
    change x ∈ elements (Hereditary.map f (value S e (.set n child label) a)) ↔ _
    rw [Hereditary.elements_map]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨i,b,ht,rfl⟩ := (mem_value_set S e n child label a y).mp hy
      apply (mem_value_set T e n child label (f ∘ a) _).mpr
      refine ⟨i,f ∘ b,?_,(ih i b).symm⟩
      have heq : Sum.elim (f ∘ b) (f ∘ a) = f ∘ Sum.elim b a := by
        funext j; cases j <;> rfl
      rw [heq,← tupleType_iso S T e f hf,ht]
    · intro hx
      obtain ⟨i,b,ht,hx⟩ := (mem_value_set T e n child label (f ∘ a) x).mp hx
      let c := f.symm ∘ b
      have hc : f ∘ c = b := by funext j; simp [c]
      refine ⟨value S e (child i) c,?_,?_⟩
      · apply (mem_value_set S e n child label a _).mpr
        refine ⟨i,c,?_,rfl⟩
        rw [tupleType_iso S T e f hf]
        have heq : f ∘ Sum.elim c a = Sum.elim b (f ∘ a) := by
          funext j; cases j <;> simp [c]
        rw [heq,ht]
      · rw [ih,hc,hx]

end Form

def cross31 : J ⊕ J ↪ (J ⊕ J) ⊕ J where
  toFun := Sum.elim Sum.inr (fun j => Sum.inl (Sum.inl j))
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def cross42 : J ⊕ J ↪ ((J ⊕ J) ⊕ J) ⊕ J where
  toFun := Sum.elim Sum.inr (fun j => Sum.inl (Sum.inl (Sum.inr j)))
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def cross34 : J ⊕ J ↪ ((J ⊕ J) ⊕ J) ⊕ J where
  toFun := Sum.elim (fun j => Sum.inl (Sum.inr j)) Sum.inr
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

@[simp] theorem elim_comp_cross31 (a b c : J → A) :
    Sum.elim (Sum.elim a b) c ∘ cross31 = Sum.elim c a := by
  funext j; cases j <;> rfl

@[simp] theorem elim_comp_cross42 (a b c d : J → A) :
    Sum.elim (Sum.elim (Sum.elim a b) c) d ∘ cross42 = Sum.elim d b := by
  funext j; cases j <;> rfl

@[simp] theorem elim_comp_cross34 (a b c d : J → A) :
    Sum.elim (Sum.elim (Sum.elim a b) c) d ∘ cross34 = Sum.elim c d := by
  funext j; cases j <;> rfl


variable {G : Type*} [Group G] [MulAction G A]

variable [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A] {s : ℕ}

variable (S : Structure R A) (e2 : Fin s ⊕ Fin s ↪ I)

variable (hAut : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

open Form

include hAut in
omit [Fintype I] in
theorem value_smul (g : G) (φ : Form (Fin s) (Set (Formula R I))) (a : Fin s → A) :
    g • value S e2 φ a = value S e2 φ (fun i => g • a i) := by
  exact value_iso S S e2 (MulAction.toPerm g) (fun r a b => (hAut g r a b).symm) φ a

include hAut in
omit [Fintype I] in
theorem value_supported (φ : Form (Fin s) (Set (Formula R I))) (a : Fin s → A) :
    Supports (G := G) a (value S e2 φ a) := by
  intro g hg
  rw [value_smul S e2 hAut]
  exact congrArg (value S e2 φ) (funext hg)

omit [Fintype A] [Nonempty A] in
theorem hereditary_intro (x : HF A) (hx : Supported (G := G) s x)
    (hm : ∀ y ∈ x, HereditarilySupported (G := G) s y) :
    HereditarilySupported (G := G) s x := by
  intro y hy
  cases hy with
  | refl => exact hx
  | tail hpath hstep => exact hm _ hstep _ hpath

include hAut in
omit [Fintype I] in
theorem value_hereditarily_supported (φ : Form (Fin s) (Set (Formula R I)))
    (a : Fin s → A) : HereditarilySupported (G := G) s (value S e2 φ a) := by
  induction φ generalizing a with
  | atom i =>
    apply hereditary_intro _ ⟨a,value_supported S e2 hAut _ a⟩
    intro y hy
    exact (not_mem_atom y (a i) hy).elim
  | set n child label ih =>
    apply hereditary_intro _ ⟨a,value_supported S e2 hAut _ a⟩
    intro y hy
    obtain ⟨i,b,ht,rfl⟩ := (mem_value_set S e2 n child label a y).mp hy
    exact ih i b


end

end WitnessedSeparation.Forms



namespace WitnessedSeparation.Counting

noncomputable section

open Classical

variable {R I J A B : Type*} [DecidableEq I]

def triangular {X Y : Type*} (e : X ≃ Y) (f : X → A ≃ B) : X × A ≃ Y × B where
  toFun p := (e p.1, f p.1 p.2)
  invFun p := (e.symm p.1, (f (e.symm p.1)).symm p.2)
  left_inv p := by simp
  right_inv p := by simp

def snocTuple {n : ℕ} (a : Fin n → A) (x : A) : Fin (n+1) → A :=
  Fin.lastCases x a

@[simp] theorem snocTuple_castSucc {n : ℕ} (a : Fin n → A) (x : A) (i : Fin n) :
    snocTuple a x i.castSucc = a i := by simp [snocTuple]

@[simp] theorem snocTuple_last {n : ℕ} (a : Fin n → A) (x : A) :
    snocTuple a x (Fin.last n) = x := by simp [snocTuple]

def snocEquiv (n : ℕ) : (Fin (n+1) → A) ≃ (Fin n → A) × A where
  toFun a := (fun i => a i.castSucc, a (Fin.last n))
  invFun p := snocTuple p.1 p.2
  left_inv a := by
    funext i
    induction i using Fin.lastCases <;> simp
  right_inv p := by ext <;> simp

def appendPosition (J : Type*) (n : ℕ) : (J ⊕ Fin n) ⊕ Unit ≃ J ⊕ Fin (n+1) where
  toFun := Sum.elim (Sum.elim Sum.inl (fun i => Sum.inr i.castSucc)) (fun _ => Sum.inr (Fin.last n))
  invFun := Sum.elim (fun j => Sum.inl (Sum.inl j))
    (Fin.lastCases (Sum.inr ()) (fun i => Sum.inl (Sum.inr i)))
  left_inv p := by rcases p with (j|i)|u <;> simp
  right_inv p := by
    rcases p with j|i
    · rfl
    · induction i using Fin.lastCases <;> simp


end

end WitnessedSeparation.Counting



namespace WitnessedSeparation.Forms

noncomputable section

open Classical Counting Hereditary

open scoped BigOperators

variable {R I A B P : Type*} [Fintype I] [DecidableEq I]

variable [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] [Fintype P]

variable {s : ℕ}

def Molecules (S : Structure R A) (ep : P ⊕ Fin s ↪ I)
    (p : P → A) (τ : Set (Formula R I)) :=
  {a : Fin s → A // tupleType S ep (Sum.elim p a) = τ}

instance instFintypeMolecules (S : Structure R A) (ep : P ⊕ Fin s ↪ I)
    (p : P → A) (τ : Set (Formula R I)) : Fintype (Molecules S ep p τ) :=
  inferInstanceAs (Fintype {a : Fin s → A // tupleType S ep (Sum.elim p a) = τ})

def labelValues (S : Structure R A) (ep : P ⊕ Fin s ↪ I)
    (e2 : Fin s ⊕ Fin s ↪ I) (p : P → A) (τ : Set (Formula R I))
    (φ : Form (Fin s) (Set (Formula R I))) : Set (HF A) :=
  Set.range (fun a : Molecules S ep p τ => Form.value S e2 φ a.1)

instance instFintypeElemHFLabelValues (S : Structure R A) (ep : P ⊕ Fin s ↪ I)
    (e2 : Fin s ⊕ Fin s ↪ I) (p : P → A) (τ : Set (Formula R I))
    (φ : Form (Fin s) (Set (Formula R I))) : Fintype (labelValues S ep e2 p τ φ) :=
  (Set.finite_range _).fintype

section Group

variable {G : Type*} [Group G] [MulAction G A]

variable (S : Structure R A) (ep : P ⊕ Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)

variable (hAut : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

variable (p : P → A) (τ : Set (Formula R I))

include hAut in
omit [Fintype I] [Fintype A] in
theorem mol_type_smul (g : G) (hp : ∀ i, g • p i = p i) (a : Fin s → A) :
    tupleType S ep (Sum.elim p (fun i => g • a i)) = tupleType S ep (Sum.elim p a) := by
  have hh := tupleType_iso S S ep (MulAction.toPerm g) (fun r a b => (hAut g r a b).symm)
    (Sum.elim p a)
  have hh' : (MulAction.toPerm g) ∘ Sum.elim p a = Sum.elim p (fun i => g • a i) := by
    funext i; rcases i with i|i
    · exact hp i
    · rfl
  rw [hh'] at hh
  exact hh.symm

def moleculesPerm (g : G) (hp : ∀ i, g • p i = p i) :
    Molecules S ep p τ ≃ Molecules S ep p τ :=
  (Equiv.piCongrRight (fun _ : Fin s => MulAction.toPerm g)).subtypeEquiv
    (fun a => by
      change tupleType S ep (Sum.elim p a) = τ ↔
        tupleType S ep (Sum.elim p (fun i => g • a i)) = τ
      rw [mol_type_smul S ep hAut p g hp a])

end Group


variable (S : Structure R A) (T : Structure R B)

variable (ep : P ⊕ Fin s ↪ I) (epp : (P ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e2 : Fin s ⊕ Fin s ↪ I)

variable (e3 : (Fin s ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e4 : ((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s ↪ I)

def skipMiddle : P ⊕ Fin s ↪ (P ⊕ Fin s) ⊕ Fin s :=
  Function.Embedding.sumMap Function.Embedding.inl (Function.Embedding.refl _)

def lastTwo : Fin s ⊕ Fin s ↪ (P ⊕ Fin s) ⊕ Fin s :=
  Function.Embedding.sumMap Function.Embedding.inr (Function.Embedding.refl _)

omit [Fintype A] [Nonempty A] [Fintype P] in
@[simp] theorem elim_skipMiddle (p : P → A) (a b : Fin s → A) :
    (Sum.elim (Sum.elim p a) b) ∘ skipMiddle = Sum.elim p b := by
  funext j; cases j <;> rfl

omit [Fintype A] [Nonempty A] [Fintype P] in
@[simp] theorem elim_lastTwo (p : P → A) (a b : Fin s → A) :
    (Sum.elim (Sum.elim p a) b) ∘ lastTwo = Sum.elim a b := by
  funext j; cases j <;> rfl


end

end WitnessedSeparation.Forms



namespace WitnessedSeparation

noncomputable section

open Classical

def cellSetoid {L X : Type*} (C : L → Set X) : Setoid L :=
  ⟨fun l k => C l = C k,⟨fun _ => rfl,Eq.symm,Eq.trans⟩⟩

end

end WitnessedSeparation

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_FormTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedSeparation.Forms

noncomputable section

open Classical Counting Hereditary

variable {R I A B P G H : Type*}

variable [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]

variable [Nonempty A] [Nonempty B] [Fintype P]

variable [Group G] [MulAction G A] [Group H] [MulAction H B]

variable {s : ℕ}

abbrev Domain (G : Type*) [Group G] [MulAction G A] (s : ℕ) :=
  {x : HF A // HereditarilySupported (G := G) s x}

def Cell (S : Structure R A) (ep : P ⊕ Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)
    (p : P → A) (φ : Form (Fin s) (Set (Formula R I))) (τ : Set (Formula R I)) :
    Set (Domain (A := A) G s) :=
  {x | x.1 ∈ labelValues S ep e2 p τ φ}

variable (S : Structure R A) (T : Structure R B)

variable (ep : P ⊕ Fin s ↪ I) (epp : (P ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e2 : Fin s ⊕ Fin s ↪ I) (e3 : (Fin s ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e4 : ((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s ↪ I)

variable (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

variable (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)

def cellEquiv (p : P → A) (φ : Form (Fin s) (Set (Formula R I))) (τ : Set (Formula R I)) :
    Cell (G := G) S ep e2 p φ τ ≃ labelValues S ep e2 p τ φ :=
  Equiv.subtypeSubtypeEquivSubtype
    (p := HereditarilySupported (G := G) s)
    (q := fun x => x ∈ labelValues S ep e2 p τ φ) (fun hx => by
    obtain ⟨a,rfl⟩ := hx
    exact value_hereditarily_supported S e2 hAutA φ a.1)

end





noncomputable section

open Classical Counting Hereditary

variable {R I A B V G H : Type*}

variable [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]

variable [Nonempty A] [Nonempty B] [Fintype V] [DecidableEq V]

variable [Group G] [MulAction G A] [Group H] [MulAction H B]

variable {s : ℕ}

inductive HFRelation (R : Type*)
  | mem | atom | base (r : R)

def hfStructure (S : Structure R A) : Structure (HFRelation R) (Domain (A := A) G s) where
  rel
    | .mem, x, y => x.1 ∈ y.1
    | .atom, x, _ => isSet x.1 = false
    | .base r, x, y => ∃ a b, x.1 = Hereditary.atom a ∧ y.1 = Hereditary.atom b ∧ S.rel r a b

def Represented (S : Structure R A) (T : Structure R B)
    (ef : V × Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)
    (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s) : Prop :=
  ∃ φ : V → Form (Fin s) (Set (Formula R I)), ∃ a : V × Fin s → A,
    ∃ b : V × Fin s → B,
      (∀ i, Form.value S e2 (φ i) (fun j => a (i,j)) = (v i).1) ∧
      (∀ i, Form.value T e2 (φ i) (fun j => b (i,j)) = (w i).1) ∧
      tupleType S ef a = tupleType T ef b

def twoBlocks (i j : V) (h : i ≠ j) : Fin s ⊕ Fin s ↪ V × Fin s where
  toFun := Sum.elim (Prod.mk i) (Prod.mk j)
  inj' := by
    intro a b hab
    cases a <;> cases b <;> simp only [Sum.elim_inl,Sum.elim_inr,Prod.mk.injEq] at hab
    · congr 1; exact hab.2
    · exact (h hab.1).elim
    · exact (h hab.1.symm).elim
    · congr 1; exact hab.2

omit [Fintype A] [Nonempty A] [Fintype V] [DecidableEq V] in
@[simp] theorem comp_twoBlocks (i j : V) (h : i ≠ j) (a : V × Fin s → A) :
    a ∘ twoBlocks i j h = Sum.elim (fun k => a (i,k)) (fun k => a (j,k)) := by
  funext x; cases x <;> rfl

def splitBlock (i : V) : ({j : V // j ≠ i} × Fin s) ⊕ Fin s ≃ V × Fin s where
  toFun := Sum.elim (fun x => (x.1.1,x.2)) (fun j => (i,j))
  invFun := fun x => if h : x.1 = i then .inr x.2 else .inl (⟨x.1,h⟩,x.2)
  left_inv := by
    intro x; cases x with
    | inl x => simp [x.1.2]
    | inr j => simp
  right_inv := by
    intro x; by_cases h : x.1 = i
    · simp [h]; exact Prod.ext h.symm rfl
    · simp [h]

variable (S : Structure R A) (T : Structure R B)

variable (ef : V × Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)

variable (e3 : (Fin s ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e4 : ((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s ↪ I)

omit [Fintype V] in
@[simp] theorem splitBlock_symm_new (i : V) (k : Fin s) :
    (splitBlock (s := s) i).symm (i,k) = .inr k := by simp [splitBlock]

omit [Fintype V] in
@[simp] theorem splitBlock_symm_old (i j : V) (h : j ≠ i) (k : Fin s) :
    (splitBlock (s := s) i).symm (j,k) = .inl (⟨j,h⟩,k) := by simp [splitBlock,h]

variable (eplus : (V × Fin s) ⊕ Fin s ↪ I)

variable (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

variable (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)

def namesOfCard {J : Type*} [Fintype J] {M : ℕ} (h : Fintype.card J ≤ M) : J ↪ Fin M :=
  (Fintype.equivFin J).toEmbedding.trans (Fin.castLEEmb h)

def HomogeneousThrough (S : Structure R A) (G : Type*) [Group G] [MulAction G A]
    (M r : ℕ) : Prop :=
  ∀ k ≤ r, ∀ e : Fin k ↪ Fin M, ∀ a b : Fin k → A,
    tupleType S e a = tupleType S e b → ∃ g : G, ∀ j, g • a j = b j

end

end WitnessedSeparation.Forms



namespace WitnessedSeparation.Grid

open Support Hereditary

noncomputable section

variable {n : ℕ} {b : Vertex n → Scalar}

@[simp] theorem central_smul_HF (k : CentralGroup n) (x : HF (Atom b)) :
    k • x = centralHom k • x := rfl

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Interpretations

structure Structure (R : Type) where
  Carrier : Type
  finite : Fintype Carrier
  rel : R → Carrier → Carrier → Bool

attribute [instance] Structure.finite

end WitnessedSeparation.Interpretations



end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_CountingTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedSeparation.HFCoding

noncomputable section

open Classical Finset Hereditary Counting

variable {A R : Type} {d : Set (HF A)}

abbrev Domain (d : Set (HF A)) := {x : HF A // x ∈ d}

variable (hd : ∀ x ∈ d, ∀ y, y ∈ x → y ∈ d)

variable (S : Counting.Structure R (Domain d)) {m : ℕ}

def SingletonTest (u a : Domain d) : Prop :=
  isSet u.val = true ∧ ∀ w : Domain d, w.val ∈ u.val ↔ w = a

def DoubleTest (u a b : Domain d) : Prop :=
  isSet u.val = true ∧ ∀ w : Domain d, w.val ∈ u.val ↔ w = a ∨ w = b

include hd

theorem singletonTest_iff (u a : Domain d) : SingletonTest u a ↔ u.val = Hereditary.singleton a.val := by
  constructor
  · rintro ⟨hu,h⟩
    apply ext_sets hu (isSet_ofFinset _)
    intro w
    change w ∈ u.val ↔ w ∈ Hereditary.singleton a.val
    rw [Hereditary.mem_singleton]
    constructor
    · intro hw
      exact congrArg Subtype.val ((h ⟨w,hd _ u.property _ hw⟩).mp hw)
    · rintro rfl
      exact (h a).mpr rfl
  · intro h
    constructor
    · rw [h]; exact isSet_ofFinset _
    · intro w
      rw [h,Hereditary.mem_singleton]
      exact Subtype.val_injective.eq_iff

theorem doubleTest_iff (u a b : Domain d) : DoubleTest u a b ↔ u.val = double a.val b.val := by
  constructor
  · rintro ⟨hu,h⟩
    apply ext_sets hu (isSet_ofFinset _)
    intro w
    change w ∈ u.val ↔ w ∈ double a.val b.val
    rw [mem_double]
    constructor
    · intro hw
      rcases (h ⟨w,hd _ u.property _ hw⟩).mp hw with h|h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
    · rintro (rfl|rfl)
      · exact (h a).mpr (Or.inl rfl)
      · exact (h b).mpr (Or.inr rfl)
  · intro h
    constructor
    · rw [h]; exact isSet_ofFinset _
    · intro w
      rw [h,mem_double]
      exact or_congr Subtype.val_injective.eq_iff Subtype.val_injective.eq_iff

end

end WitnessedSeparation.HFCoding



namespace WitnessedSeparation.Counting

noncomputable section

open Classical Finset

variable {R ι : Type*} {D : ι → Type*} (S : ∀ i, Structure R (D i)) {m n k : ℕ}

def UniformDefinable (m n : ℕ) (P : ∀ i, (Fin n → D i) → Prop) : Prop :=
  ∀ args : Fin n → Fin m, ∃ φ : Formula R (Fin m),
    φ.free ⊆ univ.image args ∧ ∀ i v, φ.eval (S i) v ↔ P i (v ∘ args)

namespace UniformDefinable

variable {S} {P Q : ∀ i, (Fin n → D i) → Prop}

theorem congr (h : UniformDefinable S m n P) (heq : ∀ i v, P i v ↔ Q i v) :
    UniformDefinable S m n Q := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h args
  exact ⟨φ,hφ,fun i v => (he i v).trans (heq _ _)⟩

theorem reindex (h : UniformDefinable S m n P) (f : Fin n → Fin k) :
    UniformDefinable S m k (fun i v => P i (v ∘ f)) := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h (args ∘ f)
  refine ⟨φ,?_,fun i v => he i v⟩
  intro j hj
  obtain ⟨l,_,rfl⟩ := mem_image.mp (hφ hj)
  exact mem_image.mpr ⟨f l,mem_univ _,rfl⟩

theorem falsum : UniformDefinable S m n (fun _ _ => False) :=
  fun _ => ⟨.falsum,by simp [Formula.free],fun _ _ => Iff.rfl⟩

theorem neg (h : UniformDefinable S m n P) : UniformDefinable S m n (fun i v => ¬ P i v) := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h args
  exact ⟨.neg φ,hφ,fun i v => not_congr (he i v)⟩

theorem and (h : UniformDefinable S m n P) (h' : UniformDefinable S m n Q) :
    UniformDefinable S m n (fun i v => P i v ∧ Q i v) := by
  intro args
  obtain ⟨φ,hφ,he⟩ := h args
  obtain ⟨ψ,hψ,he'⟩ := h' args
  exact ⟨.and φ ψ,union_subset hφ hψ,fun i v => and_congr (he i v) (he' i v)⟩

theorem or (h : UniformDefinable S m n P) (h' : UniformDefinable S m n Q) :
    UniformDefinable S m n (fun i v => P i v ∨ Q i v) :=
  (h.neg.and h'.neg).neg.congr (fun _ _ => by tauto)

theorem imp (h : UniformDefinable S m n P) (h' : UniformDefinable S m n Q) :
    UniformDefinable S m n (fun i v => P i v → Q i v) :=
  (h.neg.or h').congr (fun _ _ => by tauto)

theorem iff (h : UniformDefinable S m n P) (h' : UniformDefinable S m n Q) :
    UniformDefinable S m n (fun i v => P i v ↔ Q i v) :=
  ((h.imp h').and (h'.imp h)).congr (fun _ _ => by tauto)

theorem equal (a b : Fin n) : UniformDefinable S m n (fun _ v => v a = v b) := by
  intro args
  refine ⟨.equal (args a) (args b),?_,fun _ _ => Iff.rfl⟩
  simp only [Formula.free,insert_subset_iff,singleton_subset_iff]
  exact ⟨mem_image.mpr ⟨a,mem_univ _,rfl⟩,mem_image.mpr ⟨b,mem_univ _,rfl⟩⟩

theorem fresh (args : Fin n → Fin m) (hn : n < m) : ∃ i, ∀ j, args j ≠ i := by
  have hns : ¬ Function.Surjective args := by
    intro hs
    have h := Fintype.card_le_of_surjective args hs
    simp only [Fintype.card_fin] at h
    omega
  simp only [Function.Surjective] at hns
  push Not at hns
  exact hns

theorem updated_args {X : Type*} (args : Fin n → Fin m) (i : Fin m)
    (hi : ∀ j, args j ≠ i) (v : Fin m → X) (x : X) :
    Function.update v i x ∘ Fin.cons i args = Fin.cons x (v ∘ args) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [hi j]

theorem free_binder {args : Fin n → Fin m} {i : Fin m} {φ : Formula R (Fin m)}
    (hφ : φ.free ⊆ univ.image (Fin.cons i args)) : φ.free.erase i ⊆ univ.image args := by
  intro j hj
  obtain ⟨k,_,hk⟩ := mem_image.mp (hφ (mem_erase.mp hj).2)
  cases k using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero] at hk
    exact False.elim ((mem_erase.mp hj).1 hk.symm)
  | succ k => exact mem_image.mpr ⟨k,mem_univ _,hk⟩

theorem ex {P : ∀ i, (Fin (n+1) → D i) → Prop} (h : UniformDefinable S m (n+1) P) (hn : n < m) :
    UniformDefinable S m n (fun i v => ∃ x, P i (Fin.cons x v)) := by
  intro args
  obtain ⟨a,ha⟩ := fresh args hn
  obtain ⟨φ,hφ,he⟩ := h (Fin.cons a args)
  refine ⟨.ex a φ,free_binder hφ,?_⟩
  intro i v
  apply exists_congr
  intro x
  simpa only [updated_args args a ha] using he i (Function.update v a x)

theorem all {P : ∀ i, (Fin (n+1) → D i) → Prop} (h : UniformDefinable S m (n+1) P) (hn : n < m) :
    UniformDefinable S m n (fun i v => ∀ x, P i (Fin.cons x v)) :=
  (h.neg.ex hn).neg.congr (fun _ _ => by simp)

theorem exact {P : ∀ i, (Fin (n+1) → D i) → Prop} (h : UniformDefinable S m (n+1) P) (hn : n < m) (k : ℕ) :
    UniformDefinable S m n (fun i v => Nonempty ({x : D i // P i (Fin.cons x v)} ≃ Fin k)) := by
  intro args
  obtain ⟨a,ha⟩ := fresh args hn
  obtain ⟨φ,hφ,he⟩ := h (Fin.cons a args)
  refine ⟨.exact a k φ,free_binder hφ,?_⟩
  intro i v
  let e : {x : D i // φ.eval (S i) (Function.update v a x)} ≃ {x : D i // P i (Fin.cons x (v ∘ args))} :=
    Equiv.subtypeEquivRight (fun x => by simpa only [updated_args args a ha] using he i (Function.update v a x))
  exact ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩,fun ⟨f⟩ => ⟨e.trans f⟩⟩

theorem exists_finset {κ : Type*} {P : κ → ∀ i, (Fin n → D i) → Prop} (t : Finset κ)
    (h : ∀ a ∈ t, UniformDefinable S m n (P a)) : UniformDefinable S m n (fun i v => ∃ a ∈ t, P a i v) := by
  induction t using Finset.induction_on with
  | empty => exact (falsum (S := S)).congr (fun _ _ => by simp)
  | @insert a t ha ih =>
    exact ((h a (mem_insert_self _ _)).or (ih (fun b hb => h b (mem_insert_of_mem hb)))).congr
      (fun _ _ => by simp only [mem_insert,exists_eq_or_imp])

end UniformDefinable

end

end WitnessedSeparation.Counting



namespace WitnessedSeparation.HFCoding

noncomputable section

open Classical Finset Hereditary Counting

variable {ι R : Type} {A : ι → Type} {d : ∀ i, Set (HF (A i))}

variable (S : ∀ i, Counting.Structure R (Domain (d i))) {m : ℕ}

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (hm : 6 ≤ m)

include hmem hset hm

theorem uniform_singleton : UniformDefinable S m 2 (fun _ v => SingletonTest (v 0) (v 1)) := by
  have hs : UniformDefinable S m 2 (fun _ v => isSet (v 0).val = true) := by
    simpa using hset.reindex (![0] : Fin 1 → Fin 2)
  have hbody : UniformDefinable S m 3 (fun _ v => (v 0).val ∈ (v 1).val ↔ v 0 = v 2) := by
    have hmem' : UniformDefinable S m 3 (fun _ v => (v 0).val ∈ (v 1).val) := by
      simpa using hmem.reindex (![0,1] : Fin 2 → Fin 3)
    exact hmem'.iff (UniformDefinable.equal 0 2)
  exact hs.and (hbody.all (by omega))

theorem uniform_double : UniformDefinable S m 3 (fun _ v => DoubleTest (v 0) (v 1) (v 2)) := by
  have hs : UniformDefinable S m 3 (fun _ v => isSet (v 0).val = true) := by
    simpa using hset.reindex (![0] : Fin 1 → Fin 3)
  have hbody : UniformDefinable S m 4 (fun _ v => (v 0).val ∈ (v 1).val ↔ v 0 = v 2 ∨ v 0 = v 3) := by
    have hmem' : UniformDefinable S m 4 (fun _ v => (v 0).val ∈ (v 1).val) := by
      simpa using hmem.reindex (![0,1] : Fin 2 → Fin 4)
    exact hmem'.iff ((UniformDefinable.equal 0 2).or (UniformDefinable.equal 0 3))
  exact hs.and (hbody.all (by omega))

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

include hd

theorem uniform_ordinal (hpure : ∀ i k, ordinal (A := A i) k ∈ d i) (k : ℕ) :
    UniformDefinable S m 1 (fun _ v => (v 0).val = ordinal k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hor : UniformDefinable S m 2 (fun _ v => ∃ j ∈ range k, (v 0).val = ordinal j) := by
      apply UniformDefinable.exists_finset
      intro j hj
      simpa using (ih j (mem_range.mp hj)).reindex (![0] : Fin 1 → Fin 2)
    have hbody := (hmem.iff hor).all (by omega : 1 < m)
    apply (hset.and hbody).congr
    intro i v
    change (isSet (v 0).val = true ∧ ∀ w : Domain (d i),
      w.val ∈ (v 0).val ↔ ∃ j ∈ range k, w.val = ordinal j) ↔ _
    constructor
    · rintro ⟨hv,h⟩
      apply ext_sets hv (ordinal_isSet k)
      intro w
      rw [mem_ordinal]
      constructor
      · intro hw
        obtain ⟨j,hj,hjw⟩ := (h ⟨w,hd i _ (v 0).property _ hw⟩).mp hw
        exact ⟨j,mem_range.mp hj,hjw⟩
      · rintro ⟨j,hj,rfl⟩
        exact (h ⟨ordinal j,hpure i j⟩).mpr ⟨j,mem_range.mpr hj,rfl⟩
    · intro hv
      refine ⟨by rw [hv]; exact ordinal_isSet k,?_⟩
      intro w
      rw [hv,mem_ordinal]
      simp only [mem_range]

end

end WitnessedSeparation.HFCoding



end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_EncodedCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace WitnessedSeparation.Grid

noncomputable section

open Classical Finset Support

variable {n : ℕ}

def localSizeBound : ℕ := 3^25

def atomSizeConstant : ℕ := 3*localSizeBound+localSizeBound^6

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Grid

noncomputable section

open Classical Hereditary Counting HFCoding Interpretations

variable {n : ℕ} (b : Vertex n → Scalar)

variable {ι : Type} (bs : ι → Vertex n → Scalar) {s m : ℕ}

def programDomain (i : ι) : Set (HF (Atom (bs i))) := HereditarilySupported (G := CentralGroup n) s

def programHF (i : ι) : Counting.Structure (Forms.HFRelation AnalysisSymbol) (Domain (programDomain bs (s := s) i)) :=
  Forms.hfStructure (analysisStructure (bs i))

end





noncomputable section

open Classical Hereditary Counting HFCoding Interpretations

variable {n B K N m M : ℕ}
  (vstar : Vertex n)

def twoCharges : Bool → Vertex n → Scalar
  | false => 0
  | true => Pi.single vstar 1

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Quantitative

noncomputable section

open Filter Asymptotics Topology

def radius (C q L : ℝ) : ℕ := ⌈2*L*(q*Real.logb 3 (C*L^3))^2⌉₊

def palette (L : ℝ) : ℕ := ⌊L^((7:ℝ)/4)⌋₊

end





def timeExponent (c d : ℕ) := c + 2*d + 2

def traceExponent (c d : ℕ) := 3*timeExponent c d + 4

end WitnessedSeparation.Quantitative



end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_Machines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace WitnessedSeparation.Operational

noncomputable section

open Classical Hereditary Finset

variable {A B R F : Type*} {arity : F → ℕ}

local instance instDecidableEqHF {C : Type*} : DecidableEq (HF C) := Classical.decEq _

abbrev empty : HF A := ordinal 0

def inputRelation (rel : R → A → A → Bool) (r : R) (x y : HF A) : Prop :=
  ∃ a b, x = atom a ∧ y = atom b ∧ rel r a b = true

def allAtoms [Fintype A] : HF A := ofFinset (univ.image atom)

def unionHF (x : HF A) : HF A := ofFinset ((elements x).biUnion elements)

def uniqueHF (x : HF A) : HF A :=
  if h : ∃ a, elements x = {a} then h.choose else empty

lemma uniqueHF_spec (x : HF A) :
    (∃ a, elements x = {a} ∧ uniqueHF x = a) ∨
      (¬ ∃ a, elements x = {a}) ∧ uniqueHF x = empty := by
  by_cases h : ∃ a, elements x = {a}
  · exact Or.inl ⟨h.choose,h.choose_spec,by simp only [uniqueHF,dite_eq_left h]⟩
  · exact Or.inr ⟨h,by simp only [uniqueHF,dite_eq_right h]⟩

def cardinalityHF (x : HF A) : HF A := ordinal (elements x).card

end

end WitnessedSeparation.Operational



namespace WitnessedSeparation.Hereditary

noncomputable section

open Classical Finset

variable {A B : Type*}

local instance instDecidableEqHF_2 {C : Type*} : DecidableEq (HF C) := Classical.decEq _

lemma mem_mapEquiv (e : A ≃ B) (x y : HF A) : map e x ∈ map e y ↔ x ∈ y := by
  change map e x ∈ elements (map e y) ↔ x ∈ elements y
  rw [elements_map]
  constructor
  · intro h
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp h
    exact (mapEquiv e).injective he ▸ hz
  · intro h
    exact Finset.mem_image.mpr ⟨x,h,rfl⟩

lemma rtc_map (e : A ≃ B) {x y : HF A}
    (h : Relation.ReflTransGen (fun a b : HF A => a ∈ b) x y) :
    Relation.ReflTransGen (fun a b : HF B => a ∈ b) (map e x) (map e y) := by
  induction h with
  | refl => exact .refl
  | tail hab hbc ih => exact ih.tail ((mem_mapEquiv e _ _).mpr hbc)

lemma closure_map (e : A ≃ B) (x : HF A) : closure (map e x) = (closure x).image (map e) := by
  ext y
  obtain ⟨z,rfl⟩ := (mapEquiv e).surjective y
  rw [mem_closure_iff,mem_image]
  constructor
  · intro h
    have h' : Relation.ReflTransGen (fun a b : HF A => a ∈ b) z x := by
      have hm := rtc_map e.symm h
      change Relation.ReflTransGen (fun a b : HF A => a ∈ b)
        ((mapEquiv e).symm ((mapEquiv e) z)) ((mapEquiv e).symm ((mapEquiv e) x)) at hm
      simpa only [Equiv.symm_apply_apply] using hm
    exact ⟨z,(mem_closure_iff z x).mpr h',rfl⟩
  · rintro ⟨w,hw,he⟩
    have h := (mem_closure_iff w x).mp hw
    have hm := rtc_map e h
    exact he ▸ hm

def familyClosure (f : Finset (HF A)) : Finset (HF A) := f.biUnion closure

lemma mem_familyClosure {f : Finset (HF A)} {x : HF A} :
    x ∈ familyClosure f ↔ ∃ y ∈ f, x ∈ closure y := by simp [familyClosure]

lemma familyClosure_contains {f : Finset (HF A)} {x : HF A} (hx : x ∈ f) :
    x ∈ familyClosure f := mem_familyClosure.mpr ⟨x,hx,mem_closure_self x⟩

lemma familyClosure_transitive {f : Finset (HF A)} {x y : HF A}
    (hx : x ∈ familyClosure f) (hy : y ∈ x) : y ∈ familyClosure f := by
  obtain ⟨z,hz,hxz⟩ := mem_familyClosure.mp hx
  exact mem_familyClosure.mpr ⟨z,hz,closure_transitive hxz hy⟩

end

end WitnessedSeparation.Hereditary



namespace WitnessedSeparation.Operational





noncomputable section

open Classical Hereditary Finset

variable {A B R F : Type*} {arity : F → ℕ}

local instance instDecidableEqHF_2 {C : Type*} : DecidableEq (HF C) := Classical.decEq _

abbrev lift (e : A ≃ B) : HF A ≃ HF B := mapEquiv e

@[simp] lemma lift_empty (e : A ≃ B) : lift e empty = empty := map_ordinal e 0

@[simp] lemma lift_ordinal (e : A ≃ B) (n : ℕ) : lift e (ordinal n) = ordinal n := map_ordinal e n

@[simp] lemma lift_double (e : A ≃ B) (x y : HF A) : lift e (double x y) = double (lift e x) (lift e y) := map_double e x y

@[simp] lemma lift_isSet (e : A ≃ B) (x : HF A) : isSet (lift e x) = isSet x := isSet_map e x

@[simp] lemma lift_empty_iff (e : A ≃ B) (x : HF A) : lift e x = empty ↔ x = empty := by
  rw [← lift_empty e,Equiv.apply_eq_iff_eq]

@[simp] lemma lift_mem_iff (e : A ≃ B) (x y : HF A) : lift e x ∈ lift e y ↔ x ∈ y := mem_mapEquiv e x y

lemma lift_elements (e : A ≃ B) (x : HF A) : elements (lift e x) = (elements x).image (lift e) := elements_map e x

lemma lift_ofFinset (e : A ≃ B) (s : Finset (HF A)) : lift e (ofFinset s) = ofFinset (s.image (lift e)) := map_ofFinset e s

lemma lift_allAtoms [Fintype A] [Fintype B] (e : A ≃ B) : lift e allAtoms = allAtoms := by
  rw [allAtoms,lift_ofFinset,allAtoms]
  congr 1
  ext x
  simp only [mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨y,⟨a,rfl⟩,rfl⟩
    exact ⟨e a,rfl⟩
  · rintro ⟨b,rfl⟩
    exact ⟨atom (e.symm b),⟨e.symm b,rfl⟩,by simp [lift,mapEquiv]⟩

lemma lift_union (e : A ≃ B) (x : HF A) : lift e (unionHF x) = unionHF (lift e x) := by
  rw [unionHF,lift_ofFinset,unionHF,lift_elements]
  congr 1
  ext z
  simp only [mem_image,mem_biUnion]
  constructor
  · rintro ⟨z,⟨y,hy,hz⟩,rfl⟩
    exact ⟨lift e y,⟨y,hy,rfl⟩,(lift_mem_iff e z y).mpr hz⟩
  · rintro ⟨y,⟨w,hw,rfl⟩,hz⟩
    refine ⟨(lift e).symm z,⟨w,hw,?_⟩,Equiv.apply_symm_apply _ _⟩
    have := (lift_mem_iff e ((lift e).symm z) w).mp
    apply this
    simpa only [Equiv.apply_symm_apply] using (show z ∈ lift e w from hz)

lemma lift_unique (e : A ≃ B) (x : HF A) : lift e (uniqueHF x) = uniqueHF (lift e x) := by
  rcases uniqueHF_spec x with ⟨a,ha,hu⟩ | ⟨ha,hu⟩
  · have h : elements (lift e x) = {lift e a} := by rw [lift_elements,ha,image_singleton]
    rcases uniqueHF_spec (lift e x) with ⟨b,hb,hv⟩ | ⟨hb,hv⟩
    · rw [hu,hv]
      exact singleton_injective (h.symm.trans hb)
    · exact (hb ⟨_,h⟩).elim
  · rcases uniqueHF_spec (lift e x) with ⟨b,hb,hv⟩ | ⟨hb,hv⟩
    · exfalso
      apply ha
      refine ⟨(lift e).symm b,?_⟩
      apply (image_injective (lift e).injective)
      rw [← lift_elements,hb,image_singleton,Equiv.apply_symm_apply]
    · rw [hu,hv,lift_empty]

lemma lift_card (e : A ≃ B) (x : HF A) : lift e (cardinalityHF x) = cardinalityHF (lift e x) := by
  simp only [cardinalityHF,lift_ordinal,lift_elements,card_image_of_injective _ (lift e).injective]

lemma lift_input (e : A ≃ B) (rel : R → A → A → Bool) (rel' : R → B → B → Bool)
    (hrel : ∀ r a b, rel' r (e a) (e b) = rel r a b) (r : R) (x y : HF A) :
    inputRelation rel' r (lift e x) (lift e y) ↔ inputRelation rel r x y := by
  constructor
  · rintro ⟨a,b,ha,hb,hr⟩
    refine ⟨e.symm a,e.symm b,?_,?_,?_⟩
    · apply (lift e).injective
      simpa [lift,mapEquiv] using ha
    · apply (lift e).injective
      simpa [lift,mapEquiv] using hb
    · simpa only [← hrel,Equiv.apply_symm_apply] using hr
  · rintro ⟨a,b,rfl,rfl,hr⟩
    exact ⟨e a,e b,rfl,rfl,by rw [hrel]; exact hr⟩

end

end WitnessedSeparation.Operational



namespace WitnessedSeparation.Hereditary

noncomputable section

open Classical Finset

variable {A : Type*}

local instance instDecidableEqHF_3 {C : Type*} : DecidableEq (HF C) := Classical.decEq _

lemma closure_ofFinset (s : Finset (HF A)) :
    closure (ofFinset s) = insert (ofFinset s) (familyClosure s) := by
  rw [closure,elements_ofFinset]
  congr 1
  ext x
  simp [familyClosure]

lemma closure_subset_of_transitive {s : Finset (HF A)}
    (hs : ∀ x ∈ s, ∀ y, y ∈ x → y ∈ s) {x : HF A} (hx : x ∈ s) : closure x ⊆ s := by
  intro y hy
  have h := (mem_closure_iff y x).mp hy
  clear hy
  induction h with
  | refl => exact hx
  | @tail b c h hbc ih => exact ih (hs c hx b hbc)

lemma elements_subset_closure (x : HF A) : elements x ⊆ closure x := by
  intro y hy
  exact closure_member_subset hy (mem_closure_self y)

lemma closure_atom (a : A) : closure (atom a) = {atom a} := by
  rw [closure,elements_atom]
  simp

lemma closure_double_subset (x y : HF A) :
    closure (double x y) ⊆ insert (double x y) (closure x ∪ closure y) := by
  rw [double,closure_ofFinset]
  intro z hz
  simp only [mem_insert,mem_union] at hz ⊢
  rcases hz with h | h
  · exact Or.inl h
  · obtain ⟨w,hw,hz⟩ := mem_familyClosure.mp h
    have he : w = x ∨ w = y := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hw
    rcases he with he | he
    · rw [he] at hz; exact Or.inr (Or.inl hz)
    · rw [he] at hz; exact Or.inr (Or.inr hz)

lemma closure_ordinal (n : ℕ) : closure (ordinal (A := A) n) = (range (n+1)).image ordinal := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [closure]
    ext x
    simp only [mem_insert,mem_biUnion,mem_attach,true_and,Subtype.exists,mem_image,mem_range]
    constructor
    · rintro (rfl | ⟨y,hy,hx⟩)
      · exact ⟨n,by omega,rfl⟩
      · obtain ⟨j,hj,rfl⟩ := (mem_ordinal y n).mp hy
        rw [ih j hj] at hx
        obtain ⟨k,hk,rfl⟩ := mem_image.mp hx
        exact ⟨k,by simp only [mem_range] at hk; omega,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      by_cases he : j = n
      · exact Or.inl (by rw [he])
      · exact Or.inr ⟨ordinal j,(mem_ordinal _ _).mpr ⟨j,by omega,rfl⟩,mem_closure_self _⟩

lemma card_closure_ordinal (n : ℕ) : (closure (ordinal (A := A) n)).card = n+1 := by
  rw [closure_ordinal,card_image_of_injective _ (fun _ _ h => ordinal_injective h),card_range]

end

end WitnessedSeparation.Hereditary

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_EvaluationTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedSeparation.Operational





noncomputable section

open Classical Hereditary Counting HFCoding Finset

variable {ι R : Type} {A : ι → Type} [∀ i, Fintype (A i)]

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure R (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (hm : 6 ≤ m)

include hd in
omit [(i : ι) → Fintype (A i)] in
lemma member_count_iff (i : ι) (x : Domain (d i)) (n : ℕ) :
    Nonempty ({y : Domain (d i) // y.val ∈ x.val} ≃ Fin n) ↔ (elements x.val).card = n := by
  let e : {y : Domain (d i) // y.val ∈ x.val} ≃ {y // y ∈ elements x.val} :=
    { toFun := fun y => ⟨y.val.val,y.property⟩
      invFun := fun y => ⟨⟨y.val,hd i _ x.property _ y.property⟩,y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  constructor
  · rintro ⟨f⟩
    have h := Fintype.card_congr (e.symm.trans f)
    simpa using h
  · intro h
    let f := (Fintype.equivFin {y // y ∈ elements x.val}).trans (finCongr (by simpa using h))
    exact ⟨e.trans f⟩

include hd hmem hset hm

omit [(i : ι) → Fintype (A i)] in
lemma uniform_double_value : UniformDefinable S m 3
    (fun _ v => (v 0).val = double (v 1).val (v 2).val) :=
  (HFCoding.uniform_double S hmem hset hm).congr
    (fun i v => HFCoding.doubleTest_iff (hd i) (v 0) (v 1) (v 2))

omit [(i : ι) → Fintype (A i)] in
lemma uniform_singleton_value : UniformDefinable S m 2
    (fun _ v => (v 0).val = Hereditary.singleton (v 1).val) :=
  (HFCoding.uniform_singleton S hmem hset hm).congr
    (fun i v => HFCoding.singletonTest_iff (hd i) (v 0) (v 1))

include ha in
lemma uniform_atoms : UniformDefinable S m 1 (fun i v => (v 0).val = (allAtoms : HF (A i))) := by
  have hs : UniformDefinable S m 2 (fun _ v => isSet (v 0).val = false) := by
    apply (hset.reindex (![0] : Fin 1 → Fin 2)).neg.congr
    intro i v; dsimp; cases isSet (v 0).val <;> simp
  have hbody := (hmem.iff hs).all (by omega : 1 < m)
  apply (hset.and hbody).congr
  intro i v
  change (isSet (v 0).val = true ∧ ∀ y : Domain (d i),
    y.val ∈ (v 0).val ↔ isSet y.val = false) ↔ _
  constructor
  · rintro ⟨h0,h⟩
    apply ext_sets h0 (isSet_ofFinset _)
    intro y
    simp only [mem_ofFinset,mem_image,mem_univ,true_and]
    constructor
    · intro hy
      have ht := (h ⟨y,hd i _ (v 0).property _ hy⟩).mp hy
      change isSet y = false at ht
      rcases atom_or_set y with ⟨a,rfl⟩ | he
      · exact ⟨a,rfl⟩
      · rw [he,isSet_ofFinset] at ht; contradiction
    · rintro ⟨a,rfl⟩
      exact (h ⟨atom a,ha i a⟩).mpr rfl
  · intro he
    constructor
    · rw [he]; exact isSet_ofFinset _
    · intro y
      rw [he]
      simp only [allAtoms,mem_ofFinset,mem_image,mem_univ,true_and]
      constructor
      · rintro ⟨a,he⟩; rw [← he]; rfl
      · intro ht
        rcases atom_or_set y.val with ⟨a,he⟩ | he
        · exact ⟨a,he.symm⟩
        · rw [he,isSet_ofFinset] at ht; contradiction

omit [(i : ι) → Fintype (A i)] in
lemma uniform_union : UniformDefinable S m 2
    (fun _ v => (v 0).val = unionHF (v 1).val) := by
  have hz : UniformDefinable S m 4
      (fun _ v => (v 0).val ∈ (v 3).val ∧ (v 1).val ∈ (v 0).val) :=
    (hmem.reindex (![0,3] : Fin 2 → Fin 4)).and (hmem.reindex (![1,0] : Fin 2 → Fin 4))
  have hleft : UniformDefinable S m 3 (fun _ v => (v 0).val ∈ (v 1).val) :=
    hmem.reindex (![0,1] : Fin 2 → Fin 3)
  have hbody := (hleft.iff (hz.ex (by omega))).all (by omega : 2 < m)
  have hset' := hset.reindex (![0] : Fin 1 → Fin 2)
  apply (hset'.and hbody).congr
  intro i v
  change (isSet (v 0).val = true ∧ ∀ y : Domain (d i),
    y.val ∈ (v 0).val ↔ ∃ z : Domain (d i), z.val ∈ (v 1).val ∧ y.val ∈ z.val) ↔ _
  have hmemu (y : HF (A i)) : y ∈ unionHF (v 1).val ↔
      ∃ z : Domain (d i), z.val ∈ (v 1).val ∧ y ∈ z.val := by
    simp only [unionHF,mem_ofFinset,mem_biUnion]
    constructor
    · rintro ⟨z,hz,hy⟩
      exact ⟨⟨z,hd i _ (v 1).property _ hz⟩,hz,hy⟩
    · rintro ⟨z,hz,hy⟩; exact ⟨z.val,hz,hy⟩
  constructor
  · rintro ⟨h0,h⟩
    apply ext_sets h0 (isSet_ofFinset _)
    intro y
    change y ∈ (v 0).val ↔ y ∈ unionHF (v 1).val
    rw [hmemu]
    constructor
    · intro hy; exact (h ⟨y,hd i _ (v 0).property _ hy⟩).mp hy
    · rintro ⟨z,hz,hy⟩
      exact (h ⟨y,hd i _ z.property _ hy⟩).mpr ⟨z,hz,hy⟩
  · intro he
    constructor
    · rw [he]; exact isSet_ofFinset _
    · intro y; rw [he,hmemu]

include hp in
omit [(i : ι) → Fintype (A i)] in
lemma uniform_unique : UniformDefinable S m 2
    (fun _ v => (v 0).val = uniqueHF (v 1).val) := by
  have hsing := uniform_singleton_value d S hd hmem hset hm
  have hyes := hsing.reindex (![1,0] : Fin 2 → Fin 2)
  have hex : UniformDefinable S m 2 (fun i v => ∃ z : Domain (d i),
      (v 1).val = Hereditary.singleton z.val) := by
    apply ((hsing.reindex (![2,0] : Fin 2 → Fin 3)).ex (by omega)).congr
    intro i v
    apply exists_congr
    intro z
    rfl
  have hempt := (HFCoding.uniform_ordinal S hmem hset hm hd hp 0).reindex (![0] : Fin 1 → Fin 2)
  apply (hyes.or (hempt.and hex.neg)).congr
  intro i v
  change ((v 1).val = Hereditary.singleton (v 0).val ∨
    ((v 0).val = empty ∧ ¬ ∃ z : Domain (d i), (v 1).val = Hereditary.singleton z.val)) ↔ _
  have hs (z : HF (A i)) : (v 1).val = Hereditary.singleton z ↔ elements (v 1).val = {z} := by
    constructor
    · intro h; rw [h]; exact elements_ofFinset _
    · intro h
      rcases atom_or_set (v 1).val with ⟨a,he⟩ | he
      · rw [he,elements_atom] at h
        exact False.elim (by simpa using congrArg Finset.card h)
      · rw [he,h]; rfl
  have hexi : (∃ z : Domain (d i), (v 1).val = Hereditary.singleton z.val) ↔
      ∃ z, elements (v 1).val = {z} := by
    constructor
    · rintro ⟨z,hz⟩; exact ⟨z.val,(hs _).mp hz⟩
    · rintro ⟨z,hz⟩
      exact ⟨⟨z,hd i _ (v 1).property _ (by change z ∈ elements (v 1).val; rw [hz]; simp)⟩,(hs z).mpr hz⟩
  rw [hs,hexi]
  rcases uniqueHF_spec (v 1).val with ⟨z,hz,he⟩ | ⟨hne,he⟩
  · rw [he,hz]
    simp only [Finset.singleton_inj,exists_eq',not_true_eq_false,and_false,or_false]
    exact eq_comm
  · rw [he]
    constructor
    · rintro (h | ⟨h,_⟩)
      · exact False.elim (hne ⟨_,h⟩)
      · exact h
    · intro h; exact Or.inr ⟨h,hne⟩

def BoundedCard (K : ℕ) {i : ι} (z x : Domain (d i)) : Prop :=
  (elements x.val).card ≤ K ∧ z.val = cardinalityHF x.val

include hp in
omit [(i : ι) → Fintype (A i)] in
lemma uniform_card (K : ℕ) : UniformDefinable S m 2
    (fun _i v => BoundedCard d K (v 0) (v 1)) := by
  have hmemb : UniformDefinable S m 3 (fun _ v => (v 0).val ∈ (v 2).val) :=
    hmem.reindex (![0,2] : Fin 2 → Fin 3)
  have hdis : UniformDefinable S m 2 (fun i v => ∃ n ∈ range (K+1),
      Nonempty ({y : Domain (d i) // y.val ∈ (v 1).val} ≃ Fin n) ∧ (v 0).val = ordinal n) := by
    apply UniformDefinable.exists_finset
    intro n hn
    have hc := hmemb.exact (by omega) n
    have ho := (HFCoding.uniform_ordinal S hmem hset hm hd hp n).reindex (![0] : Fin 1 → Fin 2)
    exact hc.and ho
  apply hdis.congr
  intro i v
  simp only [member_count_iff d hd,mem_range,BoundedCard,cardinalityHF]
  constructor
  · rintro ⟨n,hn,hc,he⟩; exact ⟨by omega,by rwa [hc]⟩
  · rintro ⟨hc,he⟩; exact ⟨_,by omega,rfl,he⟩

end

end WitnessedSeparation.Operational



namespace WitnessedSeparation.Counting.UniformDefinable

noncomputable section

open Classical Finset

variable {ι R : Type} {D : ι → Type} {S : ∀ i, Structure R (D i)} {m n r : ℕ}

lemma compose_unary {P : ∀ i, (Fin (n+1) → D i) → Prop}
    {Q : ∀ i, (Fin 2 → D i) → Prop}
    (hP : UniformDefinable S m (n+1) P) (hQ : UniformDefinable S m 2 Q)
    (hr : n+1 < m) : UniformDefinable S m (n+1)
      (fun i v => ∃ x, P i (Fin.cons x (Fin.tail v)) ∧ Q i ![v 0,x]) := by
  have h1 := hP.reindex (Fin.cons 0 (fun j => j.succ.succ) : Fin (n+1) → Fin (n+2))
  have h2 := hQ.reindex (![1,0] : Fin 2 → Fin (n+2))
  apply ((h1.and h2).ex hr).congr
  intro i v
  apply exists_congr; intro x
  have he : Fin.cons x v ∘ (Fin.cons 0 (fun j => j.succ.succ) : Fin (n+1) → Fin (n+2)) =
      Fin.cons x (Fin.tail v) := by funext j; refine Fin.cases rfl (fun _ => rfl) j
  have he2 : Fin.cons x v ∘ (![1,0] : Fin 2 → Fin (n+2)) = ![v 0,x] := by
    funext j; fin_cases j <;> rfl
  simp only [he,he2]

lemma compose_binary {P Q : ∀ i, (Fin (n+1) → D i) → Prop}
    {T : ∀ i, (Fin 3 → D i) → Prop}
    (hP : UniformDefinable S m (n+1) P) (hQ : UniformDefinable S m (n+1) Q)
    (hT : UniformDefinable S m 3 T) (hr : n+2 < m) :
    UniformDefinable S m (n+1) (fun i v => ∃ x y,
      P i (Fin.cons x (Fin.tail v)) ∧ Q i (Fin.cons y (Fin.tail v)) ∧ T i ![v 0,x,y]) := by
  have h1 := hP.reindex (Fin.cons 1 (fun j => j.succ.succ.succ) : Fin (n+1) → Fin (n+3))
  have h2 := hQ.reindex (Fin.cons 0 (fun j => j.succ.succ.succ) : Fin (n+1) → Fin (n+3))
  have h3 := hT.reindex (![2,1,0] : Fin 3 → Fin (n+3))
  apply (((h1.and (h2.and h3)).ex hr).ex (by omega)).congr
  intro i v
  apply exists_congr; intro x
  apply exists_congr; intro y
  have he1 : Fin.cons y (Fin.cons x v) ∘
      (Fin.cons 1 (fun j => j.succ.succ.succ) : Fin (n+1) → Fin (n+3)) =
        Fin.cons x (Fin.tail v) := by funext j; refine Fin.cases rfl (fun _ => rfl) j
  have he2 : Fin.cons y (Fin.cons x v) ∘
      (Fin.cons 0 (fun j => j.succ.succ.succ) : Fin (n+1) → Fin (n+3)) =
        Fin.cons y (Fin.tail v) := by funext j; refine Fin.cases rfl (fun _ => rfl) j
  have he3 : Fin.cons y (Fin.cons x v) ∘ (![2,1,0] : Fin 3 → Fin (n+3)) = ![v 0,x,y] := by
    funext j; fin_cases j <;> rfl
  simp only [he1,he2,he3]

end

end WitnessedSeparation.Counting.UniformDefinable



end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_TraceGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace WitnessedSeparation.Operational





noncomputable section

open Classical Hereditary Finset

variable {A B R F : Type} {arity : F → ℕ} [Fintype A] [Fintype B]

local instance instDecidableEqHF_7 {C : Type} : DecidableEq (HF C) := Classical.decEq _

omit [Fintype A] [Fintype B] in
lemma lift_closure (e : A ≃ B) (x : HF A) : closure (lift e x) = (closure x).image (lift e) := closure_map e x

end

end WitnessedSeparation.Operational



namespace WitnessedSeparation.Hereditary

noncomputable section

open Classical Finset

variable {A : Type}

local instance instDecidableEqHF_4 : DecidableEq (HF A) := Classical.decEq _

def descendants (t : Finset (HF A)) : ℕ → Finset (HF A)
  | 0 => t
  | k+1 => descendants t k ∪ (descendants t k).biUnion elements

lemma descendants_mono (t : Finset (HF A)) (k : ℕ) : descendants t k ⊆ descendants t (k+1) := subset_union_left

lemma roots_subset_descendants (t : Finset (HF A)) (k : ℕ) : t ⊆ descendants t k := by
  induction k with
  | zero => exact subset_rfl
  | succ k ih => exact ih.trans (descendants_mono t k)

lemma descendants_subset (t : Finset (HF A)) (k : ℕ) : descendants t k ⊆ familyClosure t := by
  induction k with
  | zero => exact fun _ hx => familyClosure_contains hx
  | succ k ih =>
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact ih hx
    · obtain ⟨y,hy,hxy⟩ := mem_biUnion.mp hx
      exact familyClosure_transitive (ih hy) hxy

lemma descendants_stable (t : Finset (HF A)) (k : ℕ)
    (hs : descendants t (k+1) ⊆ descendants t k) : descendants t k = familyClosure t := by
  apply subset_antisymm (descendants_subset t k)
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_familyClosure.mp hx
  have h := (mem_closure_iff x y).mp hxy
  have hc : ∀ {a b : HF A}, a ∈ b → b ∈ descendants t k → a ∈ descendants t k := by
    intro a b hab hb
    exact hs (mem_union_right _ (mem_biUnion.mpr ⟨b,hb,hab⟩))
  have aux : ∀ {a b : HF A}, Relation.ReflTransGen (fun x y : HF A => x ∈ y) a b →
      b ∈ descendants t k → a ∈ descendants t k := by
    intro a b hr
    induction hr with
    | refl => exact fun ha => ha
    | tail hab hbc ih => exact fun hb => ih (hc hbc hb)
  exact aux h (roots_subset_descendants t k hy)

lemma descendants_card_lower (t : Finset (HF A)) (k : ℕ)
    (hne : descendants t k ≠ familyClosure t) : k ≤ (descendants t k).card := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hproper : descendants t k ⊂ descendants t (k+1) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨descendants_mono t k,?_⟩
      intro he
      exact hne (he.symm.trans (descendants_stable t k (he ▸ subset_rfl)))
    have hprev : descendants t k ≠ familyClosure t := by
      intro he
      exact hne (subset_antisymm (descendants_subset t (k+1)) (he ▸ descendants_mono t k))
    have hh := card_lt_card hproper
    have hi := ih hprev
    omega

end

end WitnessedSeparation.Hereditary

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_ChoiceTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary WitnessedSeparation.Counting WitnessedSeparation.HFCoding

local instance instDecidableEqHF {A : Type*} : DecidableEq (HF A) := Classical.decEq _

lemma TC_eq_familyClosure {A : Type} (x : HF A) : TC x = familyClosure (elements x) := by
  ext y
  simp only [TC,familyClosure,Finset.mem_biUnion]

lemma descendants_TC_subset {A : Type} (x : HF A) (k : ℕ) :
    descendants (elements x) k ⊆ TC x := by
  rw [TC_eq_familyClosure]
  exact descendants_subset _ _

lemma descendants_TC_bound {A : Type} (x : HF A) (p : ℕ) :
    (TC x).card ≤ p ↔ (descendants (elements x) (p+1)).card ≤ p := by
  constructor
  · exact fun h => (Finset.card_le_card (descendants_TC_subset x _)).trans h
  · intro h
    by_cases he : descendants (elements x) (p+1) = TC x
    · rwa [he] at h
    · have he' : descendants (elements x) (p+1) ≠ familyClosure (elements x) := by
        simpa only [TC_eq_familyClosure] using he
      have hh := descendants_card_lower (elements x) (p+1) he'
      omega

lemma TC_in_domain {A : Type} (d : Set (HF A))
    (hd : ∀ x ∈ d, ∀ y, y ∈ x → y ∈ d) {x : HF A} (hx : x ∈ d) :
    ∀ y ∈ TC x, y ∈ d := by
  intro y hy
  rw [TC_eq_familyClosure] at hy
  obtain ⟨z,hz,hyz⟩ := mem_familyClosure.mp hy
  have hz' : z ∈ d := hd x hx z hz
  have hr := (mem_closure_iff _ _).mp hyz
  clear hx hz hyz
  induction hr with
  | refl => exact hz'
  | @tail u v huv hvz ih => exact ih (hd _ hz' _ hvz)

variable {ι R : Type} {A : ι → Type}

variable (d : ∀ i, Set (HF (A i)))

variable (S : ∀ i, WitnessedSeparation.Counting.Structure R (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hm : 3 ≤ m)

include hd hmem hm

lemma uniform_descendants (k : ℕ) : UniformDefinable S m 2
    (fun _ v => (v 0).val ∈ descendants (elements (v 1).val) k) := by
  induction k with
  | zero => exact hmem
  | succ k ih =>
    have hleft := ih.reindex (![0,2] : Fin 2 → Fin 3)
    have hright := hmem.reindex (![1,0] : Fin 2 → Fin 3)
    apply (ih.or ((hleft.and hright).ex (by omega))).congr
    intro i v
    change ((v 0).val ∈ descendants (elements (v 1).val) k ∨
      ∃ z : Domain (d i), z.val ∈ descendants (elements (v 1).val) k ∧
        (v 0).val ∈ z.val) ↔ _
    simp only [descendants,Finset.mem_union,Finset.mem_biUnion]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨z,hz,hy⟩; exact ⟨z.val,hz,hy⟩
    · rintro ⟨z,hz,hy⟩
      exact ⟨⟨z,TC_in_domain (d i) (hd i) (v 1).property z
        (descendants_TC_subset _ _ hz)⟩,hz,hy⟩

omit hmem hm in
lemma descendants_count_iff (i : ι) (x : Domain (d i)) (k j : ℕ) :
    Nonempty ({y : Domain (d i) // y.val ∈ descendants (elements x.val) k} ≃ Fin j) ↔
      (descendants (elements x.val) k).card = j := by
  let t := descendants (elements x.val) k
  have ht : ∀ y ∈ t, y ∈ d i := fun y hy =>
    TC_in_domain (d i) (hd i) x.property y (descendants_TC_subset _ _ hy)
  let e : {y : Domain (d i) // y.val ∈ t} ≃ {y // y ∈ t} :=
    { toFun := fun y => ⟨y.val.val,y.property⟩
      invFun := fun y => ⟨⟨y.val,ht y.val y.property⟩,y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  constructor
  · rintro ⟨f⟩
    have hh := Fintype.card_congr (e.symm.trans f)
    simpa [t] using hh
  · intro hh
    let f := (Fintype.equivFin {y // y ∈ t}).trans (finCongr (by simpa [t] using hh))
    exact ⟨e.trans f⟩

lemma uniform_TC_bound (p : ℕ) : UniformDefinable S m 1
    (fun _ v => (TC (v 0).val).card ≤ p) := by
  have hr := uniform_descendants d S hd hmem hm (p+1)
  have hh := UniformDefinable.exists_finset (Finset.range (p+1))
    (fun j _ => hr.exact (by omega : 1 < m) j)
  apply hh.congr
  intro i v
  simp only [Fin.cons_zero,Fin.cons_one,descendants_count_iff d hd,Finset.mem_range,Nat.lt_succ_iff]
  rw [descendants_TC_bound]
  exact ⟨fun ⟨j,hj,he⟩ => he ▸ hj,fun h => ⟨_,h,rfl⟩⟩

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

abbrev Traced (A : Type) (X : Type) := X × Finset (HF A)

def tracedLoop {A : Type} (p : ℕ) (step : HF A → Traced A (HF A)) :
    ℕ → HF A → Traced A (HF A)
  | 0, _ => (emptyHF, closure emptyHF)
  | fuel+1, x =>
      if (TC x).card ≤ p then
        let r := step x
        if x = r.1 then (x,r.2) else
          let s := tracedLoop p step fuel r.1
          (s.1,r.2 ∪ s.2)
      else (emptyHF,closure emptyHF)

mutual
  def Term.traced {A : Type} [Fintype A] (S : Input A) (p : ℕ) :
      {n : ℕ} → Term n → (Fin n → HF A) → Traced A (HF A)
    | _, .var j, env => (env j,closure (env j))
    | _, .empty, _ => (emptyHF,closure emptyHF)
    | _, .atoms, _ =>
        let x := ofFinset (Finset.univ.image atom)
        (x,closure x)
    | _, .pair a b, env =>
        let x := a.traced S p env
        let y := b.traced S p env
        (double x.1 y.1,insert (double x.1 y.1) (x.2 ∪ y.2))
    | _, .union a, env =>
        let x := a.traced S p env
        (unionHF x.1,insert (unionHF x.1) x.2)
    | _, .unique a, env =>
        let x := a.traced S p env
        (uniqueHF x.1,insert (uniqueHF x.1) x.2)
    | _, .card a, env =>
        let x := a.traced S p env
        (cardHF x.1,closure (cardHF x.1) ∪ x.2)
    | _, .comprehend body range guard, env =>
        let r := range.traced S p env
        let test := fun x => guard.traced S p (Fin.cons x env)
        let val := fun x => body.traced S p (Fin.cons x env)
        let selected := (elements r.1).filter (fun x => (test x).1 = true)
        let out := ofFinset (selected.image (fun x => (val x).1))
        (out, insert out (r.2 ∪ (elements r.1).biUnion (fun x => (test x).2) ∪
          selected.biUnion (fun x => (val x).2)))
    | _, .iterate step, env =>
        tracedLoop p (fun x => step.traced S p (Fin.cons x env)) (p+1) emptyHF
  def Formula.traced {A : Type} [Fintype A] (S : Input A) (p : ℕ) :
      {n : ℕ} → Formula n → (Fin n → HF A) → Traced A Bool
    | _, .equal a b, env =>
        let x := a.traced S p env
        let y := b.traced S p env
        (decide (x.1 = y.1),x.2 ∪ y.2)
    | _, .input r a b, env =>
        let x := a.traced S p env
        let y := b.traced S p env
        (inputHF S r x.1 y.1,x.2 ∪ y.2)
    | _, .neg a, env =>
        let x := a.traced S p env
        (!x.1,x.2)
    | _, .and a b, env =>
        let x := a.traced S p env
        let y := b.traced S p env
        (x.1 && y.1,x.2 ∪ y.2)
    | _, .or a b, env =>
        let x := a.traced S p env
        let y := b.traced S p env
        (x.1 || y.1,x.2 ∪ y.2)
    | _, .wsc _ _ _ _, _ => (false,∅)
end

variable {A : Type} [Fintype A]

omit [Fintype A] in
lemma iterationLoop_traced (q : ℕ) (step : HF A → Result (HF A))
    (ts : HF A → Traced A (HF A)) (h : ∀ x, step x = some (ts x).1)
    (fuel : ℕ) (x : HF A) :
    iterationLoop q step fuel x = some (tracedLoop q ts fuel x).1 := by
  induction fuel generalizing x with
  | zero => rfl
  | succ fuel ih =>
    by_cases hx : (TC x).card ≤ q
    · simp only [iterationLoop,tracedLoop,ite_eq_left hx,h x,Option.bind_some]
      by_cases he : x = (ts x).1
      · simp only [ite_eq_left he]
      · simp only [ite_eq_right he]
        exact ih _
    · simp only [iterationLoop,tracedLoop,ite_eq_right hx]

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type}

def ClosedTrace (F : Finset (HF A)) : Prop := ∀ x ∈ F, closure x ⊆ F

lemma closedTrace_closure (x : HF A) : ClosedTrace (closure x) := by
  intro y hy
  exact closure_subset_of_transitive (fun z hz w hw => closure_transitive hz hw) hy

lemma closedTrace_union {F G : Finset (HF A)} (hF : ClosedTrace F) (hG : ClosedTrace G) :
    ClosedTrace (F ∪ G) := by
  intro x hx y hy
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_left _ (hF _ hx hy)
  · exact Finset.mem_union_right _ (hG _ hx hy)

lemma closedTrace_biUnion {X : Type} (t : Finset X) (f : X → Finset (HF A))
    (hf : ∀ x ∈ t, ClosedTrace (f x)) : ClosedTrace (t.biUnion f) := by
  intro x hx y hy
  obtain ⟨z,hz,hxz⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨z,hz,hf z hz _ hxz hy⟩

lemma closedTrace_insert {F : Finset (HF A)} (hF : ClosedTrace F) (x : HF A)
    (hx : closure x ⊆ insert x F) : ClosedTrace (insert x F) := by
  intro y hy z hz
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact hx hz
  · exact Finset.mem_insert_of_mem (hF y hy hz)

lemma closure_emptyHF : closure (emptyHF : HF A) = {emptyHF} := by
  simp only [emptyHF,closure_ofFinset,familyClosure,Finset.biUnion_empty,Finset.insert_empty]

lemma closure_unionHF_subset (x : HF A) :
    closure (unionHF x) ⊆ insert (unionHF x) (closure x) := by
  rw [unionHF,closure_ofFinset]
  intro z hz
  simp only [Finset.mem_insert] at hz
  rcases hz with he | hz
  · exact Finset.mem_insert.mpr (Or.inl he)
  apply Finset.mem_insert_of_mem
  obtain ⟨y,hy,hzy⟩ := mem_familyClosure.mp hz
  obtain ⟨w,hw,hyw⟩ := Finset.mem_biUnion.mp hy
  exact (closure_member_subset hw) ((closure_member_subset hyw) hzy)

lemma closure_uniqueHF_subset (x : HF A) :
    closure (uniqueHF x) ⊆ insert (uniqueHF x) (closure x) := by
  unfold uniqueHF
  split
  · rename_i h
    have hm : h.choose ∈ x := by
      change h.choose ∈ elements x
      exact Eq.mpr (congrArg (fun t : Finset (HF A) => h.choose ∈ t) h.choose_spec)
        (Finset.mem_singleton_self _)
    exact (closure_member_subset hm).trans (Finset.subset_insert _ _)
  · rw [closure_emptyHF]
    exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)

lemma tracedLoop_closure_subset (p : ℕ) (step : HF A → Traced A (HF A))
    (hs : ∀ x, closure (step x).1 ⊆ (step x).2) (fuel : ℕ) (x : HF A) :
    closure (tracedLoop p step fuel x).1 ⊆ (tracedLoop p step fuel x).2 := by
  induction fuel generalizing x with
  | zero => exact Finset.Subset.refl _
  | succ fuel ih =>
    simp only [tracedLoop]
    split_ifs with hb he
    · calc
        closure x = closure (step x).1 := congrArg closure he
        _ ⊆ (step x).2 := hs x
    · exact (ih _).trans Finset.subset_union_right
    · exact Finset.Subset.refl _

lemma tracedLoop_closed (p : ℕ) (step : HF A → Traced A (HF A))
    (hs : ∀ x, ClosedTrace (step x).2) (fuel : ℕ) (x : HF A) :
    ClosedTrace (tracedLoop p step fuel x).2 := by
  induction fuel generalizing x with
  | zero => exact closedTrace_closure _
  | succ fuel ih =>
    simp only [tracedLoop]
    split_ifs
    · exact hs x
    · exact closedTrace_union (hs x) (ih _)
    · exact closedTrace_closure _

variable [Fintype A]

lemma Term.traced_closure (S : Input A) (p : ℕ) {n : ℕ} (t : Term n)
    (env : Fin n → HF A) : closure (t.traced S p env).1 ⊆ (t.traced S p env).2 := by
  cases t with
  | var j => exact Finset.Subset.refl _
  | empty => exact Finset.Subset.refl _
  | atoms => exact Finset.Subset.refl _
  | pair a b =>
    intro z hz
    have hh := closure_double_subset _ _ hz
    simp only [Term.traced,Finset.mem_insert,Finset.mem_union] at hh ⊢
    rcases hh with he | ha | hb
    · exact Or.inl he
    · exact Or.inr (Or.inl (a.traced_closure S p env ha))
    · exact Or.inr (Or.inr (b.traced_closure S p env hb))
  | union a =>
    exact (closure_unionHF_subset _).trans (Finset.insert_subset_insert _ (a.traced_closure S p env))
  | unique a =>
    exact (closure_uniqueHF_subset _).trans (Finset.insert_subset_insert _ (a.traced_closure S p env))
  | card a => exact Finset.subset_union_left
  | comprehend body range guard =>
    simp only [Term.traced,closure_ofFinset]
    intro z hz
    simp only [Finset.mem_insert] at hz
    rcases hz with he | hz
    · exact Finset.mem_insert.mpr (Or.inl he)
    apply Finset.mem_insert_of_mem
    obtain ⟨y,hy,hzy⟩ := mem_familyClosure.mp hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨x,hx,body.traced_closure S p _ hzy⟩)
  | iterate step =>
    exact tracedLoop_closure_subset p _ (fun x => step.traced_closure S p (Fin.cons x env)) _ _

lemma Term.traced_self (S : Input A) (p : ℕ) {n : ℕ} (t : Term n)
    (env : Fin n → HF A) : (t.traced S p env).1 ∈ (t.traced S p env).2 :=
  t.traced_closure S p env (mem_closure_self _)

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary Finset

variable {A : Type}

lemma closure_eq_insert_TC (x : HF A) : closure x = insert x (TC x) := by
  rw [Hereditary.closure]
  ext y
  simp only [TC,mem_insert,mem_biUnion,mem_attach,true_and,Subtype.exists]
  constructor <;> rintro (h | ⟨a,ha,h⟩)
  · exact Or.inl h
  · exact Or.inr ⟨a,ha,h⟩
  · exact Or.inl h
  · exact Or.inr ⟨a,ha,h⟩

lemma closure_card_le_TC (x : HF A) : (closure x).card ≤ (TC x).card+1 := by
  rw [closure_eq_insert_TC]
  exact card_insert_le _ _

lemma card_closure_atoms [Fintype A] :
    (closure (ofFinset (univ.image (atom (A := A))))).card ≤ Fintype.card A+1 := by
  have he : familyClosure (univ.image (atom (A := A))) = univ.image atom := by
    ext x
    simp only [familyClosure,mem_biUnion,mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨_,⟨a,rfl⟩,h⟩
      rw [closure_atom] at h
      exact ⟨a,(Finset.mem_singleton.mp h).symm⟩
    · rintro ⟨a,rfl⟩
      exact ⟨atom a,⟨a,rfl⟩,mem_closure_self _⟩
  have hh : closure (ofFinset (univ.image (atom (A := A)))) =
      insert (ofFinset (univ.image atom)) (univ.image atom) := by
    rw [closure_ofFinset,he]
    ext x
    simp only [mem_insert,mem_image,mem_univ,true_and]
  rw [hh]
  exact (card_insert_le _ _).trans (Nat.add_le_add_right
    (card_image_le.trans (by rw [card_univ])) 1)

lemma tracedLoop_card (p : ℕ) (step : HF A → Traced A (HF A)) (C : ℕ)
    (hs : ∀ x, (TC x).card ≤ p → (step x).2.card ≤ C) (fuel : ℕ) (x : HF A) :
    (tracedLoop p step fuel x).2.card ≤ fuel*C+1 := by
  induction fuel generalizing x with
  | zero => simp only [tracedLoop,closure_emptyHF,card_singleton,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ fuel ih =>
    simp only [tracedLoop]
    split_ifs with hb he
    · change (step x).2.card ≤ (fuel+1)*C+1
      have hh := hs x hb
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    · have hh := (card_union_le (step x).2 (tracedLoop p step fuel (step x).1).2).trans
        (add_le_add (hs x hb) (ih (step x).1))
      calc
        _ ≤ C + (fuel*C+1) := hh
        _ = (fuel+1)*C+1 := by ring
    · simp only [closure_emptyHF,card_singleton]
      omega

mutual
  def Term.traceBound : {n : ℕ} → Term n → Polynomial ℕ
    | _, .var _ => .X
    | _, .empty => 1
    | _, .atoms => .X
    | _, .pair a b => 1+a.traceBound+b.traceBound
    | _, .union a | _, .unique a => 1+a.traceBound
    | _, .card a => 1+2*a.traceBound
    | _, .comprehend body range guard => 1+range.traceBound+range.traceBound *
        (guard.traceBound.comp (.X+range.traceBound)+body.traceBound.comp (.X+range.traceBound))
    | _, .iterate step => 1+.X*(step.traceBound.comp (2*.X))
  def Formula.traceBound : {n : ℕ} → Formula n → Polynomial ℕ
    | _, .equal a b | _, .input _ a b => a.traceBound+b.traceBound
    | _, .neg a => a.traceBound
    | _, .and a b | _, .or a b => a.traceBound+b.traceBound
    | _, .wsc _ _ _ _ => 0
end

variable [Fintype A]

def tracePotential {n : ℕ} (p : ℕ) (env : Fin n → HF A) : ℕ :=
  Fintype.card A+p+1+∑ j, (closure (env j)).card

lemma tracePotential_var {n : ℕ} (p : ℕ) (env : Fin n → HF A) (j : Fin n) :
    (closure (env j)).card ≤ tracePotential p env := by
  unfold tracePotential
  exact (single_le_sum (f := fun j => (closure (env j)).card)
    (fun _ _ => Nat.zero_le _) (mem_univ j)).trans (Nat.le_add_left _ _)

lemma tracePotential_cons {n : ℕ} (p : ℕ) (env : Fin n → HF A) (x : HF A) :
    tracePotential p (Fin.cons x env) = tracePotential p env+(closure x).card := by
  simp only [tracePotential,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
  omega

end

end WitnessedChoice.BGS

end

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_TermGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary WitnessedSeparation.HFCoding

variable {A : Type}

def LoopGraph (d : Set (HF A)) (p : ℕ) {n : ℕ}
    (step : Domain d → (Fin (n+1) → Domain d) → Prop) :
    ℕ → Domain d → Domain d → (Fin n → Domain d) → Prop
  | 0, z, _, _ => z.val = emptyHF
  | fuel+1, z, x, env =>
      ((TC x.val).card > p ∧ z.val = emptyHF) ∨
      ((TC x.val).card ≤ p ∧ ∃ y : Domain d, step y (Fin.cons x env) ∧
        ((x = y ∧ z = x) ∨ (x ≠ y ∧ LoopGraph d p step fuel z y env)))

mutual
  def Term.Graph [Fintype A] (d : Set (HF A)) (S : Input A) (p K : ℕ) :
      {n : ℕ} → Term n → Domain d → (Fin n → Domain d) → Prop
    | _, .var j, z, env => z = env j
    | _, .empty, z, _ => z.val = emptyHF
    | _, .atoms, z, _ => z.val = ofFinset (Finset.univ.image atom)
    | _, .pair a b, z, env => ∃ x y : Domain d,
        a.Graph d S p K x env ∧ b.Graph d S p K y env ∧ z.val = double x.val y.val
    | _, .union a, z, env => ∃ x : Domain d, a.Graph d S p K x env ∧ z.val = unionHF x.val
    | _, .unique a, z, env => ∃ x : Domain d, a.Graph d S p K x env ∧ z.val = uniqueHF x.val
    | _, .card a, z, env => ∃ x : Domain d, a.Graph d S p K x env ∧
        (elements x.val).card ≤ K ∧ z.val = cardHF x.val
    | _, .comprehend body range guard, z, env => ∃ r : Domain d,
        range.Graph d S p K r env ∧
        (∀ x : Domain d, x.val ∈ r.val → ∃ b : Bool,
          guard.Graph d S p K b (Fin.cons x env) ∧
            (b = true → ∃ y : Domain d, body.Graph d S p K y (Fin.cons x env))) ∧
        isSet z.val = true ∧ ∀ y : Domain d, y.val ∈ z.val ↔ ∃ x : Domain d,
          x.val ∈ r.val ∧ guard.Graph d S p K true (Fin.cons x env) ∧
            body.Graph d S p K y (Fin.cons x env)
    | _, .iterate step, z, env => ∃ x : Domain d, x.val = emptyHF ∧
        LoopGraph d p (step.Graph d S p K) (p+1) z x env
  def Formula.Graph [Fintype A] (d : Set (HF A)) (S : Input A) (p K : ℕ) :
      {n : ℕ} → Formula n → Bool → (Fin n → Domain d) → Prop
    | _, .equal a b, v, env => ∃ x y : Domain d,
        a.Graph d S p K x env ∧ b.Graph d S p K y env ∧ v = decide (x.val = y.val)
    | _, .input r a b, v, env => ∃ x y : Domain d,
        a.Graph d S p K x env ∧ b.Graph d S p K y env ∧ v = inputHF S r x.val y.val
    | _, .neg a, v, env => ∃ b : Bool, a.Graph d S p K b env ∧ v = !b
    | _, .and a b, v, env => ∃ c e : Bool, a.Graph d S p K c env ∧
        b.Graph d S p K e env ∧ v = (c && e)
    | _, .or a b, v, env => ∃ c e : Bool, a.Graph d S p K c env ∧
        b.Graph d S p K e env ∧ v = (c || e)
    | _, .wsc _ _ _ _, _, _ => False
end

lemma domain_cons_val {d : Set (HF A)} {n : ℕ} (x : Domain d) (env : Fin n → Domain d) :
    (fun j => ((Fin.cons x env : Fin (_+1) → Domain d) j).val) = Fin.cons x.val (fun j => (env j).val) := by
  funext j
  exact Fin.cases rfl (fun _ => rfl) j

lemma LoopGraph.sound {d : Set (HF A)} (p : ℕ) {n : ℕ}
    (step : Domain d → (Fin (n+1) → Domain d) → Prop)
    (ts : HF A → Traced A (HF A)) (env : Fin n → Domain d)
    (hs : ∀ x y : Domain d, step y (Fin.cons x env) → y.val = (ts x.val).1)
    (fuel : ℕ) (z x : Domain d) (h : LoopGraph d p step fuel z x env) :
    z.val = (tracedLoop p ts fuel x.val).1 := by
  induction fuel generalizing z x with
  | zero => exact h
  | succ fuel ih =>
    rcases h with ⟨hb,hz⟩ | ⟨hb,y,hy,he⟩
    · simpa only [tracedLoop,ite_eq_right (by omega : ¬ (TC x.val).card ≤ p)] using hz
    · have hval := hs x y hy
      rcases he with ⟨rfl,rfl⟩ | ⟨hne,hrec⟩
      · simp only [tracedLoop,ite_eq_left hb,ite_eq_left hval]
      · have hn : x.val ≠ (ts x.val).1 := fun h => hne (Subtype.ext (h.trans hval.symm))
        simp only [tracedLoop,ite_eq_left hb,ite_eq_right hn]
        rw [← hval]
        exact ih z y hrec

variable [Fintype A]

mutual
  lemma Term.graph_sound (d : Set (HF A)) (S : Input A) (p K : ℕ)
      (hd : ∀ x ∈ d, ∀ y, y ∈ x → y ∈ d) {n : ℕ}
      (t : Term n) (z : Domain d) (env : Fin n → Domain d)
      (h : t.Graph d S p K z env) : z.val = (t.traced S p (fun j => (env j).val)).1 := by
    cases t with
    | var j => exact congrArg Subtype.val h
    | empty => exact h
    | atoms => exact h
    | pair a b =>
      obtain ⟨x,y,hx,hy,hz⟩ := h
      change z.val = double (a.traced S p (fun j => (env j).val)).1
        (b.traced S p (fun j => (env j).val)).1
      exact hz.trans (congrArg₂ double (a.graph_sound d S p K hd x env hx)
        (b.graph_sound d S p K hd y env hy))
    | union a =>
      obtain ⟨x,hx,hz⟩ := h
      exact hz.trans (congrArg unionHF (a.graph_sound d S p K hd x env hx))
    | unique a =>
      obtain ⟨x,hx,hz⟩ := h
      exact hz.trans (congrArg uniqueHF (a.graph_sound d S p K hd x env hx))
    | card a =>
      obtain ⟨x,hx,_,hz⟩ := h
      exact hz.trans (congrArg cardHF (a.graph_sound d S p K hd x env hx))
    | comprehend body range guard =>
      obtain ⟨r,hr,hall,hz,hmem⟩ := h
      have her := range.graph_sound d S p K hd r env hr
      apply ext_sets hz (isSet_ofFinset _)
      intro y
      simp only [mem_ofFinset,Finset.mem_image,Finset.mem_filter]
      constructor
      · intro hy
        obtain ⟨x,hx,hg,hb⟩ := (hmem ⟨y,hd _ z.property _ hy⟩).mp hy
        refine ⟨x.val,⟨by rwa [← her],?_⟩,?_⟩
        · have hh := guard.graph_sound d S p K hd true (Fin.cons x env) hg
          simpa only [domain_cons_val] using hh.symm
        · have hh := body.graph_sound d S p K hd ⟨y,hd _ z.property _ hy⟩ (Fin.cons x env) hb
          simpa only [domain_cons_val] using hh.symm
      · rintro ⟨x,⟨hxr,hgt⟩,hey⟩
        have hxd : x ∈ d := hd _ r.property _ (by rwa [her])
        let xx : Domain d := ⟨x,hxd⟩
        have hxx : xx.val ∈ r.val := by change x ∈ r.val; rwa [her]
        obtain ⟨v,hv,hbody⟩ := hall xx hxx
        have he := guard.graph_sound d S p K hd v (Fin.cons xx env) hv
        simp only [domain_cons_val] at he
        have hvt : v = true := he.trans hgt
        obtain ⟨w,hw⟩ := hbody hvt
        have hew := body.graph_sound d S p K hd w (Fin.cons xx env) hw
        simp only [domain_cons_val] at hew
        have hwval : w.val = y := hew.trans hey
        have hyd : y ∈ d := hwval ▸ w.property
        apply (hmem ⟨y,hyd⟩).mpr
        refine ⟨xx,hxx,hvt ▸ hv,?_⟩
        have heq : w = (⟨y,hyd⟩ : Domain d) := Subtype.ext hwval
        rwa [← heq]
    | iterate step =>
      obtain ⟨x,hx,hl⟩ := h
      have hh := LoopGraph.sound p (step.Graph d S p K)
        (fun y => step.traced S p (Fin.cons y (fun j => (env j).val))) env
        (fun x y h => by simpa only [domain_cons_val] using
          step.graph_sound d S p K hd y (Fin.cons x env) h) (p+1) z x hl
      simpa only [Term.traced,hx] using hh
  termination_by sizeOf t
  decreasing_by all_goals subst_vars; simp_wf <;> omega
  lemma Formula.graph_sound (d : Set (HF A)) (S : Input A) (p K : ℕ)
      (hd : ∀ x ∈ d, ∀ y, y ∈ x → y ∈ d) {n : ℕ}
      (f : Formula n) (v : Bool) (env : Fin n → Domain d)
      (h : f.Graph d S p K v env) : v = (f.traced S p (fun j => (env j).val)).1 := by
    cases f with
    | equal a b =>
      obtain ⟨x,y,hx,hy,hv⟩ := h
      exact hv.trans (congrArg₂ (fun x y : HF A => decide (x = y))
        (a.graph_sound d S p K hd x env hx) (b.graph_sound d S p K hd y env hy))
    | input r a b =>
      obtain ⟨x,y,hx,hy,hv⟩ := h
      exact hv.trans (congrArg₂ (inputHF S r)
        (a.graph_sound d S p K hd x env hx) (b.graph_sound d S p K hd y env hy))
    | neg a =>
      obtain ⟨b,hb,hv⟩ := h
      change v = !(a.traced S p (fun j => (env j).val)).1
      exact hv.trans (congrArg Bool.not (a.graph_sound d S p K hd b env hb))
    | and a b =>
      obtain ⟨c,e,hc,he,hv⟩ := h
      exact hv.trans (congrArg₂ Bool.and (a.graph_sound d S p K hd c env hc)
        (b.graph_sound d S p K hd e env he))
    | or a b =>
      obtain ⟨c,e,hc,he,hv⟩ := h
      exact hv.trans (congrArg₂ Bool.or (a.graph_sound d S p K hd c env hc)
        (b.graph_sound d S p K hd e env he))
    | wsc step choice witness output => exact h.elim
  termination_by sizeOf f
  decreasing_by all_goals subst_vars; simp_wf <;> omega
end

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary WitnessedSeparation.HFCoding

variable {A : Type}

def AdmissibleTrace (d : Set (HF A)) (K : ℕ) (F : Finset (HF A)) : Prop :=
  ∀ x ∈ F, x ∈ d ∧ (elements x).card ≤ K

lemma AdmissibleTrace.mono {d : Set (HF A)} {K : ℕ} {F G : Finset (HF A)}
    (h : AdmissibleTrace d K F) (hg : G ⊆ F) : AdmissibleTrace d K G :=
  fun x hx => h x (hg hx)

lemma LoopGraph.complete {d : Set (HF A)} (p K : ℕ) {n : ℕ}
    (step : Domain d → (Fin (n+1) → Domain d) → Prop)
    (ts : HF A → Traced A (HF A)) (env : Fin n → Domain d)
    (hout : ∀ x, (ts x).1 ∈ (ts x).2)
    (hs : ∀ x y : Domain d, AdmissibleTrace d K (ts x.val).2 →
      y.val = (ts x.val).1 → step y (Fin.cons x env))
    (fuel : ℕ) (z x : Domain d)
    (ht : AdmissibleTrace d K (tracedLoop p ts fuel x.val).2)
    (hz : z.val = (tracedLoop p ts fuel x.val).1) :
    LoopGraph d p step fuel z x env := by
  induction fuel generalizing z x with
  | zero => exact hz
  | succ fuel ih =>
    by_cases hb : (TC x.val).card ≤ p
    · have htstep : AdmissibleTrace d K (ts x.val).2 := by
        simp only [tracedLoop,ite_eq_left hb] at ht
        split_ifs at ht with he
        · exact ht
        · exact ht.mono Finset.subset_union_left
      let y : Domain d := ⟨(ts x.val).1,(htstep _ (hout _)).1⟩
      refine Or.inr ⟨hb,y,hs x y htstep rfl,?_⟩
      by_cases he : x.val = (ts x.val).1
      · left
        exact ⟨Subtype.ext he,Subtype.ext (by simpa only [tracedLoop,ite_eq_left hb,ite_eq_left he] using hz)⟩
      · right
        refine ⟨fun h => he (congrArg Subtype.val h),?_⟩
        apply ih z y
        · exact ht.mono (by simp only [tracedLoop,ite_eq_left hb,ite_eq_right he]; exact Finset.subset_union_right)
        · simpa only [tracedLoop,ite_eq_left hb,ite_eq_right he] using hz
    · exact Or.inl ⟨by omega,by simpa only [tracedLoop,ite_eq_right hb] using hz⟩

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary WitnessedSeparation.Counting WitnessedSeparation.HFCoding

variable {ι R : Type} {D : ι → Type} {S : ∀ i, Counting.Structure R (D i)} {m n : ℕ}

lemma uniform_const (P : Prop) : UniformDefinable S m n (fun _ _ => P) := by
  by_cases h : P
  · exact UniformDefinable.falsum.neg.congr (fun _ _ => by simp [h])
  · exact UniformDefinable.falsum.congr (fun _ _ => by simp [h])

lemma uniform_exists_finite {X : Type} [Fintype X] {P : X → ∀ i, (Fin n → D i) → Prop}
    (h : ∀ x, UniformDefinable S m n (P x)) :
    UniformDefinable S m n (fun i v => ∃ x, P x i v) := by
  simpa only [Finset.mem_univ,true_and] using
    UniformDefinable.exists_finset Finset.univ (fun x _ => h x)

lemma uniform_decide {P : ∀ i, (Fin n → D i) → Prop}
    (h : UniformDefinable S m n P) (b : Bool) :
    UniformDefinable S m n (fun i v => b = decide (P i v)) := by
  cases b
  · exact h.neg.congr (fun _ _ => by simp)
  · exact h.congr (fun _ _ => by simp)

lemma uniform_formula_binary
    {P Q : ∀ i, (Fin (n+1) → D i) → Prop} {T : ∀ i, (Fin 2 → D i) → Prop}
    (hP : UniformDefinable S m (n+1) P) (hQ : UniformDefinable S m (n+1) Q)
    (hT : UniformDefinable S m 2 T) (hr : n+1 < m) :
    UniformDefinable S m n (fun i v => ∃ x y,
      P i (Fin.cons x v) ∧ Q i (Fin.cons y v) ∧ T i ![x,y]) := by
  have h1 := hP.reindex (Fin.cons 1 (fun j => j.succ.succ) : Fin (n+1) → Fin (n+2))
  have h2 := hQ.reindex (Fin.cons 0 (fun j => j.succ.succ) : Fin (n+1) → Fin (n+2))
  have h3 := hT.reindex (![1,0] : Fin 2 → Fin (n+2))
  apply (((h1.and (h2.and h3)).ex hr).ex (by omega)).congr
  intro i v
  apply exists_congr; intro x
  apply exists_congr; intro y
  have h1' : Fin.cons y (Fin.cons x v) ∘
      (Fin.cons 1 (fun j => j.succ.succ) : Fin (n+1) → Fin (n+2)) = Fin.cons x v := by
    funext j; exact Fin.cases rfl (fun _ => rfl) j
  have h2' : Fin.cons y (Fin.cons x v) ∘
      (Fin.cons 0 (fun j => j.succ.succ) : Fin (n+1) → Fin (n+2)) = Fin.cons y v := by
    funext j; exact Fin.cases rfl (fun _ => rfl) j
  have h3' : Fin.cons y (Fin.cons x v) ∘ (![1,0] : Fin 2 → Fin (n+2)) = ![x,y] := by
    funext j; fin_cases j <;> rfl
  simp only [h1',h2',h3']

variable {A : ι → Type} (d : ∀ i, Set (HF (A i)))

variable (T : ∀ i, Counting.Structure R (Domain (d i)))

variable (hmem : UniformDefinable T m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable T m 1 (fun _ v => isSet (v 0).val = true))

include hmem hset in
lemma uniform_BGS_comprehension
    {P : ∀ i, Domain (d i) → (Fin n → Domain (d i)) → Prop}
    {Q : ∀ i, Bool → (Fin (n+1) → Domain (d i)) → Prop}
    {B : ∀ i, Domain (d i) → (Fin (n+1) → Domain (d i)) → Prop}
    (hP : UniformDefinable T m (n+1) (fun i v => P i (v 0) (Fin.tail v)))
    (hQ : ∀ b, UniformDefinable T m (n+1) (fun i v => Q i b v))
    (hB : UniformDefinable T m (n+2) (fun i v => B i (v 0) (Fin.tail v)))
    (hm : n+4 ≤ m) : UniformDefinable T m (n+1) (fun i v => ∃ r,
      P i r (Fin.tail v) ∧
      (∀ x : Domain (d i), x.val ∈ r.val → ∃ b : Bool,
        Q i b (Fin.cons x (Fin.tail v)) ∧
          (b = true → ∃ y : Domain (d i), B i y (Fin.cons x (Fin.tail v)))) ∧
      isSet (v 0).val = true ∧ ∀ y : Domain (d i), y.val ∈ (v 0).val ↔
        ∃ x : Domain (d i), x.val ∈ r.val ∧ Q i true (Fin.cons x (Fin.tail v)) ∧
          B i y (Fin.cons x (Fin.tail v))) := by
  have hBtotal := (hB.reindex
    (Fin.cons 0 (Fin.cons 1 (fun j => j.succ.succ.succ.succ)) : Fin (n+2) → Fin (n+4))).ex (by omega)
  have htotal := ((hmem.reindex (![0,1] : Fin 2 → Fin (n+3))).imp
    (uniform_exists_finite (fun b : Bool =>
      ((hQ b).reindex (Fin.cons 0 (fun j => j.succ.succ.succ) : Fin (n+1) → Fin (n+3))).and
        ((uniform_const (b = true)).imp hBtotal)))).all (by omega)
  have hguard := (hQ true).reindex
    (Fin.cons 0 (fun j => j.succ.succ.succ.succ) : Fin (n+1) → Fin (n+4))
  have hbody := hB.reindex
    (Fin.cons 1 (Fin.cons 0 (fun j => j.succ.succ.succ.succ)) : Fin (n+2) → Fin (n+4))
  have hrhs := ((hmem.reindex (![0,2] : Fin 2 → Fin (n+4))).and (hguard.and hbody)).ex (by omega)
  have hext := ((hmem.reindex (![0,2] : Fin 2 → Fin (n+3))).iff hrhs).all (by omega)
  have hbound := hP.reindex (Fin.cons 0 (fun j => j.succ.succ) : Fin (n+1) → Fin (n+2))
  have hset' := hset.reindex (![1] : Fin 1 → Fin (n+2))
  apply ((hbound.and (htotal.and (hset'.and hext))).ex (by omega)).congr
  intro i v
  simp only [Fin.comp_cons,Fin.cons_zero,Fin.tail_cons,Function.comp_apply]
  rfl

lemma LoopGraph.uniform (p : ℕ)
    (step : ∀ i, Domain (d i) → (Fin (n+1) → Domain (d i)) → Prop)
    (hstep : UniformDefinable T m (n+2) (fun i v => step i (v 0) (Fin.tail v)))
    (hcut : UniformDefinable T m 1 (fun _ v => (TC (v 0).val).card ≤ p))
    (hemp : UniformDefinable T m 1 (fun _ v => (v 0).val = emptyHF))
    (hm : n+2 < m) (fuel : ℕ) : UniformDefinable T m (n+2)
      (fun i v => LoopGraph (d i) p (step i) fuel (v 0) (v 1) (Fin.tail (Fin.tail v))) := by
  induction fuel with
  | zero => exact hemp.reindex ![0]
  | succ fuel ih =>
    have hc := hcut.reindex (![1] : Fin 1 → Fin (n+2))
    have hz := hemp.reindex (![0] : Fin 1 → Fin (n+2))
    have hs := hstep.reindex (Fin.cons 0 (Fin.cons 2 (fun j => j.succ.succ.succ)) : Fin (n+2) → Fin (n+3))
    have hxy : UniformDefinable T m (n+3) (fun _ v => v 2 = v 0) := UniformDefinable.equal 2 0
    have hzx : UniformDefinable T m (n+3) (fun _ v => v 1 = v 2) := UniformDefinable.equal 1 2
    have hrec := ih.reindex (Fin.cons 1 (Fin.cons 0 (fun j => j.succ.succ.succ)) : Fin (n+2) → Fin (n+3))
    have hy := (hs.and ((hxy.and hzx).or (hxy.neg.and hrec))).ex hm
    apply ((hc.neg.and hz).or (hc.and hy)).congr
    intro i v
    have hvc : v ∘ (![1] : Fin 1 → Fin (n+2)) = ![v 1] := by
      funext j; fin_cases j; rfl
    have hvz : v ∘ (![0] : Fin 1 → Fin (n+2)) = ![v 0] := by
      funext j; fin_cases j; rfl
    have hs' (y : Domain (d i)) : Fin.cons y v ∘
        (Fin.cons 0 (Fin.cons 2 (fun j => j.succ.succ.succ)) : Fin (n+2) → Fin (n+3)) =
        Fin.cons y (Fin.cons (v 1) (Fin.tail (Fin.tail v))) := by
      funext j; refine Fin.cases rfl (fun j => ?_) j
      exact Fin.cases rfl (fun _ => rfl) j
    have hr' (y : Domain (d i)) : Fin.cons y v ∘
        (Fin.cons 1 (Fin.cons 0 (fun j => j.succ.succ.succ)) : Fin (n+2) → Fin (n+3)) =
        Fin.cons (v 0) (Fin.cons y (Fin.tail (Fin.tail v))) := by
      funext j; refine Fin.cases rfl (fun j => ?_) j
      exact Fin.cases rfl (fun _ => rfl) j
    simp only [hvc,hvz,hs',hr',Fin.cons_zero,Fin.tail_cons]
    simp only [LoopGraph,not_le]
    rfl

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary WitnessedSeparation.Counting WitnessedSeparation.HFCoding

lemma unionHF_eq_operational {A : Type} (x : HF A) : unionHF x = Operational.unionHF x := by
  unfold unionHF Operational.unionHF
  congr 1
  ext y
  simp only [Finset.mem_biUnion]

lemma atomsHF_eq_operational {A : Type} [Fintype A] :
    ofFinset (Finset.univ.image (atom (A := A))) = (Operational.allAtoms : HF A) := by
  unfold Operational.allAtoms
  congr 1
  ext y
  simp only [Finset.mem_image]

mutual
  def Term.graphWidth : {n : ℕ} → Term n → ℕ
    | n, .var _ | n, .empty | n, .atoms => n+8
    | n, .pair a b => n+8+a.graphWidth+b.graphWidth
    | n, .union a | n, .unique a | n, .card a => n+8+a.graphWidth
    | n, .comprehend b r g => n+8+b.graphWidth+r.graphWidth+g.graphWidth
    | n, .iterate step => n+8+step.graphWidth
  def Formula.graphWidth : {n : ℕ} → Formula n → ℕ
    | n, .equal a b | n, .input _ a b => n+8+a.graphWidth+b.graphWidth
    | n, .neg a => n+8+a.graphWidth
    | n, .and a b | n, .or a b => n+8+a.graphWidth+b.graphWidth
    | n, .wsc _ _ _ _ => n+8
end

end

end WitnessedChoice.BGS

end

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary Finset

open WitnessedSeparation.Operational (lift lift_elements lift_ofFinset lift_empty lift_double)

variable {A B : Type}

lemma lift_emptyHF (e : A ≃ B) : lift e emptyHF = emptyHF := Operational.lift_empty e

lemma lift_unionHF (e : A ≃ B) (x : HF A) : lift e (unionHF x) = unionHF (lift e x) := by
  simpa only [unionHF_eq_operational] using Operational.lift_union e x

lemma lift_uniqueHF (e : A ≃ B) (x : HF A) : lift e (uniqueHF x) = uniqueHF (lift e x) :=
  Operational.lift_unique e x

lemma lift_cardHF (e : A ≃ B) (x : HF A) : lift e (cardHF x) = cardHF (lift e x) :=
  Operational.lift_card e x

lemma lift_atomsHF [Fintype A] [Fintype B] (e : A ≃ B) :
    lift e (ofFinset (univ.image (atom (A := A)))) = ofFinset (univ.image atom) := by
  simpa only [atomsHF_eq_operational] using Operational.lift_allAtoms e

lemma lift_inputHF (e : A ≃ B) (S : Input A) (T : Input B)
    (h : ∀ r a b, T.rel r (e a) (e b) = S.rel r a b) (r : Symbol) (x y : HF A) :
    inputHF T r (lift e x) (lift e y) = inputHF S r x y := by
  apply Bool.eq_iff_iff.mpr
  simpa only [inputHF,decide_eq_true_eq,Operational.inputRelation] using
    Operational.lift_input e S.rel T.rel h r x y

variable [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
lemma lift_closureHF (e : A ≃ B) (x : HF A) :
    closure (lift e x) = (closure x).image (lift e) := by
  ext y
  have hh := congrArg (fun z : Finset (HF B) => y ∈ z) (Operational.lift_closure e x)
  simpa only [mem_image] using Iff.of_eq hh

omit [Fintype A] [Fintype B] in
lemma lift_TC (e : A ≃ B) (x : HF A) : TC (lift e x) = (TC x).image (lift e) := by
  simp only [TC,lift_elements,biUnion_image,image_biUnion,lift_closureHF]

omit [Fintype A] [Fintype B] in
lemma lift_TC_card (e : A ≃ B) (x : HF A) : (TC (lift e x)).card = (TC x).card := by
  rw [lift_TC,card_image_of_injective _ (lift e).injective]

omit [Fintype A] [Fintype B] in
lemma lift_cons (e : A ≃ B) {n : ℕ} (env : Fin n → HF A) (x : HF A) :
    (fun j => lift e ((Fin.cons x env : Fin (n+1) → HF A) j)) =
      Fin.cons (lift e x) (fun j => lift e (env j)) := by
  funext j; exact Fin.cases rfl (fun _ => rfl) j

omit [Fintype A] [Fintype B] in
lemma tracedLoop_transport (e : A ≃ B) (p : ℕ)
    (a : HF A → Traced A (HF A)) (b : HF B → Traced B (HF B))
    (h : ∀ x, b (lift e x) = (lift e (a x).1,(a x).2.image (lift e)))
    (fuel : ℕ) (x : HF A) :
    tracedLoop p b fuel (lift e x) =
      (lift e (tracedLoop p a fuel x).1,(tracedLoop p a fuel x).2.image (lift e)) := by
  induction fuel generalizing x with
  | zero => simp only [tracedLoop,lift_emptyHF,closure_emptyHF,image_singleton]
  | succ fuel ih =>
    simp only [tracedLoop,lift_TC_card,h,Equiv.apply_eq_iff_eq]
    split_ifs with hb he
    · rfl
    · simp only [ih,image_union]
    · simp only [lift_emptyHF,closure_emptyHF,image_singleton]

omit [Fintype A] [Fintype B] in
lemma selected_transport (e : A ≃ B) (r : HF A)
    (a : HF A → Bool) (b : HF B → Bool) (h : ∀ x, b (lift e x) = a x) :
    ((elements (lift e r)).filter (fun y => b y = true)) =
      ((elements r).filter (fun x => a x = true)).image (lift e) := by
  rw [lift_elements]
  ext y
  simp only [mem_filter,mem_image]
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,hy⟩
    exact ⟨x,⟨hx,by rwa [h] at hy⟩,rfl⟩
  · rintro ⟨x,⟨hx,hy⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,by rwa [h]⟩

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

open WitnessedSeparation.Grid WitnessedSeparation.Quantitative

def gridInput {n : ℕ} (b : Vertex n → Grid.Scalar) : FiniteInput :=
  ⟨Atom b,inferInstance,atomInput b⟩

end

end WitnessedChoice.BGS

end

section

namespace WitnessedChoice

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type} [Fintype A]

def fullAut (S : Input A) : Subgroup (Equiv.Perm A) where
  carrier := {g | ∀ r a b, S.rel r (g a) (g b) = S.rel r a b}
  one_mem' := by intro r a b; rfl
  mul_mem' := by
    intro g h hg hh r a b
    exact (hg r (h a) (h b)).trans (hh r a b)
  inv_mem' := by
    intro g hg r a b
    symm
    simpa using hg r (g⁻¹ a) (g⁻¹ b)

def paramAut (S : Input A) (α : HF A) : Subgroup (Equiv.Perm A) :=
  fullAut S ⊓ MulAction.stabilizer (Equiv.Perm A) α

def stateCode (x : Finset A) : HF A := ofFinset (x.image atom)

def choiceCode : Option A → HF A
  | none => ordinal 0
  | some a => atom a

structure Selection (A : Type) where
  candidates : Finset A → Finset A
  witnesses : Finset A → Finset (Equiv.Perm A)

namespace Selection

variable (P : Selection A)

def TransitiveAt (x : Finset A) : Prop :=
  ∀ a ∈ P.candidates x, ∀ b ∈ P.candidates x,
    ∃ g ∈ P.witnesses x, g a = b

def choices (x : Finset A) : Finset (Option A) :=
  if (P.candidates x).Nonempty ∧ P.TransitiveAt x then
    (P.candidates x).image some
  else {none}

def advance (x : Finset A) : Option A → Finset A
  | none => x
  | some a => insert a x

def Prefix (b : ℕ → Finset A) (c : ℕ → Option A) (k : ℕ) : Prop :=
  b 0 = ∅ ∧ ∀ i < k, c i ∈ P.choices (b i) ∧ b (i+1) = advance (b i) (c i)

def FirstStabilization (b : ℕ → Finset A) (c : ℕ → Option A) (t : ℕ) : Prop :=
  P.Prefix b c (t+1) ∧ (∀ i < t, b i ≠ b (i+1)) ∧ b t = b (t+1)

def witnessAt (_terminal intermediate : Finset A) : Finset (Equiv.Perm A) :=
  P.witnesses intermediate

def HistoryAut (S : Input A) (α : HF A) (b : ℕ → Finset A) (i : ℕ)
    (g : Equiv.Perm A) : Prop :=
  g ∈ paramAut S α ∧ ∀ j ≤ i, g • stateCode (b j) = stateCode (b j)

def WitnessedAt (S : Input A) (α : HF A) (b : ℕ → Finset A)
    (terminal : Finset A) (i : ℕ) : Prop :=
  (P.choices (b i)).Nonempty ∧
  (∀ g ∈ P.witnessAt terminal (b i), HistoryAut S α b i g) ∧
  ∀ u ∈ P.choices (b i), ∀ v ∈ P.choices (b i),
    ∃ g ∈ P.witnessAt terminal (b i), g • choiceCode u = choiceCode v

def Filtered (S : Input A) (α : HF A) : Prop :=
  (∀ x, (1 : Equiv.Perm A) ∈ P.witnesses x) ∧
  (∀ x g, g ∈ P.witnesses x → g ∈ paramAut S α) ∧
  (∀ x g, g ∈ P.witnesses x → ∀ a ∈ x, g a = a)

end Selection

end

end WitnessedChoice

end

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_Syntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace WitnessedChoice

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type}

@[simp] theorem stateCode_inj {x y : Finset A} : stateCode x = stateCode y ↔ x = y := by
  unfold stateCode
  rw [ofFinset_inj]
  exact Finset.image_inj atom_injective

@[simp] theorem smul_stateCode (g : Equiv.Perm A) (x : Finset A) :
    g • stateCode x = stateCode (x.image g) := by
  simp only [stateCode, smul_ofFinset, Finset.image_image]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_image, Function.comp_apply, smul_atom]
  rfl

@[simp] theorem smul_choiceCode (g : Equiv.Perm A) (c : Option A) :
    g • choiceCode c = choiceCode (c.map g) := by
  cases c <;> simp [choiceCode, ordinal, smul_ofFinset]

namespace Selection

variable {P : Selection A}

theorem choices_nonempty (x : Finset A) : (P.choices x).Nonempty := by
  unfold choices
  split_ifs with h
  · exact h.1.image _
  · exact Finset.singleton_nonempty _

@[simp] theorem some_mem_choices {x : Finset A} {a : A} :
    some a ∈ P.choices x ↔ a ∈ P.candidates x ∧ P.TransitiveAt x := by
  unfold choices
  split_ifs with h
  · simp [h.2]
  · simp only [Finset.mem_singleton, reduceCtorEq, false_iff, not_and]
    intro ha ht
    exact h ⟨⟨a, ha⟩, ht⟩

@[simp] theorem none_mem_choices {x : Finset A} :
    none ∈ P.choices x ↔ ¬ ((P.candidates x).Nonempty ∧ P.TransitiveAt x) := by
  unfold choices
  split_ifs <;> simp_all

end Selection

end

end WitnessedChoice

end

section

namespace WitnessedChoice

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type}

@[simp] theorem choiceCode_inj {c d : Option A} : choiceCode c = choiceCode d ↔ c = d := by
  cases c with
  | none =>
    cases d with
    | none => simp
    | some a =>
      constructor
      · intro h
        have he := congrArg isSet h
        simp [choiceCode, ordinal] at he
      · simp
  | some a =>
    cases d with
    | none =>
      constructor
      · intro h
        have he := congrArg isSet h
        simp [choiceCode, ordinal] at he
      · simp
    | some b =>
      simp only [choiceCode, Option.some.injEq]
      exact atom_injective.eq_iff

@[simp] theorem image_inv_image (g : Equiv.Perm A) (x : Finset A) :
    (x.image g).image (g⁻¹ : Equiv.Perm A) = x := by
  simp [Finset.image_image, Function.comp_def]

namespace Selection

variable [Fintype A]

variable {P : Selection A} {S : Input A} {α : HF A}

omit [Fintype A] in
@[simp] theorem advance_image (g : Equiv.Perm A) (x : Finset A) (c : Option A) :
    (advance x c).image g = advance (x.image g) (c.map g) := by
  cases c <;> simp [advance]

def selected (x : Finset A) : Option A := (choices_nonempty (P := P) x).choose

def run (P : Selection A) : ℕ → Finset A
  | 0 => ∅
  | k+1 => advance (run P k) (P.selected (run P k))

end Selection

end

end WitnessedChoice

end

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type} [Fintype A]

def decodeState (x : HF A) : Finset A := Finset.univ.filter (fun a => atom a ∈ elements x)

def decodeChoice (x : HF A) : Option A :=
  if h : ∃ a, x = atom a then some h.choose else none

@[simp] theorem decodeState_code (x : Finset A) : decodeState (stateCode x) = x := by
  ext a
  simp [decodeState, stateCode, atom_injective.eq_iff]

@[simp] theorem decodeChoice_code (c : Option A) : decodeChoice (choiceCode c) = c := by
  cases c with
  | none =>
    have h : ¬ ∃ a : A, (ordinal (A := A) 0) = atom a := by
      rintro ⟨a, ha⟩
      have hi := congrArg isSet ha
      simp at hi
    simp [choiceCode, decodeChoice, h]
  | some a =>
    change (if h : ∃ b : A, atom a = atom b then some h.choose else none) = some a
    split
    next h => exact congrArg some (atom_injective h.choose_spec.symm)
    next h => exact (h ⟨a, rfl⟩).elim

omit [Fintype A] in
@[simp] theorem TC_stateCode (x : Finset A) : TC (stateCode x) = x.image atom := by
  have hc (a : A) : closure (atom a) = {atom a} := by
    rw [WitnessedSeparation.Hereditary.closure]
    rw [WitnessedSeparation.Hereditary.elements_atom]
    simp
  ext z
  simp [TC, stateCode, hc, eq_comm]

structure Realizes (P : Selection A)
    (step : HF A → HF A → Result (HF A))
    (choice : HF A → Result (HF A))
    (witness : HF A → HF A → Result (HF A)) : Prop where
  choice_eq : ∀ x, choice (stateCode x) =
    some (ofFinset ((P.choices x).image choiceCode))
  step_eq : ∀ x c, c ∈ P.choices x → step (stateCode x) (choiceCode c) =
    some (stateCode (Selection.advance x c))
  witness_eq : ∀ z x, witness (stateCode z) (stateCode x) =
    some (ofFinset ((P.witnesses x).image permutationGraph))

end

end WitnessedChoice.BGS

end

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

def liftRen {n m : ℕ} (f : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.cases 0 (Fin.succ ∘ f)

@[simp] lemma liftRen_zero {n m : ℕ} (f : Fin n → Fin m) : liftRen f 0 = 0 := rfl

@[simp] lemma liftRen_succ {n m : ℕ} (f : Fin n → Fin m) (i : Fin n) :
    liftRen f i.succ = (f i).succ := rfl

lemma cons_comp_liftRen {X : Type} {n m : ℕ} (f : Fin n → Fin m) (env : Fin m → X) (x : X) :
    Fin.cons x env ∘ liftRen f = Fin.cons x (env ∘ f) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

mutual
  def Term.rename {n m : ℕ} (f : Fin n → Fin m) : Term n → Term m
    | .var i => .var (f i)
    | .empty => .empty
    | .atoms => .atoms
    | .pair a b => .pair (a.rename f) (b.rename f)
    | .union a => .union (a.rename f)
    | .unique a => .unique (a.rename f)
    | .card a => .card (a.rename f)
    | .comprehend body range guard => .comprehend (body.rename (liftRen f))
        (range.rename f) (guard.rename (liftRen f))
    | .iterate step => .iterate (step.rename (liftRen f))
  def Formula.rename {n m : ℕ} (f : Fin n → Fin m) : Formula n → Formula m
    | .equal a b => .equal (a.rename f) (b.rename f)
    | .input r a b => .input r (a.rename f) (b.rename f)
    | .neg a => .neg (a.rename f)
    | .and a b => .and (a.rename f) (b.rename f)
    | .or a b => .or (a.rename f) (b.rename f)
    | .wsc step choice witness output => .wsc (step.rename (liftRen (liftRen f)))
        (choice.rename (liftRen f)) (witness.rename (liftRen (liftRen f)))
        (output.rename (liftRen f))
end

mutual
  @[simp] theorem Term.rename_count {n m : ℕ} (t : Term n) (f : Fin n → Fin m) :
      (t.rename f).wscCount = t.wscCount := by
    cases t with
    | var i => rfl
    | empty => rfl
    | atoms => rfl
    | pair a b => simp only [Term.rename,Term.wscCount,a.rename_count,b.rename_count]
    | union a => exact a.rename_count f
    | unique a => exact a.rename_count f
    | card a => exact a.rename_count f
    | comprehend b r g => simp only [Term.rename,Term.wscCount,b.rename_count,r.rename_count,g.rename_count]
    | iterate s => exact s.rename_count (liftRen f)
  @[simp] theorem Formula.rename_count {n m : ℕ} (a : Formula n) (f : Fin n → Fin m) :
      (a.rename f).wscCount = a.wscCount := by
    cases a with
    | equal a b => simp only [Formula.rename,Formula.wscCount,a.rename_count,b.rename_count]
    | input r a b => simp only [Formula.rename,Formula.wscCount,a.rename_count,b.rename_count]
    | neg a => exact a.rename_count f
    | and a b => simp only [Formula.rename,Formula.wscCount,a.rename_count,b.rename_count]
    | or a b => simp only [Formula.rename,Formula.wscCount,a.rename_count,b.rename_count]
    | wsc s c w o => simp only [Formula.rename,Formula.wscCount,s.rename_count,c.rename_count,w.rename_count,o.rename_count]
end

variable {A : Type} [Fintype A]

mutual
  theorem Term.eval_rename (S : Input A) (p : Polynomial ℝ) {n m : ℕ}
      (t : Term n) (ht : t.wscCount = 0) (f : Fin n → Fin m) (env : Fin m → HF A) :
      (t.rename f).eval S p env = t.eval S p (env ∘ f) := by
    cases t with
    | var i => rfl
    | empty => rfl
    | atoms => rfl
    | pair a b =>
      simp only [Term.wscCount,Nat.add_eq_zero_iff] at ht
      simp only [Term.rename,Term.eval,a.eval_rename S p ht.1,b.eval_rename S p ht.2]
    | union a => simp only [Term.rename,Term.eval,a.eval_rename S p ht]
    | unique a => simp only [Term.rename,Term.eval,a.eval_rename S p ht]
    | card a => simp only [Term.rename,Term.eval,a.eval_rename S p ht]
    | comprehend b r g =>
      simp only [Term.wscCount,Nat.add_eq_zero_iff] at ht
      simp only [Term.rename,Term.eval,r.eval_rename S p ht.1.2]
      congr 1
      funext x
      have hb : (fun x => (b.rename (liftRen f)).eval S p (Fin.cons x env)) =
          fun x => b.eval S p (Fin.cons x (env ∘ f)) := by
        funext x
        rw [b.eval_rename S p ht.1.1,cons_comp_liftRen]
      have hg : (fun x => (g.rename (liftRen f)).eval S p (Fin.cons x env)) =
          fun x => g.eval S p (Fin.cons x (env ∘ f)) := by
        funext x
        rw [g.eval_rename S p ht.2,cons_comp_liftRen]
      rw [hb,hg]
    | iterate s =>
      simp only [Term.rename,Term.eval]
      congr 1
      funext x
      rw [s.eval_rename S p ht,cons_comp_liftRen]
  theorem Formula.eval_rename (S : Input A) (p : Polynomial ℝ) {n m : ℕ}
      (a : Formula n) (ht : a.wscCount = 0) (f : Fin n → Fin m) (env : Fin m → HF A) :
      (a.rename f).eval S p env = a.eval S p (env ∘ f) := by
    cases a with
    | equal a b =>
      simp only [Formula.wscCount,Nat.add_eq_zero_iff] at ht
      simp only [Formula.rename,Formula.eval,a.eval_rename S p ht.1,b.eval_rename S p ht.2]
    | input r a b =>
      simp only [Formula.wscCount,Nat.add_eq_zero_iff] at ht
      simp only [Formula.rename,Formula.eval,a.eval_rename S p ht.1,b.eval_rename S p ht.2]
    | neg a => simp only [Formula.rename,Formula.eval,a.eval_rename S p ht]
    | and a b =>
      simp only [Formula.wscCount,Nat.add_eq_zero_iff] at ht
      simp only [Formula.rename,Formula.eval,a.eval_rename S p ht.1,b.eval_rename S p ht.2]
    | or a b =>
      simp only [Formula.wscCount,Nat.add_eq_zero_iff] at ht
      simp only [Formula.rename,Formula.eval,a.eval_rename S p ht.1,b.eval_rename S p ht.2]
    | wsc s c w o => simp only [Formula.wscCount] at ht; omega
end

def Term.up {n : ℕ} (t : Term n) : Term (n+1) := t.rename Fin.succ

def Formula.up {n : ℕ} (a : Formula n) : Formula (n+1) := a.rename Fin.succ

def Formula.truth {n : ℕ} : Formula n := .equal .empty .empty

def Term.singleton {n : ℕ} (a : Term n) : Term n := .pair a a

def Term.cup {n : ℕ} (a b : Term n) : Term n := .union (.pair a b)

def Term.orderedPair {n : ℕ} (a b : Term n) : Term n := .pair a.singleton (.pair a b)

def Formula.existsIn {n : ℕ} (r : Term n) (a : Formula (n+1)) : Formula n :=
  .neg (.equal (.comprehend .empty r a) .empty)

def Formula.allIn {n : ℕ} (r : Term n) (a : Formula (n+1)) : Formula n :=
  .neg (.existsIn r (.neg a))

def Formula.mem {n : ℕ} (a b : Term n) : Formula n :=
  .existsIn b (.equal (.var 0) a.up)

def Term.when {n : ℕ} (a : Term n) (g : Formula n) : Term n :=
  .comprehend a.up (.singleton .empty) g.up

def Term.cond {n : ℕ} (g : Formula n) (a b : Term n) : Term n :=
  .unique ((a.when g).cup (b.when (.neg g)))

@[simp] theorem Term.up_count {n : ℕ} (t : Term n) : t.up.wscCount = t.wscCount :=
  t.rename_count _

@[simp] theorem Formula.up_count {n : ℕ} (f : Formula n) : f.up.wscCount = f.wscCount :=
  f.rename_count _

@[simp] theorem Term.eval_up (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (t : Term n) (h : t.wscCount = 0) (env : Fin n → HF A) (x : HF A) :
    t.up.eval S p (Fin.cons x env) = t.eval S p env :=
  t.eval_rename S p h _ _

@[simp] theorem Formula.eval_up (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (f : Formula n) (h : f.wscCount = 0) (env : Fin n → HF A) (x : HF A) :
    f.up.eval S p (Fin.cons x env) = f.eval S p env :=
  f.eval_rename S p h _ _

omit [Fintype A] in
lemma collect_pure (r : HF A) (g : HF A → Bool) (b : HF A → HF A) :
    collect r (fun x => some (g x)) (fun x => some (b x)) =
      some (ofFinset (((elements r).filter (fun x => g x = true)).image b)) := by
  simp [collect]

omit [Fintype A] in
@[simp] lemma elements_emptyHF : elements (emptyHF : HF A) = ∅ := elements_ofFinset _

omit [Fintype A] in
@[simp] lemma uniqueHF_singleton (x : HF A) : uniqueHF (singleton x) = x := by
  unfold uniqueHF
  have h : ∃ y, elements (singleton x) = {y} := ⟨x,by simp [WitnessedSeparation.Hereditary.singleton]⟩
  rw [dite_eq_left h]
  exact Finset.singleton_injective (h.choose_spec.symm.trans (elements_ofFinset {x}))

omit [Fintype A] in
@[simp] lemma uniqueHF_empty : uniqueHF (emptyHF : HF A) = emptyHF := by
  unfold uniqueHF
  apply dite_eq_right
  simp

omit [Fintype A] in
@[simp] lemma unionHF_double (x y : HF A) :
    unionHF (double x y) = ofFinset (elements x ∪ elements y) := by
  simp [unionHF,double]

lemma Formula.eval_truth (S : Input A) (p : Polynomial ℝ) {n : ℕ} (env : Fin n → HF A) :
    (Formula.truth (n := n)).eval S p env = some true := by
  simp [truth,eval,Term.eval,lift₂]

lemma Formula.eval_existsIn (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (r : Term n) (a : Formula (n+1)) (env : Fin n → HF A)
    {rv : HF A} {av : HF A → Bool} (hr : r.eval S p env = some rv)
    (ha : ∀ x, a.eval S p (Fin.cons x env) = some (av x)) :
    (Formula.existsIn r a).eval S p env =
      some (decide (∃ x ∈ elements rv, av x = true)) := by
  have hf : (fun x => a.eval S p (Fin.cons x env)) = fun x => some (av x) := funext ha
  simp only [existsIn,Formula.eval,Term.eval,hr,Option.bind_some,hf]
  rw [collect_pure]
  simp only [lift₂,Option.bind_some,Option.map_some,Option.some.injEq]
  have he : ofFinset (((elements rv).filter (fun x => av x = true)).image (fun _ => (emptyHF : HF A))) = emptyHF ↔
      ¬ ∃ x ∈ elements rv, av x = true := by
    rw [emptyHF,ofFinset_inj,Finset.image_eq_empty]
    simp
  simp only [he,decide_not,Bool.not_not]

lemma Formula.eval_allIn (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (r : Term n) (a : Formula (n+1)) (env : Fin n → HF A)
    {rv : HF A} {av : HF A → Bool} (hr : r.eval S p env = some rv)
    (ha : ∀ x, a.eval S p (Fin.cons x env) = some (av x)) :
    (Formula.allIn r a).eval S p env =
      some (decide (∀ x ∈ elements rv, av x = true)) := by
  have hn (x : HF A) : (Formula.neg a).eval S p (Fin.cons x env) = some (!(av x)) := by
    simp [Formula.eval,ha]
  change ((Formula.existsIn r (.neg a)).eval S p env).map Bool.not = _
  rw [eval_existsIn S p r (.neg a) env hr hn]
  simp only [Option.map_some,Option.some.injEq]
  have he : (∃ x ∈ elements rv, av x = false) ↔ ¬ (∀ x ∈ elements rv, av x = true) := by
    simp only [not_forall, exists_prop, Bool.not_eq_true]
  simp only [Bool.not_eq_true_eq_eq_false, he, decide_not, Bool.not_not]

lemma Term.eval_singleton (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (a : Term n) (env : Fin n → HF A) {x : HF A}
    (ha : a.eval S p env = some x) :
    a.singleton.eval S p env = some (Hereditary.singleton x) := by
  simp [Term.singleton,eval,ha,lift₂,Hereditary.singleton,double]

lemma Term.eval_cup (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (a b : Term n) (env : Fin n → HF A) {x y : HF A}
    (ha : a.eval S p env = some x) (hb : b.eval S p env = some y) :
    (a.cup b).eval S p env = some (ofFinset (elements x ∪ elements y)) := by
  simp [Term.cup,eval,ha,hb,lift₂]

lemma Term.eval_orderedPair (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (a b : Term n) (env : Fin n → HF A) {x y : HF A}
    (ha : a.eval S p env = some x) (hb : b.eval S p env = some y) :
    (a.orderedPair b).eval S p env = some (Hereditary.pair x y) := by
  simp [Term.orderedPair,Term.singleton,eval,ha,hb,lift₂,
    Hereditary.pair,Hereditary.singleton,double]

lemma Formula.eval_mem (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (a b : Term n) (hz : a.wscCount = 0) (env : Fin n → HF A) {x y : HF A}
    (ha : a.eval S p env = some x) (hb : b.eval S p env = some y) :
    (Formula.mem a b).eval S p env = some (decide (x ∈ elements y)) := by
  have he : ∀ z, (Formula.equal (.var 0) a.up).eval S p (Fin.cons z env) =
      some (decide (z = x)) := by
    intro z
    simp [Formula.eval,Term.eval,Term.eval_up S p a hz env z,ha,lift₂]
  rw [Formula.mem,eval_existsIn S p b _ env hb he]
  congr 1
  simp

lemma Term.eval_when (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (a : Term n) (g : Formula n) (hz : a.wscCount = 0) (hg : g.wscCount = 0)
    (env : Fin n → HF A) {x : HF A} {c : Bool}
    (ha : a.eval S p env = some x) (hc : g.eval S p env = some c) :
    (a.when g).eval S p env = some (if c then Hereditary.singleton x else emptyHF) := by
  simp only [Term.when,eval,Term.eval_singleton S p .empty env rfl,Option.bind_some]
  have hgu : (fun z => g.up.eval S p (Fin.cons z env)) = fun _ => some c := by
    funext z
    rw [Formula.eval_up S p g hg env z,hc]
  have hbo : (fun z => a.up.eval S p (Fin.cons z env)) = fun _ => some x := by
    funext z
    rw [Term.eval_up S p a hz env z,ha]
  rw [hgu,hbo,collect_pure]
  cases c <;> simp [Hereditary.singleton,emptyHF]

lemma Term.eval_cond (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (g : Formula n) (a b : Term n)
    (hg : g.wscCount = 0) (hz : a.wscCount = 0) (hw : b.wscCount = 0)
    (env : Fin n → HF A) {c : Bool} {x y : HF A}
    (hc : g.eval S p env = some c) (ha : a.eval S p env = some x)
    (hb : b.eval S p env = some y) :
    (Term.cond g a b).eval S p env = some (if c then x else y) := by
  have hn : (Formula.neg g).eval S p env = some (!c) := by simp [Formula.eval,hc]
  have hnz : (Formula.neg g).wscCount = 0 := hg
  have hw1 := Term.eval_when S p a g hz hg env ha hc
  have hw2 := Term.eval_when S p b (.neg g) hw hnz env hb hn
  simp only [Term.cond,Term.eval,Term.eval_cup S p _ _ env hw1 hw2,Option.map_some]
  cases c
  · simpa [emptyHF,Hereditary.singleton] using uniqueHF_singleton (A := A) y
  · simpa [emptyHF,Hereditary.singleton] using uniqueHF_singleton (A := A) x

def Term.letIn {n : ℕ} (v : Term n) (b : Term (n+1)) : Term n :=
  .unique (.comprehend b v.singleton .truth)

def Formula.letIn {n : ℕ} (v : Term n) (b : Formula (n+1)) : Formula n :=
  .existsIn v.singleton b

end

end WitnessedChoice.BGS

end

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

@[simp] lemma cons_two {X : Type*} {n : ℕ} (a b c : X) (env : Fin n → X) :
    (Fin.cons a (Fin.cons b (Fin.cons c env)) : Fin (n+3) → X) 2 = c := by
  change (Fin.cons a (Fin.cons b (Fin.cons c env)) : Fin (n+3) → X) (1 : Fin (n+2)).succ = c
  rw [Fin.cons_succ,Fin.cons_one,Fin.cons_zero]

def Term.mapSet {n : ℕ} (r : Term n) (b : Term (n+1)) : Term n :=
  .comprehend b r .truth

def Term.bindSet {n : ℕ} (r : Term n) (b : Term (n+1)) : Term n :=
  .union (r.mapSet b)

def Term.addPairBody {n : ℕ} : Term (n+3) :=
  (Term.var 2).cup ((Term.orderedPair (.var 1) (.var 0)).singleton)

def Term.partialPool {n : ℕ} : ℕ → Term n
  | 0 => Term.empty.singleton
  | k+1 => (partialPool k).bindSet
      (Term.atoms.bindSet (Term.atoms.mapSet Term.addPairBody))

def Term.completeRelation {n : ℕ} : Term (n+1) :=
  (Term.var 0).cup (.comprehend (Term.orderedPair (.var 0) (.var 0)) .atoms
    (.neg (.existsIn .atoms (.mem (Term.orderedPair (.var 1) (.var 0)) (.var 2)))))

def Term.identityRelation {n : ℕ} : Term n :=
  .comprehend (Term.orderedPair (.var 0) (.var 0)) .atoms .truth

def Term.localPool {n : ℕ} (B : ℕ) : Term n :=
  Term.identityRelation.singleton.cup ((Term.partialPool B).mapSet Term.completeRelation)

@[simp] lemma Term.mapSet_count {n : ℕ} (r : Term n) (b : Term (n+1)) :
    (r.mapSet b).wscCount = b.wscCount + r.wscCount := by
  simp only [mapSet,Term.wscCount,Formula.truth,Formula.wscCount,Nat.add_zero]

@[simp] lemma Term.bindSet_count {n : ℕ} (r : Term n) (b : Term (n+1)) :
    (r.bindSet b).wscCount = b.wscCount + r.wscCount := r.mapSet_count b

@[simp] lemma Term.partialPool_count {n : ℕ} (B : ℕ) : (Term.partialPool (n := n) B).wscCount = 0 := by
  induction B with
  | zero => rfl
  | succ k ih =>
    simp only [partialPool,bindSet_count,mapSet_count,addPairBody,Term.cup,
      Term.singleton,Term.orderedPair,Term.wscCount,ih,Nat.add_zero]

@[simp] lemma Term.completeRelation_count {n : ℕ} : (Term.completeRelation (n := n)).wscCount = 0 := rfl

@[simp] lemma Term.identityRelation_count {n : ℕ} : (Term.identityRelation (n := n)).wscCount = 0 := rfl

@[simp] lemma Term.localPool_count {n : ℕ} (B : ℕ) : (Term.localPool (n := n) B).wscCount = 0 := by
  simp only [localPool,Term.cup,Term.singleton,Term.wscCount,mapSet_count,
    partialPool_count,completeRelation_count,identityRelation_count,Nat.add_zero]

variable {A : Type} [Fintype A]

lemma Term.eval_comprehend (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (r : Term n) (b : Term (n+1)) (g : Formula (n+1)) (env : Fin n → HF A)
    {rv : HF A} {f : HF A → HF A} {c : HF A → Bool}
    (hr : r.eval S p env = some rv)
    (hb : ∀ x, b.eval S p (Fin.cons x env) = some (f x))
    (hg : ∀ x, g.eval S p (Fin.cons x env) = some (c x)) :
    (Term.comprehend b r g).eval S p env =
      some (ofFinset (((elements rv).filter (fun x => c x = true)).image f)) := by
  have hf := funext hb
  have hc := funext hg
  simp only [Term.eval,hr,Option.bind_some,hf,hc,collect_pure]

lemma Term.eval_mapSet (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (r : Term n) (b : Term (n+1)) (env : Fin n → HF A)
    {rv : HF A} {f : HF A → HF A} (hr : r.eval S p env = some rv)
    (hb : ∀ x, b.eval S p (Fin.cons x env) = some (f x)) :
    (r.mapSet b).eval S p env = some (ofFinset ((elements rv).image f)) := by
  have hf : (fun x => b.eval S p (Fin.cons x env)) = fun x => some (f x) := funext hb
  simp only [mapSet,Term.eval,hr,Option.bind_some,hf,Formula.eval_truth]
  rw [collect_pure]
  simp

lemma Term.eval_bindSet (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (r : Term n) (b : Term (n+1)) (env : Fin n → HF A)
    {rv : HF A} {f : HF A → HF A} (hr : r.eval S p env = some rv)
    (hb : ∀ x, b.eval S p (Fin.cons x env) = some (f x)) :
    (r.bindSet b).eval S p env =
      some (ofFinset ((elements rv).biUnion (fun x => elements (f x)))) := by
  simp only [bindSet,Term.eval,eval_mapSet S p r b env hr hb,Option.map_some,unionHF,
    elements_ofFinset]
  congr 2
  ext x
  simp

lemma Term.eval_addPairBody (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (env : Fin n → HF A) (r a b : HF A) :
    (Term.addPairBody (n := n)).eval S p (Fin.cons b (Fin.cons a (Fin.cons r env))) =
      some (ofFinset (insert (Hereditary.pair a b) (elements r))) := by
  have hp := Term.eval_orderedPair S p (Term.var (1 : Fin (n+3))) (Term.var 0)
    (Fin.cons b (Fin.cons a (Fin.cons r env))) rfl rfl
  have hs := Term.eval_singleton S p _ _ hp
  have hc := Term.eval_cup S p (Term.var (2 : Fin (n+3))) _ _ rfl hs
  simpa only [addPairBody,Hereditary.singleton,elements_ofFinset,Finset.union_singleton,Fin.cons_zero,Fin.cons_one,Fin.cons_succ,cons_two] using hc

end

end WitnessedChoice.BGS

end

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_QuotedSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedChoice.RelationPools

noncomputable section

open Classical

variable {A : Type} [Fintype A]

abbrev Relation (A : Type) := Finset (A × A)

def graph (g : Equiv.Perm A) : Relation A := Finset.univ.image (fun a => (a,g a))

@[simp] lemma mem_graph (g : Equiv.Perm A) (a b : A) :
    (a,b) ∈ graph g ↔ g a = b := by
  simp [graph]

def compose (l c : Relation A) : Relation A := Finset.univ.filter fun ab =>
  ∃ u, (ab.1,u) ∈ l ∧ (u,ab.2) ∈ c

@[simp] lemma mem_compose (l c : Relation A) (a b : A) :
    (a,b) ∈ compose l c ↔ ∃ u, (a,u) ∈ l ∧ (u,b) ∈ c := by
  simp [compose]

@[simp] lemma compose_graph (g h : Equiv.Perm A) :
    compose (graph g) (graph h) = graph (h*g) := by
  ext ab
  rcases ab with ⟨a,b⟩
  simp [Equiv.Perm.mul_apply]

@[irreducible] def localBound : ℕ := 16*(3^9+3^29)

def localRelation {B : ℕ} (p q : Fin B → A) : Relation A :=
  (Finset.univ.image (fun i => (p i,q i))) ∪
    ((Finset.univ.filter (fun a => ∀ i, a ≠ p i)).image (fun a => (a,a)))

def localPool (B : ℕ) : Finset (Relation A) :=
  insert (graph 1) (Finset.univ.image (fun pq : (Fin B → A) × (Fin B → A) =>
    localRelation pq.1 pq.2))

end

end WitnessedChoice.RelationPools



namespace WitnessedChoice

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

open RelationPools

variable {A : Type} [Fintype A]

def edgeAtoms (S : Input A) : Finset A := Finset.univ.filter fun a => S.rel .Ed a a = true

def configAtoms (S : Input A) : Finset A := Finset.univ.filter fun a => S.rel .Cf a a = true

def edgeRow (S : Input A) (a : A) : Finset A := (edgeAtoms S).filter fun s => S.rel .EB a s = true

def vertexRow (S : Input A) (a : A) : Finset A := (configAtoms S).filter fun s => S.rel .VB a s = true

def edgeBlocks (S : Input A) : Finset (Finset A) := (edgeAtoms S).image (edgeRow S)

def vertexBlocks (S : Input A) : Finset (Finset A) := (configAtoms S).image (vertexRow S)

def blocks (S : Input A) : Finset (Finset A) := edgeBlocks S ∪ vertexBlocks S

def tupleCode : List (HF A) → HF A
  | [] => ordinal 0
  | x::xs => pair x (tupleCode xs)

def parameterCode (α : Fin 4 → Finset A) : HF A := tupleCode (List.ofFn (stateCode ∘ α))

variable (B : ℕ)

def PoolFilter (S : Input A) (x : Finset A) (g : Equiv.Perm A) : Prop :=
  g ∈ fullAut S ∧ (∀ u ∈ blocks S, u.image g = u) ∧ ∀ a ∈ x, g a = a

def witnessPool (S : Input A) (valid : Prop) (cyclePool : Finset A → Finset (Relation A))
    (x : Finset A) : Finset (Equiv.Perm A) :=
  if valid then insert 1 (Finset.univ.filter fun g => PoolFilter S x g ∧
    ∃ l ∈ localPool B, ∃ c ∈ cyclePool x, compose l c = graph g)
  else {1}

def guardedSelection (S : Input A) (valid : Prop) (D : Finset A → Finset A)
    (C : Finset A → Finset (Relation A)) : Selection A where
  candidates := fun x => if valid then D x else ∅
  witnesses := witnessPool B S valid C

end

end WitnessedChoice



namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary RelationPools

variable {A : Type}

def pairCode (ab : A × A) : HF A := pair (atom ab.1) (atom ab.2)

def relationCode (r : Relation A) : HF A := ofFinset (r.image pairCode)

lemma pairCode_injective : Function.Injective (pairCode (A := A)) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have hh := pair_injective h
  exact Prod.ext (atom_injective hh.1) (atom_injective hh.2)

@[simp] lemma pairCode_eq {ab cd : A × A} : pairCode ab = pairCode cd ↔ ab = cd :=
  pairCode_injective.eq_iff

@[simp] lemma elements_relationCode (r : Relation A) : elements (relationCode r) = r.image pairCode :=
  elements_ofFinset _

@[simp] lemma relationCode_empty : relationCode (∅ : Relation A) = emptyHF := by
  simp [relationCode,emptyHF]

@[simp] lemma relationCode_insert (ab : A × A) (r : Relation A) :
    relationCode (insert ab r) = ofFinset (insert (pairCode ab) (elements (relationCode r))) := by
  simp only [relationCode,Finset.image_insert,elements_ofFinset]

variable [Fintype A]

@[simp] lemma relationCode_graph (g : Equiv.Perm A) : relationCode (graph g) = permutationGraph g := by
  simp only [relationCode,graph,permutationGraph,Finset.image_image,pairCode,Function.comp_def]

def partialRelations : ℕ → Finset (Relation A)
  | 0 => {∅}
  | k+1 => (partialRelations k).biUnion fun r => Finset.univ.biUnion fun a : A =>
      Finset.univ.image fun b : A => insert (a,b) r

omit [Fintype A] in
lemma tupleImage_cons {B : ℕ} (p q : Fin B → A) (a b : A) :
    (Finset.univ.image (fun i => (Fin.cons a p i,Fin.cons b q i))) =
      insert (a,b) (Finset.univ.image (fun i => (p i,q i))) := by
  ext cd
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert]
  constructor
  · rintro ⟨i,rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inl rfl
    · exact Or.inr ⟨j,rfl⟩
  · rintro (rfl|⟨j,rfl⟩)
    · exact ⟨0,rfl⟩
    · exact ⟨j.succ,rfl⟩

lemma partialRelations_eq (B : ℕ) : partialRelations (A := A) B =
    Finset.univ.image (fun pq : (Fin B → A) × (Fin B → A) =>
      Finset.univ.image (fun i => (pq.1 i,pq.2 i))) := by
  induction B with
  | zero =>
    ext r
    simp only [partialRelations,Finset.mem_singleton,Finset.mem_image,Finset.mem_univ,
      true_and,Prod.exists]
    constructor
    · rintro rfl
      exact ⟨Fin.elim0,Fin.elim0,by simp⟩
    · rintro ⟨p,q,rfl⟩
      simp
  | succ B ih =>
    ext r
    simp only [partialRelations,ih,Finset.mem_biUnion,Finset.mem_image,
      Finset.mem_univ,true_and,Prod.exists]
    constructor
    · rintro ⟨r,⟨p,q,rfl⟩,a,b,rfl⟩
      exact ⟨Fin.cons a p,Fin.cons b q,tupleImage_cons p q a b⟩
    · rintro ⟨p,q,rfl⟩
      refine ⟨Finset.univ.image (fun i => (Fin.tail p i,Fin.tail q i)),
        ⟨Fin.tail p,Fin.tail q,rfl⟩,p 0,q 0,?_⟩
      simpa only [Fin.cons_self_tail] using (tupleImage_cons (Fin.tail p) (Fin.tail q) (p 0) (q 0)).symm

lemma Term.eval_partialPool (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (B : ℕ) (env : Fin n → HF A) :
    (Term.partialPool B).eval S p env =
      some (ofFinset ((partialRelations (A := A) B).image relationCode)) := by
  induction B with
  | zero =>
    simpa only [partialPool,partialRelations,Finset.image_singleton,relationCode_empty,
      Hereditary.singleton] using Term.eval_singleton S p (Term.empty) env rfl
  | succ B ih =>
    have hb (r : HF A) :
        (Term.atoms.bindSet (Term.atoms.mapSet (Term.addPairBody (n := n)))).eval S p
          (Fin.cons r env) = some (ofFinset (Finset.univ.biUnion fun a : A =>
            Finset.univ.image fun b : A => ofFinset (insert (pairCode (a,b)) (elements r)))) := by
      have hmap (a : HF A) := Term.eval_mapSet S p Term.atoms Term.addPairBody
        (Fin.cons a (Fin.cons r env)) rfl
        (fun b => Term.eval_addPairBody S p env r a b)
      have hh := Term.eval_bindSet S p Term.atoms (Term.atoms.mapSet Term.addPairBody)
        (Fin.cons r env) rfl hmap
      simpa only [elements_ofFinset,Finset.image_biUnion,Finset.image_image,
        Function.comp_def,pairCode] using hh
    have hh := Term.eval_bindSet S p (Term.partialPool B)
      (Term.atoms.bindSet (Term.atoms.mapSet Term.addPairBody)) env ih hb
    change _ = _ at hh
    convert hh using 1
    congr 2
    simp only [partialRelations,Finset.biUnion_image,Finset.image_image,
      elements_ofFinset,Finset.image_biUnion,Function.comp_def,relationCode_insert]

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary RelationPools

variable {A : Type} [Fintype A]

def completeHF (r : HF A) : HF A := ofFinset (elements r ∪
  ((Finset.univ.filter fun a : A => ∀ b : A, pairCode (a,b) ∉ elements r).image
    (fun a => pairCode (a,a))))

lemma Term.eval_completeRelation (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (env : Fin n → HF A) (r : HF A) :
    (Term.completeRelation (n := n)).eval S p (Fin.cons r env) = some (completeHF r) := by
  have hg (a : HF A) :
      (Formula.neg (Formula.existsIn Term.atoms (Formula.mem
        (Term.orderedPair (Term.var 1) (Term.var 0)) (Term.var 2)))).eval S p
        (Fin.cons a (Fin.cons r env)) =
      some (decide (∀ b : A, Hereditary.pair a (atom b) ∉ elements r)) := by
    have hm (b : HF A) := Formula.eval_mem S p
      (Term.orderedPair (Term.var (1 : Fin (n+3))) (Term.var 0)) (Term.var 2) rfl
      (Fin.cons b (Fin.cons a (Fin.cons r env)))
      (Term.eval_orderedPair S p _ _ _ rfl rfl) rfl
    have hh := Formula.eval_existsIn S p Term.atoms
      (Formula.mem (Term.orderedPair (Term.var 1) (Term.var 0)) (Term.var 2))
      (Fin.cons a (Fin.cons r env)) rfl hm
    simp only [Formula.eval,hh,Option.map_some]
    simp only [elements_ofFinset,Fin.cons_one,cons_two,Fin.cons_zero,
      Finset.mem_image,Finset.mem_univ,true_and,decide_eq_true_eq]
    by_cases h : ∃ b : A, Hereditary.pair a (atom b) ∈ elements r
    · obtain ⟨b,hb⟩ := h
      have he : ∃ b : A, Hereditary.pair a (atom b) ∈ elements r := ⟨b,hb⟩
      have hn : ¬ ∀ b : A, Hereditary.pair a (atom b) ∉ elements r := fun h => h b hb
      simp [he,hn]
    · simp only [not_exists] at h
      simp [h]
  have hb (a : HF A) := Term.eval_orderedPair S p (Term.var (0 : Fin (n+2))) (Term.var 0)
    (Fin.cons a (Fin.cons r env)) rfl rfl
  have hh := Term.eval_comprehend S p Term.atoms
    (Term.orderedPair (Term.var 0) (Term.var 0))
    (Formula.neg (Formula.existsIn Term.atoms (Formula.mem
      (Term.orderedPair (Term.var 1) (Term.var 0)) (Term.var 2))))
    (Fin.cons r env) rfl hb hg
  have hc := Term.eval_cup S p (Term.var (0 : Fin (n+1))) _ (Fin.cons r env) rfl hh
  have hc' : (Term.completeRelation (n := n)).eval S p (Fin.cons r env) =
      some (ofFinset (elements r ∪ (((Finset.univ.image atom).filter
        (fun a : HF A => decide (∀ b : A, Hereditary.pair a (atom b) ∉ elements r) = true)).image
        (fun a => Hereditary.pair a a)))) := by
    simpa only [completeRelation,elements_ofFinset,Fin.cons_zero] using hc
  rw [hc']
  apply congrArg some
  unfold completeHF
  apply congrArg ofFinset
  apply congrArg (fun z => elements r ∪ z)
  symm
  ext z
  simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,
    decide_eq_true_eq,pairCode]
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨atom a,⟨⟨a,rfl⟩,(Finset.mem_filter.mp ha).2⟩,rfl⟩
  · rintro ⟨z,⟨⟨a,rfl⟩,ha⟩,rfl⟩
    exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩,rfl⟩

omit [Fintype A] in
@[simp] lemma mem_elements_relationCode (r : Relation A) (a b : A) :
    pairCode (a,b) ∈ elements (relationCode r) ↔ (a,b) ∈ r := by
  simp [relationCode,pairCode_injective.mem_finset_image]

lemma completeHF_tuple {B : ℕ} (p q : Fin B → A) :
    completeHF (relationCode (Finset.univ.image (fun i => (p i,q i)))) =
      relationCode (localRelation p q) := by
  apply ofFinset_inj.mpr
  simp only [relationCode,elements_ofFinset,localRelation,Finset.image_union]
  congr 1
  ext z
  simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,
    pairCode_eq]
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨(a,a),⟨a,?_,rfl⟩,rfl⟩
    intro i hi
    apply ha (q i)
    exact ⟨(p i,q i),⟨i,rfl⟩,by rw [hi]⟩
  · rintro ⟨_,⟨a,ha,rfl⟩,rfl⟩
    refine ⟨a,?_,rfl⟩
    rintro b ⟨_,⟨i,rfl⟩,he⟩
    exact ha i (congrArg Prod.fst he).symm

lemma Term.eval_identityRelation (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (env : Fin n → HF A) :
    (Term.identityRelation (n := n)).eval S p env = some (relationCode (graph 1)) := by
  have hh := Term.eval_mapSet S p Term.atoms
    (Term.orderedPair (Term.var (0 : Fin (n+1))) (Term.var 0)) env rfl
    (fun a => Term.eval_orderedPair S p _ _ _ rfl rfl)
  simpa only [mapSet,identityRelation,elements_ofFinset,Finset.image_image,relationCode,
    graph,pairCode,Function.comp_def,Fin.cons_zero,Equiv.Perm.one_apply] using hh

lemma Term.eval_localPool (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (B : ℕ) (env : Fin n → HF A) :
    (Term.localPool B).eval S p env =
      some (ofFinset ((RelationPools.localPool (A := A) B).image relationCode)) := by
  have hh := Term.eval_mapSet S p (Term.partialPool B) Term.completeRelation env
    (Term.eval_partialPool S p B env) (fun r => Term.eval_completeRelation S p env r)
  have hc := Term.eval_cup S p (Term.identityRelation.singleton) _ env
    (Term.eval_singleton S p _ env (Term.eval_identityRelation S p env)) hh
  convert hc using 1
  congr 2
  simp only [RelationPools.localPool,Finset.image_insert,Hereditary.singleton,elements_ofFinset,
    Finset.singleton_union,Finset.image_image,partialRelations_eq,Function.comp_def,completeHF_tuple]

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

structure QuotedTerm (n : ℕ) where
  code : Term n
  meaning : {A : Type} → [Fintype A] → Input A → (Fin n → HF A) → HF A
  count : code.wscCount = 0
  correct : ∀ {A : Type} [Fintype A] (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A),
    code.eval S p env = some (meaning S env)

structure QuotedFormula (n : ℕ) where
  code : Formula n
  meaning : {A : Type} → [Fintype A] → Input A → (Fin n → HF A) → Prop
  count : code.wscCount = 0
  correct : ∀ {A : Type} [Fintype A] (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A),
    code.eval S p env = some (decide (meaning S env))

namespace QuotedTerm

variable {n m : ℕ}

def var (j : Fin n) : QuotedTerm n := ⟨.var j,fun _ env => env j,rfl,fun _ _ _ => rfl⟩

def empty : QuotedTerm n := ⟨.empty,fun _ _ => emptyHF,rfl,fun _ _ _ => rfl⟩

def atoms : QuotedTerm n := ⟨.atoms,fun _ _ => ofFinset (Finset.univ.image atom),rfl,fun _ _ _ => rfl⟩

def rename (a : QuotedTerm n) (f : Fin n → Fin m) : QuotedTerm m where
  code := a.code.rename f
  meaning := fun S env => a.meaning S (env ∘ f)
  count := (a.code.rename_count f).trans a.count
  correct S p env := (a.code.eval_rename S p a.count f env).trans (a.correct S p (env ∘ f))

def up (a : QuotedTerm n) : QuotedTerm (n+1) := a.rename Fin.succ

def double (a b : QuotedTerm n) : QuotedTerm n where
  code := .pair a.code b.code
  meaning := fun S env => Hereditary.double (a.meaning S env) (b.meaning S env)
  count := by simp only [Term.wscCount,a.count,b.count,Nat.add_zero]
  correct S p env := by simp only [Term.eval,a.correct,b.correct,lift₂,Option.bind_some,Option.map_some]

def union (a : QuotedTerm n) : QuotedTerm n where
  code := .union a.code
  meaning := fun S env => unionHF (a.meaning S env)
  count := a.count
  correct S p env := by simp only [Term.eval,a.correct,Option.map_some]

def unique (a : QuotedTerm n) : QuotedTerm n where
  code := .unique a.code
  meaning := fun S env => uniqueHF (a.meaning S env)
  count := a.count
  correct S p env := by simp only [Term.eval,a.correct,Option.map_some]

def card (a : QuotedTerm n) : QuotedTerm n where
  code := .card a.code
  meaning := fun S env => cardHF (a.meaning S env)
  count := a.count
  correct S p env := by simp only [Term.eval,a.correct,Option.map_some]

def singleton (a : QuotedTerm n) : QuotedTerm n := a.double a

def cup (a b : QuotedTerm n) : QuotedTerm n := (a.double b).union

def pair (a b : QuotedTerm n) : QuotedTerm n := a.singleton.double (a.double b)

end QuotedTerm

namespace QuotedFormula

variable {n m : ℕ}

def eq (a b : QuotedTerm n) : QuotedFormula n where
  code := .equal a.code b.code
  meaning := fun S env => a.meaning S env = b.meaning S env
  count := by simp only [Formula.wscCount,a.count,b.count,Nat.add_zero]
  correct S p env := by
    simp only [Formula.eval,a.correct,b.correct,lift₂,Option.bind_some,Option.map_some]
    exact congrArg some (decide_eq_decide.mpr Iff.rfl)

def input (r : Symbol) (a b : QuotedTerm n) : QuotedFormula n where
  code := .input r a.code b.code
  meaning := fun S env => inputHF S r (a.meaning S env) (b.meaning S env) = true
  count := by simp only [Formula.wscCount,a.count,b.count,Nat.add_zero]
  correct S p env := by simp only [Formula.eval,a.correct,b.correct,lift₂,Option.bind_some,Option.map_some,Bool.decide_eq_true]

def truth : QuotedFormula n := eq .empty .empty

def neg (a : QuotedFormula n) : QuotedFormula n where
  code := .neg a.code
  meaning := fun S env => ¬ a.meaning S env
  count := a.count
  correct S p env := by simp only [Formula.eval,a.correct,Option.map_some,decide_not]

def and (a b : QuotedFormula n) : QuotedFormula n where
  code := .and a.code b.code
  meaning := fun S env => a.meaning S env ∧ b.meaning S env
  count := by simp only [Formula.wscCount,a.count,b.count,Nat.add_zero]
  correct S p env := by simp only [Formula.eval,a.correct,b.correct,lift₂,Option.bind_some,Option.map_some,Bool.decide_and]

def or (a b : QuotedFormula n) : QuotedFormula n where
  code := .or a.code b.code
  meaning := fun S env => a.meaning S env ∨ b.meaning S env
  count := by simp only [Formula.wscCount,a.count,b.count,Nat.add_zero]
  correct S p env := by simp only [Formula.eval,a.correct,b.correct,lift₂,Option.bind_some,Option.map_some,Bool.decide_or]

def imp (a b : QuotedFormula n) : QuotedFormula n := a.neg.or b

def iff (a b : QuotedFormula n) : QuotedFormula n := (a.imp b).and (b.imp a)

def mem (a b : QuotedTerm n) : QuotedFormula n where
  code := .mem a.code b.code
  meaning := fun S env => a.meaning S env ∈ elements (b.meaning S env)
  count := by simp only [Formula.mem,Formula.existsIn,Term.up,Term.rename_count,
    Formula.wscCount,Term.wscCount,a.count,b.count,Nat.add_zero]
  correct S p env := by
    rw [Formula.eval_mem S p _ _ a.count env (a.correct S p env) (b.correct S p env)]
    exact congrArg some (decide_eq_decide.mpr Iff.rfl)

def existsIn (r : QuotedTerm n) (a : QuotedFormula (n+1)) : QuotedFormula n where
  code := .existsIn r.code a.code
  meaning := fun S env => ∃ x ∈ elements (r.meaning S env), a.meaning S (Fin.cons x env)
  count := by simp only [Formula.existsIn,Term.wscCount,Formula.wscCount,r.count,a.count,Nat.add_zero]
  correct S p env := by
    rw [Formula.eval_existsIn S p r.code a.code env (r.correct S p env) (fun _ => a.correct S p _)]
    exact congrArg some (decide_eq_decide.mpr (by simp only [decide_eq_true_eq]))

def allIn (r : QuotedTerm n) (a : QuotedFormula (n+1)) : QuotedFormula n where
  code := .allIn r.code a.code
  meaning := fun S env => ∀ x ∈ elements (r.meaning S env), a.meaning S (Fin.cons x env)
  count := by simp only [Formula.allIn,Formula.existsIn,Term.wscCount,Formula.wscCount,r.count,a.count,Nat.add_zero]
  correct S p env := by
    rw [Formula.eval_allIn S p r.code a.code env (r.correct S p env) (fun _ => a.correct S p _)]
    exact congrArg some (decide_eq_decide.mpr (by simp only [decide_eq_true_eq]))

end QuotedFormula

namespace QuotedTerm

variable {n : ℕ}

def comprehend (r : QuotedTerm n) (body : QuotedTerm (n+1)) (guard : QuotedFormula (n+1)) : QuotedTerm n where
  code := .comprehend body.code r.code guard.code
  meaning := fun S env => ofFinset (((elements (r.meaning S env)).filter
    (fun x => guard.meaning S (Fin.cons x env))).image (fun x => body.meaning S (Fin.cons x env)))
  count := by simp only [Term.wscCount,r.count,body.count,guard.count,Nat.add_zero]
  correct S p env := by
    simpa only [decide_eq_true_eq] using Term.eval_comprehend S p r.code body.code guard.code env
      (r.correct S p env) (fun _ => body.correct S p _) (fun _ => guard.correct S p _)

def map (r : QuotedTerm n) (body : QuotedTerm (n+1)) : QuotedTerm n := r.comprehend body .truth

def bind (r : QuotedTerm n) (body : QuotedTerm (n+1)) : QuotedTerm n := (r.map body).union

def filter (r : QuotedTerm n) (guard : QuotedFormula (n+1)) : QuotedTerm n := r.comprehend (.var 0) guard

def inter (a b : QuotedTerm n) : QuotedTerm n := a.filter (.mem (.var 0) b.up)

def diff (a b : QuotedTerm n) : QuotedTerm n := a.filter (.neg (.mem (.var 0) b.up))

def cond (g : QuotedFormula n) (a b : QuotedTerm n) : QuotedTerm n where
  code := .cond g.code a.code b.code
  meaning := fun S env => if g.meaning S env then a.meaning S env else b.meaning S env
  count := by simp only [Term.cond,Term.cup,Term.when,Term.singleton,Term.up_count,
    Formula.up_count,Term.wscCount,Formula.wscCount,g.count,a.count,b.count,Nat.add_zero]
  correct S p env := by
    simpa only [decide_eq_true_eq] using Term.eval_cond S p g.code a.code b.code
      g.count a.count b.count env (g.correct S p env) (a.correct S p env) (b.correct S p env)

end QuotedTerm

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

open RelationPools

namespace QuotedTerm

variable {n : ℕ}

def describe (a : QuotedTerm n)
    (f : {A : Type} → [Fintype A] → Input A → (Fin n → HF A) → HF A)
    (h : ∀ {A : Type} [Fintype A] (S : Input A) env, a.meaning S env = f S env) : QuotedTerm n where
  code := a.code
  meaning := f
  count := a.count
  correct S p env := (a.correct S p env).trans (congrArg some (h S env))

variable {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

@[simp] lemma meaning_var (j : Fin n) : (var j).meaning S env = env j := rfl

@[simp] lemma meaning_empty : (empty : QuotedTerm n).meaning S env = emptyHF := rfl

@[simp] lemma meaning_atoms : (atoms : QuotedTerm n).meaning S env = stateCode Finset.univ := rfl

@[simp] lemma meaning_up (a : QuotedTerm n) (x : HF A) : a.up.meaning S (Fin.cons x env) = a.meaning S env := rfl

@[simp] lemma meaning_double (a b : QuotedTerm n) : (a.double b).meaning S env = Hereditary.double (a.meaning S env) (b.meaning S env) := rfl

@[simp] lemma meaning_singleton (a : QuotedTerm n) : a.singleton.meaning S env = Hereditary.singleton (a.meaning S env) := by simp [singleton,Hereditary.double,Hereditary.singleton]

@[simp] lemma meaning_pair (a b : QuotedTerm n) : (a.pair b).meaning S env = Hereditary.pair (a.meaning S env) (b.meaning S env) := by simp [pair,Hereditary.pair]

@[simp] lemma meaning_filter (a : QuotedTerm n) (g : QuotedFormula (n+1)) :
    (a.filter g).meaning S env = ofFinset ((elements (a.meaning S env)).filter fun x => g.meaning S (Fin.cons x env)) := by
  simp [filter,comprehend]

@[simp] lemma meaning_map (a : QuotedTerm n) (b : QuotedTerm (n+1)) :
    (a.map b).meaning S env = ofFinset ((elements (a.meaning S env)).image fun x => b.meaning S (Fin.cons x env)) := by
  simp [map,comprehend,QuotedFormula.truth,QuotedFormula.eq]

@[simp] lemma meaning_cup (a b : QuotedTerm n) :
    (a.cup b).meaning S env = ofFinset (elements (a.meaning S env) ∪ elements (b.meaning S env)) := by
  simp [cup,union,Hereditary.double,unionHF]

@[simp] lemma meaning_bind (a : QuotedTerm n) (b : QuotedTerm (n+1)) :
    (a.bind b).meaning S env = ofFinset ((elements (a.meaning S env)).biUnion fun x => elements (b.meaning S (Fin.cons x env))) := by
  simp [bind,union,unionHF,Finset.image_biUnion]

end QuotedTerm

namespace QuotedFormula

variable {n : ℕ}

def allList : List (QuotedFormula n) → QuotedFormula n
  | [] => truth
  | a::l => a.and (allList l)

def allSymbols (q : Symbol → QuotedFormula n) : QuotedFormula n :=
  allList (Finset.univ.toList.map q)

def link (a b r : QuotedTerm n) : QuotedFormula n := mem (a.pair b) r

variable {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

@[simp] lemma meaning_eq (a b : QuotedTerm n) : (eq a b).meaning S env ↔ a.meaning S env = b.meaning S env := Iff.rfl

@[simp] lemma meaning_input (r : Symbol) (a b : QuotedTerm n) : (input r a b).meaning S env ↔ inputHF S r (a.meaning S env) (b.meaning S env) = true := Iff.rfl

@[simp] lemma meaning_mem (a b : QuotedTerm n) : (mem a b).meaning S env ↔ a.meaning S env ∈ elements (b.meaning S env) := Iff.rfl

@[simp] lemma meaning_and (a b : QuotedFormula n) : (a.and b).meaning S env ↔ a.meaning S env ∧ b.meaning S env := Iff.rfl

@[simp] lemma meaning_or (a b : QuotedFormula n) : (a.or b).meaning S env ↔ a.meaning S env ∨ b.meaning S env := Iff.rfl

@[simp] lemma meaning_neg (a : QuotedFormula n) : a.neg.meaning S env ↔ ¬ a.meaning S env := Iff.rfl

@[simp] lemma meaning_imp (a b : QuotedFormula n) : (a.imp b).meaning S env ↔ (a.meaning S env → b.meaning S env) := by simp only [imp,meaning_or,meaning_neg]; tauto

@[simp] lemma meaning_iff (a b : QuotedFormula n) : (a.iff b).meaning S env ↔ (a.meaning S env ↔ b.meaning S env) := by simp [iff,iff_iff_implies_and_implies]

@[simp] lemma meaning_allIn (r : QuotedTerm n) (a : QuotedFormula (n+1)) :
    (allIn r a).meaning S env ↔ ∀ x ∈ elements (r.meaning S env), a.meaning S (Fin.cons x env) := Iff.rfl

@[simp] lemma meaning_existsIn (r : QuotedTerm n) (a : QuotedFormula (n+1)) :
    (existsIn r a).meaning S env ↔ ∃ x ∈ elements (r.meaning S env), a.meaning S (Fin.cons x env) := Iff.rfl

@[simp] lemma meaning_allList (l : List (QuotedFormula n)) : (allList l).meaning S env ↔ ∀ q ∈ l, q.meaning S env := by
  induction l with
  | nil => simp [allList,truth,eq]
  | cons q l ih => simp [allList,ih]

@[simp] lemma meaning_allSymbols (q : Symbol → QuotedFormula n) : (allSymbols q).meaning S env ↔ ∀ r, (q r).meaning S env := by
  simp [allSymbols]

@[simp] lemma meaning_link (a b r : QuotedTerm n) : (link a b r).meaning S env ↔ Hereditary.pair (a.meaning S env) (b.meaning S env) ∈ elements (r.meaning S env) := by simp [link]

end QuotedFormula

variable {A : Type}

@[simp] lemma inputHF_atoms (S : Input A) (r : Symbol) (a b : A) :
    inputHF S r (atom a) (atom b) = S.rel r a b := by
  simp [inputHF,atom_injective.eq_iff]

@[simp] lemma pair_mem_relationCode (a b : A) (r : Relation A) :
    Hereditary.pair (atom a) (atom b) ∈ elements (relationCode r) ↔ (a,b) ∈ r := by
  change pairCode (a,b) ∈ elements (relationCode r) ↔ _
  simp [relationCode]

@[simp] lemma all_stateCode (s : Finset A) (P : HF A → Prop) :
    (∀ x ∈ elements (stateCode s), P x) ↔ ∀ a ∈ s, P (atom a) := by simp [stateCode]

@[simp] lemma exists_stateCode (s : Finset A) (P : HF A → Prop) :
    (∃ x ∈ elements (stateCode s), P x) ↔ ∃ a ∈ s, P (atom a) := by simp [stateCode]

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary RelationPools

@[simp] lemma fin_cons_two {n : ℕ} {X : Sort*} (x : X) (f : Fin (n+2) → X) : (Fin.cons x f : Fin (n+2+1) → X) 2 = f 1 := rfl

@[simp] lemma fin_cons_three {n : ℕ} {X : Sort*} (x : X) (f : Fin (n+3) → X) : (Fin.cons x f : Fin (n+3+1) → X) 3 = f 2 := rfl

@[simp] lemma fin_cons_four {n : ℕ} {X : Sort*} (x : X) (f : Fin (n+4) → X) : (Fin.cons x f : Fin (n+4+1) → X) 4 = f 3 := rfl

@[simp] lemma fin_cons_five {n : ℕ} {X : Sort*} (x : X) (f : Fin (n+5) → X) : (Fin.cons x f : Fin (n+5+1) → X) 5 = f 4 := rfl

namespace QuotedTerm

variable {n : ℕ}

def atomFilter (q : QuotedFormula (n+1)) : QuotedTerm n :=
  (atoms.filter q).describe
    (fun S env => stateCode (Finset.univ.filter fun a => q.meaning S (Fin.cons (atom a) env))) (by
      intro A _ S env
      simp only [meaning_filter,meaning_atoms,stateCode,elements_ofFinset]
      apply ofFinset_inj.mpr
      ext x
      simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]
      aesop)

@[simp] lemma meaning_atomFilter {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)
    (q : QuotedFormula (n+1)) :
    (atomFilter q).meaning S env = stateCode (Finset.univ.filter fun a => q.meaning S (Fin.cons (atom a) env)) := rfl

def relation (q : QuotedFormula (n+2)) : QuotedTerm n :=
  (atoms.bind (atoms.comprehend ((var 1).pair (var 0)) q)).describe
    (fun S env => relationCode (Finset.univ.filter fun ab =>
      q.meaning S (Fin.cons (atom ab.2) (Fin.cons (atom ab.1) env)))) (by
      intro A _ S env
      simp only [meaning_bind,meaning_atoms,comprehend,meaning_pair,meaning_var,
        relationCode,stateCode,elements_ofFinset]
      apply ofFinset_inj.mpr
      ext x
      simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,
        true_and,Prod.exists]
      constructor
      · rintro ⟨a,⟨a',rfl⟩,b,⟨⟨b',rfl⟩,hq⟩,rfl⟩
        exact ⟨a',b',hq,rfl⟩
      · rintro ⟨a,b,hq,rfl⟩
        exact ⟨atom a,⟨a,rfl⟩,atom b,⟨⟨b,rfl⟩,hq⟩,rfl⟩)

@[simp] lemma meaning_relation {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)
    (q : QuotedFormula (n+2)) :
    (relation q).meaning S env = relationCode (Finset.univ.filter fun ab =>
      q.meaning S (Fin.cons (atom ab.2) (Fin.cons (atom ab.1) env))) := rfl

def edgeAtoms : QuotedTerm n := atomFilter (.input .Ed (.var 0) (.var 0))

def configAtoms : QuotedTerm n := atomFilter (.input .Cf (.var 0) (.var 0))

def edgeRow (a : QuotedTerm n) : QuotedTerm n := edgeAtoms.filter (.input .EB a.up (.var 0))

def vertexRow (a : QuotedTerm n) : QuotedTerm n := configAtoms.filter (.input .VB a.up (.var 0))

def edgeBlocks : QuotedTerm n := edgeAtoms.map (edgeRow (.var 0))

def vertexBlocks : QuotedTerm n := configAtoms.map (vertexRow (.var 0))

def blocks : QuotedTerm n := edgeBlocks.cup vertexBlocks

def identity : QuotedTerm n where
  code := .identityRelation
  meaning := fun _ _ => relationCode (graph 1)
  count := Term.identityRelation_count
  correct S p env := Term.eval_identityRelation S p env

def localRelations (B : ℕ) : QuotedTerm n where
  code := .localPool B
  meaning := fun _ _ => ofFinset ((localPool B).image relationCode)
  count := Term.localPool_count B
  correct S p env := Term.eval_localPool S p B env

def composition (l c : QuotedTerm n) : QuotedTerm n := relation
  (.existsIn .atoms ((QuotedFormula.link (.var 2) (.var 0) l.up.up.up).and
    (.link (.var 0) (.var 1) c.up.up.up)))

variable {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

@[simp] lemma meaning_edgeAtoms : (edgeAtoms : QuotedTerm n).meaning S env = stateCode (WitnessedChoice.edgeAtoms S) := by
  simp [edgeAtoms,WitnessedChoice.edgeAtoms]

@[simp] lemma meaning_configAtoms : (configAtoms : QuotedTerm n).meaning S env = stateCode (WitnessedChoice.configAtoms S) := by
  simp [configAtoms,WitnessedChoice.configAtoms]

end QuotedTerm

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary RelationPools

variable {A : Type} [Fintype A]

def FunctionalOnto (r : Relation A) : Prop :=
  (∀ a, ∃! b, (a,b) ∈ r) ∧ ∀ b, ∃ a, (a,b) ∈ r

def RawFilter (S : Input A) (x : Finset A) (r : Relation A) : Prop :=
  FunctionalOnto r ∧
  (∀ R a a' b b', (a,b) ∈ r → (a',b') ∈ r → S.rel R a a' = S.rel R b b') ∧
  (∀ u ∈ blocks S, ∀ a ∈ u, ∀ b, (a,b) ∈ r → b ∈ u) ∧
  ∀ a ∈ x, (a,a) ∈ r

namespace QuotedFormula

variable {n : ℕ}

def functional (r : QuotedTerm n) : QuotedFormula n :=
  allIn .atoms (existsIn .atoms
    ((link (.var 1) (.var 0) r.up.up).and
      (allIn .atoms ((link (.var 2) (.var 0) r.up.up.up).imp (eq (.var 0) (.var 1))))))

def onto (r : QuotedTerm n) : QuotedFormula n :=
  allIn .atoms (existsIn .atoms (link (.var 0) (.var 1) r.up.up))

def preserves (r : QuotedTerm n) : QuotedFormula n := allSymbols fun R =>
  allIn .atoms (allIn .atoms (allIn .atoms (allIn .atoms
    (((link (.var 3) (.var 1) r.up.up.up.up).and
      (link (.var 2) (.var 0) r.up.up.up.up)).imp
      ((input R (.var 3) (.var 2)).iff (input R (.var 1) (.var 0)))))))

def fixesBlocks (r : QuotedTerm n) : QuotedFormula n :=
  allIn .blocks (allIn (.var 0) (allIn .atoms
    ((link (.var 1) (.var 0) r.up.up.up).imp (mem (.var 0) (.var 2)))))

def fixesState (x r : QuotedTerm n) : QuotedFormula n :=
  allIn .atoms ((mem (.var 0) x.up).imp (link (.var 0) (.var 0) r.up))

def filter (x r : QuotedTerm n) : QuotedFormula n :=
  (functional r).and ((onto r).and ((preserves r).and ((fixesBlocks r).and (fixesState x r))))

end QuotedFormula

end

end WitnessedChoice.BGS

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_GuardedProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


namespace WitnessedChoice.BGS
open Classical WitnessedSeparation WitnessedSeparation.Hereditary


namespace QuotedTerm
open RelationPools

section

variable {n : ℕ}

def witnessRelations (B : ℕ) (valid : QuotedFormula n) (x C : QuotedTerm n) : QuotedTerm n :=
  cond valid
    (identity.singleton.cup ((localRelations B).bind
      (C.up.comprehend (composition (.var 1) (.var 0))
        (.filter x.up.up (composition (.var 1) (.var 0)))))) identity.singleton

def guardedChoice (D M : QuotedTerm n) : QuotedTerm n :=
  cond ((QuotedFormula.eq D .empty).neg.and
      (.allIn D (.allIn D.up
        (.existsIn M.up.up (.link (.var 2) (.var 1) (.var 0)))))) D empty.singleton

def selectionStep (x y : QuotedTerm n) : QuotedTerm n :=
  x.cup ((y.double y.unique).inter edgeAtoms)

variable {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

@[simp] lemma meaning_cond (g : QuotedFormula n) (a b : QuotedTerm n) :
    (cond g a b).meaning S env = if g.meaning S env then a.meaning S env else b.meaning S env := rfl

end

variable {n : ℕ} {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

omit [Fintype A] in
@[simp] lemma uniqueHF_atom (a : A) : uniqueHF (atom a) = emptyHF := by
  unfold uniqueHF
  simp only [elements_atom]
  apply dite_eq_right
  simp

@[simp] lemma meaning_unique (x : QuotedTerm n) :
    x.unique.meaning S env = uniqueHF (x.meaning S env) := rfl

@[simp] lemma meaning_inter (x y : QuotedTerm n) :
    (x.inter y).meaning S env = ofFinset (elements (x.meaning S env) ∩ elements (y.meaning S env)) := by
  simp only [inter,meaning_filter,QuotedFormula.meaning_mem,meaning_var,meaning_up,
    Fin.cons_zero,Finset.filter_mem_eq_inter]

end QuotedTerm


namespace QuotedTerm

variable {n : ℕ}

def triple (a b c : QuotedTerm n) : QuotedTerm n := a.pair (b.pair c)

def successor (a : QuotedTerm n) : QuotedTerm n := a.cup a.singleton

def indices : QuotedTerm n := atoms.card.successor

end QuotedTerm

namespace QuotedFormula

variable {n : ℕ}

def incident (v e : QuotedTerm n) : QuotedFormula n :=
  existsIn v (existsIn e.up (input .I (.var 1) (.var 0)))

def adjacent (J u w : QuotedTerm n) : QuotedFormula n :=
  (eq u w).neg.and (existsIn J ((incident u.up (.var 0)).and (incident w.up (.var 0))))

end QuotedFormula

namespace QuotedTerm

variable {n : ℕ}

def distanceBase (V : QuotedTerm n) : QuotedTerm n := V.map (triple (.var 0) (.var 0) .empty)

def distanceFresh (V J R : QuotedTerm n) : QuotedTerm n :=
  V.bind (V.up.bind ((indices.filter
    ((QuotedFormula.mem (successor (.var 0)) indices).and
      (.existsIn V.up.up.up
        ((QuotedFormula.mem (triple (.var 3) (.var 0) (.var 1)) R.up.up.up.up).and
          ((QuotedFormula.eq (.var 0) (.var 2)).or
            (.adjacent J.up.up.up.up (.var 0) (.var 2))))))).map
              (triple (.var 2) (.var 1) (successor (.var 0)))))

def distanceStep (V J R : QuotedTerm n) : QuotedTerm n :=
  (R.cup (distanceBase V)).cup (distanceFresh V J R)

def tripleDomain (V : QuotedTerm n) : QuotedTerm n :=
  V.bind (V.up.bind (indices.map (triple (.var 2) (.var 1) (.var 0))))

variable {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

@[simp] lemma meaning_triple (a b c : QuotedTerm n) :
    (triple a b c).meaning S env = Hereditary.pair (a.meaning S env)
      (Hereditary.pair (b.meaning S env) (c.meaning S env)) := by simp [triple]

@[simp] lemma meaning_successor (a : QuotedTerm n) :
    a.successor.meaning S env = ofFinset (insert (a.meaning S env) (elements (a.meaning S env))) := by
  simp [successor,Hereditary.singleton]

@[simp] lemma meaning_card (a : QuotedTerm n) : a.card.meaning S env = cardHF (a.meaning S env) := rfl

@[simp] lemma meaning_indices : (indices : QuotedTerm n).meaning S env = ordinal (Fintype.card A+1) := by
  simp only [indices,meaning_successor,meaning_card,meaning_atoms,cardHF,stateCode,
    elements_ofFinset,Finset.card_image_of_injective _ atom_injective,Finset.card_univ,ordinal]

end QuotedTerm

namespace QuotedFormula

variable {n : ℕ} {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

@[simp] lemma meaning_incident (v e : QuotedTerm n) :
    (incident v e).meaning S env ↔ ∃ t ∈ elements (v.meaning S env),
      ∃ s ∈ elements (e.meaning S env), inputHF S .I t s = true := by simp [incident]

@[simp] lemma meaning_adjacent (J u w : QuotedTerm n) :
    (adjacent J u w).meaning S env ↔ u.meaning S env ≠ w.meaning S env ∧
      ∃ e ∈ elements (J.meaning S env),
        (∃ t ∈ elements (u.meaning S env), ∃ s ∈ elements e, inputHF S .I t s = true) ∧
        (∃ t ∈ elements (w.meaning S env), ∃ s ∈ elements e, inputHF S .I t s = true) := by
  simp [adjacent]

end QuotedFormula


structure CPTTerm (n : ℕ) where
  code : Term n
  count : code.wscCount = 0

structure CPTFormula (n : ℕ) where
  code : Formula n
  count : code.wscCount = 0

namespace CPTTerm

variable {n m : ℕ} {A : Type} [Fintype A]

def value (t : CPTTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) : HF A :=
  (t.code.total S p t.count env).choose

def quoted (t : QuotedTerm n) : CPTTerm n := ⟨t.code,t.count⟩

def rename (t : CPTTerm n) (f : Fin n → Fin m) : CPTTerm m :=
  ⟨t.code.rename f,(t.code.rename_count f).trans t.count⟩

def up (t : CPTTerm n) : CPTTerm (n+1) := t.rename Fin.succ

def letIn (t : CPTTerm n) (b : CPTTerm (n+1)) : CPTTerm n :=
  ⟨t.code.letIn b.code,by simp only [Term.letIn,Term.singleton,Formula.truth,
    Term.wscCount,Formula.wscCount,t.count,b.count,Nat.add_zero]⟩

def iterate (b : CPTTerm (n+1)) : CPTTerm n := ⟨.iterate b.code,b.count⟩

def distance (V J : CPTTerm n) : CPTTerm n :=
  V.letIn (J.up.letIn ((quoted (QuotedTerm.distanceStep (.var 2) (.var 1) (.var 0))).iterate))

end CPTTerm

namespace CPTFormula

variable {n m : ℕ} {A : Type} [Fintype A]

def value (t : CPTFormula n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) : Bool :=
  (t.code.total S p t.count env).choose

def quoted (t : QuotedFormula n) : CPTFormula n := ⟨t.code,t.count⟩

def letIn (t : CPTTerm n) (b : CPTFormula (n+1)) : CPTFormula n :=
  ⟨Formula.letIn t.code b.code,by simp only [Formula.letIn,Formula.existsIn,Term.singleton,
    Term.wscCount,Formula.wscCount,t.count,b.count,Nat.add_zero]⟩

end CPTFormula


namespace QuotedTerm

section

variable {n : ℕ}

def nat : ℕ → QuotedTerm n
  | 0 => empty
  | k+1 => successor (nat k)

def fst (a : QuotedTerm n) : QuotedTerm n :=
  ((a.filter (.eq (.card (.var 0)) (nat 1))).union).unique

def snd (a : QuotedTerm n) : QuotedTerm n :=
  cond (.eq a.union.card (nat 1)) a.fst
    ((a.union.diff a.fst.singleton).unique)

def component (a : QuotedTerm n) : ℕ → QuotedTerm n
  | 0 => a.fst
  | k+1 => (a.snd).component k

variable {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

@[simp] lemma meaning_union (a : QuotedTerm n) :
    a.union.meaning S env = unionHF (a.meaning S env) := rfl

@[simp] lemma meaning_diff (a b : QuotedTerm n) :
    (a.diff b).meaning S env = ofFinset ((elements (a.meaning S env)).filter
      fun z => z ∉ elements (b.meaning S env)) := by simp [diff]

@[simp] lemma meaning_nat (k : ℕ) : (nat (n := n) k).meaning S env = ordinal k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [nat,meaning_successor,ih,ordinal]

end

variable {n : ℕ}

def tupleProduct : {n : ℕ} → (k : ℕ) → QuotedTerm n → QuotedTerm n
  | _, 0, _ => empty.singleton
  | _, k+1, r => r.bind ((tupleProduct k r.up).map ((var 1).pair (var 0)))

variable {A : Type} [Fintype A]

def blockParameters : QuotedTerm n := tupleProduct 4 vertexBlocks

end QuotedTerm


namespace QuotedFormula

variable {n : ℕ}

def falsehood : QuotedFormula n := truth.neg

def anyList : List (QuotedFormula n) → QuotedFormula n
  | [] => falsehood
  | a::l => a.or (anyList l)

def allFin (k : ℕ) (f : Fin k → QuotedFormula n) : QuotedFormula n := allList (List.ofFn f)

def anyFin (k : ℕ) (f : Fin k → QuotedFormula n) : QuotedFormula n := anyList (List.ofFn f)

def nonempty (a : QuotedTerm n) : QuotedFormula n := (eq a .empty).neg

end QuotedFormula

namespace QuotedTerm

variable {n : ℕ}

def distanceAt (R u v : QuotedTerm n) : QuotedTerm n :=
  (indices.filter ((QuotedFormula.mem (triple u.up v.up (.var 0)) R.up).and
    (.allIn indices ((QuotedFormula.mem (.var 0) (.var 1)).imp
      ((QuotedFormula.mem (triple u.up.up v.up.up (.var 0)) R.up.up).neg))))).unique

end QuotedTerm

namespace QuotedFormula

open QuotedTerm

variable {n : ℕ}

def connected (R u v : QuotedTerm n) : QuotedFormula n :=
  mem (triple u v atoms.card) R

def resolving (α V R : QuotedTerm n) : QuotedFormula n :=
  allIn V (allIn V.up ((allFin 4 (fun i =>
    eq (distanceAt R.up.up ((α.up.up).component i.val) (.var 1))
      (distanceAt R.up.up ((α.up.up).component i.val) (.var 0)))).imp (eq (.var 1) (.var 0))))

def vertexLt (α R u v : QuotedTerm n) : QuotedFormula n :=
  anyFin 4 (fun i => (allFin 4 (fun j => if j.val < i.val then
    eq (distanceAt R (α.component j.val) u) (distanceAt R (α.component j.val) v)
    else truth)).and
      (mem (distanceAt R (α.component i.val) u) (distanceAt R (α.component i.val) v)))

def leastVertex (α V R v : QuotedTerm n) : QuotedFormula n :=
  (mem v V).and (allIn V ((vertexLt α.up R.up (.var 0) v.up).neg))

def hasEndpoints (e u v : QuotedTerm n) : QuotedFormula n :=
  (eq u v).neg.and ((incident u e).and (incident v e))

def edgeLt (α V R e f : QuotedTerm n) : QuotedFormula n :=
  existsIn V (existsIn V.up (existsIn V.up.up (existsIn V.up.up.up
    (allList [hasEndpoints e.up.up.up.up (.var 3) (.var 2),
      hasEndpoints f.up.up.up.up (.var 1) (.var 0),
      vertexLt α.up.up.up.up R.up.up.up.up (.var 3) (.var 2),
      vertexLt α.up.up.up.up R.up.up.up.up (.var 1) (.var 0),
      (vertexLt α.up.up.up.up R.up.up.up.up (.var 3) (.var 1)).or
        ((eq (.var 3) (.var 1)).and
          (vertexLt α.up.up.up.up R.up.up.up.up (.var 2) (.var 0)))]))))

def parentEligible (E R r v w : QuotedTerm n) : QuotedFormula n :=
  (adjacent E v w).and (eq (distanceAt R r w).successor (distanceAt R r v))

def parent (α V E R r v w : QuotedTerm n) : QuotedFormula n :=
  (parentEligible E R r v w).and
    (allIn V ((parentEligible E.up R.up r.up v.up (.var 0)).imp
      ((vertexLt α.up R.up (.var 0) w.up).neg)))

end QuotedFormula

namespace QuotedTerm

open QuotedFormula

variable {n : ℕ}

def root (α V R : QuotedTerm n) : QuotedTerm n :=
  (V.filter (leastVertex α.up V.up R.up (.var 0))).unique

def tree (α V E R : QuotedTerm n) : QuotedTerm n :=
  E.filter (existsIn V.up (existsIn V.up.up
    ((parent α.up.up.up V.up.up.up E.up.up.up R.up.up.up
      (root α V R).up.up.up (.var 1) (.var 0)).and
        (hasEndpoints (.var 2) (.var 1) (.var 0)))))

def nextEdges (α V E R T x : QuotedTerm n) : QuotedTerm n :=
  ((E.diff T).filter (eq (x.up.inter (.var 0)) .empty)).filter
    (allIn (E.diff T).up (((eq (x.up.up.inter (.var 0)) .empty).and
      (edgeLt α.up.up V.up.up R.up.up (.var 0) (.var 1))).neg))

end QuotedTerm

namespace SourceSyntax

open QuotedTerm QuotedFormula

variable {n : ℕ}

def next4 (i : Fin 4) : Fin 4 := ⟨(i.val+1)%4,Nat.mod_lt _ (by decide)⟩

def prev4 (i : Fin 4) : Fin 4 := ⟨(i.val+3)%4,Nat.mod_lt _ (by decide)⟩

def fv (f : QuotedTerm n) (i : Fin 4) : QuotedTerm n := f.fst.component i.val

def fe (f : QuotedTerm n) (i : Fin 4) : QuotedTerm n := f.snd.component i.val

def faceDescription (f : QuotedTerm n) : QuotedFormula n :=
  allFin 4 (fun i => (allFin 4 (fun j => if i=j then truth else
    ((eq (fv f i) (fv f j)).neg.and (eq (fe f i) (fe f j)).neg))).and
      (hasEndpoints (fe f i) (fv f i) (fv f (next4 i))))

def faces (V E : QuotedTerm n) : QuotedTerm n :=
  ((tupleProduct 4 V).bind ((tupleProduct 4 E.up).map ((var 1).pair (var 0)))).filter
    (faceDescription (.var 0))

def adjacentMatch (f s t : QuotedTerm n) (i j : Fin 4) : QuotedFormula n :=
  allList [mem s (fe f i),mem t (fe f j),
    existsIn (fv f (if j=next4 i then j else i))
      ((input .I (.var 0) s.up).and (input .I (.var 0) t.up))]

def matchFace (f s t : QuotedTerm n) : QuotedFormula n :=
  anyFin 4 (fun i => anyFin 4 (fun j =>
    (mem s (fe f i)).and ((mem t (fe f j)).and
      (if j=next4 i ∨ j=prev4 i then adjacentMatch f s t i j else
        existsIn (fe f (next4 i))
          ((adjacentMatch f.up s.up (.var 0) i (next4 i)).and
            (adjacentMatch f.up t.up (.var 0) j (next4 i)))))))

def side (f e : QuotedTerm n) : QuotedFormula n :=
  anyFin 4 (fun i => eq e (fe f i))

def onSide (f s : QuotedTerm n) : QuotedFormula n :=
  anyFin 4 (fun i => mem s (fe f i))

def baseEq (F e s t : QuotedTerm n) : QuotedFormula n :=
  allIn F ((side (.var 0) e.up).imp (matchFace (.var 0) s.up t.up))

def candidates (F N x : QuotedTerm n) : QuotedTerm n :=
  N.bind ((var 0).filter (allIn F.up.up ((side (.var 0) (.var 2)).imp
    (allIn x.up.up.up ((onSide (.var 1) (.var 0)).imp
      (matchFace (.var 1) (.var 2) (.var 0)))))))

end SourceSyntax


namespace CPTTerm

variable {n : ℕ} {A : Type} [Fintype A]

def comprehend (r : CPTTerm n) (body : CPTTerm (n+1)) (guard : CPTFormula (n+1)) : CPTTerm n :=
  ⟨.comprehend body.code r.code guard.code,by
    simp only [Term.wscCount,r.count,body.count,guard.count,Nat.add_zero]⟩

def map (r : CPTTerm n) (body : CPTTerm (n+1)) : CPTTerm n :=
  r.comprehend body (.quoted .truth)

end CPTTerm


section

open RelationPools

variable {A : Type} [Fintype A]

def decodeRelation (r : HF A) : Relation A :=
  Finset.univ.filter fun ab => pairCode ab ∈ elements r

@[simp] lemma decodeRelation_code (r : Relation A) : decodeRelation (relationCode r) = r := by
  ext ab
  simp [decodeRelation]

namespace QuotedTerm

variable {n : ℕ}

def normalizeRelation (r : QuotedTerm n) : QuotedTerm n :=
  relation (.link (.var 1) (.var 0) r.up.up)

def normalizeRelations (r : QuotedTerm n) : QuotedTerm n := r.map (normalizeRelation (.var 0))

def normalizeCandidates (r : QuotedTerm n) : QuotedTerm n :=
  atomFilter ((QuotedFormula.mem (.var 0) r.up).and (.input .Ed (.var 0) (.var 0)))

@[simp] lemma meaning_normalizeRelation (S : Input A) (env : Fin n → HF A) (r : QuotedTerm n) :
    (normalizeRelation r).meaning S env = relationCode (decodeRelation (r.meaning S env)) := by
  simp only [normalizeRelation,meaning_relation,QuotedFormula.meaning_link,meaning_var,
    meaning_up,Fin.cons_zero,Fin.cons_one,decodeRelation,pairCode]
  congr 1

@[simp] lemma meaning_normalizeRelations (S : Input A) (env : Fin n → HF A) (r : QuotedTerm n) :
    (normalizeRelations r).meaning S env = ofFinset
      (((elements (r.meaning S env)).image decodeRelation).image relationCode) := by
  simp [normalizeRelations,Finset.image_image,Function.comp_def]

@[simp] lemma meaning_normalizeCandidates (S : Input A) (env : Fin n → HF A) (r : QuotedTerm n) :
    (normalizeCandidates r).meaning S env = stateCode
      (decodeState (r.meaning S env) ∩ WitnessedChoice.edgeAtoms S) := by
  simp only [normalizeCandidates,meaning_atomFilter,QuotedFormula.meaning_and,
    QuotedFormula.meaning_mem,QuotedFormula.meaning_input,meaning_var,meaning_up,Fin.cons_zero,inputHF_atoms]
  congr 1
  ext a
  simp [decodeState,WitnessedChoice.edgeAtoms]

end QuotedTerm

namespace CPTTerm

variable {n : ℕ}

def normalizeCandidates (t : CPTTerm n) : CPTTerm n :=
  t.letIn (.quoted (QuotedTerm.normalizeCandidates (.var 0)))

def normalizeRelations (t : CPTTerm n) : CPTTerm n :=
  t.letIn (.quoted (QuotedTerm.normalizeRelations (.var 0)))

end CPTTerm

structure GuardedProgram where
  localBound : ℕ
  candidates : CPTTerm 2
  cycles : CPTTerm 2
  output : CPTFormula 2

namespace GuardedProgram

variable (G : GuardedProgram)

def witnesses : CPTTerm 2 := G.cycles.normalizeRelations.letIn
  (.quoted (QuotedTerm.witnessRelations G.localBound .truth (.var 1) (.var 0)))

def choice : CPTTerm 2 := G.candidates.normalizeCandidates.letIn
  (G.witnesses.up.letIn (.quoted (QuotedTerm.guardedChoice (.var 1) (.var 0))))

def step : QuotedTerm 3 := QuotedTerm.selectionStep (.var 1) (.var 0)

def witness : CPTTerm 3 := G.witnesses.rename ![0,2]

def formula : Formula 1 := .wsc step.code G.choice.code G.witness.code G.output.code

variable (S : Input A) (p : Polynomial ℝ) (α : HF A)

def candidateSet (x : Finset A) : Finset A :=
  decodeState (G.candidates.value S p (Fin.cons (stateCode x) (Fin.cons α Fin.elim0))) ∩
    WitnessedChoice.edgeAtoms S

def cycleSet (x : Finset A) : Finset (Relation A) :=
  (elements (G.cycles.value S p (Fin.cons (stateCode x) (Fin.cons α Fin.elim0)))).image decodeRelation

def selection : Selection A := guardedSelection G.localBound S True
  (G.candidateSet S p α) (G.cycleSet S p α)

end GuardedProgram

end


structure ClosedGuardedProgram where
  parameters : CPTTerm 0
  body : GuardedProgram

namespace ClosedGuardedProgram

variable (G : ClosedGuardedProgram)

def parameterTerm : CPTTerm 0 := G.parameters.letIn (.quoted
  (QuotedTerm.blockParameters.filter (.mem (.var 0) (.var 1))))

def formula : Formula 0 := Formula.existsIn G.parameterTerm.code G.body.formula

def sentence (p : Polynomial ℝ) : Sentence := ⟨G.formula,p⟩

end ClosedGuardedProgram


namespace SourceSyntax

open QuotedTerm QuotedFormula

variable {n : ℕ}

def connWithout (H h u v : QuotedTerm n) : QuotedFormula n :=
  existsIn H ((eq (var 0).fst h.up).and (connected (var 0).snd u.up v.up))

def traversal (V T H e u v : QuotedTerm n) : QuotedTerm n :=
  (triple e u v).singleton.cup (T.bind (V.up.bind
    ((V.up.up.filter (allList [hasEndpoints (var 2) (var 1) (var 0),
      (connWithout H.up.up.up (var 2) v.up.up.up u.up.up.up).neg,
      connWithout H.up.up.up (var 2) v.up.up.up (var 1),
      connWithout H.up.up.up (var 2) u.up.up.up (var 0)])).map
        (triple (var 2) (var 1) (var 0)))))

def traversalEdge (Γ h : QuotedTerm n) : QuotedFormula n :=
  existsIn Γ (eq (var 0).fst h.up)

def directedZ (R Γ o h s t : QuotedTerm n) : QuotedFormula n :=
  existsIn Γ ((eq (var 0).fst h.up).and
    (((mem (distanceAt R.up o.up (var 0).snd.fst)
      (distanceAt R.up o.up (var 0).snd.snd)).and (input (.Z 1) s.up t.up)).or
     ((mem (distanceAt R.up o.up (var 0).snd.fst)
      (distanceAt R.up o.up (var 0).snd.snd)).neg.and (input (.Z 2) s.up t.up))))

def cycleY (E F R Γ o : QuotedTerm n) : QuotedTerm n :=
  relation (existsIn E.up.up (allList [mem (var 2) (var 0),mem (var 1) (var 0),
    ((traversalEdge Γ.up.up.up (var 0)).neg.and (eq (var 2) (var 1))).or
      ((traversalEdge Γ.up.up.up (var 0)).and
        ((baseEq F.up.up.up (var 0) (var 2) (var 1)).and
          (directedZ R.up.up.up Γ.up.up.up o.up.up.up (var 0) (var 2) (var 1))))]))

def cycleX (V E cY : QuotedTerm n) : QuotedTerm n :=
  relation (existsIn V.up.up (allList [mem (var 2) (var 0),mem (var 1) (var 0),
    allIn E.up.up.up ((incident (var 1) (var 0)).imp
      (existsIn (var 0) (existsIn (var 1)
        (allList [input .I (var 5) (var 1),input .I (var 4) (var 0),
          link (var 1) (var 0) cY.up.up.up.up.up.up]))))]))

def cycleRelation (V E F R Γ o : QuotedTerm n) : QuotedTerm n :=
  (cycleY E F R Γ o).cup (cycleX V E (cycleY E F R Γ o))

def cycleRelations (V E F R T H N : QuotedTerm n) : QuotedTerm n :=
  identity.singleton.cup (N.bind (V.up.bind (V.up.up.bind
    ((V.up.up.up.filter (hasEndpoints (var 3) (var 2) (var 1))).map
      (cycleRelation V.up.up.up.up E.up.up.up.up F.up.up.up.up R.up.up.up.up
        (traversal V.up.up.up.up T.up.up.up.up H.up.up.up.up (var 3) (var 2) (var 1))
        (var 0))))))

def complete (E T x : QuotedTerm n) : QuotedFormula n :=
  allList [eq x (x.inter QuotedTerm.edgeAtoms),
    allIn (E.diff T) (eq (x.up.inter (var 0)).card (nat 1)),
    allIn T (eq (x.up.inter (var 0)) empty)]

def allowed (E T x v t : QuotedTerm n) : QuotedFormula n :=
  allIn (E.diff T) ((incident v.up (var 0)).imp
    (existsIn (x.up.inter (var 0)) (input .I t.up.up (var 0))))

def unsupported (V T S v t : QuotedTerm n) : QuotedFormula n :=
  existsIn T (existsIn V.up (allList [
    (eq (var 0) v.up.up).neg,incident v.up.up (var 1),incident (var 0) (var 1),
    (existsIn ((var 0).diff S.up.up)
      (existsIn (var 2) ((input .I t.up.up.up.up (var 0)).and
        (input .I (var 1) (var 0))))).neg]))

def deletedStep (V E T x S : QuotedTerm n) : QuotedTerm n :=
  S.cup (QuotedTerm.configAtoms.filter (existsIn V.up ((mem (var 1) (var 0)).and
    ((allowed E.up.up T.up.up x.up.up (var 0) (var 1)).neg.or
      (unsupported V.up.up T.up.up S.up.up (var 0) (var 1))))))

end SourceSyntax

namespace SourceProgram

open QuotedTerm QuotedFormula SourceSyntax

def distances {n : ℕ} : CPTTerm n := CPTTerm.distance (.quoted QuotedTerm.vertexBlocks) (.quoted QuotedTerm.edgeBlocks)

def parameters : CPTTerm 0 := distances.letIn (.quoted (blockParameters.filter
  (resolving (var 0) QuotedTerm.vertexBlocks (var 1))))

def candidates : CPTTerm 2 := distances.letIn (.quoted
  (SourceSyntax.candidates (faces QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks)
    (nextEdges (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0)
      (tree (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0)) (var 1)) (var 1)))

def connTable {n : ℕ} (V T : QuotedTerm n) : CPTTerm n :=
  (CPTTerm.quoted T).map ((CPTTerm.distance (.quoted V.up)
    (.quoted (T.up.diff (var 0).singleton))).letIn (.quoted ((var 1).pair (var 0))))

def cycles : CPTTerm 2 := distances.letIn ((CPTTerm.quoted
  (tree (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0))).letIn
    ((connTable QuotedTerm.vertexBlocks (var 0)).letIn (.quoted
      (cycleRelations QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (faces QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks) (var 2)
        (var 1) (var 0) (nextEdges (var 4) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 2) (var 1) (var 3))))))

def output : CPTFormula 2 := CPTFormula.letIn distances
  (CPTFormula.letIn (.quoted (tree (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0)))
    (CPTFormula.letIn ((CPTTerm.quoted
      (deletedStep QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 1) (var 3) (var 0))).iterate)
      (.quoted ((complete QuotedTerm.edgeBlocks (var 1) (var 3)).and
        (allIn QuotedTerm.vertexBlocks (nonempty ((var 0).diff (var 1))))))))

def program : ClosedGuardedProgram :=
  { parameters := parameters
    body := { localBound := RelationPools.localBound
              candidates := candidates
              cycles := cycles
              output := output } }

end SourceProgram


end WitnessedChoice.BGS

end

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_TreeElimination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type}

namespace FiniteIteration

variable {X : Type}

def run (f : Finset X → Finset X) : ℕ → Finset X
  | 0 => ∅
  | k+1 => f (run f k)

end FiniteIteration

end

end WitnessedChoice.BGS



namespace WitnessedChoice.BGS.BFS

noncomputable section

open Classical SimpleGraph

variable {V : Type} [Fintype V]

abbrev Item (V : Type) (k : ℕ) := V × V × Fin (k+1)

def update (G : SimpleGraph V) (k : ℕ) (R : Finset (Item V k)) : Finset (Item V k) :=
  R ∪ Finset.univ.filter (fun x => x.1 = x.2.1 ∧ x.2.2.val = 0) ∪
    Finset.univ.filter (fun x => ∃ u : V, ∃ j : Fin (k+1),
      (x.1,u,j) ∈ R ∧ x.2.2.val = j.val+1 ∧ (u = x.2.1 ∨ G.Adj u x.2.1))

@[simp] lemma mem_update (G : SimpleGraph V) (k : ℕ) (R : Finset (Item V k)) (x : Item V k) :
    x ∈ update G k R ↔ (x ∈ R ∨ (x.1 = x.2.1 ∧ x.2.2.val = 0)) ∨
      ∃ u : V, ∃ j : Fin (k+1), (x.1,u,j) ∈ R ∧ x.2.2.val = j.val+1 ∧
        (u = x.2.1 ∨ G.Adj u x.2.1) := by simp [update,or_assoc]

def closure (G : SimpleGraph V) (k : ℕ) : Finset (Item V k) :=
  FiniteIteration.run (update G k) (Fintype.card (Item V k))

def good (G : SimpleGraph V) (k : ℕ) : Finset (Item V k) :=
  Finset.univ.filter (fun x => ∃ w : G.Walk x.1 x.2.1, w.length ≤ x.2.2.val)

end

end WitnessedChoice.BGS.BFS



namespace WitnessedChoice.BGS





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

namespace QuotedTerm

variable {n : ℕ} {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

def HFTriple (u v i : HF A) : HF A := Hereditary.pair u (Hereditary.pair v i)

@[simp] lemma mem_distanceBase (V : QuotedTerm n) (z : HF A) :
    z ∈ elements ((distanceBase V).meaning S env) ↔
      ∃ v ∈ elements (V.meaning S env), HFTriple v v emptyHF = z := by
  simp [distanceBase,HFTriple]

@[simp] lemma mem_distanceFresh (V J R : QuotedTerm n) (z : HF A) :
    z ∈ elements ((distanceFresh V J R).meaning S env) ↔
    ∃ v ∈ elements (V.meaning S env), ∃ w ∈ elements (V.meaning S env),
      ∃ i ∈ elements (ordinal (A := A) (Fintype.card A+1)),
        ofFinset (insert i (elements i)) ∈ elements (ordinal (A := A) (Fintype.card A+1)) ∧
        (∃ u ∈ elements (V.meaning S env),
          HFTriple v u i ∈ elements (R.meaning S env) ∧
          (u=w ∨ (QuotedFormula.adjacent J.up.up (.var 0) (.var 1)).meaning S
            (Fin.cons u (Fin.cons w env)))) ∧
        HFTriple v w (ofFinset (insert i (elements i))) = z := by
  simp [distanceFresh,HFTriple,QuotedFormula.adjacent,and_assoc,fin_cons_three]

end QuotedTerm

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

open QuotedTerm

variable {A V : Type} [Fintype A] [Fintype V]

def blockIncident (S : Input A) (v e : HF A) : Prop :=
  ∃ t ∈ elements v, ∃ s ∈ elements e, inputHF S .I t s = true

def blockAdjacent (S : Input A) (J u v : HF A) : Prop :=
  u ≠ v ∧ ∃ e ∈ elements J, blockIncident S u e ∧ blockIncident S v e

def distanceCode (code : V → HF A) (x : BFS.Item V (Fintype.card A)) : HF A :=
  HFTriple (code x.1) (code x.2.1) (ordinal x.2.2.val)

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary QuotedTerm

namespace QuotedFormula

variable {n : ℕ} {A : Type} [Fintype A]

@[simp] lemma meaning_allFin (S : Input A) (env : Fin n → HF A) (k : ℕ)
    (f : Fin k → QuotedFormula n) : (allFin k f).meaning S env ↔ ∀ i, (f i).meaning S env := by
  simp [allFin]

@[simp] lemma meaning_anyList (S : Input A) (env : Fin n → HF A) (l : List (QuotedFormula n)) :
    (anyList l).meaning S env ↔ ∃ q ∈ l, q.meaning S env := by
  induction l with
  | nil => simp [anyList,falsehood,truth]
  | cons q l ih => simp [anyList,ih]

@[simp] lemma meaning_anyFin (S : Input A) (env : Fin n → HF A) (k : ℕ)
    (f : Fin k → QuotedFormula n) : (anyFin k f).meaning S env ↔ ∃ i, (f i).meaning S env := by
  simp [anyFin]

end QuotedFormula

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

namespace QuotedTerm

variable {A : Type} [Fintype A] {n : ℕ}

def firstHF (x : HF A) : HF A := uniqueHF (unionHF (ofFinset
  ((elements x).filter (fun z => cardHF z = ordinal 1))))

def secondHF (x : HF A) : HF A :=
  if cardHF (unionHF x) = ordinal 1 then firstHF x else
    uniqueHF (ofFinset ((elements (unionHF x)).filter
      (fun z => z ∉ elements (Hereditary.singleton (firstHF x)))))

@[simp] lemma meaning_fst (S : Input A) (env : Fin n → HF A) (a : QuotedTerm n) :
    a.fst.meaning S env = firstHF (a.meaning S env) := by
  simp [fst,firstHF]

@[simp] lemma meaning_snd (S : Input A) (env : Fin n → HF A) (a : QuotedTerm n) :
    a.snd.meaning S env = secondHF (a.meaning S env) := by
  simp [snd,secondHF,meaning_cond]

end QuotedTerm

end

end WitnessedChoice.BGS



namespace WitnessedChoice.TreeTest

noncomputable section

open Classical

structure RootedTree (V : Type) where
  root : V
  parent : V → V
  level : V → ℕ
  parent_lower : ∀ v, v ≠ root → level (parent v) < level v

namespace RootedTree

variable {V A : Type} (T : RootedTree V)

def Adj (v w : V) : Prop :=
  (v ≠ T.root ∧ T.parent v = w) ∨ (w ≠ T.root ∧ T.parent w = v)

variable (B : V → Finset A) (rel : V → V → A → A → Prop)
  (hroot : (B T.root).Nonempty)
  (hext : ∀ v, v ≠ T.root → ∀ a ∈ B (T.parent v), ∃ b ∈ B v, rel (T.parent v) v a b)

def label (v : V) : {a : A // a ∈ B v} :=
  if hv : v = T.root then
    ⟨hroot.choose, hv ▸ hroot.choose_spec⟩
  else
    let u := label (T.parent v)
    let h := hext v hv u.val u.property
    ⟨h.choose, h.choose_spec.1⟩
termination_by T.level v
decreasing_by exact T.parent_lower v hv

end RootedTree

structure Problem (V A : Type) where
  tree : RootedTree V
  configs : Finset A
  block : V → Finset A
  block_subset : ∀ v, block v ⊆ configs
  block_unique : ∀ v w a, a ∈ block v → a ∈ block w → v = w
  allowed : A → Prop
  compatible : V → V → A → A → Prop
  compatible_symm : ∀ v w a b, compatible v w a b → compatible w v b a

namespace Problem

variable {V A : Type} (P : Problem V A)

def update (S : Finset A) : Finset A := S ∪ P.configs.filter (fun a =>
  ¬ P.allowed a ∨ ∃ v, a ∈ P.block v ∧ ∃ w, P.tree.Adj v w ∧
    ¬ ∃ b ∈ P.block w, b ∉ S ∧ P.compatible v w a b)

def run : ℕ → Finset A
  | 0 => ∅
  | k+1 => P.update (run k)

def deleted : Finset A := P.run P.configs.card

def survivors (v : V) : Finset A := (P.block v).filter (· ∉ P.deleted)

def Solution (t : V → A) : Prop :=
  (∀ v, t v ∈ P.block v ∧ P.allowed (t v)) ∧
    ∀ v w, P.tree.Adj v w → P.compatible v w (t v) (t w)

end Problem

end

end WitnessedChoice.TreeTest

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_GridGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical Support

variable {n : ℕ}

def facePlane : Face n → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

def faceSide : Face n → Fin 4 → Edge n
  | .inl (i,j,k) => ![ex i j.castSucc k, ey i.succ j k, ex i j.succ k, ey i.castSucc j k]
  | .inr (.inl (i,j,k)) => ![ex i j k.castSucc, ez i.succ j k, ex i j k.succ, ez i.castSucc j k]
  | .inr (.inr (i,j,k)) => ![ey i j k.castSucc, ez i j.succ k, ey i j k.succ, ez i j.castSucc k]

def sideAxis : Fin 3 → Fin 4 → Fin 3 :=
  ![![0,1,0,1], ![0,2,0,2], ![1,2,1,2]]

lemma support_cycle (f : Face n) (e : Edge n) (h : cycle f e ≠ 0) :
    ∃ i, faceSide f i = e := by
  by_contra hn
  have hh (i : Fin 4) : e ≠ faceSide f i := fun he => hn ⟨i,he.symm⟩
  apply h
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩)
  all_goals
    have h0 := hh 0
    have h1 := hh 1
    have h2 := hh 2
    have h3 := hh 3
    simp [faceSide] at h0 h1 h2 h3
    simp [cycle,Pi.single_eq_of_ne,h0,h1,h2,h3]

def faceCorner : Face n → Fin 4 → Vertex n
  | .inl (i,j,k) => ![(i.castSucc,j.castSucc,k),(i.succ,j.castSucc,k),
      (i.succ,j.succ,k),(i.castSucc,j.succ,k)]
  | .inr (.inl (i,j,k)) => ![(i.castSucc,j,k.castSucc),(i.succ,j,k.castSucc),
      (i.succ,j,k.succ),(i.castSucc,j,k.succ)]
  | .inr (.inr (i,j,k)) => ![(i,j.castSucc,k.castSucc),(i,j.succ,k.castSucc),
      (i,j.succ,k.succ),(i,j.castSucc,k.succ)]

abbrev VertexFaces (v : Vertex n) :=
  {f : Face n // ∃ e : IncidentEdges v, cycle f e.val ≠ 0}

variable {b : Vertex n → Scalar} {v : Vertex n}

def Configuration.faceValue (s : Configuration b v) (f : VertexFaces v) : Plane :=
  (s.state f.property.choose).face ⟨f.val,f.property.choose_spec⟩

def Configuration.code (e0 : IncidentEdges v) (s : Configuration b v) :
    (VertexFaces v → Plane) × ({e : IncidentEdges v // e ≠ e0} → Scalar) :=
  (s.faceValue,fun e => (s.state e.val).flow)

end





noncomputable section

open Classical WitnessedChoice.TreeTest

variable {n : ℕ}

structure ParentEdges (T : RootedTree (Vertex n)) where
  edge : (v : Vertex n) → v ≠ T.root → Edge n
  endpoints : ∀ v h,
    (head (edge v h) = v ∧ tail (edge v h) = T.parent v) ∨
    (tail (edge v h) = v ∧ head (edge v h) = T.parent v)

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

def treeEdges : Finset (Edge n) :=
  Finset.univ.image (fun v : {v : Vertex n // v ≠ T.root} => P.edge v.val v.property)

def sign (v : Vertex n) (h : v ≠ T.root) : Scalar :=
  if head (P.edge v h) = v then 1 else -1

def route (Q : ParentEdges T) (v : Vertex n) : Edge n → Scalar :=
  if hv : v = T.root then 0 else
    Pi.single (Q.edge v hv) (Q.sign v hv) + route Q (T.parent v)
termination_by T.level v
decreasing_by exact T.parent_lower v hv

lemma boundary_single (e : Edge n) (a : Scalar) :
    boundary (Pi.single e a) = a • (Pi.single (head e) 1 - Pi.single (tail e) 1) := by
  rw [WitnessedSeparation.Grid.boundary_single]
  simp only [smul_sub,← Pi.single_smul,smul_eq_mul,mul_one]

lemma boundary_parent (v : Vertex n) (hv : v ≠ T.root) :
    boundary (Pi.single (P.edge v hv) (P.sign v hv)) =
      Pi.single v 1 - Pi.single (T.parent v) 1 := by
  rw [boundary_single]
  rcases P.endpoints v hv with ⟨hh,ht⟩ | ⟨ht,hh⟩
  · simp [sign,hh,ht]
  · have hne : head (P.edge v hv) ≠ v := by
      intro he
      have hp : T.parent v = v := hh.symm.trans he
      have := T.parent_lower v hv
      rw [hp] at this
      omega
    rw [sign,ite_eq_right hne,ht,hh,neg_smul,one_smul]
    abel

lemma boundary_route (v : Vertex n) :
    boundary (P.route v) = Pi.single v 1 - Pi.single T.root 1 := by
  induction v using (measure T.level).wf.induction with
  | h v ih =>
    rw [route]
    split_ifs with hv
    · subst v
      simp
    · rw [map_add,P.boundary_parent v hv,ih (T.parent v) (T.parent_lower v hv)]
      abel

def fundamental (e : Edge n) (a : Scalar) : Edge n → Scalar :=
  Pi.single e a + a • P.route (tail e) - a • P.route (head e)

lemma boundary_fundamental (e : Edge n) (a : Scalar) : boundary (P.fundamental e a) = 0 := by
  rw [fundamental,map_sub,map_add,map_smul,map_smul,boundary_single,
    P.boundary_route,P.boundary_route]
  simp only [smul_sub]
  abel

def flow (e : Edge n) (a : Scalar) : FlowSpace n := ⟨P.fundamental e a,P.boundary_fundamental e a⟩

def solve (r : Vertex n → Scalar) : Edge n → Scalar := ∑ v, r v • P.route v

end ParentEdges

end





noncomputable section

open Classical Support WitnessedChoice.TreeTest

variable {n : ℕ}

def ConsistentSelection (x : Finset (Σ e : Edge n, LocalGroup e)) : Prop :=
  (∀ r ∈ x, ∀ s ∈ x, r.1 = s.1 → r = s) ∧
  ∀ r ∈ x, ∀ s ∈ x, ∀ f : Face n, ∀ hr : cycle f r.1 ≠ 0, ∀ hs : cycle f s.1 ≠ 0,
    r.2.face ⟨f,hr⟩ = s.2.face ⟨f,hs⟩

def selectedVectors (x : Finset (Σ e : Edge n, LocalGroup e)) (f : Face n) : Plane :=
  if h : ∃ r ∈ x, cycle f r.1 ≠ 0 then
    h.choose.2.face ⟨f,h.choose_spec.2⟩ else 0

def selectedScalars (x : Finset (Σ e : Edge n, LocalGroup e)) (e : Edge n) : Scalar :=
  if h : ∃ r ∈ x, r.1 = e then h.choose.2.flow else 0

def globalStates (u : Face n → Plane) (z : Edge n → Scalar) (e : Edge n) : LocalGroup e :=
  ⟨fun f => u f.val,z e⟩

lemma globalStates_compatible (u : Face n → Plane) (z : Edge n → Scalar) (v : Vertex n) :
    Compatible (fun e : IncidentEdges v => globalStates u z e.val) := by
  intro e e' f hf hf'
  rfl

lemma globalStates_charge (u : Face n → Plane) (z : Edge n → Scalar) (v : Vertex n) :
    divergence (fun e : IncidentEdges v => globalStates u z e.val) = boundary z v :=
  sum_incident z v

def globalConfiguration (b : Vertex n → Scalar) (u : Face n → Plane)
    (z : Edge n → Scalar) (hz : boundary z = b) (v : Vertex n) : Configuration b v where
  state := fun e => globalStates u z e.val
  compatible := globalStates_compatible u z v
  charge := (globalStates_charge u z v).trans (congrFun hz v)

end





noncomputable section

open Classical Support

variable {n : ℕ} {v : Vertex n} {b : Vertex n → Scalar}

def extendVertexScalars (b : Vertex n → Scalar) (v : Vertex n) (e0 : IncidentEdges v)
    (z : IncidentEdges v → Scalar) (e : IncidentEdges v) : Scalar :=
  if e = e0 then (epsilon v e0.val)⁻¹ *
    (b v - ∑ h ∈ Finset.univ.erase e0, epsilon v h.val * z h)
  else z e

end





noncomputable section

open Classical Support

variable {n : ℕ}

def vertexCoord (v : Vertex n) : Fin 3 → Fin (n+1) := ![v.1,v.2.1,v.2.2]

def planeAxis (p a : Fin 3) : Prop := ∃ i : Fin 4, sideAxis p i = a

instance instDecidablePlaneAxis (p a : Fin 3) : Decidable (planeAxis p a) := Classical.propDecidable _

def faceBase (f : Face n) : Fin 3 → Fin (n+1) := vertexCoord (faceCorner f 0)

lemma vertexCoord_injective : Function.Injective (vertexCoord (n := n)) := by
  intro v w h
  exact Prod.ext (congrFun h 0) (Prod.ext (congrFun h 1) (congrFun h 2))

end





noncomputable section

open Classical Support

variable {n : ℕ} {b : Vertex n → Scalar}

@[simp] lemma castSucc_ne_succ_self (i : Fin n) : i.castSucc ≠ i.succ := by
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_castSucc,Fin.val_succ] at hh
  omega

@[simp] lemma succ_ne_castSucc_self (i : Fin n) : i.succ ≠ i.castSucc :=
  (castSucc_ne_succ_self i).symm

lemma cycle_faceSide (f : Face n) (i : Fin 4) : cycle f (faceSide f i) ≠ 0 := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;> fin_cases i
  all_goals simp [cycle,faceSide,ex,ey,ez]

lemma faceSide_injective_index (f : Face n) : Function.Injective (faceSide f) := by
  intro i j
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;> fin_cases i <;> fin_cases j
  all_goals simp [faceSide,ex,ey,ez]

def AdjacentIndex (i j : Fin 4) : Prop := j = i+1 ∨ i = j+1

end





noncomputable section

open Classical Support WitnessedChoice

variable {n : ℕ} {b : Vertex n → Scalar}

def actionPerm (g : BoxGroup n) : Equiv.Perm (Atom b) := MulAction.toPerm g

@[simp] lemma actionPerm_apply (g : BoxGroup n) (a : Atom b) : actionPerm g a = g • a := rfl

def edgeFootprint (F : Finset (Face n)) : Finset (Edge n) :=
  F.biUnion fun f => Finset.univ.image (faceSide f)

def vertexFootprint (F : Finset (Face n)) : Finset (Vertex n) :=
  F.biUnion fun f => Finset.univ.image (faceCorner f)

def edgeBlockSet (b : Vertex n → Scalar) (e : Edge n) : Finset (Atom b) :=
  Finset.univ.image (fun s : LocalGroup e => .inl ⟨e,s⟩)

def vertexBlockSet (b : Vertex n → Scalar) (v : Vertex n) : Finset (Atom b) :=
  Finset.univ.image (fun s : Configuration b v => .inr ⟨v,s⟩)

def affectedAtoms (b : Vertex n → Scalar) (E : Finset (Edge n)) (V : Finset (Vertex n)) : Finset (Atom b) :=
  (E.biUnion (edgeBlockSet b)) ∪ (V.biUnion (vertexBlockSet b))

end





noncomputable section

open Classical Support WitnessedChoice

variable {n : ℕ} {b : Vertex n → Scalar}

def AcceptsFaces (x : Finset (Σ e : Edge n, LocalGroup e)) (e : Edge n) (s : LocalGroup e) : Prop :=
  ∀ t ∈ x, ∀ f : Face n, ∀ he : cycle f e ≠ 0, ∀ ht : cycle f t.1 ≠ 0,
    s.face ⟨f,he⟩ = t.2.face ⟨f,ht⟩

def faceDelta (e : Edge n) (s t : LocalGroup e) (f : Face n) : Plane :=
  if h : cycle f e ≠ 0 then t.face ⟨f,h⟩ - s.face ⟨f,h⟩ else 0

end





noncomputable section

open Classical SimpleGraph

variable {n : ℕ}

def boxGraph (n : ℕ) : SimpleGraph (Vertex n) :=
  (pathGraph (n+1)).boxProd ((pathGraph (n+1)).boxProd (pathGraph (n+1)))

lemma boxGraph_connected (n : ℕ) : (boxGraph n).Connected := by
  simp only [boxGraph,connected_boxProd,pathGraph_connected,and_self]

lemma boxGraph_tail_head (e : Edge n) : (boxGraph n).Adj (tail e) (head e) := by
  rcases e with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals simp [boxGraph,boxProd_adj,pathGraph_adj,tail,head]

lemma boxGraph_adj_iff (u v : Vertex n) : (boxGraph n).Adj u v ↔
    ∃ e : Edge n, (u = tail e ∧ v = head e) ∨ (v = tail e ∧ u = head e) := by
  constructor
  · intro h
    rcases u with ⟨i,j,k⟩
    rcases v with ⟨i',j',k'⟩
    simp only [boxGraph,boxProd_adj,pathGraph_adj,Prod.mk.injEq] at h
    rcases h with ⟨h,he⟩ | ⟨h,hi⟩
    · rcases he with ⟨rfl,rfl⟩
      rcases h with h | h
      · refine ⟨ex ⟨i.val,by omega⟩ j k,Or.inl ⟨?_,?_⟩⟩
        · rfl
        · apply Prod.ext
          · apply Fin.ext; exact h.symm
          · rfl
      · refine ⟨ex ⟨i'.val,by omega⟩ j k,Or.inr ⟨?_,?_⟩⟩
        · rfl
        · apply Prod.ext
          · apply Fin.ext; exact h.symm
          · rfl
    · subst i'
      rcases h with ⟨h,hk⟩ | ⟨h,hj⟩
      · subst k'
        rcases h with h | h
        · refine ⟨ey i ⟨j.val,by omega⟩ k,Or.inl ⟨?_,?_⟩⟩
          · rfl
          · simp only [ey,head,Prod.mk.injEq,true_and,and_true]
            exact Fin.ext h.symm
        · refine ⟨ey i ⟨j'.val,by omega⟩ k,Or.inr ⟨?_,?_⟩⟩
          · rfl
          · simp only [ey,head,Prod.mk.injEq,true_and,and_true]
            exact Fin.ext h.symm
      · subst j'
        rcases h with h | h
        · refine ⟨ez i j ⟨k.val,by omega⟩,Or.inl ⟨?_,?_⟩⟩
          · rfl
          · simp only [ez,head,Prod.mk.injEq,true_and]
            exact Fin.ext h.symm
        · refine ⟨ez i j ⟨k'.val,by omega⟩,Or.inr ⟨?_,?_⟩⟩
          · rfl
          · simp only [ez,head,Prod.mk.injEq,true_and]
            exact Fin.ext h.symm
  · rintro ⟨e,(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩
    · exact boxGraph_tail_head e
    · exact (boxGraph_tail_head e).symm

def cornerAnchors (n : ℕ) : Fin 4 → Vertex n :=
  ![(0,0,0),(Fin.last n,0,0),(0,Fin.last n,0),(0,0,Fin.last n)]

end

end WitnessedSeparation.Grid

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_AnchoredTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedChoice

noncomputable section

open Classical

namespace AnchoredTree

variable {V : Type} [Fintype V]

def key (G : SimpleGraph V) (α : Fin 4 → V) (v : V) : Lex (Fin 4 → ℕ) :=
  toLex (fun i => G.dist (α i) v)

def Resolving (G : SimpleGraph V) (α : Fin 4 → V) : Prop := Function.Injective (key G α)

def Eligible (G : SimpleGraph V) (r v w : V) : Prop := G.Adj v w ∧ G.dist r w + 1 = G.dist r v

omit [Fintype V] in
lemma exists_eligible (G : SimpleGraph V) (hG : G.Connected) (r v : V) (hv : v ≠ r) :
    ∃ w, Eligible G r v w := by
  obtain ⟨p,hp⟩ := hG.exists_walk_length_eq_dist v r
  cases p with
  | nil => exact (hv rfl).elim
  | @cons _ w _ hadj q =>
    refine ⟨w,hadj,?_⟩
    have hle := G.dist_le q
    have hd := hadj.diff_dist_adj (u := r)
    simp only [SimpleGraph.Walk.length_cons] at hp
    rw [G.dist_comm (u := v) (v := r)] at hp
    rw [G.dist_comm (u := w) (v := r)] at hle
    omega

omit [Fintype V] in
lemma exists_min_key (G : SimpleGraph V) (α : Fin 4 → V) (D : Finset V) (hD : D.Nonempty) :
    ∃ v ∈ D, ∀ w ∈ D, ¬key G α w < key G α v := by
  let K := D.image (key G α)
  have hK : K.Nonempty := hD.image _
  obtain ⟨v,hv,he⟩ := Finset.mem_image.mp (Finset.min'_mem K hK)
  refine ⟨v,hv,?_⟩
  intro w hw hlt
  have hm := Finset.min'_le K (key G α w) (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
  rw [←he] at hm
  exact (not_lt_of_ge hm) hlt

lemma exists_parent (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V)
    (v : V) (hv : v ≠ α 0) :
    ∃ w, Eligible G (α 0) v w ∧ ∀ z, Eligible G (α 0) v z → ¬key G α z < key G α w := by
  obtain ⟨w,hw⟩ := exists_eligible G hG (α 0) v hv
  obtain ⟨z,hz,hm⟩ := exists_min_key G α (Finset.univ.filter (Eligible G (α 0) v))
    ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩⟩
  exact ⟨z,(Finset.mem_filter.mp hz).2,fun y hy => hm y (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩)⟩

def parent (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V) (v : V) : V :=
  if hv : v = α 0 then α 0 else (exists_parent G hG α v hv).choose

lemma parent_property (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V)
    (v : V) (hv : v ≠ α 0) :
    Eligible G (α 0) v (parent G hG α v) ∧
      ∀ z, Eligible G (α 0) v z → ¬key G α z < key G α (parent G hG α v) := by
  rw [parent,dite_eq_right hv]
  exact (exists_parent G hG α v hv).choose_spec

def rooted (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V) : TreeTest.RootedTree V where
  root := α 0
  parent := parent G hG α
  level := G.dist (α 0)
  parent_lower v hv := by have h := (parent_property G hG α v hv).1.2; omega

end AnchoredTree

end

end WitnessedChoice



namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

@[simp] lemma mem_edgeBlockSet (e : Edge n) (a : Atom b) :
    a ∈ edgeBlockSet b e ↔ ∃ s : LocalGroup e, a = .inl ⟨e,s⟩ := by
  simp only [edgeBlockSet,Finset.mem_image,Finset.mem_univ,true_and]
  aesop

@[simp] lemma mem_vertexBlockSet (v : Vertex n) (a : Atom b) :
    a ∈ vertexBlockSet b v ↔ ∃ s : Configuration b v, a = .inr ⟨v,s⟩ := by
  simp only [vertexBlockSet,Finset.mem_image,Finset.mem_univ,true_and]
  aesop

def vertexCode (b : Vertex n → Scalar) (v : Vertex n) : HF (Atom b) := stateCode (vertexBlockSet b v)

def edgeCode (b : Vertex n → Scalar) (e : Edge n) : HF (Atom b) := stateCode (edgeBlockSet b e)

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

def edgeGraph (T : Finset (Edge n)) : SimpleGraph (Vertex n) where
  Adj u v := ∃ e ∈ T, (u = tail e ∧ v = head e) ∨ (v = tail e ∧ u = head e)
  symm := ⟨by intro u v; rintro ⟨e,he,h⟩; exact ⟨e,he,h.symm⟩⟩
  loopless := ⟨by
    intro v
    rintro ⟨e,he,h|h⟩
    all_goals exact head_ne_tail e (h.2.symm.trans h.1)⟩

end





noncomputable section

open Classical

variable {n : ℕ}

lemma xy_incident_face (i : Fin n) (j k : Fin (n+1)) (i' k' : Fin (n+1)) (j' : Fin n) (v : Vertex n)
    (hv : incident v (ex i j k)) (hw : incident v (ey i' j' k')) :
    ∃ f : Face n, cycle f (ex i j k) ≠ 0 ∧ cycle f (ey i' j' k') ≠ 0 := by
  rcases hv with hv|hv
  all_goals subst v
  all_goals rcases hw with hw|hw
  all_goals simp only [head,tail] at hw
  all_goals rcases hw with ⟨hi,hj,hk⟩
  all_goals refine ⟨.inl (i,j',k),?_,?_⟩
  all_goals solve
    | (convert cycle_faceSide (n := n) (.inl (i,j',k)) 0 using 1 ; simp_all [faceSide])
    | (convert cycle_faceSide (n := n) (.inl (i,j',k)) 1 using 1 ; simp_all [faceSide])
    | (convert cycle_faceSide (n := n) (.inl (i,j',k)) 2 using 1 ; simp_all [faceSide])
    | (convert cycle_faceSide (n := n) (.inl (i,j',k)) 3 using 1 ; simp_all [faceSide])

lemma xz_incident_face (i : Fin n) (j k : Fin (n+1)) (i' j' : Fin (n+1)) (k' : Fin n) (v : Vertex n)
    (hv : incident v (ex i j k)) (hw : incident v (ez i' j' k')) :
    ∃ f : Face n, cycle f (ex i j k) ≠ 0 ∧ cycle f (ez i' j' k') ≠ 0 := by
  rcases hv with hv|hv
  all_goals subst v
  all_goals rcases hw with hw|hw
  all_goals simp only [head,tail] at hw
  all_goals rcases hw with ⟨hi,hj,hk⟩
  all_goals refine ⟨.inr (.inl (i,j,k')),?_,?_⟩
  all_goals solve
    | (convert cycle_faceSide (n := n) (.inr (.inl (i,j,k'))) 0 using 1 ; simp_all [faceSide])
    | (convert cycle_faceSide (n := n) (.inr (.inl (i,j,k'))) 1 using 1 ; simp_all [faceSide])
    | (convert cycle_faceSide (n := n) (.inr (.inl (i,j,k'))) 2 using 1 ; simp_all [faceSide])
    | (convert cycle_faceSide (n := n) (.inr (.inl (i,j,k'))) 3 using 1 ; simp_all [faceSide])

lemma yz_incident_face (j : Fin n) (i k : Fin (n+1)) (i' j' : Fin (n+1)) (k' : Fin n) (v : Vertex n)
    (hv : incident v (ey i j k)) (hw : incident v (ez i' j' k')) :
    ∃ f : Face n, cycle f (ey i j k) ≠ 0 ∧ cycle f (ez i' j' k') ≠ 0 := by
  rcases hv with hv|hv
  all_goals subst v
  all_goals rcases hw with hw|hw
  all_goals simp only [head,tail] at hw
  all_goals rcases hw with ⟨hi,hj,hk⟩
  all_goals refine ⟨.inr (.inr (i,j,k')),?_,?_⟩
  all_goals solve
    | (convert cycle_faceSide (n := n) (.inr (.inr (i,j,k'))) 0 using 1 ; simp_all [faceSide])
    | (convert cycle_faceSide (n := n) (.inr (.inr (i,j,k'))) 1 using 1 ; simp_all [faceSide])
    | (convert cycle_faceSide (n := n) (.inr (.inr (i,j,k'))) 2 using 1 ; simp_all [faceSide])
    | (convert cycle_faceSide (n := n) (.inr (.inr (i,j,k'))) 3 using 1 ; simp_all [faceSide])

lemma incident_perpendicular_face (v : Vertex n) (e e' : Edge n)
    (hv : incident v e) (hw : incident v e') (ha : edgeAxis e ≠ edgeAxis e') :
    ∃ f : Face n, cycle f e ≠ 0 ∧ cycle f e' ≠ 0 := by
  have swap : (∃ f : Face n, cycle f e' ≠ 0 ∧ cycle f e ≠ 0) →
      ∃ f : Face n, cycle f e ≠ 0 ∧ cycle f e' ≠ 0 := by
    rintro ⟨f,hf,hf'⟩; exact ⟨f,hf',hf⟩
  rcases e with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals rcases e' with ⟨i',j',k'⟩ | (⟨i',j',k'⟩ | ⟨i',j',k'⟩)
  all_goals first
    | exact (ha rfl).elim
    | exact xy_incident_face _ _ _ _ _ _ v hv hw
    | exact xz_incident_face _ _ _ _ _ _ v hv hw
    | exact yz_incident_face _ _ _ _ _ _ v hv hw
    | exact swap (xy_incident_face _ _ _ _ _ _ v hw hv)
    | exact swap (xz_incident_face _ _ _ _ _ _ v hw hv)
    | exact swap (yz_incident_face _ _ _ _ _ _ v hw hv)

end





noncomputable section

open Classical SimpleGraph

variable {n : ℕ}

lemma square_common_neighbors (f : Face n) (i : Fin 4) (v : Vertex n)
    (h₀ : (boxGraph n).Adj (faceCorner f i) v)
    (h₂ : (boxGraph n).Adj (faceCorner f (i+2)) v) :
    v = faceCorner f (i+1) ∨ v = faceCorner f (i+3) := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;> fin_cases i
  all_goals
    simp [boxGraph,boxProd_adj,pathGraph_adj,faceCorner,Prod.ext_iff,Fin.ext_iff] at h₀ h₂ ⊢
    omega

end





noncomputable section

open Classical

abbrev Direction := Fin 3 × Bool

def directionVector (d : Direction) : Fin 3 → ℤ :=
  fun a => if a = d.1 then (if d.2 then 1 else -1) else 0

def oppositeDirection (d : Direction) : Direction := (d.1,!d.2)

lemma direction_neg (d : Direction) : directionVector (oppositeDirection d) = -directionVector d := by
  rcases d with ⟨a,b⟩
  funext i
  cases b <;> by_cases h : i = a <;> simp [directionVector,oppositeDirection,h]

lemma four_direction_pattern : ∀ d₀ d₁ d₂ d₃ : Direction,
    directionVector d₀ + directionVector d₁ + directionVector d₂ + directionVector d₃ = 0 →
    directionVector d₀ + directionVector d₁ ≠ 0 →
    directionVector d₁ + directionVector d₂ ≠ 0 →
    d₂ = oppositeDirection d₀ ∧ d₃ = oppositeDirection d₁ ∧ d₀.1 ≠ d₁.1 := by
  decide

end





noncomputable section

open Classical SimpleGraph

variable {n : ℕ}

def vertexInt (v : Vertex n) : Fin 3 → ℤ := fun a => (vertexCoord v a).val

lemma vertexInt_injective : Function.Injective (vertexInt (n := n)) := by
  intro v w h
  apply vertexCoord_injective
  funext a
  apply Fin.ext
  exact Int.ofNat_inj.mp (congrFun h a)

lemma head_vertexInt (e : Edge n) :
    vertexInt (head e) = vertexInt (tail e) + directionVector (edgeAxis e,true) := by
  rcases e with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩)
  all_goals
    funext a
    fin_cases a <;> simp [vertexInt,vertexCoord,head,tail,directionVector,edgeAxis]

lemma endpoints_direction (u v : Vertex n) (e : Edge n)
    (h : (u = tail e ∧ v = head e) ∨ (v = tail e ∧ u = head e)) :
    ∃ d : Direction, d.1 = edgeAxis e ∧ vertexInt v - vertexInt u = directionVector d := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨(edgeAxis e,true),rfl,by rw [head_vertexInt]; abel⟩
  · refine ⟨(edgeAxis e,false),rfl,?_⟩
    have ht : directionVector (edgeAxis e,false) = -directionVector (edgeAxis e,true) :=
      direction_neg (edgeAxis e,true)
    rw [head_vertexInt,ht]
    abel

lemma square_consecutive_perpendicular (v : Fin 4 → Vertex n) (e : Fin 4 → Edge n)
    (hv : Function.Injective v)
    (he : ∀ i, (v i = tail (e i) ∧ v (i+1) = head (e i)) ∨
      (v (i+1) = tail (e i) ∧ v i = head (e i))) :
    edgeAxis (e 0) ≠ edgeAxis (e 1) := by
  choose d hd hvec using fun i => endpoints_direction (v i) (v (i+1)) (e i) (he i)
  have hzero : directionVector (d 0) + directionVector (d 1) +
      directionVector (d 2) + directionVector (d 3) = 0 := by
    rw [← hvec 0,← hvec 1,← hvec 2,← hvec 3]
    change (vertexInt (v 1) - vertexInt (v 0)) + (vertexInt (v 2) - vertexInt (v 1)) +
      (vertexInt (v 3) - vertexInt (v 2)) + (vertexInt (v 0) - vertexInt (v 3)) = 0
    abel
  have hz₁ : directionVector (d 0) + directionVector (d 1) ≠ 0 := by
    intro h
    have hh : vertexInt (v 2) = vertexInt (v 0) := by
      have h' : vertexInt (v 2) - vertexInt (v 0) = 0 := by
        calc
          _ = directionVector (d 0) + directionVector (d 1) := by
            rw [← hvec 0,← hvec 1]
            change vertexInt (v 2) - vertexInt (v 0) =
              (vertexInt (v 1) - vertexInt (v 0)) + (vertexInt (v 2) - vertexInt (v 1))
            abel
          _ = 0 := h
      exact sub_eq_zero.mp h'
    exact (by decide : (2 : Fin 4) ≠ 0) (hv (vertexInt_injective hh))
  have hz₂ : directionVector (d 1) + directionVector (d 2) ≠ 0 := by
    intro h
    have hh : vertexInt (v 3) = vertexInt (v 1) := by
      have h' : vertexInt (v 3) - vertexInt (v 1) = 0 := by
        calc
          _ = directionVector (d 1) + directionVector (d 2) := by
            rw [← hvec 1,← hvec 2]
            change vertexInt (v 3) - vertexInt (v 1) =
              (vertexInt (v 2) - vertexInt (v 1)) + (vertexInt (v 3) - vertexInt (v 2))
            abel
          _ = 0 := h
      exact sub_eq_zero.mp h'
    exact (by decide : (3 : Fin 4) ≠ 1) (hv (vertexInt_injective hh))
  simpa only [hd] using (four_direction_pattern _ _ _ _ hzero hz₁ hz₂).2.2

lemma faceCorner_index_injective (f : Face n) : Function.Injective (faceCorner f) := by
  intro i j
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;> fin_cases i <;> fin_cases j
  all_goals simp [faceCorner,castSucc_ne_succ_self,succ_ne_castSucc_self]

lemma incident_faceSide (f : Face n) (i : Fin 4) (v : Vertex n) :
    incident v (faceSide f i) ↔ v = faceCorner f i ∨ v = faceCorner f (i+1) := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;> fin_cases i
  all_goals simp [incident,faceSide,faceCorner,tail,head,ex,ey,ez,or_comm,eq_comm]

lemma square_index_calculation : ∀ i j a b c : Fin 4, i ≠ j →
    (a=i ∨ a=i+1) → (b=i ∨ b=i+1) → (b=j ∨ b=j+1) → (c=j ∨ c=j+1) →
    a ≠ b → b ≠ c → c = a+2 := by decide

lemma face_chain_opposite (f : Face n) (i j : Fin 4) (v₀ v₁ v₂ : Vertex n)
    (hij : i ≠ j) (h01 : v₀ ≠ v₁) (h12 : v₁ ≠ v₂)
    (hi₀ : incident v₀ (faceSide f i)) (hi₁ : incident v₁ (faceSide f i))
    (hj₁ : incident v₁ (faceSide f j)) (hj₂ : incident v₂ (faceSide f j)) :
    ∃ k : Fin 4, v₀ = faceCorner f k ∧ v₂ = faceCorner f (k+2) := by
  have h0 : ∃ a, v₀ = faceCorner f a := by
    rcases (incident_faceSide f i v₀).mp hi₀ with h|h <;> exact ⟨_,h⟩
  have h1 : ∃ a, v₁ = faceCorner f a := by
    rcases (incident_faceSide f i v₁).mp hi₁ with h|h <;> exact ⟨_,h⟩
  have h2 : ∃ a, v₂ = faceCorner f a := by
    rcases (incident_faceSide f j v₂).mp hj₂ with h|h <;> exact ⟨_,h⟩
  obtain ⟨a,rfl⟩ := h0
  obtain ⟨b,rfl⟩ := h1
  obtain ⟨c,rfl⟩ := h2
  have hc : c = a+2 := square_index_calculation i j a b c hij
    (by simpa only [incident_faceSide,(faceCorner_index_injective f).eq_iff] using hi₀)
    (by simpa only [incident_faceSide,(faceCorner_index_injective f).eq_iff] using hi₁)
    (by simpa only [incident_faceSide,(faceCorner_index_injective f).eq_iff] using hj₁)
    (by simpa only [incident_faceSide,(faceCorner_index_injective f).eq_iff] using hj₂)
    (fun h => h01 (congrArg _ h)) (fun h => h12 (congrArg _ h))
  exact ⟨a,rfl,congrArg _ hc⟩

lemma edge_eq_of_endpoints (e f : Edge n)
    (h : (tail e=tail f ∧ head e=head f) ∨ (tail e=head f ∧ head e=tail f)) : e=f := by
  rcases e with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩)
  all_goals rcases f with ⟨x',y',z'⟩ | (⟨x',y',z'⟩ | ⟨x',y',z'⟩)
  all_goals simp [tail,head,Prod.ext_iff,Fin.ext_iff] at h ⊢
  all_goals omega

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.TreeTest

variable {n : ℕ}

def symEdge (e : Edge n) : Sym2 (Vertex n) := s(tail e, head e)

end

end WitnessedSeparation.Grid


section

namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

def anchoredTree (α : Fin 4 → Vertex n) : TreeTest.RootedTree (Vertex n) :=
  AnchoredTree.rooted (boxGraph n) (boxGraph_connected n) α

def anchoredParents (α : Fin 4 → Vertex n) : ParentEdges (anchoredTree α) where
  edge v hv := ((boxGraph_adj_iff v ((anchoredTree α).parent v)).mp
    (AnchoredTree.parent_property (boxGraph n) (boxGraph_connected n) α v hv).1.1).choose
  endpoints v hv := by
    have h := ((boxGraph_adj_iff v ((anchoredTree α).parent v)).mp
      (AnchoredTree.parent_property (boxGraph n) (boxGraph_connected n) α v hv).1.1).choose_spec
    rcases h with ⟨h,h'⟩ | ⟨h',h⟩
    · exact Or.inr ⟨h.symm,h'.symm⟩
    · exact Or.inl ⟨h.symm,h'.symm⟩

end

end WitnessedSeparation.Grid

end


namespace WitnessedSeparation.Grid

noncomputable section

open Classical SimpleGraph

variable {n : ℕ}

lemma endpoints_iff_incident (u v : Vertex n) (e : Edge n) (hne : u ≠ v) :
    ((u = tail e ∧ v = head e) ∨ (v = tail e ∧ u = head e)) ↔
      incident u e ∧ incident v e := by
  simp only [incident]
  constructor
  · rintro (⟨hu,hv⟩|⟨hv,hu⟩)
    · exact ⟨Or.inr hu.symm,Or.inl hv.symm⟩
    · exact ⟨Or.inl hu.symm,Or.inr hv.symm⟩
  · rintro ⟨(hu|hu),(hv|hv)⟩
    · exact (hne (hu.symm.trans hv)).elim
    · exact Or.inr ⟨hv.symm,hu.symm⟩
    · exact Or.inl ⟨hu.symm,hv.symm⟩
    · exact (hne (hu.symm.trans hv)).elim

lemma edge_eq_of_common_incidents (u v : Vertex n) (e f : Edge n) (hne : u ≠ v)
    (heu : incident u e) (hev : incident v e) (hfu : incident u f) (hfv : incident v f) : e=f := by
  have he := (endpoints_iff_incident u v e hne).mpr ⟨heu,hev⟩
  have hf := (endpoints_iff_incident u v f hne).mpr ⟨hfu,hfv⟩
  apply edge_eq_of_endpoints
  rcases he with ⟨he₁,he₂⟩|⟨he₂,he₁⟩
  all_goals rcases hf with ⟨hf₁,hf₂⟩|⟨hf₂,hf₁⟩
  · exact Or.inl ⟨he₁.symm.trans hf₁,he₂.symm.trans hf₂⟩
  · exact Or.inr ⟨he₁.symm.trans hf₁,he₂.symm.trans hf₂⟩
  · exact Or.inr ⟨he₂.symm.trans hf₂,he₁.symm.trans hf₁⟩
  · exact Or.inl ⟨he₂.symm.trans hf₂,he₁.symm.trans hf₁⟩

lemma edge_on_face (f : Face n) (i j : Fin 4) (e : Edge n) (hij : AdjacentIndex i j)
    (hi : incident (faceCorner f i) e) (hj : incident (faceCorner f j) e) : cycle f e ≠ 0 := by
  rcases hij with rfl|rfl
  · have hn : faceCorner f i ≠ faceCorner f (i+1) := by
      intro h
      have hh := faceCorner_index_injective f h
      have hbad : ∀ i : Fin 4, i ≠ i+1 := by decide
      exact hbad i hh
    have he := edge_eq_of_common_incidents _ _ e (faceSide f i) hn hi hj
      ((incident_faceSide f i _).mpr (Or.inl rfl))
      ((incident_faceSide f i _).mpr (Or.inr rfl))
    rw [he]
    exact cycle_faceSide f i
  · have hn : faceCorner f j ≠ faceCorner f (j+1) := by
      intro h
      have hh := faceCorner_index_injective f h
      have hbad : ∀ i : Fin 4, i ≠ i+1 := by decide
      exact hbad j hh
    have he := edge_eq_of_common_incidents _ _ e (faceSide f j) hn hj hi
      ((incident_faceSide f j _).mpr (Or.inl rfl))
      ((incident_faceSide f j _).mpr (Or.inr rfl))
    rw [he]
    exact cycle_faceSide f j

lemma indexed_cycle_incident (v : Fin 4 → Vertex n) (e : Fin 4 → Edge n)
    (he : ∀ i, (v i = tail (e i) ∧ v (i+1) = head (e i)) ∨
      (v (i+1) = tail (e i) ∧ v i = head (e i))) (i : Fin 4) :
    incident (v i) (e i) ∧ incident (v (i+1)) (e i) := by
  rcases he i with ⟨h,h'⟩|⟨h',h⟩
  · exact ⟨Or.inr h.symm,Or.inl h'.symm⟩
  · exact ⟨Or.inl h.symm,Or.inr h'.symm⟩

theorem indexed_fourcycle_is_face (v : Fin 4 → Vertex n) (e : Fin 4 → Edge n)
    (hv : Function.Injective v) (heinj : Function.Injective e)
    (he : ∀ i, (v i = tail (e i) ∧ v (i+1) = head (e i)) ∨
      (v (i+1) = tail (e i) ∧ v i = head (e i))) :
    ∃ f : Face n, ∀ i, cycle f (e i) ≠ 0 := by
  have hi := indexed_cycle_incident v e he
  obtain ⟨f,hf₀,hf₁⟩ := incident_perpendicular_face (v 1) (e 0) (e 1)
    (hi 0).2 (hi 1).1 (square_consecutive_perpendicular v e hv he)
  obtain ⟨i,hi₀⟩ := support_cycle f (e 0) hf₀
  obtain ⟨j,hj₁⟩ := support_cycle f (e 1) hf₁
  have hij : i ≠ j := by
    intro h
    have hh : e 0=e 1 := hi₀.symm.trans (h ▸ hj₁)
    exact (by decide : (0 : Fin 4) ≠ 1) (heinj hh)
  obtain ⟨k,h₀,h₂⟩ := face_chain_opposite f i j (v 0) (v 1) (v 2) hij
    (fun h => (by decide : (0 : Fin 4) ≠ 1) (hv h))
    (fun h => (by decide : (1 : Fin 4) ≠ 2) (hv h))
    (hi₀ ▸ (hi 0).1) (hi₀ ▸ (hi 0).2) (hj₁ ▸ (hi 1).1) (hj₁ ▸ (hi 1).2)
  have hadj (i : Fin 4) : (boxGraph n).Adj (v i) (v (i+1)) :=
    (boxGraph_adj_iff _ _).mpr ⟨e i,he i⟩
  have h₁ : v 1=faceCorner f (k+1) ∨ v 1=faceCorner f (k+3) :=
    square_common_neighbors f k (v 1) (h₀ ▸ hadj 0) (h₂ ▸ (hadj 1).symm)
  have h₃ : v 3=faceCorner f (k+1) ∨ v 3=faceCorner f (k+3) :=
    square_common_neighbors f k (v 3) (h₀ ▸ (hadj 3).symm) (h₂ ▸ hadj 2)
  have hv₁₃ : v 1 ≠ v 3 := fun h => (by decide : (1 : Fin 4) ≠ 3) (hv h)
  have sufficient (J : Fin 4 → Fin 4) (hJ : ∀ i, v i = faceCorner f (J i))
      (hA : ∀ i, AdjacentIndex (J i) (J (i+1))) : ∀ i, cycle f (e i) ≠ 0 := by
    intro i
    exact edge_on_face f _ _ (e i) (hA i) (hJ i ▸ (hi i).1) (hJ (i+1) ▸ (hi i).2)
  refine ⟨f,?_⟩
  rcases h₁ with h₁|h₁
  all_goals rcases h₃ with h₃|h₃
  · exact (hv₁₃ (h₁.trans h₃.symm)).elim
  · refine sufficient ![k,k+1,k+2,k+3] ?_ ?_
    · intro i; fin_cases i <;> assumption
    · have h : ∀ k i : Fin 4, AdjacentIndex (![k,k+1,k+2,k+3] i)
          (![k,k+1,k+2,k+3] (i+1)) := by unfold AdjacentIndex; decide
      exact h k
  · refine sufficient ![k,k+3,k+2,k+1] ?_ ?_
    · intro i; fin_cases i <;> assumption
    · have h : ∀ k i : Fin 4, AdjacentIndex (![k,k+3,k+2,k+1] i)
          (![k,k+3,k+2,k+1] (i+1)) := by unfold AdjacentIndex; decide
      exact h k
  · exact (hv₁₃ (h₁.trans h₃.symm)).elim

end





noncomputable section

open Classical Support

variable {n : ℕ} {b : Vertex n → Scalar}

structure CycleFrame (n : ℕ) where
  vertex : Fin 4 → Vertex n
  edge : Fin 4 → Edge n
  vertex_injective : Function.Injective vertex
  edge_injective : Function.Injective edge
  endpoints : ∀ i, (vertex i = tail (edge i) ∧ vertex (i+1) = head (edge i)) ∨
    (vertex (i+1) = tail (edge i) ∧ vertex i = head (edge i))

namespace CycleFrame

variable (C : CycleFrame n)

def face : Face n := (indexed_fourcycle_is_face C.vertex C.edge C.vertex_injective C.edge_injective C.endpoints).choose

lemma on_face (i : Fin 4) : cycle C.face (C.edge i) ≠ 0 :=
  (indexed_fourcycle_is_face C.vertex C.edge C.vertex_injective C.edge_injective C.endpoints).choose_spec i

def joint (i j : Fin 4) : Vertex n := if j=i+1 then C.vertex j else C.vertex i

def Across (i j : Fin 4) (s : LocalGroup (C.edge i)) (t : LocalGroup (C.edge j)) : Prop :=
  ∃ hi : incident (C.joint i j) (C.edge i), ∃ hj : incident (C.joint i j) (C.edge j),
    ∃ c : Configuration b (C.joint i j), c.state ⟨C.edge i,hi⟩ = s ∧ c.state ⟨C.edge j,hj⟩ = t

def Match (i j : Fin 4) (s : LocalGroup (C.edge i)) (t : LocalGroup (C.edge j)) : Prop :=
  if AdjacentIndex i j then C.Across (b := b) i j s t else
    ∃ q : LocalGroup (C.edge (i+1)), C.Across (b := b) i (i+1) s q ∧ C.Across (b := b) j (i+1) t q

end CycleFrame

def standardFrame (f : Face n) : CycleFrame n where
  vertex := faceCorner f
  edge := faceSide f
  vertex_injective := faceCorner_index_injective f
  edge_injective := faceSide_injective_index f
  endpoints i := by
    have hi := (incident_faceSide f i (faceCorner f i)).mpr (Or.inl rfl)
    have hj := (incident_faceSide f i (faceCorner f (i+1))).mpr (Or.inr rfl)
    have hne : faceCorner f i ≠ faceCorner f (i+1) := by
      intro hh
      have he := faceCorner_index_injective f hh
      have hbad : ∀ i : Fin 4, i ≠ i+1 := by decide
      exact hbad i he
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact (hne (hi.symm.trans hj)).elim
    · exact Or.inr ⟨hj.symm,hi.symm⟩
    · exact Or.inl ⟨hi.symm,hj.symm⟩
    · exact (hne (hi.symm.trans hj)).elim

end

end WitnessedSeparation.Grid

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_CycleTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

def frameCode (b : Vertex n → Scalar) (C : CycleFrame n) : HF (Atom b) :=
  Hereditary.pair (tupleCode (List.ofFn (vertexCode b ∘ C.vertex)))
    (tupleCode (List.ofFn (edgeCode b ∘ C.edge)))

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

@[simp] lemma next4_eq_add (i : Fin 4) : next4 i = i+1 := rfl

@[simp] lemma prev4_eq_add (i : Fin 4) : prev4 i = i+3 := rfl

end QuotedGrid

end

end WitnessedSeparation.Grid

end


section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

namespace SourceProgram

def cost : Polynomial ℕ :=
  Polynomial.X^2*(Polynomial.X+1) +
  (QuotedTerm.tripleDomain (QuotedTerm.vertexBlocks : QuotedTerm 0)).code.traceBound.comp
    (Polynomial.X+1) + Polynomial.X+2

def polynomial : Polynomial ℝ := cost.map (Nat.castRingHom ℝ)

end SourceProgram

end

end WitnessedChoice.BGS

namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

structure GridResources (p : Polynomial ℝ) (b : Vertex n → Scalar) : Prop where
  basic : Fintype.card (Atom b)+2 ≤ resource p (Fintype.card (Atom b))
  time : Fintype.card (BFS.Item (Vertex n) (Fintype.card (Atom b))) ≤ resource p (Fintype.card (Atom b))
  space : (TC (ofFinset (Finset.univ.image (distanceCode (vertexCode b))))).card ≤
    resource p (Fintype.card (Atom b))

end

end WitnessedSeparation.Grid

end


namespace WitnessedSeparation.Grid





noncomputable section

open Classical WitnessedChoice WitnessedChoice.TreeTest

variable {n : ℕ}

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

def cut (h : Edge n) : SimpleGraph (Vertex n) := edgeGraph (P.treeEdges.erase h)

def cutIndicator (h : Edge n) (v : Vertex n) : Scalar :=
  if (P.cut h).Reachable (head h) v then 1 else 0

end ParentEdges

end

end WitnessedSeparation.Grid


section

namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

def distancesCode (b : Vertex n → Scalar) (G : SimpleGraph (Vertex n)) : HF (Atom b) :=
  ofFinset ((BFS.closure G (Fintype.card (Atom b))).image (distanceCode (vertexCode b)))

def connTableCode (b : Vertex n → Scalar) (T : Finset (Edge n)) : HF (Atom b) :=
  ofFinset (T.image (fun h => Hereditary.pair (edgeCode b h) (distancesCode b (edgeGraph (T.erase h)))))

end

end WitnessedSeparation.Grid

end


namespace WitnessedSeparation.Grid





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary QuotedTerm

variable {n : ℕ} {b : Vertex n → Scalar}

def Traverses (T : Finset (Edge n)) (e : Edge n) (u v : Vertex n)
    (h : Edge n) (a c : Vertex n) : Prop :=
  (h=e ∧ a=u ∧ c=v) ∨ h ∈ T ∧
    ((a=tail h ∧ c=head h) ∨ (c=tail h ∧ a=head h)) ∧
    ¬(edgeGraph (T.erase h)).Reachable v u ∧
    (edgeGraph (T.erase h)).Reachable v a ∧
    (edgeGraph (T.erase h)).Reachable u c

def traversalCode (b : Vertex n → Scalar) (T : Finset (Edge n)) (e : Edge n) (u v : Vertex n) : HF (Atom b) :=
  ofFinset ((Finset.univ.filter fun hac : Edge n × Vertex n × Vertex n =>
    Traverses T e u v hac.1 hac.2.1 hac.2.2).image fun hac =>
      HFTriple (edgeCode b hac.1) (vertexCode b hac.2.1) (vertexCode b hac.2.2))

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary QuotedTerm

variable {n : ℕ} {b : Vertex n → Scalar}

def originVertex : Vertex n := (0,0,0)

end





end WitnessedSeparation.Grid

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_TreeCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

def edgeActionRelation (g : BoxGroup n) : Relation (Atom b) :=
  Finset.univ.image fun r : Σ e : Edge n, LocalGroup e =>
    ((Sum.inl r : Atom b),actionPerm g (.inl r))

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

def configActionRelation (g : BoxGroup n) : Relation (Atom b) :=
  Finset.univ.image fun r : Σ v : Vertex n, Configuration b v =>
    ((Sum.inr r : Atom b),actionPerm g (.inr r))

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary

variable {n : ℕ}

def oppositeVertex : Vertex n := (Fin.last n,Fin.last n,Fin.last n)

end





noncomputable section

open Classical WitnessedChoice

variable {n : ℕ}

abbrev VertexKey := Lex (Fin 4 → ℕ)

def vertexKey (α : Fin 4 → Vertex n) := AnchoredTree.key (boxGraph n) α

def lowEnd (α : Fin 4 → Vertex n) (e : Edge n) : Vertex n :=
  if vertexKey α (tail e) < vertexKey α (head e) then tail e else head e

def highEnd (α : Fin 4 → Vertex n) (e : Edge n) : Vertex n :=
  if vertexKey α (tail e) < vertexKey α (head e) then head e else tail e

def edgeKey (α : Fin 4 → Vertex n) (e : Edge n) : Lex (VertexKey × VertexKey) :=
  toLex (vertexKey α (lowEnd α e),vertexKey α (highEnd α e))

def leastEdges (α : Fin 4 → Vertex n) (D : Finset (Edge n)) : Finset (Edge n) :=
  D.filter (fun e => ∀ f ∈ D, ¬edgeKey α f < edgeKey α e)

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

def missingEdge (x : Finset (Σ e : Edge n, LocalGroup e)) (e : Edge n) : Prop :=
  ∀ r ∈ x, r.1 ≠ e

def remainingEdges (T : Finset (Edge n)) (x : Finset (Σ e : Edge n, LocalGroup e)) : Finset (Edge n) :=
  (Finset.univ \ T).filter (missingEdge x)

end





noncomputable section

open Classical WitnessedChoice

variable {n : ℕ}

def gridCandidates (α : Fin 4 → Vertex n) (T : Finset (Edge n))
    (x : Finset (Σ e : Edge n, LocalGroup e)) : Finset (Σ e : Edge n, LocalGroup e) :=
  Finset.univ.filter fun r => r.1 ∈ leastEdges α (remainingEdges T x) ∧ AcceptsFaces x r.1 r.2

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.TreeTest RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

def fundamentalPool (N : Finset (Edge n)) : Finset (Relation (Atom b)) :=
  (N.product Finset.univ).image fun ea => graph (actionPerm (⟨0,P.flow ea.1 ea.2⟩ : BoxGroup n))

end ParentEdges

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.TreeTest

variable {n : ℕ} {b : Vertex n → Scalar}

def edgeState (x : Finset (Σ e : Edge n, LocalGroup e)) : Finset (Atom b) := x.image Sum.inl

@[simp] lemma edgeState_empty : edgeState (b := b) ∅ = ∅ := Finset.image_empty _

@[simp] lemma edgeState_insert (r : Σ e : Edge n, LocalGroup e) (x) :
    edgeState (b := b) (insert r x) = insert (.inl r) (edgeState x) := Finset.image_insert _ _ _

end





end WitnessedSeparation.Grid

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_ChoiceSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice.TreeTest

variable {n : ℕ} {b : Vertex n → Scalar}

abbrev ConfigAtom (b : Vertex n → Scalar) := Σ v : Vertex n, Configuration b v

def configBlock (b : Vertex n → Scalar) (v : Vertex n) : Finset (ConfigAtom b) :=
  Finset.univ.image (Sigma.mk v)

lemma mem_configBlock (v : Vertex n) (a : ConfigAtom b) :
    a ∈ configBlock b v ↔ a.1 = v := by
  constructor
  · rintro ha
    obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp ha
    rfl
  · intro h
    rcases a with ⟨w,a⟩
    dsimp at h
    subst w
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩

def atEdge (a : ConfigAtom b) (e : Edge n) (h : incident a.1 e) : LocalGroup e := a.2.state ⟨e,h⟩

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

def allowedConfig (x : Finset (Σ e : Edge n, LocalGroup e)) (a : ConfigAtom b) : Prop :=
  ∀ e, e ∉ P.treeEdges → ∀ h : incident a.1 e, Sigma.mk e (atEdge a e h) ∈ x

def configCompatibility (a c : ConfigAtom b) : Prop :=
  ∀ e ∈ P.treeEdges, ∀ ha : incident a.1 e, ∀ hc : incident c.1 e,
    atEdge a e ha = atEdge c e hc

def testProblem (x : Finset (Σ e : Edge n, LocalGroup e)) : Problem (Vertex n) (ConfigAtom b) where
  tree := T
  configs := Finset.univ
  block := configBlock b
  block_subset _ _ _ := Finset.mem_univ _
  block_unique v w a hv hw := (mem_configBlock v a).mp hv |>.symm.trans ((mem_configBlock w a).mp hw)
  allowed := P.allowedConfig x
  compatible _ _ := P.configCompatibility
  compatible_symm _ _ _ _ h e he ha hc := (h e he hc ha).symm

end ParentEdges

end





end WitnessedSeparation.Grid


end OAI
end


