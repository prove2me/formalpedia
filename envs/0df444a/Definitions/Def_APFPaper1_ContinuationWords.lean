-- Prove2me | Definitions.Def_APFPaper1_ContinuationWords
-- name    : APFPaper1_ContinuationWords
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:24:30.569479+00:00
-- url     : https://prove2.me/theorems/50313061-eff3-4635-90a5-4899d81bcd34
-- title:
--   Continuations as typed words with execution and a whole-word budget
-- statement:
--   A continuation is a finite word of typed fragments. Relational execution connects its start state to an end state, and membership in Cont also requires the calibrated resource bill of the **whole word** to fit the capacity of its **starting context**.
--
--   The bundle defines word composition, execution, the budget predicate, prefix comparison and identity naming, with the elementary word and execution lemmas proved. Fragment types, execution steps, resource accounting, calibration and capacity are explicit data.
--
--   **Scope.** This is the November 12 author-approved representation of the continuation vocabulary. Null-word admissibility still requires the named zero-bill condition; prefix restriction requires the named prefix-monotonicity condition. C4 and recovery or coarse-graining transport are not encoded here. Nonnegative calibration alone does not establish monotonicity.
--
--   **Sources.** Paper 1 Supplement v9.28, lines 1224–1241, 2197–2214 and 3188–3230; RULING_Cont_Correction_2026-11-12.md.
-- source:
--   Sib v15, Definitions/Def_APFPaper1_ContinuationWords.lean (SHA-256 d8b3955914d1a23d0036257258188b72da821477d15fa8c2eaf78620e4c1b9c8); Paper 1 Supplement v9.28:1224–1241,2197–2214,3188–3230; author ruling 2026-11-12.

/-
APF Foundation Ledger — definition node. DRAFT for author and cold review. Not gated, not released, not uploaded.
name: APFPaper1_ContinuationWords
title: Continuation words, execution, and the whole-word budgeted continuation class
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1224-1241 (finite admissible continuation, clauses C1-C4, reach remark),
  2197-2214 (resource load of a protocol, context calibration), 3188-3202 (continuation word, typed process
  fragments), 3205-3230 (process category, partial word product), 3301 (hypothesis W-her and the
  fragment-monotone budget remark). Author direction 4b of 2026-10-04 (FOUNDATION_INPUTS,
  definition_corrections_20261004.Cont). Author ruling of 2026-11-12: whole-word budget; a word that changes
  context is tested against the budget of the context it starts in.
statement: A word is a finite composable sequence of typed fragments, written in execution order. A word
  executes from a raw possibility x to a raw possibility y when the single-fragment step relation composes along
  it; the empty word executes from x to x only. Cont g x is the set of words w starting in context g such that
  w executes from x to some y and the calibrated resource of the whole word w is at most the capacity of g.
  ContHereditary is the same with the budget tested on every initial segment. PrefixMonotone says the calibrated
  resource of an initial segment never exceeds that of the whole. The name of a word is the word.
supplied data, nothing assumed about it: the fragments and their typing; the step relation on single fragments
  (not assumed total, single-valued or nontrivial, Supplement 1240); the resource of every word starting in a
  context; the calibration and the capacity of each context.
fidelity exposure: the word semantics is a representation of the Supplement's continuation definition and needs
  source review (FOUNDATION_INPUTS, source_vocabulary_exposure). Clause C4 (coarse-graining) is not encoded. The
  Supplement's "recovery or coarse-graining maps" between matching contexts (3211, 3221-3226) are not represented:
  composability here is equality of the output and input contexts.
no structure, no class, no Prop-valued field: Word is an inductive type of data; everything else is a def or a
  support lemma of ordinary mathematics (CostLedger precedent: lemmas about a definition live in its module).
-/
import Mathlib.Data.NNReal.Basic

set_option autoImplicit false
namespace APFPaper1.Continuation

universe uC uF uX uR

/-- A finite composable sequence of typed fragments, in execution order (first fragment applied first).
`Frag g h` is the type of fragments with input context `g` and output context `h`. -/
inductive Word {Context : Type uC} (Frag : Context → Context → Type uF) :
    Context → Context → Type (max uC uF)
  | nil (g : Context) : Word Frag g g
  | cons {g h k : Context} (f : Frag g h) (w : Word Frag h k) : Word Frag g k

namespace Word
variable {Context : Type uC} {Frag : Context → Context → Type uF}

/-- Concatenation in execution order: `w.append u` performs `w` and then `u`. -/
def append : {g h k : Context} → Word Frag g h → Word Frag h k → Word Frag g k
  | _, _, _, nil _, u => u
  | _, _, _, cons f w, u => cons f (append w u)

/-- The word consisting of one fragment. -/
def single {g h : Context} (f : Frag g h) : Word Frag g h := cons f (nil h)

end Word

/-- A word starting in context `g`, together with the context it ends in. This is the process type of
context `g`. -/
abbrev WordFrom {Context : Type uC} (Frag : Context → Context → Type uF) (g : Context) :
    Type (max uC uF) :=
  Σ h : Context, Word Frag g h

section
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

/-- The empty word of context `g`, as a process of `g`. -/
def nullWord (g : Context) : WordFrom Frag g := ⟨g, Word.nil g⟩

/-- `v` is an initial segment of `w`: `w` is `v` followed by some word. -/
def IsPrefix {g : Context} (v w : WordFrom Frag g) : Prop :=
  ∃ u : Word Frag v.1 w.1, w.2 = v.2.append u

/-- Execution. The step relation is given on single fragments; a word executes from `x` to `z` when the
steps compose along it. The empty word executes from `x` to `x` only. -/
def Executes (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) :
    {g h : Context} → Word Frag g h → Raw g → Raw h → Prop
  | _, _, Word.nil _, x, z => x = z
  | _, _, Word.cons (g := g) (h := h) f w, x, z => ∃ y : Raw h, step g h f x y ∧ Executes step w y z

/-- The whole-word budgeted continuation class (author ruling 2026-11-12). A word of context `g` belongs to
`Cont g x` when it executes from `x` to some raw possibility and its calibrated whole resource is at most the
capacity of `g`, the context it starts in. -/
def Cont (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (g : Context) (x : Raw g) (w : WordFrom Frag g) : Prop :=
  (∃ y : Raw w.1, Executes step w.2 x y) ∧ calibration g (resource g w) ≤ C g

/-- The hereditary variant: the budget is tested on every initial segment. Not the class of record; it is
defined so that its relation to `Cont` can be stated. -/
def ContHereditary (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (g : Context) (x : Raw g) (w : WordFrom Frag g) : Prop :=
  (∃ y : Raw w.1, Executes step w.2 x y) ∧
    ∀ v : WordFrom Frag g, IsPrefix v w → calibration g (resource g v) ≤ C g

/-- Prefix-monotone calibrated resource: an initial segment never has a larger calibrated resource than the
whole word. A property the supplied resource and calibration may or may not have; the Supplement (3301) calls
fragment-monotone budgets natural and falsifiable, hypothesized and not derived. -/
def PrefixMonotone (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) : Prop :=
  ∀ (g : Context) (v w : WordFrom Frag g), IsPrefix v w →
    calibration g (resource g v) ≤ calibration g (resource g w)

/-- Names are words: the process named by a word is that word. -/
def names {g h : Context} (word : Word Frag g h) (p : WordFrom Frag g) : Prop :=
  p = ⟨h, word⟩

/-! ### Words and execution: ordinary mathematics (support lemmas, not nodes) -/

theorem Word.append_nil {g h : Context} (w : Word Frag g h) : w.append (Word.nil h) = w := by
  induction w with
  | nil g => rfl
  | cons f w ih => simp only [Word.append, ih]

theorem Word.append_assoc {g h k l : Context} (w : Word Frag g h) (u : Word Frag h k)
    (t : Word Frag k l) : (w.append u).append t = w.append (u.append t) := by
  induction w with
  | nil g => rfl
  | cons f w ih => simp only [Word.append, ih]

/-- The empty word executes from `x` to `x` only. -/
theorem executes_nil (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) (g : Context)
    (x z : Raw g) : Executes step (Word.nil g) x z ↔ x = z := Iff.rfl

theorem executes_cons (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) {g h k : Context}
    (f : Frag g h) (w : Word Frag h k) (x : Raw g) (z : Raw k) :
    Executes step (Word.cons f w) x z ↔ ∃ y : Raw h, step g h f x y ∧ Executes step w y z := Iff.rfl

/-- Execution composes along concatenation, and only so. -/
theorem executes_append (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) {g h k : Context}
    (w : Word Frag g h) (u : Word Frag h k) (x : Raw g) (z : Raw k) :
    Executes step (w.append u) x z ↔ ∃ y : Raw h, Executes step w x y ∧ Executes step u y z := by
  induction w with
  | nil g =>
    constructor
    · intro hu
      exact ⟨x, rfl, hu⟩
    · intro ⟨y, hxy, hu⟩
      cases hxy
      exact hu
  | cons f w ih =>
    constructor
    · intro ⟨y, hstep, hrest⟩
      obtain ⟨y', hw, hu⟩ := (ih u y).mp hrest
      exact ⟨y', ⟨y, hstep, hw⟩, hu⟩
    · intro ⟨y', ⟨y, hstep, hw⟩, hu⟩
      exact ⟨y, hstep, (ih u y).mpr ⟨y', hw, hu⟩⟩

theorem isPrefix_refl {g : Context} (w : WordFrom Frag g) : IsPrefix w w :=
  ⟨Word.nil w.1, (Word.append_nil w.2).symm⟩

/-- An initial segment of a word that executes from `x` executes from `x`. -/
theorem isPrefix_executes (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) {g : Context}
    (v w : WordFrom Frag g) (hpre : IsPrefix v w) (x : Raw g)
    (hw : ∃ z : Raw w.1, Executes step w.2 x z) : ∃ y : Raw v.1, Executes step v.2 x y := by
  obtain ⟨u, hu⟩ := hpre
  obtain ⟨z, hz⟩ := hw
  rw [hu] at hz
  obtain ⟨y, hv, _⟩ := (executes_append step v.2 u x z).mp hz
  exact ⟨y, hv⟩

end
end APFPaper1.Continuation


