-- Prove2me | Definitions.Def_OAIFAE002
-- name    : OAIFAE002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-24T19:27:29.678049+00:00
-- url     : https://prove2.me/theorems/6eccfeb0-3254-4d42-bb1f-1b23cd5c88c5
-- title:
--   Definitions bundle OAIFAE002 of the split of OpenAI, Finite algebraic envelopes and the Boone–Higman conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.FiniteAlgebraicEnvelopes.main`, carved from OpenAI's openai/math development (OpenAI, *Finite algebraic envelopes and the Boone–Higman conjecture*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 557 declarations of OpenAI's Lean: 34 definitions, 8 inductive types or structures, 1 instance and 514 theorems. The definitions and types are `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Build.bases`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Build.tables`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Canonical.pick`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Search.compute`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Search.output`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Search.table`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Selectors.Old`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.finiteClass`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.finiteValue`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instDecidableEqXSigma_3`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instLinearOrderSectorSigmaProdBoolState`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.evaluate`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.iteration`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.tableNormal`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Cleanup.Step`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Compiled.MachineRel`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Compiled.Step`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Compiled.cleanEntry`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.commandMap`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Path.Context`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Path.terminalLeave`, `OAI.FiniteAlgebraicEnvelopes.Compiler.RawRuns.Action.mapKeep`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Simulator.Rejects`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Simulator.finalCells`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Simulator.haltSector`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Simulator.runSector`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Surface.QuotaStep`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Surface.RawStep`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Surface.listGrade`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Surface.skeletonGrade`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Validator.Anchors`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Validator.Body`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Validator.Entry`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Validator.Extended.Step`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Validator.Left`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Validator.Ready`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Validator.Tail`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Validator.skeleton`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Word.ComputesAt`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Word.Reduce` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/BooneHigman, lean/OAI/Computability/FiniteCompiler, in whole or in part: `Control`, `Effectivity`, `MonoidAlgebras`, `Normalization`, `PartialAffine`, `Paths`, `Quotients`, `Rewriting`, `Selectors`, `SelfReference`, `Simulator`, `Surface`, `UniformControl`, `UniformMachines`, `UniformPaths`, `Validator`.
--
--   **Imports.** It imports the published bundle `Def_BooneHigman`; the bundles `OAIFAE000` and `OAIFAE001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIFAE004`.
-- source:
--   OpenAI, Finite algebraic envelopes and the Boone–Higman conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/BooneHigman, lean/OAI/Computability/FiniteCompiler at commit adc7f12

import Mathlib
import Definitions.Def_BooneHigman
import Definitions.Def_OAIFAE000
import Definitions.Def_OAIFAE001

section
-- module Solutions.OAIFAE.Validator
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.fixedFintype _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.fixedStepDecidable _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.instPrimcodableSector _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableBaseOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableTagOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite tape validation, scan reversal, and bounded cleanup.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Validator

section
open Relation

theorem step_deterministic {S Γ : Type*} (blank : Γ) :
    Relator.RightUnique (@Step S Γ blank) := by
  intro a b c hab hac
  cases hab <;> cases hac <;> rfl

/-- Validator reverse determinism, not asserted for machine phases. -/
theorem step_leftUnique {S Γ : Type*} (blank : Γ) :
    Relator.LeftUnique (@Step S Γ blank) := by
  intro a b c hac hbc
  cases hac <;> cases hbc <;> rfl

/-- An entry has clean D immediately right of its I head. -/
def Entry {S Γ : Type*} (blank : Γ) (s : Sector S Γ) : Prop :=
  s.head = .initial ∧ ∃ r, s.right = cell blank .cutD :: r

theorem entry_no_predecessor {S Γ : Type*} (blank : Γ) {a b : Sector S Γ}
    (hb : Entry blank b) : ¬ Step blank a b := by
  rintro h
  rcases hb with ⟨hh, r, hr⟩
  cases h <;> simp_all [cell]

/-- Ordered cells and both flags are preserved by every internal validator step. -/
def skeleton {S Γ : Type*} (s : Sector S Γ) :
    List (Cell S Γ) × Bool × Bool :=
  (s.left.reverse ++ s.right, s.leftBoundary, s.rightBoundary)

theorem step_skeleton {S Γ : Type*} (blank : Γ) {a b : Sector S Γ}
    (hab : Step blank a b) : skeleton a = skeleton b := by
  cases hab <;> simp [skeleton, List.reverse_cons, List.append_assoc]

open Relation
variable {S Γ : Type*} (blank : Γ)

/-- Exact clean-anchor language; dirty tags are not accepted. -/
inductive Anchors : List (Cell S Γ) → Prop
  | nil : Anchors []
  | cons (a : S) {l} : Anchors l → Anchors (cell blank (.anchor a) :: l)

/-- The right suffix tested from N: clean workspace, D, then clean anchors. -/
inductive Tail : List (Cell S Γ) → Prop
  | cut {l} : Anchors blank l → Tail (cell blank .cutD :: l)
  | work {l} : Tail l → Tail (cell blank .workspace :: l)

/-- The right suffix tested from J': anchors, C, workspace, D, anchors. -/
inductive Body : List (Cell S Γ) → Prop
  | cut {l} : Tail blank l → Body (cell blank .cutC :: l)
  | anchor (a : S) {l} : Body l → Body (cell blank (.anchor a) :: l)

/-- The reversed left side tested from I: workspace, C, then anchors. -/
inductive Left : List (Cell S Γ) → Prop
  | cut {l} : Anchors blank l → Left (cell blank .cutC :: l)
  | work {l} : Left l → Left (cell blank .workspace :: l)

/-- Necessary future checks at each phase. Already-scanned cells need not be
    constrained: backwards propagation recovers exactly the checks made. -/
def Ready (s : Sector S Γ) : Prop :=
  match s.head with
  | .initial => s.leftBoundary = true ∧ s.rightBoundary = true ∧
      Left blank s.left ∧ Tail blank s.right
  | .left => s.leftBoundary = true ∧ s.rightBoundary = true ∧
      Anchors blank s.left ∧ Body blank s.right
  | .right => s.rightBoundary = true ∧ Body blank s.right
  | .workspace => s.rightBoundary = true ∧ Tail blank s.right
  | .suffix => s.rightBoundary = true ∧ Anchors blank s.right
  | .start => True

theorem ready_predecessor {a b : Sector S Γ} (h : Step blank a b) :
    Ready blank b → Ready blank a := by
  cases h with
  | initial_workspace l r lb rb =>
      rintro ⟨hl, hr, hleft, hright⟩
      refine ⟨hl, hr, .work hleft, ?_⟩
      cases hright with | work h => exact h
  | initial_cut l r lb rb =>
      rintro ⟨hl, hr, hleft, hright⟩
      refine ⟨hl, hr, .cut hleft, ?_⟩
      cases hright with | cut h => exact h
  | left_anchor c l r lb rb =>
      rintro ⟨hl, hr, hleft, hright⟩
      refine ⟨hl, hr, .cons c hleft, ?_⟩
      cases hright with | anchor _ h => exact h
  | left_boundary r rb =>
      rintro ⟨hr, hright⟩
      exact ⟨rfl, hr, .nil, hright⟩
  | right_anchor c l r lb rb =>
      rintro ⟨hr, hright⟩
      exact ⟨hr, .anchor c hright⟩
  | right_cut l r lb rb =>
      rintro ⟨hr, hright⟩
      exact ⟨hr, .cut hright⟩
  | workspace l r lb rb =>
      rintro ⟨hr, hright⟩
      exact ⟨hr, .work hright⟩
  | workspace_cut l r lb rb =>
      rintro ⟨hr, hright⟩
      exact ⟨hr, .cut hright⟩
  | suffix_anchor c l r lb rb =>
      rintro ⟨hr, hright⟩
      exact ⟨hr, .cons c hright⟩
  | suffix_boundary l lb =>
      intro _
      exact ⟨rfl, .nil⟩

theorem reaches_ready {a b : Sector S Γ} (h : ReflTransGen (Step blank) a b) :
    Ready blank b → Ready blank a := by
  induction h with
  | refl => exact id
  | tail _ h ih => exact fun hb => ih (ready_predecessor blank h hb)

theorem anchors_iff (l : List (Cell S Γ)) :
    Anchors blank l ↔ ∃ x : List S, l = x.map (fun a => cell blank (.anchor a)) := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨[], rfl⟩
    | cons a _ ih =>
        obtain ⟨x, rfl⟩ := ih
        exact ⟨a :: x, rfl⟩
  · rintro ⟨x, rfl⟩
    induction x with
    | nil => exact .nil
    | cons a x ih => exact .cons a ih

theorem left_iff (l : List (Cell S Γ)) :
    Left blank l ↔ ∃ (s : ℕ) (x : List S),
      l = List.replicate s (cell blank .workspace) ++
        cell blank .cutC :: x.map (fun a => cell blank (.anchor a)) := by
  constructor
  · intro h
    induction h with
    | cut h =>
        obtain ⟨x, rfl⟩ := (anchors_iff blank _).mp h
        exact ⟨0, x, rfl⟩
    | work _ ih =>
        obtain ⟨s, x, rfl⟩ := ih
        exact ⟨s+1, x, by simp [List.replicate_succ]⟩
  · rintro ⟨s, x, rfl⟩
    induction s with
    | zero => exact .cut ((anchors_iff blank _).mpr ⟨x, rfl⟩)
    | succ s ih => simpa [List.replicate_succ] using Left.work ih

/-- Every entry which reaches handoff has the FULL clean form in the manuscript:
    both boundaries, all clean tags, anchors on each side, and one quota.
    In particular this is not a cleanliness assumption on the input. -/
theorem passing_entry {a b : Sector S Γ} (ha : Entry blank a)
    (hab : ReflTransGen (Step blank) a b) (hb : b.head = .start) :
    ∃ (x y : List S) (s : ℕ), a =
      ⟨.initial, List.replicate s (cell blank .workspace) ++
        cell blank .cutC :: (x.map (fun c => cell blank (.anchor c))).reverse,
        cell blank .cutD :: y.map (fun c => cell blank (.anchor c)), true, true⟩ := by
  have hready : Ready blank a := reaches_ready blank hab (by simp [Ready, hb])
  rcases a with ⟨head, l, r, lb, rb⟩
  rcases ha with ⟨rfl, r', rfl⟩
  rcases hready with ⟨rfl, rfl, hl, hr⟩
  obtain ⟨s, x, rfl⟩ := (left_iff blank _).mp hl
  cases hr with
  | cut h =>
      obtain ⟨y, rfl⟩ := (anchors_iff blank _).mp h
      exact ⟨x.reverse, y, s, by simp⟩

end

open Relation
variable {S Γ : Type*} (blank : Γ)

theorem initial_workspaces (s : ℕ) (l r : List (Cell S Γ)) (lb rb : Bool) :
    ReflTransGen (Step blank)
      ⟨.initial, List.replicate s (cell blank .workspace) ++ l, r, lb, rb⟩
      ⟨.initial, l, List.replicate s (cell blank .workspace) ++ r, lb, rb⟩ := by
  induction s generalizing r with
  | zero => exact .refl
  | succ s ih =>
      simp only [List.replicate_succ, List.cons_append]
      refine (ReflTransGen.single (Step.initial_workspace _ _ _ _)).trans ?_
      convert ih (cell blank .workspace :: r) using 1
      simp only [← List.cons_append, ← List.replicate_succ, List.replicate_succ']
      simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem left_anchors (x : List S) (l r : List (Cell S Γ)) (lb rb : Bool) :
    ReflTransGen (Step blank)
      ⟨.left, x.map (fun a => cell blank (.anchor a)) ++ l, r, lb, rb⟩
      ⟨.left, l, (x.map (fun a => cell blank (.anchor a))).reverse ++ r, lb, rb⟩ := by
  induction x generalizing r with
  | nil => exact .refl
  | cons a x ih =>
      refine (ReflTransGen.single (Step.left_anchor a _ _ _ _)).trans ?_
      simpa [List.reverse_cons, List.append_assoc] using
        ih (cell blank (.anchor a) :: r)

theorem right_anchors (x : List S) (l r : List (Cell S Γ)) (lb rb : Bool) :
    ReflTransGen (Step blank)
      ⟨.right, l, x.map (fun a => cell blank (.anchor a)) ++ r, lb, rb⟩
      ⟨.right, (x.map (fun a => cell blank (.anchor a))).reverse ++ l, r, lb, rb⟩ := by
  induction x generalizing l with
  | nil => exact .refl
  | cons a x ih =>
      refine (ReflTransGen.single (Step.right_anchor a _ _ _ _)).trans ?_
      simpa [List.reverse_cons, List.append_assoc] using
        ih (cell blank (.anchor a) :: l)

theorem workspace_many (s : ℕ) (l r : List (Cell S Γ)) (lb rb : Bool) :
    ReflTransGen (Step blank)
      ⟨.workspace, l, List.replicate s (cell blank .workspace) ++ r, lb, rb⟩
      ⟨.workspace, List.replicate s (cell blank .workspace) ++ l, r, lb, rb⟩ := by
  induction s generalizing l with
  | zero => exact .refl
  | succ s ih =>
      simp only [List.replicate_succ, List.cons_append]
      refine (ReflTransGen.single (Step.workspace _ _ _ _)).trans ?_
      convert ih (cell blank .workspace :: l) using 1
      simp only [← List.cons_append, ← List.replicate_succ, List.replicate_succ']
      simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem suffix_anchors (x : List S) (l r : List (Cell S Γ)) (lb rb : Bool) :
    ReflTransGen (Step blank)
      ⟨.suffix, l, x.map (fun a => cell blank (.anchor a)) ++ r, lb, rb⟩
      ⟨.suffix, (x.map (fun a => cell blank (.anchor a))).reverse ++ l, r, lb, rb⟩ := by
  induction x generalizing l with
  | nil => exact .refl
  | cons a x ih =>
      refine (ReflTransGen.single (Step.suffix_anchor a _ _ _ _)).trans ?_
      simpa [List.reverse_cons, List.append_assoc] using
        ih (cell blank (.anchor a) :: l)

/-- Conversely every full clean entry passes the validator, with all cells
    left of the head at the handoff to the simulated program. -/
theorem clean_entry_reaches (x y : List S) (s : ℕ) :
    ReflTransGen (Step blank)
      ⟨.initial, List.replicate s (cell blank .workspace) ++
        cell blank .cutC :: (x.map (fun a => cell blank (.anchor a))).reverse,
        cell blank .cutD :: y.map (fun a => cell blank (.anchor a)), true, true⟩
      ⟨.start, (y.map (fun a => cell blank (.anchor a))).reverse ++
        cell blank .cutD :: (List.replicate s (cell blank .workspace) ++
        cell blank .cutC :: (x.map (fun a => cell blank (.anchor a))).reverse),
        [], true, true⟩ := by
  refine (initial_workspaces blank s _ _ true true).trans ?_
  refine (ReflTransGen.single (Step.initial_cut _ _ _ _)).trans ?_
  have hx := left_anchors blank x.reverse []
    (cell blank .cutC :: (List.replicate s (cell blank .workspace) ++
      cell blank .cutD :: y.map (fun a => cell blank (.anchor a)))) true true
  simp only [List.map_reverse, List.append_nil, List.reverse_reverse] at hx
  refine hx.trans ?_
  refine (ReflTransGen.single (Step.left_boundary _ _)).trans ?_
  refine (right_anchors blank x [] _ true true).trans ?_
  simp only [List.append_nil]
  refine (ReflTransGen.single (Step.right_cut _ _ _ _)).trans ?_
  refine (workspace_many blank s _ _ true true).trans ?_
  refine (ReflTransGen.single (Step.workspace_cut _ _ _ _)).trans ?_
  have hy := suffix_anchors blank y
    (cell blank .cutD :: (List.replicate s (cell blank .workspace) ++
      cell blank .cutC :: (x.map (fun a => cell blank (.anchor a))).reverse)) [] true true
  simp only [List.append_nil] at hy
  refine hy.trans ?_
  simpa using ReflTransGen.single (Step.suffix_boundary _ true)

end FiniteAlgebraicEnvelopes.Compiler.Validator

namespace FiniteAlgebraicEnvelopes.Compiler.Validator
open Relation
variable {S Γ : Type*} (blank : Γ)

theorem clean_anchors {l : List (Cell S Γ)} (h : Anchors blank l) :
    (l.map Prod.fst).map (cell blank) = l := by
  induction h with
  | nil => rfl
  | cons a h ih => simpa [cell] using congrArg (cell blank (.anchor a) :: ·) ih

theorem clean_left {l : List (Cell S Γ)} (h : Left blank l) :
    (l.map Prod.fst).map (cell blank) = l := by
  induction h with
  | cut h => simp only [List.map_cons, cell, clean_anchors blank h]
  | work h ih => simpa [cell] using congrArg (cell blank .workspace :: ·) ih

theorem clean_tail {l : List (Cell S Γ)} (h : Tail blank l) :
    (l.map Prod.fst).map (cell blank) = l := by
  induction h with
  | cut h => simp only [List.map_cons, cell, clean_anchors blank h]
  | work h ih => simpa [cell] using congrArg (cell blank .workspace :: ·) ih

theorem cutD_not_mem_left {l : List (Cell S Γ)} (h : Left blank l) :
    cell blank .cutD ∉ l := by
  obtain ⟨s, x, rfl⟩ := (left_iff blank _).mp h
  simp [cell]

/-- Passing entries are determined by their invariant base sequence, with no
    injectivity hypothesis on the subsequent simulated-machine transitions. -/
theorem passing_entries_unique {a b : Sector S Γ}
    (ha : Entry blank a) (hb : Entry blank b)
    (hra : Ready blank a) (hrb : Ready blank b)
    (hs : baseSkeleton a = baseSkeleton b) : a = b := by
  rcases a with ⟨qa, la, ra, lba, rba⟩
  rcases b with ⟨qb, lb, rb, lbb, rbb⟩
  rcases ha with ⟨rfl, ra', rfl⟩
  rcases hb with ⟨rfl, rb', rfl⟩
  rcases hra with ⟨rfl, rfl, hal, har⟩
  rcases hrb with ⟨rfl, rfl, hbl, hbr⟩
  have hcells : la.reverse ++ cell blank .cutD :: ra' =
      lb.reverse ++ cell blank .cutD :: rb' := by
    have h := congrArg (fun z => z.1.map (cell blank)) hs
    simp only [baseSkeleton, List.map_append, List.map_reverse] at h
    simpa only [clean_left blank hal, clean_left blank hbl,
      clean_tail blank har, clean_tail blank hbr] using h
  have hnot : cell blank .cutD ∉ ra' := by
    cases har with
    | cut h =>
        obtain ⟨x, rfl⟩ := (anchors_iff blank _).mp h
        simp [cell]
  have hsplit := (List.append_cons_inj_of_notMem
    (by simpa using cutD_not_mem_left blank hal) hnot).mp hcells
  rcases hsplit with ⟨hl, _, hr⟩
  have hleft : la = lb := List.reverse_injective hl
  subst lb
  subst rb'
  rfl

end FiniteAlgebraicEnvelopes.Compiler.Validator

namespace FiniteAlgebraicEnvelopes.Compiler.Validator.Extended
open Relation
variable {S Γ M : Type*} (blank : Γ)

/-- The internal graph consists of literal validator equations and simulator
    edges. These edges contain neither quota insertion nor exit to cleanup. -/
inductive Step (r : Cfg S Γ M → Cfg S Γ M → Prop) :
    Cfg S Γ M → Cfg S Γ M → Prop
  | validator {v w} : Validator.Step blank v w → Step r (.inl v) (.inl w)
  | machine {a b} : Active a → Active b → r a b → Step r a b

theorem validator_not_start {a b : Sector S Γ} (h : Validator.Step blank a b) :
    a.head ≠ .start := by
  cases h <;> simp

theorem deterministic {r : Cfg S Γ M → Cfg S Γ M → Prop}
    (hr : Relator.RightUnique r) : Relator.RightUnique (Step blank r) := by
  intro a b c hab hac
  cases hab with
  | validator hab =>
      cases hac with
      | validator hac => exact congrArg Sum.inl (Validator.step_deterministic blank hab hac)
      | machine ha _ _ => exact False.elim (validator_not_start blank hab ha)
  | machine ha _ hab =>
      cases hac with
      | validator hac => exact False.elim (validator_not_start blank hac ha)
      | machine _ _ hac => exact hr hab hac

/-- A path starting in the validator either stays there, or first reaches its
    fresh handoff. This explicitly excludes a dirty bypass of validation. -/
theorem path_decomposition {r : Cfg S Γ M → Cfg S Γ M → Prop}
    {a : Sector S Γ} {b : Cfg S Γ M} (h : ReflTransGen (Step blank r) (.inl a) b) :
    (∃ v, b = .inl v ∧ ReflTransGen (Validator.Step blank) a v) ∨
    ∃ v, ReflTransGen (Validator.Step blank) a v ∧ v.head = .start := by
  induction h with
  | refl => exact Or.inl ⟨a, rfl, .refl⟩
  | @tail b c hab hbc ih =>
      rcases ih with ⟨v, rfl, hav⟩ | hv
      · cases hbc with
        | validator h => exact Or.inl ⟨_, rfl, hav.tail h⟩
        | machine hv _ _ => exact Or.inr ⟨v, hav, hv⟩
      · exact Or.inr hv

theorem reaches_active {r : Cfg S Γ M → Cfg S Γ M → Prop}
    {a : Sector S Γ} {b : Cfg S Γ M} (h : ReflTransGen (Step blank r) (.inl a) b)
    (hb : Active b) :
    ∃ v, ReflTransGen (Validator.Step blank) a v ∧ v.head = .start := by
  rcases path_decomposition blank h with ⟨v, rfl, hav⟩ | hv
  · exact ⟨v, hav, hb⟩
  · exact hv

/-- Pulling a path back from a non-handoff validator configuration never
    encounters a simulator edge. -/
theorem path_to_validator {r : Cfg S Γ M → Cfg S Γ M → Prop}
    {a c : Cfg S Γ M} (h : ReflTransGen (Step blank r) a c)
    {b : Sector S Γ} (hc : c = .inl b) (hb : b.head ≠ .start) :
    ∃ v, a = .inl v ∧ ReflTransGen (Validator.Step blank) v b := by
  induction h generalizing b with
  | refl => exact ⟨b, hc, .refl⟩
  | @tail c d hac hcd ih =>
      subst d
      cases hcd with
      | validator h =>
          obtain ⟨v, hav, hvc⟩ := ih rfl (validator_not_start blank h)
          exact ⟨v, hav, hvc.tail h⟩
      | machine _ hd _ => exact False.elim (hb hd)

variable (bases : M → List (Base S) × Bool × Bool)

theorem step_bases {r : Cfg S Γ M → Cfg S Γ M → Prop}
    (hr : ∀ a b, r a b → baseSkeleton bases a = baseSkeleton bases b)
    {a b : Cfg S Γ M} (h : Step blank r a b) :
    baseSkeleton bases a = baseSkeleton bases b := by
  cases h with
  | validator h =>
      have h' := Validator.step_skeleton blank h
      exact congrArg (fun z => (z.1.map Prod.fst, z.2)) h'
  | machine _ _ h => exact hr _ _ h

theorem connected_bases {r : Cfg S Γ M → Cfg S Γ M → Prop}
    (hr : ∀ a b, r a b → baseSkeleton bases a = baseSkeleton bases b)
    {a b : Cfg S Γ M} (h : EqvGen (Step blank r) a b) :
    baseSkeleton bases a = baseSkeleton bases b := by
  induction h with
  | rel _ _ h => exact step_bases blank bases hr h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Entry uniqueness survives arbitrary reverse branching in the simulated
    machine. This is source Lemma compiler-components on all dirty sectors. -/
theorem entries_unique {r : Cfg S Γ M → Cfg S Γ M → Prop}
    (hdet : Relator.RightUnique r)
    (hbase : ∀ a b, r a b → baseSkeleton bases a = baseSkeleton bases b)
    {a b : Sector S Γ} (ha : Entry blank a) (hb : Entry blank b)
    (hab : EqvGen (Step blank r) (.inl a) (.inl b)) : a = b := by
  obtain ⟨c, hac, hbc⟩ := weak_component_joins (deterministic blank hdet) hab
  have hsame : Validator.baseSkeleton a = Validator.baseSkeleton b :=
    connected_bases blank bases hbase hab
  have hactive (hc : Active c) : a = b := by
    obtain ⟨v, hav, hv⟩ := reaches_active blank hac hc
    obtain ⟨w, hbw, hw⟩ := reaches_active blank hbc hc
    apply passing_entries_unique blank ha hb _ _ hsame
    · apply reaches_ready blank hav
      simp [Ready, hv]
    · apply reaches_ready blank hbw
      simp [Ready, hw]
  cases c with
  | inr q => exact hactive trivial
  | inl v =>
      by_cases hv : v.head = .start
      · exact hactive hv
      · obtain ⟨a', heqa, hav⟩ := path_to_validator blank hac rfl hv
        obtain ⟨b', heqb, hbv⟩ := path_to_validator blank hbc rfl hv
        cases Sum.inl.inj heqa
        cases Sum.inl.inj heqb
        exact sources_unique_of_join (step_leftUnique blank)
          (fun _ => entry_no_predecessor blank ha)
          (fun _ => entry_no_predecessor blank hb) hav hbv

end FiniteAlgebraicEnvelopes.Compiler.Validator.Extended

namespace FiniteAlgebraicEnvelopes.Compiler.Scan

variable {H B T : Type*}

theorem deterministic (table : Table H B T) : Relator.RightUnique (Step table) := by
  intro a b c hab hac
  exact Option.some.inj (hab.symm.trans hac)

end FiniteAlgebraicEnvelopes.Compiler.Scan

end OAI
end

section
-- module Solutions.OAIFAE.Simulator
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.fixedFintype _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.fixedStepDecidable _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.instPrimcodableSector _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableBaseOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableTagOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Literal finite-quota machine simulation and readout correctness.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator

variable {S Γ Q : Type*}

theorem ok_terminal (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]
    (v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)) (hv : v.head = .ok) :
    Scan.step (table A M) v = none := by
  simp only [Scan.step, hv, table]
  split
  · simp [cell]
  · split <;> rfl

/-- Rewinding crosses all left cells unchanged and then changes phase at alpha.
    This lemma holds on dirty data as well as the intended clean simulation. -/
theorem rewind (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]
    (s : Resume S) (l r : List (Base S × Tag S Γ)) (rb : Bool) :
    Relation.ReflTransGen (Scan.Step (table A M))
      ⟨l,.rewind s,r,true,rb⟩ ⟨[],.scan s,l.reverse ++ r,true,rb⟩ := by
  induction l generalizing r with
  | nil =>
      apply Relation.ReflTransGen.single
      simp [Scan.Step, Scan.step, table]
  | cons a l ih =>
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        (Relation.ReflTransGen.head (by simp [Scan.Step, Scan.step, table, cell]) (ih (a::r)))

/-- Going to the right boundary also preserves every cell. -/
theorem finish (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]
    (l r : List (Base S × Tag S Γ)) (lb : Bool) :
    Relation.ReflTransGen (Scan.Step (table A M))
      ⟨l,.finish,r,lb,true⟩ ⟨r.reverse ++ l,.ok,[],lb,true⟩ := by
  induction r generalizing l with
  | nil =>
      apply Relation.ReflTransGen.single
      simp [Scan.Step, Scan.step, table]
  | cons a r ih =>
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        (Relation.ReflTransGen.head (by simp [Scan.Step, Scan.step, table, cell]) (ih (a::l)))

end FiniteAlgebraicEnvelopes.Compiler.Simulator

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
variable {H B T : Type*}

theorem cross_right (table : Table H B T) (q : H) (hd : table.direction q = .right)
    (p l r : List (B × T)) (lb rb : Bool)
    (hp : ∀ c ∈ p, table.cell q c.1 c.2 = some ⟨q,c.2,true⟩) :
    ReflTransGen (Step table) ⟨l,q,p ++ r,lb,rb⟩ ⟨p.reverse ++ l,q,r,lb,rb⟩ := by
  induction p generalizing l with
  | nil => exact .refl
  | cons c p ih =>
    rcases c with ⟨b,t⟩
    have hc := hp (b,t) (by simp)
    have hstep : Step table ⟨l,q,(b,t)::(p++r),lb,rb⟩
        ⟨(b,t)::l,q,p++r,lb,rb⟩ := by simp [Step, step, hd, hc]
    simpa only [List.cons_append, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.nil_append] using
      (ReflTransGen.head hstep (ih ((b,t)::l) fun c hc => hp c (by simp [hc])))

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

/-- One complete find/update/rewind invocation acts on the first matching
    cell. No higher-level operation is used in the actual finite table. -/
theorem scan_update (s s' : Resume S) (p r : Cells S Γ) (b : Base S) (t t' : Tag S Γ)
    (hp : ∀ c ∈ p, cell A M (.scan s) c.1 c.2 = some ⟨.scan s,c.2,true⟩)
    (hc : cell A M (.scan s) b t = some ⟨.rewind s',t',false⟩) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan s,p ++ (b,t)::r,true,true⟩
      ⟨[],.scan s',p ++ (b,t')::r,true,true⟩ := by
  have h₀ := Scan.cross_right (table A M) (.scan s) rfl p [] ((b,t)::r) true true hp
  simp only [List.append_nil] at h₀
  have h₁ : Scan.Step (table A M)
      ⟨p.reverse,.scan s,(b,t)::r,true,true⟩
      ⟨p.reverse,.rewind s',(b,t')::r,true,true⟩ := by
    simp [Scan.Step, Scan.step, table, hc]
  have h₂ := rewind A M s' p.reverse ((b,t')::r) true
  simpa using (h₀.trans ((ReflTransGen.single h₁).trans h₂))

/-- A loaded input letter is transferred to the next free workspace cell,
    expanding the prefix and shrinking the finite quota by one. -/
theorem copy_left_one (xp xs yp ys w : List S) (a : S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .input,body A xp (a::xs) yp ys w (n+1),true,true⟩
      ⟨[],.scan .input,body A (xp++[a]) xs yp ys (w++[a]) n,true,true⟩ := by
  let p := xp.map (readAnchor A · true)
  let r := xs.map (readAnchor A · false) ++ [bare A .cutC] ++
    w.map (filledWork A) ++ List.replicate (n+1) (bare A .workspace) ++
    [bare A .cutD] ++ yp.map (readAnchor A · true) ++ ys.map (readAnchor A · false)
  have h₁ := scan_update A M .input (.fill a) p r (.anchor a)
    (readAnchor A a false).2 (readAnchor A a true).2
    (by change ∀ c ∈ p, Pass A M .input c; simp [p]) (by rfl)
  let p' := (xp ++ [a]).map (readAnchor A · true) ++ xs.map (readAnchor A · false) ++
    [bare A .cutC] ++ w.map (filledWork A)
  let r' := List.replicate n (bare A .workspace) ++ [bare A .cutD] ++
    yp.map (readAnchor A · true) ++ ys.map (readAnchor A · false)
  have h₂ := scan_update A M (.fill a) .input p' r' .workspace
    (clean A.blank) (filledWork A a).2
    (by
      change ∀ c ∈ p', Pass A M (.fill a) c
      intro c hc
      simp only [p', List.mem_append, List.mem_map, List.mem_singleton] at hc
      rcases hc with ((⟨b,_,rfl⟩ | ⟨b,_,rfl⟩) | rfl) | ⟨b,_,rfl⟩ <;> simp) (by rfl)
  have heq : (⟨[],Head.scan (.fill a),p ++ (.anchor a,(readAnchor A a true).2)::r,
      true,true⟩ : Scan.Sector (Head S Q) (Base S) (Tag S Γ)) =
      ⟨[],.scan (.fill a),p' ++ (.workspace,clean A.blank)::r',true,true⟩ := by
    simp [p, r, p', r', List.replicate_succ, readAnchor, bare, List.append_assoc]
  rw [heq] at h₁
  simpa [body, p, r, p', r', List.replicate_succ, readAnchor, bare, filledWork,
    List.append_assoc] using h₁.trans h₂

theorem copy_right_one (xp yp ys w : List S) (a : S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .input,body A xp [] yp (a::ys) w (n+1),true,true⟩
      ⟨[],.scan .input,body A xp [] (yp++[a]) ys (w++[a]) n,true,true⟩ := by
  let p := xp.map (readAnchor A · true) ++ [bare A .cutC] ++ w.map (filledWork A) ++
    List.replicate (n+1) (bare A .workspace) ++ [bare A .cutD] ++
    yp.map (readAnchor A · true)
  let r := ys.map (readAnchor A · false)
  have h₁ := scan_update A M .input (.fill a) p r (.anchor a)
    (readAnchor A a false).2 (readAnchor A a true).2
    (by
      change ∀ c ∈ p, Pass A M .input c
      intro c hc
      simp only [p, List.mem_append, List.mem_map, List.mem_singleton,
        List.mem_replicate] at hc
      rcases hc with ((((⟨b,_,rfl⟩ | rfl) | ⟨b,_,rfl⟩) | ⟨_,rfl⟩) | rfl) | ⟨b,_,rfl⟩ <;>
        simp) (by rfl)
  let p' := xp.map (readAnchor A · true) ++ [bare A .cutC] ++ w.map (filledWork A)
  let r' := List.replicate n (bare A .workspace) ++ [bare A .cutD] ++
    (yp++[a]).map (readAnchor A · true) ++ ys.map (readAnchor A · false)
  have h₂ := scan_update A M (.fill a) .input p' r' .workspace
    (clean A.blank) (filledWork A a).2
    (by
      change ∀ c ∈ p', Pass A M (.fill a) c
      intro c hc
      simp only [p', List.mem_append, List.mem_map, List.mem_singleton] at hc
      rcases hc with (⟨b,_,rfl⟩ | rfl) | ⟨b,_,rfl⟩ <;> simp) (by rfl)
  have heq : (⟨[],Head.scan (.fill a),p ++ (.anchor a,(readAnchor A a true).2)::r,
      true,true⟩ : Scan.Sector (Head S Q) (Base S) (Tag S Γ)) =
      ⟨[],.scan (.fill a),p' ++ (.workspace,clean A.blank)::r',true,true⟩ := by
    simp [p, r, p', r', List.replicate_succ, readAnchor, bare, List.append_assoc]
  rw [heq] at h₁
  simpa [body, p, r, p', r', List.replicate_succ, readAnchor, bare, filledWork,
    List.append_assoc] using h₁.trans h₂

theorem copy_left (xp xs yp ys w : List S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .input,body A xp xs yp ys w (xs.length+n),true,true⟩
      ⟨[],.scan .input,body A (xp++xs) [] yp ys (w++xs) n,true,true⟩ := by
  induction xs generalizing xp w with
  | nil => simp; exact .refl
  | cons a xs ih =>
    have h := copy_left_one A M xp xs yp ys w a (xs.length+n)
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.append_assoc] using h.trans (ih (xp++[a]) (w++[a]))

theorem copy_right (xp yp ys w : List S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .input,body A xp [] yp ys w (ys.length+n),true,true⟩
      ⟨[],.scan .input,body A xp [] (yp++ys) [] (w++ys) n,true,true⟩ := by
  induction ys generalizing yp w with
  | nil => simp; exact .refl
  | cons a ys ih =>
    have h := copy_right_one A M xp yp ys w a (ys.length+n)
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.append_assoc] using h.trans (ih (yp++[a]) (w++[a]))

/-- Both anchor blocks are copied in their order, not in zipper order. -/
theorem copy_all (x y : List S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .input,body A [] x [] y [] (x.length+y.length+n),true,true⟩
      ⟨[],.scan .input,body A x [] y [] (x++y) n,true,true⟩ := by
  have h₁ := copy_left A M [] x [] y [] (y.length+n)
  have h₂ := copy_right A M x [] y x n
  simp only [List.nil_append] at h₁ h₂
  simpa only [Nat.add_assoc] using h₁.trans h₂

/-- The two final copy scans check a spare blank and position the machine at
    the first workspace cell. In particular the quota is not treated as tape
    that may silently grow during internal transitions. -/
theorem copy_enter_run (x y w : List S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .input,body A x [] y [] w (n+1),true,true⟩
      ⟨(x.map (readAnchor A · true) ++ [bare A .cutC]).reverse,.run M.initial,
        w.map (filledWork A) ++ List.replicate (n+1) (bare A .workspace) ++
          [bare A .cutD] ++ y.map (readAnchor A · true),true,true⟩ := by
  let cells := body A x [] y [] w (n+1)
  have hall : ∀ c ∈ cells, Pass A M .input c := by
    simp only [cells, body, List.map_nil, List.append_nil, List.forall_mem_append,
      List.forall_mem_map, List.forall_mem_singleton, List.forall_mem_replicate]
    simp
  have h₀ := Scan.cross_right (table A M) (.scan .input) rfl cells [] [] true true hall
  have h₁ : Scan.Step (table A M) ⟨cells.reverse,.scan .input,[],true,true⟩
      ⟨cells.reverse,.rewind .spare,[],true,true⟩ := by
    simp [Scan.Step, Scan.step, table]
  have h₂ := rewind A M .spare cells.reverse [] true
  simp only [List.reverse_reverse, List.append_nil] at h₀ h₂
  have hpre := h₀.trans ((ReflTransGen.single h₁).trans h₂)
  let p := x.map (readAnchor A · true) ++ [bare A .cutC] ++ w.map (filledWork A)
  let r := List.replicate n (bare A .workspace) ++ [bare A .cutD] ++
    y.map (readAnchor A · true)
  have hs := scan_update A M .spare .first p r .workspace (clean A.blank) (clean A.blank)
    (by
      change ∀ c ∈ p, Pass A M .spare c
      simp only [p, List.forall_mem_append, List.forall_mem_map, List.forall_mem_singleton]
      simp) (by rfl)
  have heq : cells = p ++ (.workspace,clean A.blank)::r := by
    simp [cells, body, p, r, bare, List.replicate_succ, List.append_assoc]
  rw [← heq] at hs
  let p' := x.map (readAnchor A · true) ++ [bare A .cutC]
  let r' := w.map (filledWork A) ++ List.replicate (n+1) (bare A .workspace) ++
    [bare A .cutD] ++ y.map (readAnchor A · true)
  have hp' : ∀ c ∈ p', Pass A M .first c := by
    simp only [p', List.forall_mem_append, List.forall_mem_map, List.forall_mem_singleton]
    simp
  have hf := Scan.cross_right (table A M) (.scan .first) rfl p' [] r' true true hp'
  have hnonempty : ∃ t tail, r' = (.workspace,t)::tail := by
    cases w with
    | nil => exact ⟨clean A.blank,r,by simp [r', r, bare, List.replicate_succ, List.append_assoc]⟩
    | cons a w =>
      exact ⟨(filledWork A a).2,
        w.map (filledWork A) ++ List.replicate (n+1) (bare A .workspace) ++
          [bare A .cutD] ++ y.map (readAnchor A · true),
        by simp [r', filledWork, List.append_assoc]⟩
  have hlast : Scan.Step (table A M) ⟨p'.reverse,.scan .first,r',true,true⟩
      ⟨p'.reverse,.run M.initial,r',true,true⟩ := by
    obtain ⟨tag,tail,hr⟩ := hnonempty
    simp [Scan.Step, Scan.step, table, cell, hr]
  have heq' : cells = p' ++ r' := by simp [cells, body, p', r', List.append_assoc]
  rw [← heq'] at hf
  simp only [List.append_nil] at hf
  exact hpre.trans (hs.trans (hf.tail hlast))

/-- The fresh post-validator handoff starts copying from the left boundary. -/
theorem start_copy (cells : Cells S Γ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨cells.reverse,.start,[],true,true⟩ ⟨[],.scan .input,cells,true,true⟩ := by
  have h₀ : Scan.Step (table A M) ⟨cells.reverse,.start,[],true,true⟩
      ⟨cells.reverse,.rewind .input,[],true,true⟩ := by
    simp [Scan.Step, Scan.step, table]
  simpa using (ReflTransGen.head h₀ (rewind A M .input cells.reverse [] true))

/-- Literal correctness of the complete copy/init program with any sufficient
    finite quota. Every table operation is one of the listed compiled equations. -/
theorem copy_correct (x y : List S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨(body A [] x [] y [] (x.length+y.length+n+1)).reverse,.start,[],true,true⟩
      ⟨(x.map (readAnchor A · true) ++ [bare A .cutC]).reverse,.run M.initial,
        (x++y).map (filledWork A) ++ List.replicate (n+1) (bare A .workspace) ++
          [bare A .cutD] ++ y.map (readAnchor A · true),true,true⟩ := by
  have h₀ := start_copy A M (body A [] x [] y [] (x.length+y.length+(n+1)))
  have h₁ := copy_all A M x y (n+1)
  have h₂ := copy_enter_run A M x y (x++y) n
  simpa only [Nat.add_assoc] using h₀.trans (h₁.trans h₂)

end

section
open Relation
variable {S Γ Q : Type*}

/-- Workspace in its fixed surrounding anchor/cut sector. `x` is the cells
    before C in their ordinary order, `y` the cells following D. -/
def runSector (A : Alphabet S Γ) (x y : Cells S Γ) (c : Tape (S := S) (Γ := Γ) (Q := Q)) :
    Scan.Sector (Head S Q) (Base S) (Tag S Γ) :=
  ⟨workCells c.left ++ bare A .cutC :: x.reverse, .run c.state,
    workCells c.right ++ bare A .cutD :: y, true, true⟩

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

/-- Every bounded machine transition is implemented by one or two actual
    finite scan instructions. Both the stationary left edge and true left
    movement are proved, and no quota insertion occurs during simulation. -/
theorem tapeStep_simulates (x y : Cells S Γ) {c d : Tape (S := S) (Γ := Γ) (Q := Q)}
    (h : TapeStep M c d) :
    ReflTransGen (Scan.Step (table A M)) (runSector A x y c) (runSector A x y d) := by
  cases h with
  | stay h hm =>
      apply ReflTransGen.single
      simp [Scan.Step, Scan.step, table, cell, runSector, workCells, h, hm, writeWork]
  | right h hm =>
      apply ReflTransGen.single
      simp [Scan.Step, Scan.step, table, cell, runSector, workCells, h, hm, writeWork]
  | @leftEdge q t r d h hm =>
      apply ReflTransGen.trans (b :=
        ⟨bare A .cutC :: x.reverse, .left d.state,
          (.workspace, writeWork t d.write) :: (workCells r ++ bare A .cutD :: y), true,true⟩)
      · apply ReflTransGen.single
        simp [Scan.Step, Scan.step, table, cell, runSector, workCells, h, hm, writeWork]
      · apply ReflTransGen.single
        simp [Scan.Step, Scan.step, table, cell, runSector, workCells, bare]
  | @left q v l t r d h hm =>
      apply ReflTransGen.trans (b :=
        ⟨(.workspace,v) :: (workCells l ++ bare A .cutC :: x.reverse), .left d.state,
          (.workspace, writeWork t d.write) :: (workCells r ++ bare A .cutD :: y),true,true⟩)
      · apply ReflTransGen.single
        simp [Scan.Step, Scan.step, table, cell, runSector, workCells, h, hm, writeWork]
      · apply ReflTransGen.single
        simp [Scan.Step, Scan.step, table, cell, runSector, workCells]

/-- Simulation respects literal finite traces, without a running-time bound. -/
theorem tapeRun_simulates (x y : Cells S Γ) {c d : Tape (S := S) (Γ := Γ) (Q := Q)}
    (h : ReflTransGen (TapeStep M) c d) :
    ReflTransGen (Scan.Step (table A M)) (runSector A x y c) (runSector A x y d) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.trans (tapeStep_simulates A M x y hs)

/-- Exhaustion is stuck even if the machine's current state would be halting:
    a halt must be observed at an actual workspace cell. -/
theorem quota_exhausted (x y : Cells S Γ) (q : Q) (l : List (Tag S Γ)) :
    Scan.step (table A M) (runSector A x y ⟨q,l,[]⟩) = none := by
  simp [Scan.step, table, cell, runSector, workCells, bare]

/-- A genuine in-bounds halt triggers precisely the readout rewind. -/
theorem halt_readout (x y : Cells S Γ) (q : Q) (l : List (Tag S Γ))
    (t : Tag S Γ) (r : List (Tag S Γ)) (h : M.transition q t.work = none) :
    ReflTransGen (Scan.Step (table A M))
      (runSector A x y ⟨q,l,t::r⟩)
      ⟨[],.scan .readout,
        x ++ [bare A .cutC] ++ workCells (l.reverse ++ t::r) ++ bare A .cutD :: y,
        true,true⟩ := by
  have hs : Scan.Step (table A M) (runSector A x y ⟨q,l,t::r⟩)
      ⟨workCells l ++ bare A .cutC :: x.reverse, .rewind .readout,
        workCells (t::r) ++ bare A .cutD :: y, true,true⟩ := by
    simp [Scan.Step, Scan.step, table, cell, runSector, workCells, h]
  have hr := rewind A M .readout (workCells l ++ bare A .cutC :: x.reverse)
    (workCells (t::r) ++ bare A .cutD :: y) true
  simpa [workCells, List.reverse_append, List.reverse_cons, List.map_reverse,
    List.append_assoc] using ((ReflTransGen.single hs).trans hr)

end

section
open Relation
variable {S Γ Q : Type*}

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

theorem readout_pass (l : Cells S Γ) (done : List Γ)
    (h : workView l = done.map (true,·)) :
    ∀ c ∈ l, cell A M (.scan .readout) c.1 c.2 = some ⟨.scan .readout,c.2,true⟩ := by
  rintro ⟨b,t⟩ hc
  cases b <;> try rfl
  have ht : (t.outputRead,t.work) ∈ workView l :=
    List.mem_filterMap.mpr ⟨(.workspace,t),hc,rfl⟩
  rw [h] at ht
  obtain ⟨v,_,hv⟩ := List.mem_map.mp ht
  have hr : t.outputRead = true := (congrArg Prod.fst hv).symm
  simp [cell, hr]

theorem put_pass (a : S) (l : Cells S Γ) (done : List S)
    (h : anchorView l = done.map some) :
    ∀ c ∈ l, cell A M (.scan (.put a)) c.1 c.2 = some ⟨.scan (.put a),c.2,true⟩ := by
  rintro ⟨b,t⟩ hc
  cases b <;> try rfl
  rename_i b
  have ht : t.output ∈ anchorView l := List.mem_filterMap.mpr ⟨(.anchor b,t),hc,rfl⟩
  rw [h] at ht
  obtain ⟨v,_,hv⟩ := List.mem_map.mp ht
  simp [cell, ← hv]

/-- One output letter is read from the first unread workspace cell and written
    to the first unmarked anchor. The projected views certify both orders. -/
theorem readout_one (cells : Cells S Γ) (done remaining : List Γ)
    (out : List S) (a : S) (g : Γ) (n : ℕ)
    (hw : workView cells = done.map (true,·) ++ (false,g)::remaining.map (false,·))
    (ha : anchorView cells = out.map some ++ none :: List.replicate n none)
    (hg : g ≠ A.blank) (hg' : A.output g = some a) :
    ∃ cells', ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .readout,cells,true,true⟩ ⟨[],.scan .readout,cells',true,true⟩ ∧
      workView cells' = (done ++ [g]).map (true,·) ++ remaining.map (false,·) ∧
      anchorView cells' = (out ++ [a]).map some ++ List.replicate n none := by
  obtain ⟨p,⟨b,t⟩,r,hc,hp,hb,hr⟩ := split_filterMap
    (fun c : Base S × Tag S Γ => match c.1 with
      | .workspace => some (c.2.outputRead,c.2.work) | _ => none)
    cells (done.map (true,·)) (false,g) (remaining.map (false,·)) hw
  cases b <;> simp only at hb
  all_goals try contradiction
  have ht : t.outputRead = false ∧ t.work = g := by simpa using hb
  let t' : Tag S Γ := {t with outputRead := true}
  let mid := p ++ (.workspace,t')::r
  have hs := scan_update A M .readout (.put a) p r .workspace t t'
    (readout_pass A M p done hp) (by simp [cell, ht.1, ht.2, hg, hg', t'])
  rw [← hc] at hs
  have hwm : workView mid = (done ++ [g]).map (true,·) ++ remaining.map (false,·) := by
    simp only [mid, workView_append]
    change workView p ++ (true,t.work)::workView r = _
    change workView p = _ at hp
    change workView r = _ at hr
    simp [hp, hr, ht.2, List.append_assoc]
  have ham : anchorView mid = anchorView cells := by
    rw [hc]
    simp [mid, anchorView, List.filterMap_append]
  obtain ⟨p₂,⟨b₂,t₂⟩,r₂,hc₂,hp₂,hb₂,hr₂⟩ := split_filterMap
    (fun c : Base S × Tag S Γ => match c.1 with
      | .anchor _ => some c.2.output | _ => none)
    mid (out.map some) none (List.replicate n none) (ham.trans ha)
  cases b₂ <;> simp only at hb₂
  all_goals try contradiction
  rename_i a₂
  have ht₂ : t₂.output = none := Option.some.inj hb₂
  let t₂' : Tag S Γ := {t₂ with output := some a}
  let result := p₂ ++ (.anchor a₂,t₂')::r₂
  have hs₂ := scan_update A M (.put a) .readout p₂ r₂ (.anchor a₂) t₂ t₂'
    (put_pass A M a p₂ out hp₂) (by simp [cell, ht₂, t₂'])
  rw [← hc₂] at hs₂
  refine ⟨result,hs.trans hs₂,?_,?_⟩
  · have heq : workView result = workView mid := by
      rw [hc₂]
      simp [result, workView, List.filterMap_append]
    exact heq.trans hwm
  · simp only [result, anchorView_append]
    change anchorView p₂ ++ some a :: anchorView r₂ = _
    change anchorView p₂ = _ at hp₂
    change anchorView r₂ = _ at hr₂
    simp [hp₂,hr₂,List.append_assoc]

/-- The first unread blank ends output. No cell is changed by the final sweep. -/
theorem readout_blank (cells : Cells S Γ) (done : List Γ) (rest : List (Bool × Γ))
    (hw : workView cells = done.map (true,·) ++ (false,A.blank)::rest) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .readout,cells,true,true⟩ ⟨cells.reverse,.ok,[],true,true⟩ := by
  obtain ⟨p,⟨b,t⟩,r,hc,hp,hb,_⟩ := split_filterMap
    (fun c : Base S × Tag S Γ => match c.1 with
      | .workspace => some (c.2.outputRead,c.2.work) | _ => none)
    cells (done.map (true,·)) (false,A.blank) rest hw
  cases b <;> simp only at hb
  all_goals try contradiction
  have ht : t.outputRead = false ∧ t.work = A.blank := by simpa using hb
  have h₀ := Scan.cross_right (table A M) (.scan .readout) rfl p [] ((.workspace,t)::r)
    true true (readout_pass A M p done hp)
  simp only [List.append_nil] at h₀
  have h₁ : Scan.Step (table A M) ⟨p.reverse,.scan .readout,(.workspace,t)::r,true,true⟩
      ⟨p.reverse,.finish,(.workspace,t)::r,true,true⟩ := by
    simp [Scan.Step, Scan.step, table, cell, ht.1, ht.2]
  have h₂ := finish A M p.reverse ((.workspace,t)::r) true
  simpa [hc, List.reverse_append] using h₀.trans ((ReflTransGen.single h₁).trans h₂)

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

/-- Complete readout of a finite, blank-delimited returned string. The spare
    anchor count drops by exactly one for each letter, including when that
    letter's anchor is on the other side of the workspace. -/
theorem readout_complete (out : List S) (cells : Cells S Γ) (done tail : List Γ)
    (old : List S) (n : ℕ)
    (hw : workView cells = done.map (true,·) ++
      (out.map A.input ++ A.blank::tail).map (false,·))
    (ha : anchorView cells = old.map some ++ List.replicate (out.length+n) none) :
    ∃ cells', ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .readout,cells,true,true⟩ ⟨cells'.reverse,.ok,[],true,true⟩ ∧
      anchorView cells' = (old ++ out).map some ++ List.replicate n none := by
  induction out generalizing cells done old with
  | nil =>
      refine ⟨cells,readout_blank A M cells done (tail.map (false,·)) ?_,?_⟩
      · simpa using hw
      · simpa using ha
  | cons a out ih =>
      have hw' : workView cells = done.map (true,·) ++ (false,A.input a)::
          (out.map A.input ++ A.blank::tail).map (false,·) := by simpa using hw
      have ha' : anchorView cells = old.map some ++ none::
          List.replicate (out.length+n) none := by
        have hn : (a :: out).length + n = (out.length + n) + 1 := by simp; omega
        rw [hn, List.replicate_succ] at ha
        exact ha
      obtain ⟨mid,hs,hmw,hma⟩ := readout_one A M cells done
        (out.map A.input ++ A.blank::tail) old a (A.input a) (out.length+n)
        hw' ha' (input_ne_blank A a) (A.output_input a)
      obtain ⟨result,hr,hra⟩ := ih mid (done ++ [A.input a]) (old ++ [a]) hmw hma
      refine ⟨result,hs.trans hr,?_⟩
      simpa [List.append_assoc] using hra

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

/-- Rejection here means the actual finite table has no forward accepting
    trace; it is stronger than merely failing a chosen simulation trace. -/
def Rejects (v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)) : Prop :=
  ∀ w, ReflTransGen (Scan.Step (table A M)) v w → w.head ≠ .ok

theorem terminal_of_none {v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (h : Scan.step (table A M) v = none) : Terminal (Scan.Step (table A M)) v := by
  intro w hw
  rw [Scan.Step, h] at hw
  contradiction

theorem rejects_of_stuck {v s : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (hvs : ReflTransGen (Scan.Step (table A M)) v s)
    (hs : Scan.step (table A M) s = none) (hq : s.head ≠ .ok) : Rejects A M v := by
  intro w hw hq'
  rcases ReflTransGen.total_of_right_unique (Scan.deterministic (table A M)) hvs hw with h | h
  · exact hq ((congrArg Scan.Sector.head (terminal_eq_of_reaches (terminal_of_none A M hs) h)).trans hq')
  · have he := terminal_eq_of_reaches (terminal_of_none A M (ok_terminal A M w hq')) h
    exact hq ((congrArg Scan.Sector.head he).symm.trans hq')

theorem rejects_before {v s : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (hvs : ReflTransGen (Scan.Step (table A M)) v s) (hs : Rejects A M s) : Rejects A M v := by
  intro w hw hq
  rcases ReflTransGen.total_of_right_unique (Scan.deterministic (table A M)) hvs hw with h | h
  · exact hs w h hq
  · have he := terminal_eq_of_reaches (terminal_of_none A M (ok_terminal A M w hq)) h
    exact hs s .refl ((congrArg Scan.Sector.head he).symm.trans hq)

/-- No unread cell, in particular no blank delimiter, means that readout stops
    at omega without entering the finish phase. -/
theorem readout_no_unread (cells : Cells S Γ) (done : List Γ)
    (h : workView cells = done.map (true,·)) :
    Rejects A M ⟨[],.scan .readout,cells,true,true⟩ := by
  have hr := Scan.cross_right (table A M) (.scan .readout) rfl cells [] [] true true
    (readout_pass A M cells done h)
  simp only [List.append_nil] at hr
  exact rejects_of_stuck A M hr (by simp [Scan.step,table]) (by simp)

/-- Filled anchors cannot be overwritten. Exhausting them rejects even if a
    workspace character was successfully decoded. -/
theorem put_no_anchor (cells : Cells S Γ) (old : List S) (a : S)
    (h : anchorView cells = old.map some) :
    Rejects A M ⟨[],.scan (.put a),cells,true,true⟩ := by
  have hr := Scan.cross_right (table A M) (.scan (.put a)) rfl cells [] [] true true
    (put_pass A M a cells old h)
  simp only [List.append_nil] at hr
  exact rejects_of_stuck A M hr (by simp [Scan.step,table]) (by simp)

/-- Metasymbols that are neither blank nor returned letters block output. -/
theorem readout_invalid (cells : Cells S Γ) (done : List Γ) (g : Γ)
    (rest : List (Bool × Γ))
    (h : workView cells = done.map (true,·) ++ (false,g)::rest)
    (hg : g ≠ A.blank) (hdecode : A.output g = none) :
    Rejects A M ⟨[],.scan .readout,cells,true,true⟩ := by
  obtain ⟨p,⟨b,t⟩,r,hc,hp,hb,_⟩ := split_filterMap
    (fun c : Base S × Tag S Γ => match c.1 with
      | .workspace => some (c.2.outputRead,c.2.work) | _ => none)
    cells (done.map (true,·)) (false,g) rest h
  cases b <;> simp only at hb
  all_goals try contradiction
  have ht : t.outputRead = false ∧ t.work = g := by simpa using hb
  have hr := Scan.cross_right (table A M) (.scan .readout) rfl p [] ((.workspace,t)::r)
    true true (readout_pass A M p done hp)
  simp only [List.append_nil] at hr
  rw [← hc] at hr
  exact rejects_of_stuck A M hr
    (by simp [Scan.step,table,cell,ht.1,ht.2,hg,hdecode]) (by simp)

/-- The first nonblank output symbol cannot succeed when all anchors are full. -/
theorem readout_no_anchor (cells : Cells S Γ) (done : List Γ) (rest : List (Bool × Γ))
    (old : List S) (a : S) (g : Γ)
    (hw : workView cells = done.map (true,·) ++ (false,g)::rest)
    (ha : anchorView cells = old.map some)
    (hg : g ≠ A.blank) (hdecode : A.output g = some a) :
    Rejects A M ⟨[],.scan .readout,cells,true,true⟩ := by
  obtain ⟨p,⟨b,t⟩,r,hc,hp,hb,_⟩ := split_filterMap
    (fun c : Base S × Tag S Γ => match c.1 with
      | .workspace => some (c.2.outputRead,c.2.work) | _ => none)
    cells (done.map (true,·)) (false,g) rest hw
  cases b <;> simp only at hb
  all_goals try contradiction
  have ht : t.outputRead = false ∧ t.work = g := by simpa using hb
  let t' : Tag S Γ := {t with outputRead := true}
  have hr := scan_update A M .readout (.put a) p r .workspace t t'
    (readout_pass A M p done hp) (by simp [cell,ht.1,ht.2,hg,hdecode,t'])
  rw [← hc] at hr
  apply rejects_before A M hr
  apply put_no_anchor A M (p ++ (.workspace,t')::r) old a
  rw [hc] at ha
  simpa [anchorView,List.filterMap_append] using ha

end

section
open Relation
variable {S Γ Q : Type*}

variable (A : Alphabet S Γ) (M : Machine Q Γ)

/-- A bounded operation never inspects cells beyond its current head and is
    therefore preserved by appending arbitrary extra blank quota. -/
theorem tapeStep_pad {c d : Tape (S := S) (Γ := Γ) (Q := Q)}
    (h : TapeStep M c d) (n : ℕ) : TapeStep M (pad A c n) (pad A d n) := by
  cases h with
  | stay h hm => exact .stay h hm
  | right h hm => exact .right h hm
  | leftEdge h hm => exact .leftEdge h hm
  | left h hm => exact .left h hm

/-- Every finite unbounded trace uses a finite quota. The terminal padding can
    be prescribed in advance, in particular ensuring an explicit spare blank. -/
theorem finite_quota {c d : Tape (S := S) (Γ := Γ) (Q := Q)}
    (h : ReflTransGen (UnboundedStep A M) c d) :
    ∀ n, ∃ k, n ≤ k ∧ ReflTransGen (TapeStep M) (pad A c k) (pad A d n) := by
  induction h with
  | refl => exact fun n => ⟨n,le_rfl,.refl⟩
  | @tail d e _ hs ih =>
      intro n
      cases hs with
      | within hh =>
          obtain ⟨k,hkn,hk⟩ := ih n
          exact ⟨k,hkn,hk.tail (tapeStep_pad A M hh n)⟩
      | @extend q l e hh =>
          obtain ⟨k,hkn,hk⟩ := ih (n+1)
          refine ⟨k,by omega,hk.tail ?_⟩
          simpa [pad,List.replicate_succ] using tapeStep_pad A M hh n

/-- A predicate on full tags insensitive to changes of the work symbol is an
    invariant of every bounded run, not just of a chosen clean execution. -/
theorem tapeStep_tags (P : Tag S Γ → Prop)
    (hwrite : ∀ t a, P t → P (writeWork t a))
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : TapeStep M c d)
    (hc : ∀ t ∈ c.left ++ c.right, P t) : ∀ t ∈ d.left ++ d.right, P t := by
  cases h <;> simp only [List.mem_append,List.mem_cons] at hc ⊢
  all_goals
    intro t ht
    rcases ht with (ht | ht)
    · try {exact hc t (Or.inl ht)}
      try {rcases ht with rfl | ht
           · exact hwrite _ _ (hc _ (Or.inr (Or.inl rfl)))
           · exact hc t (Or.inl ht)}
      try {exact hc t (Or.inl (Or.inr ht))}
    · try {rcases ht with rfl | ht
           · exact hwrite _ _ (hc _ (Or.inr (Or.inl rfl)))
           · exact hc t (Or.inr (Or.inr ht))}
      try {exact hc t (Or.inr (Or.inr ht))}
      try {rcases ht with rfl | rfl | ht
           · exact hc _ (Or.inl (Or.inl rfl))
           · exact hwrite _ _ (hc _ (Or.inr (Or.inl rfl)))
           · exact hc t (Or.inr (Or.inr ht))}

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ)

theorem unboundedStep_tags (P : Tag S Γ → Prop)
    (hblank : P (clean A.blank)) (hwrite : ∀ t a, P t → P (writeWork t a))
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : UnboundedStep A M c d)
    (hc : ∀ t ∈ c.left ++ c.right, P t) : ∀ t ∈ d.left ++ d.right, P t := by
  cases h with
  | within h => exact tapeStep_tags M P hwrite h hc
  | extend h =>
      apply tapeStep_tags M P hwrite h
      simpa using (show ∀ t, t ∈ _ ∨ t = clean A.blank → P t from
        fun t ht => ht.elim (fun ht => hc t (by simpa using ht)) (fun ht => ht ▸ hblank))

theorem unboundedRun_tags (P : Tag S Γ → Prop)
    (hblank : P (clean A.blank)) (hwrite : ∀ t a, P t → P (writeWork t a))
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : ReflTransGen (UnboundedStep A M) c d)
    (hc : ∀ t ∈ c.left ++ c.right, P t) : ∀ t ∈ d.left ++ d.right, P t := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact unboundedStep_tags A M P hblank hwrite hs ih

theorem halt_pad {c : Tape (S := S) (Γ := Γ) (Q := Q)} (hc : Halted A M c) (n : ℕ) :
    ∃ t r, (pad A c (n+1)).right = t::r ∧ M.transition c.state t.work = none := by
  rcases c with ⟨q,l,r⟩
  cases r with
  | nil => exact ⟨clean A.blank,List.replicate n (clean A.blank),rfl,hc⟩
  | cons t r => exact ⟨t,r ++ List.replicate (n+1) (clean A.blank),rfl,hc⟩

/-- Full cell list at readout, with the copied anchors on either side. -/
def finalCells (x y : List S) (c : Tape (S := S) (Γ := Γ) (Q := Q)) : Cells S Γ :=
  x.map (readAnchor A · true) ++ [bare A .cutC] ++
    workCells (c.left.reverse ++ c.right) ++ bare A .cutD :: y.map (readAnchor A · true)

theorem finalCells_anchors (x y : List S) (c : Tape (S := S) (Γ := Γ) (Q := Q)) :
    anchorView (finalCells A x y c) = List.replicate (x.length+y.length) none := by
  have hC : anchorView [bare A .cutC] = [] := rfl
  have hD : anchorView (bare A .cutD :: y.map (readAnchor A · true)) =
      List.replicate y.length none := anchorView_readAnchors A y true
  simp only [finalCells,anchorView_append,anchorView_readAnchors,anchorView_workCells,hC,hD]
  simp

theorem finalCells_work (x y : List S) (c : Tape (S := S) (Γ := Γ) (Q := Q))
    (hc : ∀ t ∈ c.left ++ c.right, t.outputRead = false) :
    workView (finalCells A x y c) = ((c.left.reverse ++ c.right).map Tag.work).map (false,·) := by
  have hm : (c.left.reverse ++ c.right).map (fun t => (t.outputRead,t.work)) =
      (c.left.reverse ++ c.right).map (fun t => (false,t.work)) := by
    apply List.map_congr_left
    intro t ht
    have : t.outputRead = false := hc t (by simpa using ht)
    rw [this]
  simpa [finalCells,workView_append,workView,bare,List.filterMap_append,List.filterMap_map,
    workCells,readAnchor,List.map_map,Function.comp_def] using hm

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

theorem copy_correct_pad (x y : List S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨(body A [] x [] y [] (x.length+y.length+n+1)).reverse,.start,[],true,true⟩
      (runSector A (x.map (readAnchor A · true)) (y.map (readAnchor A · true))
        (pad A (initialTape A M (x++y)) (n+1))) := by
  convert copy_correct A M x y n using 1
  simp [runSector,initialTape,pad,workCells,filledWork,bare,List.map_map,
      Function.comp_def,List.append_assoc]
  rfl

theorem halt_readout_pad (x y : List S) (c : Tape (S := S) (Γ := Γ) (Q := Q))
    (hc : Halted A M c) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      (runSector A (x.map (readAnchor A · true)) (y.map (readAnchor A · true)) (pad A c (n+1)))
      ⟨[],.scan .readout,finalCells A x y (pad A c (n+1)),true,true⟩ := by
  obtain ⟨t,r,hr,hh⟩ := halt_pad A M hc n
  have he : pad A c (n+1) = ⟨c.state,c.left,t::r⟩ := by
    cases c
    simp only [pad] at hr ⊢
    rw [hr]
  rw [he]
  exact halt_readout A M _ _ _ _ _ _ hh

omit [DecidableEq Γ] in
theorem unread_pad (c : Tape (S := S) (Γ := Γ) (Q := Q)) (n : ℕ)
    (hc : ∀ t ∈ c.left ++ c.right, t.outputRead = false) :
    ∀ t ∈ (pad A c n).left ++ (pad A c n).right, t.outputRead = false := by
  intro t ht
  simp only [pad_left,pad_right,List.mem_append,List.mem_replicate] at ht
  rcases ht with ht | ht | ⟨_,rfl⟩
  · exact hc t (List.mem_append_left _ ht)
  · exact hc t (List.mem_append_right _ ht)
  · rfl

/-- Adequate quota for every genuinely halting, length-bounded output. This
    connects the actual copy/run/readout table, including empty inputs, without
    assuming a bound on the machine's running time or workspace beforehand. -/
theorem simulation_complete (x y out : List S)
    (c : Tape (S := S) (Γ := Γ) (Q := Q))
    (hrun : ReflTransGen (UnboundedStep A M) (initialTape A M (x++y)) c)
    (hhalt : Halted A M c) (hout : Returns A c out)
    (hlen : out.length ≤ x.length+y.length) :
    ∃ s cells', ReflTransGen (Scan.Step (table A M))
      ⟨(body A [] x [] y [] s).reverse,.start,[],true,true⟩
      ⟨cells'.reverse,.ok,[],true,true⟩ ∧
      anchorView cells' = out.map some ++ List.replicate (x.length+y.length-out.length) none := by
  obtain ⟨n,tail,ho⟩ := hout
  obtain ⟨k,hk,hb⟩ := finite_quota A M hrun (n+1)
  cases k with
  | zero => omega
  | succ k =>
    have hi : ∀ t ∈ (initialTape A M (x++y)).left ++ (initialTape A M (x++y)).right,
        t.outputRead = false := by
      intro t ht
      simp only [initialTape,List.nil_append,List.mem_map] at ht
      obtain ⟨a,_,rfl⟩ := ht
      rfl
    have hc := unboundedRun_tags A M (fun t => t.outputRead = false) rfl
      (fun _ _ ht => ht) hrun hi
    have hwork := finalCells_work A x y (pad A c (n+1)) (unread_pad A c (n+1) hc)
    have he : ((pad A c (n+1)).left.reverse ++ (pad A c (n+1)).right).map Tag.work =
        out.map A.input ++ A.blank::(tail ++ [A.blank]) := by
      simpa [pad,List.map_append,List.map_replicate,clean,List.replicate_succ',
        List.append_assoc] using congrArg (· ++ [A.blank]) ho
    rw [he] at hwork
    have ha : anchorView (finalCells A x y (pad A c (n+1))) =
        ([] : List S).map some ++ List.replicate
          (out.length + (x.length+y.length-out.length)) none := by
      have hn : out.length + (x.length+y.length-out.length) = x.length+y.length := by omega
      simpa [hn] using finalCells_anchors A x y (pad A c (n+1))
    obtain ⟨cells',hr,ha'⟩ := readout_complete A M out (finalCells A x y (pad A c (n+1)))
      [] (tail ++ [A.blank]) [] (x.length+y.length-out.length) (by simpa using hwork) ha
    refine ⟨x.length+y.length+k+1,cells',?_,by simpa using ha'⟩
    exact (copy_correct_pad A M x y k).trans
      ((tapeRun_simulates A M _ _ hb).trans ((halt_readout_pad A M x y c hhalt n).trans hr))

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

/-- The first readout-rewind configuration, before any tape cell is moved. -/
def haltSector (x y : Cells S Γ) (c : Tape (S := S) (Γ := Γ) (Q := Q)) :
    Scan.Sector (Head S Q) (Base S) (Tag S Γ) :=
  ⟨workCells c.left ++ bare A .cutC :: x.reverse, .rewind .readout,
    workCells c.right ++ bare A .cutD :: y,true,true⟩

/-- Exact classification of a simulator step made in a workspace run phase.
    The only intermediate phase is the deterministic half of a left move. -/
theorem run_step_cases (x y : Cells S Γ)
    (c : Tape (S := S) (Γ := Γ) (Q := Q))
    {v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (h : Scan.Step (table A M) (runSector A x y c) v) :
    (∃ d, TapeStep M c d ∧ (v = runSector A x y d ∨
      ((∃ q, v.head = .left q) ∧ Scan.Step (table A M) v (runSector A x y d)))) ∨
    (Halted A M c ∧ v = haltSector A x y c) := by
  rcases c with ⟨q,l,r⟩
  cases r with
  | nil => simp [Scan.Step,quota_exhausted] at h
  | cons t r =>
      cases hc : M.transition q t.work with
      | none =>
          right
          constructor
          · exact hc
          · simpa [Scan.Step,Scan.step,table,cell,runSector,workCells,hc,haltSector] using h.symm
      | some d =>
          left
          cases hm : d.move with
          | stay =>
              refine ⟨⟨d.state,l,writeWork t d.write::r⟩,.stay hc hm,Or.inl ?_⟩
              simpa [Scan.Step,Scan.step,table,cell,runSector,workCells,hc,hm,writeWork] using h.symm
          | right =>
              refine ⟨⟨d.state,writeWork t d.write::l,r⟩,.right hc hm,Or.inl ?_⟩
              simpa [Scan.Step,Scan.step,table,cell,runSector,workCells,hc,hm,writeWork] using h.symm
          | left =>
              have hv : v =
                  ⟨workCells l ++ bare A .cutC :: x.reverse, .left d.state,
                    (.workspace,writeWork t d.write) :: (workCells r ++ bare A .cutD :: y),
                    true,true⟩ := by
                simpa [Scan.Step,Scan.step,table,cell,runSector,workCells,hc,hm,writeWork] using h.symm
              subst v
              cases l with
              | nil =>
                  refine ⟨⟨d.state,[],writeWork t d.write::r⟩,.leftEdge hc hm,
                    Or.inr ⟨⟨d.state,rfl⟩,?_⟩⟩
                  simp [Scan.Step,Scan.step,table,cell,runSector,workCells,bare]
              | cons a l =>
                  refine ⟨⟨d.state,l,a::writeWork t d.write::r⟩,.left hc hm,
                    Or.inr ⟨⟨d.state,rfl⟩,?_⟩⟩
                  simp [Scan.Step,Scan.step,table,cell,runSector,workCells]

/-- Arbitrary accepting paths, not just chosen forward simulations, must have
    exited the run phases through a genuine in-bounds machine halt. -/
theorem simulation_halt_sound (x y : Cells S Γ)
    {c : Tape (S := S) (Γ := Γ) (Q := Q)}
    {v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (h : ReflTransGen (Scan.Step (table A M)) (runSector A x y c) v)
    (hv : v.head = .ok) :
    ∃ d, ReflTransGen (TapeStep M) c d ∧ Halted A M d ∧
      ReflTransGen (Scan.Step (table A M)) (haltSector A x y d) v := by
  have hi :
      (∃ d, ReflTransGen (TapeStep M) c d ∧ v = runSector A x y d) ∨
      (∃ d, ReflTransGen (TapeStep M) c d ∧ (∃ q, v.head = .left q) ∧
        Scan.Step (table A M) v (runSector A x y d)) ∨
      (∃ d, ReflTransGen (TapeStep M) c d ∧ Halted A M d ∧
        ReflTransGen (Scan.Step (table A M)) (haltSector A x y d) v) := by
    clear hv
    induction h with
    | refl => exact Or.inl ⟨c,.refl,rfl⟩
    | @tail v w hpre hs ih =>
        rcases ih with ⟨d,hd,rfl⟩ | ⟨d,hd,_,hf⟩ | ⟨d,hd,hh,hr⟩
        · rcases run_step_cases A M x y d hs with ⟨e,hde,he | ⟨hq,he⟩⟩ | ⟨hh,he⟩
          · exact Or.inl ⟨e,hd.tail hde,he⟩
          · exact Or.inr (Or.inl ⟨e,hd.tail hde,hq,he⟩)
          · exact Or.inr (Or.inr ⟨d,hd,hh,he ▸ ReflTransGen.refl⟩)
        · exact Or.inl ⟨d,hd,Scan.deterministic _ hs hf⟩
        · exact Or.inr (Or.inr ⟨d,hd,hh,hr.tail hs⟩)
  rcases hi with ⟨d,_,hd⟩ | ⟨d,_,⟨q,hq⟩,_⟩ | hgood
  · simp [hd,runSector] at hv
  · simp [hq] at hv
  · exact hgood

end

section
open Relation
variable {S Γ Q : Type*}

theorem tapeRun_interpret (A : Alphabet S Γ) (M : Machine Q Γ)
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : ReflTransGen (TapeStep M) c d) :
    ReflTransGen (SemanticStep M) (interpret A c) (interpret A d) :=
  h.lift (interpret A) (fun _ _ => tapeStep_interpret A M)

theorem semantic_deterministic (M : Machine Q Γ) : Relator.RightUnique (SemanticStep M) := by
  intro a b c hab hac
  exact Option.some.inj (hab.symm.trans hac)

theorem halted_interpret (A : Alphabet S Γ) (M : Machine Q Γ)
    {c : Tape (S := S) (Γ := Γ) (Q := Q)} (h : Halted A M c) :
    Terminal (SemanticStep M) (interpret A c) := by
  intro d hd
  rcases c with ⟨q,l,r⟩
  cases r <;> simp_all [Halted,SemanticStep,semanticStep,interpret,
    Stream'.appendStream',clean,Stream'.head,Stream'.get,Stream'.const,Stream'.cons]

/-- Halts with different finite quotas represent the same semantic output.
    In particular a workspace edge can neither invent a halt nor alter one. -/
theorem halted_quota_unique (A : Alphabet S Γ) (M : Machine Q Γ)
    {start c d : Tape (S := S) (Γ := Γ) (Q := Q)} (n : ℕ)
    (hc : ReflTransGen (TapeStep M) (pad A start n) c)
    (hd : ReflTransGen (UnboundedStep A M) start d)
    (hhc : Halted A M c) (hhd : Halted A M d) : interpret A c = interpret A d := by
  have hci := tapeRun_interpret A M hc
  rw [interpret_pad] at hci
  have hdi := unboundedRun_interpret A M hd
  rcases ReflTransGen.total_of_right_unique (semantic_deterministic M) hci hdi with h | h
  · exact terminal_eq_of_reaches (halted_interpret A M hhc) h
  · exact (terminal_eq_of_reaches (halted_interpret A M hhd) h).symm

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

/-- An accepting terminal cannot be bypassed by any other finite forward path. -/
theorem accepting_after
    {v s w : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (hs : ReflTransGen (Scan.Step (table A M)) v s)
    (hw : ReflTransGen (Scan.Step (table A M)) v w) (hq : w.head = .ok) :
    ReflTransGen (Scan.Step (table A M)) s w := by
  rcases ReflTransGen.total_of_right_unique (Scan.deterministic _) hs hw with h | h
  · exact h
  · have he := terminal_eq_of_reaches (terminal_of_none A M (ok_terminal A M w hq)) h
    exact he ▸ ReflTransGen.refl

/-- Soundness of the output scans, under the literal decoding convention of
    the compiled alphabet. Both the first blank and the anchor quota are forced;
    the result is not an arbitrary truncation of a workspace string. -/
theorem readout_sound
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    (remaining : List Γ) (cells : Cells S Γ) (done : List Γ) (old : List S) (n : ℕ)
    (hw : workView cells = done.map (true,·) ++ remaining.map (false,·))
    (ha : anchorView cells = old.map some ++ List.replicate n none)
    {v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (hv : ReflTransGen (Scan.Step (table A M)) ⟨[],.scan .readout,cells,true,true⟩ v)
    (hq : v.head = .ok) :
    ∃ out tail result, remaining = out.map A.input ++ A.blank::tail ∧ out.length ≤ n ∧
      v = ⟨result.reverse,.ok,[],true,true⟩ ∧
      anchorView result = (old ++ out).map some ++ List.replicate (n-out.length) none := by
  induction remaining generalizing cells done old n with
  | nil =>
      have hr := readout_no_unread A M cells done (by simpa using hw)
      exact False.elim (hr v hv hq)
  | cons g remaining ih =>
      by_cases hg : g = A.blank
      · subst g
        have hr := readout_blank A M cells done (remaining.map (false,·)) (by simpa using hw)
        have he := terminal_eq_of_reaches (terminal_of_none A M
          (ok_terminal A M ⟨cells.reverse,.ok,[],true,true⟩ rfl))
          (accepting_after A M hr hv hq)
        exact ⟨[],remaining,cells,rfl,Nat.zero_le _,he.symm,by simpa using ha⟩
      · cases hg' : A.output g with
        | none =>
            exact False.elim ((readout_invalid A M cells done g (remaining.map (false,·))
              (by simpa using hw) hg hg') v hv hq)
        | some a =>
            cases n with
            | zero =>
                exact False.elim ((readout_no_anchor A M cells done (remaining.map (false,·)) old a g
                  (by simpa using hw) (by simpa using ha) hg hg') v hv hq)
            | succ n =>
                obtain ⟨cells',hr,hw',ha'⟩ := readout_one A M cells done remaining old a g n
                  (by simpa using hw) (by simpa only [List.replicate_succ] using ha) hg hg'
                obtain ⟨out,tail,result,hout,hlen,he,haout⟩ := ih cells' (done ++ [g])
                  (old ++ [a]) n hw' ha' (accepting_after A M hr hv hq)
                refine ⟨a::out,tail,result,?_,by simpa using Nat.succ_le_succ hlen,he,?_⟩
                · simp [hdecode g a hg',hout]
                · simpa [List.append_assoc] using haout

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ)

/-- The output of any bounded accepting computation agrees with the output of
    a genuine unbounded halt, whenever both are expressed in the literal input
    alphabet. This compares different quotas without comparing their padding. -/
theorem returned_quota_unique (M : Machine Q Γ)
    {start c d : Tape (S := S) (Γ := Γ) (Q := Q)} (n : ℕ)
    (hc : ReflTransGen (TapeStep M) (pad A start n) c)
    (hd : ReflTransGen (UnboundedStep A M) start d)
    (hhc : Halted A M c) (hhd : Halted A M d) {x y : List S}
    (hx : Returns A c x) (hy : Returns A d y) : x = y := by
  have he := halted_quota_unique A M n hc hd hhc hhd
  apply semanticReturns_unique A (returns_interpret A hx)
  rw [he]
  exact returns_interpret A hy

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

theorem haltSector_readout (x y : List S) (c : Tape (S := S) (Γ := Γ) (Q := Q)) :
    ReflTransGen (Scan.Step (table A M))
      (haltSector A (x.map (readAnchor A · true)) (y.map (readAnchor A · true)) c)
      ⟨[],.scan .readout,finalCells A x y c,true,true⟩ := by
  simpa [haltSector,finalCells,workCells,List.reverse_append,List.reverse_cons,
    List.map_reverse,List.append_assoc] using
    (rewind A M .readout
      (workCells c.left ++ bare A .cutC :: (x.map (readAnchor A · true)).reverse)
      (workCells c.right ++ bare A .cutD :: y.map (readAnchor A · true)) true)

omit [DecidableEq Γ] in
theorem tapeRun_tags (P : Tag S Γ → Prop)
    (hwrite : ∀ t a, P t → P (writeWork t a))
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : ReflTransGen (TapeStep M) c d)
    (hc : ∀ t ∈ c.left ++ c.right, P t) : ∀ t ∈ d.left ++ d.right, P t := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact tapeStep_tags M P hwrite hs ih

/-- Exact soundness from the fresh validated handoff, with a positive spare
    workspace quota. Arbitrary successes are actual halts returning exactly the
    output marks that cleanup will retain. -/
theorem simulation_sound_sufficient
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    (x y : List S) (n : ℕ)
    {v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (hv : ReflTransGen (Scan.Step (table A M))
      ⟨(body A [] x [] y [] (x.length+y.length+n+1)).reverse,.start,[],true,true⟩ v)
    (hq : v.head = .ok) :
    ∃ c out result,
      ReflTransGen (TapeStep M) (pad A (initialTape A M (x++y)) (n+1)) c ∧
      Halted A M c ∧ Returns A c out ∧ out.length ≤ x.length+y.length ∧
      v = ⟨result.reverse,.ok,[],true,true⟩ ∧
      anchorView result = out.map some ++ List.replicate (x.length+y.length-out.length) none := by
  have hrun := accepting_after A M (copy_correct_pad A M x y n) hv hq
  obtain ⟨c,hc,hh,hr⟩ := simulation_halt_sound A M _ _ hrun hq
  have hi : ∀ t ∈ (initialTape A M (x++y)).left ++ (initialTape A M (x++y)).right,
      t.outputRead = false := by
    intro t ht
    simp only [initialTape,List.nil_append,List.mem_map] at ht
    obtain ⟨a,_,rfl⟩ := ht
    rfl
  have hunread := tapeRun_tags M (fun t => t.outputRead = false) (fun _ _ ht => ht)
    hc (unread_pad A _ (n+1) hi)
  have hr' := accepting_after A M (haltSector_readout A M x y c) hr hq
  obtain ⟨out,tail,result,hout,hlen,he,ha⟩ := readout_sound A M hdecode
    ((c.left.reverse ++ c.right).map Tag.work) (finalCells A x y c) [] []
    (x.length+y.length) (by simpa using finalCells_work A x y c hunread)
    (by simpa using finalCells_anchors A x y c) hr' hq
  exact ⟨c,out,result,hc,hh,⟨0,tail,by simpa using hout⟩,hlen,he,by simpa using ha⟩

end

open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

theorem scan_exhausted (s : Resume S) (cells : Cells S Γ)
    (hp : ∀ c ∈ cells, Pass A M s c) (hb : (table A M).boundary (.scan s) = none) :
    Rejects A M ⟨[],.scan s,cells,true,true⟩ := by
  have hr := Scan.cross_right (table A M) (.scan s) rfl cells [] [] true true hp
  simp only [List.append_nil] at hr
  exact rejects_of_stuck A M hr (by
    change ((table A M).boundary (.scan s)).map _ = none
    rw [hb]; rfl) (by simp)

theorem fill_no_space (xp xs yp ys w : List S) (a : S) :
    Rejects A M ⟨[],.scan (.fill a),body A xp xs yp ys w 0,true,true⟩ := by
  apply scan_exhausted A M _ _ _ rfl
  simp only [body,List.replicate_zero,List.append_nil,List.forall_mem_append,
    List.forall_mem_map,List.forall_mem_singleton]
  simp

/-- Zero spare workspace is a genuine rejection even for empty input. -/
theorem copy_no_space (xp xs yp ys w : List S) :
    Rejects A M ⟨[],.scan .input,body A xp xs yp ys w 0,true,true⟩ := by
  cases xs with
  | cons a xs =>
      let p := xp.map (readAnchor A · true)
      let r := xs.map (readAnchor A · false) ++ [bare A .cutC] ++ w.map (filledWork A) ++
        [bare A .cutD] ++ yp.map (readAnchor A · true) ++ ys.map (readAnchor A · false)
      have h₁ := scan_update A M .input (.fill a) p r (.anchor a)
        (readAnchor A a false).2 (readAnchor A a true).2
        (by change ∀ c ∈ p, Pass A M .input c; simp [p]) (by rfl)
      have hr : ReflTransGen (Scan.Step (table A M))
          ⟨[],.scan .input,body A xp (a::xs) yp ys w 0,true,true⟩
          ⟨[],.scan (.fill a),body A (xp++[a]) xs yp ys w 0,true,true⟩ := by
        simpa [body,p,r,readAnchor,List.append_assoc] using h₁
      exact rejects_before A M hr (fill_no_space A M _ _ _ _ _ a)
  | nil =>
      cases ys with
      | cons a ys =>
          let p := xp.map (readAnchor A · true) ++ [bare A .cutC] ++ w.map (filledWork A) ++
            [bare A .cutD] ++ yp.map (readAnchor A · true)
          let r := ys.map (readAnchor A · false)
          have h₁ := scan_update A M .input (.fill a) p r (.anchor a)
            (readAnchor A a false).2 (readAnchor A a true).2
            (by
              change ∀ c ∈ p, Pass A M .input c
              simp only [p,List.forall_mem_append,List.forall_mem_map,List.forall_mem_singleton]
              simp) (by rfl)
          have hr : ReflTransGen (Scan.Step (table A M))
              ⟨[],.scan .input,body A xp [] yp (a::ys) w 0,true,true⟩
              ⟨[],.scan (.fill a),body A xp [] (yp++[a]) ys w 0,true,true⟩ := by
            simpa [body,p,r,readAnchor,List.append_assoc] using h₁
          exact rejects_before A M hr (fill_no_space A M _ _ _ _ _ a)
      | nil =>
          let cells := body A xp [] yp [] w 0
          have hp : ∀ c ∈ cells, Pass A M .input c := by
            simp only [cells,body,List.map_nil,List.replicate_zero,List.append_nil,
              List.forall_mem_append,List.forall_mem_map,List.forall_mem_singleton]
            simp
          have h₀ := Scan.cross_right (table A M) (.scan .input) rfl cells [] [] true true hp
          have h₁ : Scan.Step (table A M) ⟨cells.reverse,.scan .input,[],true,true⟩
              ⟨cells.reverse,.rewind .spare,[],true,true⟩ := by
            simp [Scan.Step,Scan.step,table]
          have h₂ := rewind A M .spare cells.reverse [] true
          simp only [List.reverse_reverse,List.append_nil] at h₀ h₂
          apply rejects_before A M (h₀.trans ((ReflTransGen.single h₁).trans h₂))
          apply scan_exhausted A M _ _ _ rfl
          simp only [cells,body,List.map_nil,List.replicate_zero,List.append_nil,
            List.forall_mem_append,List.forall_mem_map,List.forall_mem_singleton]
          simp

/-- A quota no larger than the unread input rejects: there must be space for
    every copied letter and also the spare blank tested before running. -/
theorem copy_insufficient (xp xs yp ys w : List S) (n : ℕ)
    (hn : n ≤ xs.length+ys.length) :
    Rejects A M ⟨[],.scan .input,body A xp xs yp ys w n,true,true⟩ := by
  induction n generalizing xp xs yp ys w with
  | zero => exact copy_no_space A M xp xs yp ys w
  | succ n ih =>
      cases xs with
      | cons a xs =>
          apply rejects_before A M (copy_left_one A M xp xs yp ys w a n)
          exact ih _ _ _ _ _ (by simp only [List.length_cons] at hn ⊢; omega)
      | nil =>
          cases ys with
          | nil => simp at hn
          | cons a ys =>
              apply rejects_before A M (copy_right_one A M xp yp ys w a n)
              exact ih _ _ _ _ _ (by simp only [List.length_cons, List.length_nil] at hn ⊢; omega)

/-- Insufficient quota cannot give an accepting computation from a clean
    post-validator handoff, including the zero-workspace and empty-input cases. -/
theorem simulation_insufficient (x y : List S) (s : ℕ) (hs : s ≤ x.length+y.length) :
    Rejects A M ⟨(body A [] x [] y [] s).reverse,.start,[],true,true⟩ :=
  rejects_before A M (start_copy A M _) (copy_insufficient A M [] x [] y [] s hs)

/-- Soundness for *every* clean quota, without a promise that enough was
    inserted. All accepting paths return the genuine first-blank-delimited
    machine output, in input order and within the anchor length bound. -/
theorem simulation_sound
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    (x y : List S) (s : ℕ)
    {v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (hv : ReflTransGen (Scan.Step (table A M))
      ⟨(body A [] x [] y [] s).reverse,.start,[],true,true⟩ v)
    (hq : v.head = .ok) :
    ∃ n c out result, s = x.length+y.length+n+1 ∧
      ReflTransGen (TapeStep M) (pad A (initialTape A M (x++y)) (n+1)) c ∧
      Halted A M c ∧ Returns A c out ∧ out.length ≤ x.length+y.length ∧
      v = ⟨result.reverse,.ok,[],true,true⟩ ∧
      anchorView result = out.map some ++ List.replicate (x.length+y.length-out.length) none := by
  by_cases hs : s ≤ x.length+y.length
  · exact False.elim (simulation_insufficient A M x y s hs v hv hq)
  · let n := s - (x.length+y.length+1)
    have he : s = x.length+y.length+n+1 := by dsimp [n]; omega
    rw [he] at hv
    obtain ⟨c,out,result,h⟩ := simulation_sound_sufficient A M hdecode x y n hv hq
    exact ⟨n,c,out,result,he,h⟩

end FiniteAlgebraicEnvelopes.Compiler.Simulator

end OAI
end

section
-- module Solutions.OAIFAE.Control
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Control.entryDecidable _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Control.successDecidable _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.instPrimcodableSector _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableBaseOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableTagOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite control and bounded compiler orbit normalization.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Cleanup
open Relation
variable {S Γ : Type*}

def Step (blank : Γ) (v w : Sector S Γ) : Prop := step blank v = some w

theorem deterministic (blank : Γ) : Relator.RightUnique (Step (S := S) blank) := by
  intro a b c hab hac
  exact Option.some.inj (hab.symm.trans hac)

/-- Each consumed cell is emitted before all previously emitted cells. This
    proves the leftward cleanup's order on arbitrary—not only clean—data. -/
theorem sweep (blank : Γ) (l r : List (Base S × Tag S Γ)) (a b : Bool) :
    ReflTransGen (Step blank) ⟨l,.cleanup,r,a,b⟩
      ⟨[],.cleanup,output blank l.reverse ++ r,a,b⟩ := by
  induction l generalizing r with
  | nil => exact .refl
  | cons c l ih =>
      have h : Step blank ⟨c::l,.cleanup,r,a,b⟩
          ⟨l,.cleanup,(emit c).toList.map (letter blank) ++ r,a,b⟩ := rfl
      simpa [List.reverse_cons,List.append_assoc] using
        (ReflTransGen.single h).trans (ih ((emit c).toList.map (letter blank) ++ r))

theorem normal_reached (blank : Γ) (v : Sector S Γ) :
    ReflTransGen (Step blank) v (normal blank v) := by
  rcases v with ⟨l,h,r,a,b⟩
  cases h with
  | raw => exact .refl
  | cleanup =>
      have hr := sweep blank l r a b
      cases a with
      | false => exact hr
      | true => exact hr.tail rfl

theorem normal_terminal (blank : Γ) (v : Sector S Γ) :
    step blank (normal blank v) = none := by
  rcases v with ⟨l,h,r,a,b⟩
  cases h <;> cases a <;> rfl

/-- Cleanup normal forms are invariant under either direction of any local
    cleanup equation, including in dirty sectors with missing boundaries. -/
theorem normal_invariant (blank : Γ) {v w : Sector S Γ}
    (h : EqvGen (Step blank) v w) : normal blank v = normal blank w := by
  have tv : ∀ z, ¬Step blank (normal blank v) z := by
    intro z hz
    change step blank (normal blank v) = some z at hz
    rw [normal_terminal] at hz
    cases hz
  have tw : ∀ z, ¬Step blank (normal blank w) z := by
    intro z hz
    change step blank (normal blank w) = some z at hz
    rw [normal_terminal] at hz
    cases hz
  apply terminal_unique (deterministic blank) tv tw
  exact EqvGen.trans _ _ _
    (EqvGen.symm _ _ (EqvGen.reflTransGen_le_eqvGen _ _ _ (normal_reached blank v)))
    (EqvGen.trans _ _ _ h (EqvGen.reflTransGen_le_eqvGen _ _ _ (normal_reached blank w)))

/-- Cleanup forgets empty marks, not anchor order. -/
theorem emit_anchorView (l : List (Base S × Tag S Γ)) :
    l.filterMap emit = (Simulator.anchorView l).filterMap id := by
  rw [Simulator.anchorView,List.filterMap_filterMap]
  congr 1
  funext c
  rcases c with ⟨b,t⟩
  cases b <;> rfl

theorem emit_returned (l : List (Base S × Tag S Γ)) (out : List S) (n : ℕ)
    (h : Simulator.anchorView l = out.map some ++ List.replicate n none) :
    l.filterMap emit = out := by
  rw [emit_anchorView,h,List.filterMap_append]
  simp

/-- Exact successful cleanup, including empty returned strings. -/
theorem success (blank : Γ) (l : List (Base S × Tag S Γ)) (out : List S) (n : ℕ)
    (h : Simulator.anchorView l = out.map some ++ List.replicate n none) :
    ReflTransGen (Step blank) ⟨l.reverse,.cleanup,[],true,true⟩
      ⟨[],.raw,out.map (letter blank),true,true⟩ := by
  have hr := normal_reached blank (⟨l.reverse,.cleanup,[],true,true⟩ : Sector S Γ)
  simpa [normal,output,emit_returned l out n h] using hr

/-- Grade is nonincreasing for EVERY tagged cleanup cell. Workspace marks do
    not emit letters, so grade-zero workspace can never create positive grade. -/
theorem output_grade_le (blank : Γ) (l : List (Base S × Tag S Γ)) :
    cellsGrade (output blank l) ≤ cellsGrade l := by
  induction l with
  | nil => simp [cellsGrade]
  | cons c l ih =>
      rcases c with ⟨b,t⟩
      cases b <;> simp only [output,List.filterMap_cons,emit]
      · cases t.output <;> simp_all [output,cellsGrade,letter,grade]
        omega
      all_goals simp_all [output,cellsGrade,grade]
      all_goals omega

end FiniteAlgebraicEnvelopes.Compiler.Cleanup

namespace FiniteAlgebraicEnvelopes.Compiler.Compiled

section
open Relation
variable {S Γ Q : Type*}

theorem embed_injective : Function.Injective (@embed S Γ Q) := by
  intro a b h
  simpa only [project_embed] using congrArg project h

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ) [DecidableEq Γ]

def MachineRel (a b : Cfg S Γ Q) : Prop :=
  ∃ u v, a = embed u ∧ b = embed v ∧ Scan.Step (Simulator.table A M) u v

def Step : Cfg S Γ Q → Cfg S Γ Q → Prop :=
  Validator.Extended.Step A.blank (MachineRel A M)

theorem machine_deterministic : Relator.RightUnique (MachineRel A M) := by
  rintro a b c ⟨u,v,rfl,rfl,h⟩ ⟨u',v',he,rfl,h'⟩
  cases embed_injective he
  exact congrArg embed (Scan.deterministic _ h h')

theorem deterministic : Relator.RightUnique (Step A M) :=
  Validator.Extended.deterministic A.blank (machine_deterministic A M)

theorem machine_bases (a b : Cfg S Γ Q) (h : MachineRel A M a b) : bases a = bases b := by
  obtain ⟨u,v,rfl,rfl,h⟩ := h
  simpa only [embed_bases] using Scan.step_skeleton _ h

/-- The manuscript's uniqueness of entries, now for the concrete copy/run/read
    table, not for an unspecified simulated relation. -/
theorem entries_unique {a b : Validator.Sector S Γ}
    (ha : Validator.Entry A.blank a) (hb : Validator.Entry A.blank b)
    (h : EqvGen (Step A M) (.inl a) (.inl b)) : a = b :=
  Validator.Extended.entries_unique A.blank Scan.baseSkeleton
    (machine_deterministic A M) (machine_bases A M) ha hb h

theorem embed_step {u v : MachineSector S Γ Q}
    (h : Scan.Step (Simulator.table A M) u v) : Step A M (embed u) (embed v) :=
  .machine (embed_active u) (embed_active v) ⟨u,v,rfl,rfl,h⟩

theorem embed_run {u v : MachineSector S Γ Q}
    (h : ReflTransGen (Scan.Step (Simulator.table A M)) u v) :
    ReflTransGen (Step A M) (embed u) (embed v) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (embed_step A M hs)

theorem validator_run {u v : Validator.Sector S Γ}
    (h : ReflTransGen (Validator.Step A.blank) u v) :
    ReflTransGen (Step A M) (.inl u) (.inl v) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (.validator hs)

theorem active_step {a b : Cfg S Γ Q} (ha : Validator.Extended.Active a)
    (h : Step A M a b) : MachineRel A M a b := by
  cases h with
  | validator h => exact False.elim (Validator.Extended.validator_not_start A.blank h ha)
  | machine _ _ h => exact h

/-- A path retains its actual simulator suffix after the unique validation
    handoff. This rules out a dirty intermediate state being treated as input. -/
theorem path_decomposition {a : Validator.Sector S Γ} {b : Cfg S Γ Q}
    (h : ReflTransGen (Step A M) (.inl a) b) :
    (∃ v, b = .inl v ∧ ReflTransGen (Validator.Step A.blank) a v) ∨
    ∃ v u, ReflTransGen (Validator.Step A.blank) a v ∧ v.head = .start ∧
      b = embed u ∧ ReflTransGen (Scan.Step (Simulator.table A M)) (project (.inl v)) u := by
  induction h with
  | refl => exact Or.inl ⟨a,rfl,.refl⟩
  | @tail b c _ hs ih =>
      rcases ih with ⟨v,rfl,hv⟩ | ⟨v,u,hv,hq,rfl,hr⟩
      · cases hs with
        | validator hs => exact Or.inl ⟨_,rfl,hv.tail hs⟩
        | machine ha _ hs =>
            obtain ⟨u,w,hu,rfl,hw⟩ := hs
            have he : project (.inl v) = u := by rw [hu,project_embed]
            exact Or.inr ⟨v,w,hv,ha,rfl,by rw [he]; exact .single hw⟩
      · obtain ⟨u',w,he,rfl,hw⟩ := active_step A M (embed_active u) hs
        cases embed_injective he
        exact Or.inr ⟨v,w,hv,hq,rfl,hr.tail hw⟩

theorem ok_terminal {v : MachineSector S Γ Q} (hv : v.head = .ok) :
    Terminal (Step A M) (embed v) := by
  intro u h
  have he : embed v = .inr v := by simp [embed,hv]
  rw [he] at h
  cases h with
  | machine _ _ h =>
      obtain ⟨v',w,hv',_,h⟩ := h
      have hsame : v = v' := embed_injective (he.trans hv')
      subst v'
      rw [Scan.Step,Simulator.ok_terminal A M v hv] at h
      contradiction

/-- Arbitrary dirty accepting sectors are unique within a weak component. -/
theorem ok_unique {u v : MachineSector S Γ Q} (hu : u.head = .ok) (hv : v.head = .ok)
    (h : EqvGen (Step A M) (embed u) (embed v)) : u = v :=
  embed_injective (terminal_unique (deterministic A M) (ok_terminal A M hu) (ok_terminal A M hv) h)

end

open Relation
variable {S Γ Q : Type*}

/-- The literal entry and handoff of compiler-clean-entry. -/
def cleanEntry (blank : Γ) (x y : List S) (s : ℕ) : Validator.Sector S Γ :=
  ⟨.initial,List.replicate s (Validator.cell blank .workspace) ++
    Validator.cell blank .cutC :: (x.map (fun a => Validator.cell blank (.anchor a))).reverse,
    Validator.cell blank .cutD :: y.map (fun a => Validator.cell blank (.anchor a)),true,true⟩

@[simp] theorem cleanEntry_entry (blank : Γ) (x y : List S) (s : ℕ) :
    Validator.Entry blank (cleanEntry blank x y s) := ⟨rfl,_,rfl⟩

theorem cleanEntry_reaches (blank : Γ) (x y : List S) (s : ℕ) :
    ReflTransGen (Validator.Step blank) (cleanEntry blank x y s) (handoff blank x y s) :=
  Validator.clean_entry_reaches blank x y s

theorem validator_start_terminal (blank : Γ) {v : Validator.Sector S Γ}
    (hv : v.head = .start) : Terminal (Validator.Step blank) v := by
  intro w h
  exact Validator.Extended.validator_not_start blank h hv

theorem handoff_unique (blank : Γ) (x y : List S) (s : ℕ) {v : Validator.Sector S Γ}
    (h : ReflTransGen (Validator.Step blank) (cleanEntry blank x y s) v)
    (hv : v.head = .start) : v = handoff blank x y s := by
  apply terminal_unique (Validator.step_deterministic blank)
    (validator_start_terminal blank hv) (validator_start_terminal blank rfl)
  exact EqvGen.trans _ _ _
    (EqvGen.symm _ _ (EqvGen.reflTransGen_le_eqvGen _ _ _ h))
    (EqvGen.reflTransGen_le_eqvGen _ _ _ (cleanEntry_reaches blank x y s))

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ) [DecidableEq Γ]

/-- Clean entries that meet an accepting internal sector really passed the
    validator and then ran this very machine. No cleanliness is assumed of the
    sector used for finding its weak component. -/
theorem accepting_entry_runs {a : Validator.Sector S Γ} {b : MachineSector S Γ Q}
    (ha : Validator.Entry A.blank a) (hb : b.head = .ok)
    (h : EqvGen (Step A M) (.inl a) (embed b)) :
    ∃ x y s, a = cleanEntry A.blank x y s ∧
      ReflTransGen (Scan.Step (Simulator.table A M))
        ⟨(Simulator.body A [] x [] y [] s).reverse,.start,[],true,true⟩ b := by
  have hr := reaches_terminal (deterministic A M) (ok_terminal A M hb) h
  rcases path_decomposition A M hr with ⟨v,hv,_⟩ | ⟨v,u,hv,hq,hu,hr⟩
  · simp [embed,hb] at hv
  · have hub : b = u := embed_injective hu
    subst u
    obtain ⟨x,y,s,he⟩ := Validator.passing_entry A.blank ha hv hq
    change a = cleanEntry A.blank x y s at he
    subst a
    have he := handoff_unique A.blank x y s hv hq
    subst v
    exact ⟨x,y,s,rfl,by simpa only [project_handoff] using hr⟩

/-- Concrete soundness part of Lemma compiler-components: true halted output,
    the exact length bound, AND the mandated literal cleanup word. Quota
    insufficiency is ruled out by the previously proved rejection theorem. -/
theorem accepting_entry_sound
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {a : Validator.Sector S Γ} {b : MachineSector S Γ Q}
    (ha : Validator.Entry A.blank a) (hb : b.head = .ok)
    (h : EqvGen (Step A M) (.inl a) (embed b)) :
    ∃ x y s n c out, ∃ (result : List (Base S × Tag S Γ)),
      a = cleanEntry A.blank x y s ∧ s = x.length+y.length+n+1 ∧
      ReflTransGen (Simulator.TapeStep M)
        (Simulator.pad A (Simulator.initialTape A M (x++y)) (n+1)) c ∧
      Simulator.Halted A M c ∧ Simulator.Returns A c out ∧
      out.length ≤ x.length+y.length ∧ b = ⟨result.reverse,.ok,[],true,true⟩ ∧
      ReflTransGen (Cleanup.Step A.blank) ⟨result.reverse,.cleanup,[],true,true⟩
        ⟨[],.raw,out.map (Cleanup.letter A.blank),true,true⟩ := by
  obtain ⟨x,y,s,he,hr⟩ := accepting_entry_runs A M ha hb h
  obtain ⟨n,c,out,result,hs,hc,hhalt,hout,hlen,hb,hres⟩ :=
    Simulator.simulation_sound A M hdecode x y s hr hb
  exact ⟨x,y,s,n,c,out,result,he,hs,hc,hhalt,hout,hlen,hb,
    Cleanup.success A.blank result out _ hres⟩

/-- Conversely an actual finite halted computation with the required output
    bound has some quota and gives entry-to-ok reachability and exact cleanup. -/
theorem clean_success (x y out : List S)
    (c : Simulator.Tape (S := S) (Γ := Γ) (Q := Q))
    (hrun : ReflTransGen (Simulator.UnboundedStep A M) (Simulator.initialTape A M (x++y)) c)
    (hhalt : Simulator.Halted A M c) (hout : Simulator.Returns A c out)
    (hlen : out.length ≤ x.length+y.length) :
    ∃ s, ∃ (result : List (Base S × Tag S Γ)), ReflTransGen (Step A M) (.inl (cleanEntry A.blank x y s))
      (embed ⟨result.reverse,.ok,[],true,true⟩) ∧
      ReflTransGen (Cleanup.Step A.blank) ⟨result.reverse,.cleanup,[],true,true⟩
        ⟨[],.raw,out.map (Cleanup.letter A.blank),true,true⟩ := by
  obtain ⟨s,result,hr,hres⟩ := Simulator.simulation_complete A M x y out c hrun hhalt hout hlen
  refine ⟨s,result,?_,Cleanup.success A.blank result out _ hres⟩
  have hv := validator_run A M (cleanEntry_reaches A.blank x y s)
  have he : (.inl (handoff A.blank x y s) : Cfg S Γ Q) =
      embed ⟨(Simulator.body A [] x [] y [] s).reverse,.start,[],true,true⟩ := by
    rw [← project_handoff]
    rfl
  rw [he] at hv
  exact hv.trans (embed_run A M hr)

end FiniteAlgebraicEnvelopes.Compiler.Compiled

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H H' B T : Type*}

/-- A literal relabeling of finite control commutes with one scan step. Only
    agreement at the current head is needed, permitting fused control tables. -/
theorem step_mapHead (f : H → H') (t : Table H B T) (t' : Table H' B T)
    (v : Sector H B T)
    (hd : t'.direction (f v.head) = t.direction v.head)
    (hc : ∀ b a, t'.cell (f v.head) b a = (t.cell v.head b a).map (mapInstruction f))
    (hb : t'.boundary (f v.head) = (t.boundary v.head).map f) :
    step t' (mapHead f v) = (step t v).map (mapHead f) := by
  rcases v with ⟨l,q,r,a,b⟩
  simp only [mapHead] at hd hc hb ⊢
  unfold step
  simp only [hd]
  cases hdir : t.direction q <;> dsimp only
  · cases l with
    | nil => cases a <;> simp [hb,mapHead,Option.map_map,Function.comp_def]
    | cons c l =>
        rcases c with ⟨base,tag⟩
        dsimp only
        rw [hc]
        cases hcell : t.cell q base tag with
        | none => rfl
        | some ins => rcases ins with ⟨iq,it,ic⟩; cases ic <;> rfl
  · cases r with
    | nil => cases b <;> simp [hb,mapHead,Option.map_map,Function.comp_def]
    | cons c r =>
        rcases c with ⟨base,tag⟩
        dsimp only
        rw [hc]
        cases hcell : t.cell q base tag with
        | none => rfl
        | some ins => rcases ins with ⟨iq,it,ic⟩; cases ic <;> rfl

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Control

section
open Relation
variable {S Γ Q : Type*}

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

theorem step_machine (v : Compiled.MachineSector S Γ Q) :
    Scan.step (table A M) (machine v) = (Scan.step (Simulator.table A M) v).map machine := by
  apply Scan.step_mapHead
  · rfl
  · intro b a; rfl
  · rfl

theorem step_validator (v : Validator.Sector S Γ) (hv : v.head ≠ .start) :
    Scan.step (table A M) (validator v) =
      (Scan.step (Validator.table (S := S) A.blank) (Validator.toScan v)).map (Scan.mapHead validatorHead) := by
  apply Scan.step_mapHead
  · cases v with | mk q l r a b => cases q <;> rfl
  · intro b a
    cases v with | mk q l r ls rs => cases q <;> first | rfl | exact False.elim (hv rfl)
  · cases v with | mk q l r a b => cases q <;> first | rfl | exact False.elim (hv rfl)

end

open Relation
variable {S Γ Q : Type*}

theorem sector_cases (v : Sector S Γ Q) :
    (∃ w : Validator.Sector S Γ, w.head ≠ .start ∧ v = validator w) ∨
    ∃ w : Compiled.MachineSector S Γ Q, v = machine w := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q with
  | machine q => exact Or.inr ⟨⟨l,q,r,a,b⟩,rfl⟩
  | initial => exact Or.inl ⟨⟨.initial,l,r,a,b⟩,by simp,rfl⟩
  | left => exact Or.inl ⟨⟨.left,l,r,a,b⟩,by simp,rfl⟩
  | right => exact Or.inl ⟨⟨.right,l,r,a,b⟩,by simp,rfl⟩
  | workspace => exact Or.inl ⟨⟨.workspace,l,r,a,b⟩,by simp,rfl⟩
  | suffix => exact Or.inl ⟨⟨.suffix,l,r,a,b⟩,by simp,rfl⟩

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

theorem validator_step {v w : Validator.Sector S Γ} (h : Validator.Step A.blank v w) :
    Scan.Step (table A M) (validator v) (validator w) := by
  rw [Scan.Step,step_validator A M v (Validator.Extended.validator_not_start A.blank h),
    Validator.step_toScan A.blank h]
  rfl

theorem machine_step {v w : Compiled.MachineSector S Γ Q}
    (h : Scan.Step (Simulator.table A M) v w) :
    Scan.Step (table A M) (machine v) (machine w) := by
  rw [Scan.Step,step_machine A M,h]
  rfl

theorem cfg_step {v w : Sector S Γ Q} (h : Scan.Step (table A M) v w) :
    Compiled.Step A M (toCfg v) (toCfg w) := by
  rcases sector_cases v with ⟨v,hv,rfl⟩ | ⟨v,rfl⟩
  · rw [Scan.Step,step_validator A M v hv] at h
    obtain ⟨u,hu,rfl⟩ := Option.map_eq_some_iff.mp h
    have he : Scan.mapHead (validatorHead (S := S) (Q := Q)) u =
        validator (Validator.ofScan u) := rfl
    rw [he,cfg_validator,cfg_validator]
    exact .validator (Validator.step_ofScan A.blank hu)
  · rw [Scan.Step,step_machine A M] at h
    obtain ⟨u,hu,rfl⟩ := Option.map_eq_some_iff.mp h
    rw [cfg_machine,cfg_machine]
    exact Compiled.embed_step A M hu

theorem ofCfg_step {v w : Compiled.Cfg S Γ Q} (h : Compiled.Step A M v w) :
    Scan.Step (table A M) (ofCfg v) (ofCfg w) := by
  cases h with
  | validator h => exact validator_step A M h
  | machine _ _ h =>
      obtain ⟨u,v,rfl,rfl,h⟩ := h
      rw [ofCfg_embed,ofCfg_embed]
      exact machine_step A M h

theorem cfg_connected {v w : Sector S Γ Q} (h : EqvGen (Scan.Step (table A M)) v w) :
    EqvGen (Compiled.Step A M) (toCfg v) (toCfg w) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (cfg_step A M h)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

theorem ofCfg_runs {v w : Compiled.Cfg S Γ Q} (h : ReflTransGen (Compiled.Step A M) v w) :
    ReflTransGen (Scan.Step (table A M)) (ofCfg v) (ofCfg w) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (ofCfg_step A M h)

end FiniteAlgebraicEnvelopes.Compiler.Control

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
variable {H B T : Type*} [Fintype H] [Fintype B] [Fintype T]
  [DecidableEq H] [DecidableEq B] [DecidableEq T]

theorem literalComponent_eq (table : Table H B T) {v w : Sector H B T}
    (h : EqvGen (Step table) v w) : literalComponent table v = literalComponent table w := by
  ext u
  simp only [mem_literalComponent]
  exact ⟨fun hv => .trans _ _ _ (.symm _ _ h) hv,fun hw => .trans _ _ _ h hw⟩

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler
variable {α : Type*}

theorem prioritySet_subset (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] (s : Finset α) :
    prioritySet P Q s ⊆ s := by
  unfold prioritySet
  split <;> first | exact Finset.filter_subset _ _ | skip
  split
  · exact Finset.filter_subset _ _
  · exact Finset.Subset.refl _

theorem prioritySet_first (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    {s : Finset α} (hs : ∃ a ∈ s, P a) {b : α} (hb : b ∈ prioritySet P Q s) : P b := by
  have hn : (s.filter P).Nonempty := by
    obtain ⟨a,ha,hp⟩ := hs
    exact ⟨a,Finset.mem_filter.mpr ⟨ha,hp⟩⟩
  rw [prioritySet,ite_eq_left hn] at hb
  exact (Finset.mem_filter.mp hb).2

theorem prioritySet_second (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    {s : Finset α} (hp : ¬ ∃ a ∈ s, P a) (hq : ∃ a ∈ s, Q a)
    {b : α} (hb : b ∈ prioritySet P Q s) : Q b := by
  have hn : ¬ (s.filter P).Nonempty := by
    rintro ⟨a,ha⟩
    exact hp ⟨a,(Finset.mem_filter.mp ha).1,(Finset.mem_filter.mp ha).2⟩
  have hm : (s.filter Q).Nonempty := by
    obtain ⟨a,ha,hq⟩ := hq
    exact ⟨a,Finset.mem_filter.mpr ⟨ha,hq⟩⟩
  rw [prioritySet,ite_eq_right hn,ite_eq_left hm] at hb
  exact (Finset.mem_filter.mp hb).2

end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
variable {H B T : Type*} [Fintype H] [Fintype B] [Fintype T]
  [DecidableEq H] [DecidableEq B] [DecidableEq T] [LinearOrder (Sector H B T)]
variable (table : Table H B T) (P Q : Sector H B T → Prop) [DecidablePred P] [DecidablePred Q]

theorem representative_mem (v : Sector H B T) :
    representative table P Q v ∈ prioritySet P Q (literalComponent table v) :=
  Finset.min'_mem _ _

theorem representative_connected (v : Sector H B T) :
    EqvGen (Step table) v (representative table P Q v) :=
  (mem_literalComponent table _ _).mp
    (prioritySet_subset _ _ _ (representative_mem table P Q v))

theorem representative_eq {v w : Sector H B T} (h : EqvGen (Step table) v w) :
    representative table P Q v = representative table P Q w := by
  unfold representative
  simp only [literalComponent_eq table h]

theorem representative_first (v : Sector H B T)
    (h : ∃ w, EqvGen (Step table) v w ∧ P w) : P (representative table P Q v) := by
  apply prioritySet_first P Q _ (representative_mem table P Q v)
  simpa only [mem_literalComponent] using h

theorem representative_second (v : Sector H B T)
    (hp : ¬ ∃ w, EqvGen (Step table) v w ∧ P w)
    (hq : ∃ w, EqvGen (Step table) v w ∧ Q w) : Q (representative table P Q v) := by
  apply prioritySet_second P Q _ _ (representative_mem table P Q v)
  · simpa only [mem_literalComponent] using hp
  · simpa only [mem_literalComponent] using hq

end FiniteAlgebraicEnvelopes.Compiler.Scan

end OAI
end

section
-- module Solutions.OAIFAE.Surface
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.instPrimcodableSector _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableBaseOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableTagOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Surface alphabet, preprocessing, and grading estimates.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Surface

section
open Relation

variable {S Γ H : Type*}

/-- Literal clean-anchor slides, oriented to the leftmost reachable head gap. -/
inductive RawStep (blank : Γ) : Sector S Γ H → Sector S Γ H → Prop
  | slide (a : S) (l r : Cells S Γ) (lb rb : Bool) :
      RawStep blank ⟨Validator.cell blank (.anchor a)::l,.raw,r,lb,rb⟩
        ⟨l,.raw,Validator.cell blank (.anchor a)::r,lb,rb⟩

theorem rawStep_deterministic (blank : Γ) : Relator.RightUnique (RawStep (H := H) (S := S) blank) := by
  intro a b c hab hac
  cases hab; cases hac; rfl

theorem rawStep_grade (blank : Γ) {v w : Sector S Γ H} (h : RawStep blank v w) :
    grade v = grade w := by
  cases h
  simp [grade,Cleanup.cellsGrade,Validator.cell,Cleanup.grade]
  omega

variable (blank : Γ) [DecidableEq S] [DecidableEq Γ]

theorem rawSweep_reaches (l r : Cells S Γ) (lb rb : Bool) :
    ReflTransGen (RawStep blank) (⟨l,.raw,r,lb,rb⟩ : Sector S Γ H) (rawSweep blank l r lb rb) := by
  induction l generalizing r with
  | nil => exact .refl
  | cons c l ih =>
      rcases c with ⟨b,t⟩
      cases b with
      | anchor a =>
          by_cases ht : t = clean blank
          · subst t
            simpa [rawSweep,Validator.cell] using
              (ReflTransGen.single (RawStep.slide a l r lb rb)).trans
                (ih (Validator.cell blank (.anchor a)::r))
          · simp only [rawSweep,ite_eq_right ht]
            exact .refl
      | cutC | cutD | workspace => exact .refl

theorem rawSweep_terminal (l r : Cells S Γ) (lb rb : Bool) :
    Terminal (RawStep (H := H) blank) (rawSweep blank l r lb rb) := by
  induction l generalizing r with
  | nil => intro w hw; cases hw
  | cons c l ih =>
      rcases c with ⟨b,t⟩
      cases b with
      | anchor a =>
          by_cases ht : t = clean blank
          · simp only [rawSweep,ite_eq_left ht]
            exact ih _
          · simp only [rawSweep,ite_eq_right ht]
            intro w hw
            cases hw
            exact ht rfl
      | cutC | cutD | workspace => intro w hw; cases hw

theorem rawNormal_reaches (v : Sector S Γ H) : ReflTransGen (RawStep blank) v (rawNormal blank v) := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q with
  | raw => exact rawSweep_reaches blank l r a b
  | pending | cleanup | internal _ => exact .refl

theorem rawNormal_terminal (v : Sector S Γ H) : Terminal (RawStep blank) (rawNormal blank v) := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q with
  | raw => exact rawSweep_terminal blank l r a b
  | pending | cleanup | internal _ => intro w hw; cases hw

theorem rawNormal_invariant {v w : Sector S Γ H} (h : EqvGen (RawStep blank) v w) :
    rawNormal blank v = rawNormal blank w := by
  apply terminal_unique (rawStep_deterministic blank) (rawNormal_terminal blank v) (rawNormal_terminal blank w)
  exact .trans _ _ _ (.symm _ _ (EqvGen.reflTransGen_le_eqvGen _ _ _ (rawNormal_reaches blank v)))
    (.trans _ _ _ h (EqvGen.reflTransGen_le_eqvGen _ _ _ (rawNormal_reaches blank w)))

theorem rawNormal_grade (v : Sector S Γ H) : grade (rawNormal blank v) = grade v := by
  have aux : ∀ {a b : Sector S Γ H}, ReflTransGen (RawStep blank) a b → grade b = grade a := by
    intro a b h
    induction h with
    | refl => rfl
    | tail _ h ih => exact (rawStep_grade blank h).symm.trans ih
  exact aux (rawNormal_reaches blank v)

theorem rawSweep_clean (w : List S) (r : Cells S Γ) (lb rb : Bool) :
    rawSweep (H := H) blank (w.map (Validator.cell blank ∘ Base.anchor)) r lb rb =
      ⟨[],.raw,(w.reverse.map (Validator.cell blank ∘ Base.anchor))++r,lb,rb⟩ := by
  induction w generalizing r with
  | nil => rfl
  | cons a w ih =>
      simp only [List.map_cons,Function.comp_apply,Validator.cell,rawSweep,↓reduceIte]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc,Validator.cell]

end

section
open Relation
variable {S Γ H : Type*} (blank : Γ)

/-- The quota rule is applicable only at the literal clean right cut. -/
inductive QuotaStep : Sector S Γ H → Sector S Γ H → Prop
  | trim (l r : Cells S Γ) (lb rb : Bool) :
      QuotaStep ⟨Validator.cell blank .workspace::l,.pending,
          Validator.cell blank .cutD::r,lb,rb⟩
        ⟨l,.pending,Validator.cell blank .cutD::r,lb,rb⟩

theorem quotaStep_deterministic : Relator.RightUnique (QuotaStep (S := S) (H := H) blank) := by
  intro a b c hab hac
  cases hab; cases hac; rfl

theorem quotaStep_grade {v w : Sector S Γ H} (h : QuotaStep blank v w) :
    grade v = grade w := by
  cases h
  simp [grade,Cleanup.cellsGrade,Validator.cell,Cleanup.grade]

theorem quotaStep_left {v w : Sector S Γ H} (h : QuotaStep blank v w) :
    ∃ l, v.left = Validator.cell blank .workspace::l := by
  cases h
  exact ⟨_,rfl⟩

variable [DecidableEq S] [DecidableEq Γ]

theorem trimQuota_terminal (l : Cells S Γ) :
    ∀ r, trimQuota blank l ≠ Validator.cell blank .workspace::r := by
  induction l with
  | nil => intro r h; cases h
  | cons c l ih =>
      by_cases h : c = Validator.cell blank .workspace
      · simpa only [trimQuota,ite_eq_left h] using ih
      · simp only [trimQuota,ite_eq_right h]
        intro r hh
        exact h (List.cons.inj hh).1

theorem trimQuota_reaches (l r : Cells S Γ) (lb rb : Bool) :
    ReflTransGen (QuotaStep blank)
      (⟨l,.pending,Validator.cell blank .cutD::r,lb,rb⟩ : Sector S Γ H)
      ⟨trimQuota blank l,.pending,Validator.cell blank .cutD::r,lb,rb⟩ := by
  induction l with
  | nil => exact .refl
  | cons c l ih =>
      by_cases h : c = Validator.cell blank .workspace
      · subst c
        simpa only [trimQuota,↓reduceIte] using (ReflTransGen.single (QuotaStep.trim l r lb rb)).trans ih
      · simpa only [trimQuota,ite_eq_right h] using
          (ReflTransGen.refl : ReflTransGen (QuotaStep blank)
            (⟨c::l,.pending,Validator.cell blank .cutD::r,lb,rb⟩ : Sector S Γ H) _)

theorem quotaNormal_reaches (v : Sector S Γ H) :
    ReflTransGen (QuotaStep blank) v (quotaNormal blank v) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | pending =>
      cases r with
      | nil => exact .refl
      | cons d r =>
          by_cases h : d = Validator.cell blank .cutD
          · subst d
            simpa only [quotaNormal,↓reduceIte] using trimQuota_reaches blank l r lb rb
          · simp only [quotaNormal,ite_eq_right h]
            exact .refl
  | raw | cleanup | internal _ => exact .refl

theorem quotaNormal_terminal (v : Sector S Γ H) : Terminal (QuotaStep blank) (quotaNormal blank v) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | pending =>
      cases r with
      | nil => intro z hz; cases hz
      | cons d r =>
          by_cases h : d = Validator.cell blank .cutD
          · subst d
            simp only [quotaNormal,↓reduceIte]
            intro z hz
            obtain ⟨l',hl⟩ := quotaStep_left blank hz
            exact trimQuota_terminal blank l l' hl
          · simp only [quotaNormal,ite_eq_right h]
            intro z hz
            cases hz
            exact h rfl
  | raw | cleanup | internal _ => intro z hz; cases hz

theorem quotaNormal_invariant {v w : Sector S Γ H} (h : EqvGen (QuotaStep blank) v w) :
    quotaNormal blank v = quotaNormal blank w := by
  apply terminal_unique (quotaStep_deterministic blank) (quotaNormal_terminal blank v) (quotaNormal_terminal blank w)
  exact .trans _ _ _ (.symm _ _ (EqvGen.reflTransGen_le_eqvGen _ _ _ (quotaNormal_reaches blank v)))
    (.trans _ _ _ h (EqvGen.reflTransGen_le_eqvGen _ _ _ (quotaNormal_reaches blank w)))

theorem quotaNormal_grade (v : Sector S Γ H) : grade (quotaNormal blank v) = grade v := by
  have aux : ∀ {a b : Sector S Γ H}, ReflTransGen (QuotaStep blank) a b → grade b = grade a := by
    intro a b h
    induction h with
    | refl => rfl
    | tail _ h ih => exact (quotaStep_grade blank h).symm.trans ih
  exact aux (quotaNormal_reaches blank v)

theorem pendingPreprocess_invariant {v w : Sector S Γ H} (h : EqvGen (QuotaStep blank) v w) :
    pendingPreprocess blank v = pendingPreprocess blank w := by
  simp only [pendingPreprocess,quotaNormal_invariant blank h]

def listGrade (l : List (Sector S Γ H)) : ℕ := (l.map grade).sum

theorem unmerge_grade (v : Sector S Γ H) : listGrade (unmerge blank v) = grade v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases l with
  | nil => rfl
  | cons c l =>
      cases q with
      | pending =>
          cases r with
          | nil => rfl
          | cons d r =>
              by_cases h : c = Validator.cell blank .cutC ∧ d = Validator.cell blank .cutD
              · rcases h with ⟨rfl,rfl⟩
                simp [unmerge,listGrade,rawNormal_grade]
                simp [grade,Cleanup.cellsGrade,Validator.cell,Cleanup.grade]
                omega
              · simp [unmerge,h,listGrade]
      | raw | cleanup | internal _ => simp [unmerge,listGrade]

theorem pendingPreprocess_grade (v : Sector S Γ H) :
    listGrade (pendingPreprocess blank v) = grade v := by
  rw [pendingPreprocess,unmerge_grade,quotaNormal_grade]

theorem trimQuota_workspace (s : ℕ) (l : Cells S Γ) :
    trimQuota blank (List.replicate s (Validator.cell blank .workspace) ++ l) = trimQuota blank l := by
  induction s with
  | zero => rfl
  | succ s ih => simpa [List.replicate_succ,trimQuota] using ih

/-- The literal merge is undone, even on dirty/incomplete surroundings. -/
theorem pendingPreprocess_merge (l r : Cells S Γ) (s : ℕ) (lb rb : Bool) :
    pendingPreprocess (H := H) blank
      ⟨List.replicate s (Validator.cell blank .workspace) ++ Validator.cell blank .cutC::l,
        .pending,Validator.cell blank .cutD::r,lb,rb⟩ =
      [rawNormal blank ⟨l,.raw,[],lb,true⟩,rawNormal blank ⟨[],.raw,r,true,rb⟩] := by
  simp only [pendingPreprocess,quotaNormal]
  rw [trimQuota_workspace]
  simp [trimQuota,unmerge,Validator.cell]

end

open Relation
variable {S Γ H : Type*}

theorem cleanupNormal_grade (blank : Γ) (v : Sector S Γ H) :
    grade (cleanupNormal blank v) ≤ grade v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | cleanup =>
      have h := Cleanup.output_grade_le blank l.reverse
      rw [Cleanup.cellsGrade_reverse] at h
      simp only [cleanupNormal,Cleanup.normal,ofCleanup,Scan.mapHead,grade,
        Cleanup.cellsGrade_append]
      simp only [Cleanup.cellsGrade,List.map_nil,List.sum_nil] at h ⊢
      cases lb <;> cases rb <;> simp_all
      all_goals omega
  | raw | pending | internal _ => exact le_rfl

variable (blank : Γ) [DecidableEq S] [DecidableEq Γ]

theorem cleanupPreprocess_grade (v : Sector S Γ H) :
    grade (cleanupPreprocess blank v) ≤ grade v := by
  rw [cleanupPreprocess,rawNormal_grade]
  exact cleanupNormal_grade blank v

theorem cleanupPreprocess_invariant {v w : Cleanup.Sector S Γ}
    (h : EqvGen (Cleanup.Step blank) v w) :
    cleanupPreprocess blank (ofCleanup (H := H) v) = cleanupPreprocess blank (ofCleanup w) := by
  simp only [cleanupPreprocess_ofCleanup,Cleanup.normal_invariant blank h]

end FiniteAlgebraicEnvelopes.Compiler.Surface

namespace FiniteAlgebraicEnvelopes.Compiler.Control
open Relation
variable {S Γ Q : Type*}

theorem entry_cases (blank : Γ) {v : Sector S Γ Q} (h : Entry blank v) :
    ∃ w : Validator.Sector S Γ, Validator.Entry blank w ∧ v = validator w := by
  rcases v with ⟨l,q,r,lb,rb⟩
  obtain ⟨rfl,hr⟩ := h
  refine ⟨⟨.initial,l,r,lb,rb⟩,⟨rfl,?_⟩,rfl⟩
  cases r with
  | nil => cases hr
  | cons d r => exact ⟨r,by simpa using hr⟩

theorem entry_validator (blank : Γ) {w : Validator.Sector S Γ} (h : Validator.Entry blank w) :
    Entry blank (validator (Q := Q) w) := by
  rcases w with ⟨q,l,r,lb,rb⟩
  obtain ⟨rfl,r,rfl⟩ := h
  exact ⟨rfl,rfl⟩

theorem success_cases {v : Sector S Γ Q} (h : Success v) :
    ∃ w : Compiled.MachineSector S Γ Q, w.head = .ok ∧ w.right = [] ∧
      w.rightBoundary = true ∧ v = machine w := by
  rcases v with ⟨l,q,r,lb,rb⟩
  obtain ⟨rfl,rfl,rfl⟩ := h
  exact ⟨⟨l,.ok,[],lb,true⟩,rfl,rfl,rfl,rfl⟩

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

theorem entries_unique {v w : Sector S Γ Q} (hv : Entry A.blank v) (hw : Entry A.blank w)
    (h : EqvGen (Scan.Step (table A M)) v w) : v = w := by
  obtain ⟨v,hve,rfl⟩ := entry_cases A.blank hv
  obtain ⟨w,hwe,rfl⟩ := entry_cases A.blank hw
  have hc := cfg_connected A M h
  rw [cfg_validator,cfg_validator] at hc
  exact congrArg validator (Compiled.entries_unique A M hve hwe hc)

theorem successes_unique {v w : Sector S Γ Q} (hv : Success v) (hw : Success w)
    (h : EqvGen (Scan.Step (table A M)) v w) : v = w := by
  obtain ⟨v,hve,_,_,rfl⟩ := success_cases hv
  obtain ⟨w,hwe,_,_,rfl⟩ := success_cases hw
  have hc := cfg_connected A M h
  rw [cfg_machine,cfg_machine] at hc
  exact congrArg machine (Compiled.ok_unique A M hve hwe hc)

variable [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Sector S Γ Q)]

theorem representative_connected (v : Sector S Γ Q) :
    EqvGen (Scan.Step (table A M)) v (representative A M v) :=
  Scan.representative_connected _ _ _ v

theorem representative_eq {v w : Sector S Γ Q}
    (h : EqvGen (Scan.Step (table A M)) v w) : representative A M v = representative A M w :=
  Scan.representative_eq _ _ _ h

theorem representative_entry {v : Sector S Γ Q} (hv : Entry A.blank v) :
    representative A M v = v := by
  apply (entries_unique A M hv _ (representative_connected A M v)).symm
  exact Scan.representative_first _ _ _ v ⟨v,.refl _,hv⟩

theorem representative_success {v : Sector S Γ Q} (hv : Success v)
    (hn : ¬ ∃ w, EqvGen (Scan.Step (table A M)) v w ∧ Entry A.blank w) :
    representative A M v = v := by
  apply (successes_unique A M hv _ (representative_connected A M v)).symm
  exact Scan.representative_second _ _ _ v hn ⟨v,.refl _,hv⟩

end FiniteAlgebraicEnvelopes.Compiler.Control

namespace FiniteAlgebraicEnvelopes.Compiler.Surface

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

theorem internalPreprocess_invariant {v w : Control.Sector S Γ Q}
    (h : EqvGen (Scan.Step (Control.table A M)) v w) :
    internalPreprocess A M v = internalPreprocess A M w := by
  simp only [internalPreprocess,Control.representative_eq A M h]

theorem internalPreprocess_entry (v : Control.Sector S Γ Q) (hv : Control.Entry A.blank v) :
    internalPreprocess A M v = pendingPreprocess A.blank
      ⟨v.left,.pending,v.right,v.leftBoundary,v.rightBoundary⟩ := by
  simp only [internalPreprocess,Control.representative_entry A M hv,ite_eq_left hv]

theorem internalPreprocess_success (v : Control.Sector S Γ Q) (hv : Control.Success v)
    (hn : ¬ ∃ w, EqvGen (Scan.Step (Control.table A M)) v w ∧ Control.Entry A.blank w) :
    internalPreprocess A M v =
      [cleanupPreprocess A.blank ⟨v.left,.cleanup,v.right,v.leftBoundary,v.rightBoundary⟩] := by
  have he : ¬ Control.Entry A.blank v := fun h => hn ⟨v,.refl _,h⟩
  simp only [internalPreprocess,Control.representative_success A M hv hn,ite_eq_right he,ite_eq_left hv]

end

open Relation
variable {S Γ H H' : Type*}

def skeletonGrade (s : List (Base S) × Bool × Bool) : ℕ :=
  (s.1.map Cleanup.grade).sum + 1 + (if s.2.1 then 1 else 0) + (if s.2.2 then 1 else 0)

theorem grade_skeleton (v : Sector S Γ H) : grade v = skeletonGrade (Scan.baseSkeleton v) := by
  simp [grade,skeletonGrade,Scan.baseSkeleton,Cleanup.cellsGrade,List.map_reverse,
    List.map_append,List.map_map]
  omega

theorem grade_eq_of_skeleton {v : Sector S Γ H} {w : Sector S Γ H'}
    (h : Scan.baseSkeleton v = Scan.baseSkeleton w) : grade v = grade w := by
  rw [grade_skeleton,grade_skeleton,h]

variable {Q : Type*} (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

theorem internalPreprocess_grade (v : Control.Sector S Γ Q) :
    listGrade (internalPreprocess A M v) ≤ grade (Scan.mapHead Head.internal v) := by
  have he : grade (Scan.mapHead Head.internal (Control.representative A M v)) =
      grade (Scan.mapHead Head.internal v) := by
    apply grade_eq_of_skeleton
    simp only [Scan.skeleton_mapHead]
    exact (Scan.connected_skeleton _ (Control.representative_connected A M v)).symm
  unfold internalPreprocess
  dsimp only
  split
  · rw [pendingPreprocess_grade]
    exact he.le
  · split
    · simp only [listGrade,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
      exact (cleanupPreprocess_grade A.blank _).trans he.le
    · simpa only [listGrade,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using he.le

theorem preprocess_grade (v : Sector S Γ (Control.Head S Q)) :
    listGrade (preprocess A M v) ≤ grade v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | raw => simp [preprocess,listGrade,rawNormal_grade]
  | pending => exact (pendingPreprocess_grade A.blank _).le
  | cleanup => exact cleanupPreprocess_grade A.blank _
  | internal q => exact internalPreprocess_grade A M ⟨l,q,r,lb,rb⟩

theorem preprocess_rawStep {v w : Sector S Γ (Control.Head S Q)} (h : RawStep A.blank v w) :
    preprocess A M v = preprocess A M w := by
  cases h
  exact congrArg (fun x => [x]) (rawNormal_invariant A.blank (.rel _ _ (.slide _ _ _ _ _)))

theorem preprocess_quotaStep {v w : Sector S Γ (Control.Head S Q)} (h : QuotaStep A.blank v w) :
    preprocess A M v = preprocess A M w := by
  cases h
  exact pendingPreprocess_invariant A.blank (.rel _ _ (.trim _ _ _ _))

theorem preprocess_cleanupStep {v w : Cleanup.Sector S Γ} (h : Cleanup.Step A.blank v w) :
    preprocess A M (ofCleanup v) = preprocess A M (ofCleanup w) := by
  simp only [preprocess_ofCleanup,cleanupPreprocess_invariant A.blank (.rel _ _ h)]

theorem preprocess_entryStep (l r : Cells S Γ) (lb rb : Bool) :
    preprocess A M ⟨l,.pending,Validator.cell A.blank .cutD::r,lb,rb⟩ =
    preprocess A M ⟨l,.internal .initial,Validator.cell A.blank .cutD::r,lb,rb⟩ := by
  exact (internalPreprocess_entry A M
    (⟨l,.initial,Validator.cell A.blank .cutD::r,lb,rb⟩ : Control.Sector S Γ Q) ⟨rfl,rfl⟩).symm

theorem preprocess_internalStep {v w : Control.Sector S Γ Q}
    (h : Scan.Step (Control.table A M) v w) :
    preprocess A M (Scan.mapHead Head.internal v) = preprocess A M (Scan.mapHead Head.internal w) := by
  rcases v with ⟨l,q,r,a,b⟩
  rcases w with ⟨l',q',r',a',b'⟩
  change internalPreprocess A M ⟨l,q,r,a,b⟩ = internalPreprocess A M ⟨l',q',r',a',b'⟩
  exact internalPreprocess_invariant A M (.rel _ _ h)

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
/-- The two outputs of unmerging a *clean full* entry are precisely the two
    full raw words. This includes zero workspace and empty x or y. -/
theorem pendingPreprocess_cleanEntry (x y : List S) (s : ℕ) :
    pendingPreprocess (H := Control.Head S Q) A.blank
      ⟨(Compiled.cleanEntry A.blank x y s).left,.pending,
        (Compiled.cleanEntry A.blank x y s).right,true,true⟩ =
      [raw A.blank x,raw A.blank y] := by
  rw [Compiled.cleanEntry,pendingPreprocess_merge]
  change [rawSweep A.blank ((x.map (Validator.cell A.blank ∘ Base.anchor)).reverse) [] true true,
    raw A.blank y] = [raw A.blank x,raw A.blank y]
  rw [← List.map_reverse,rawSweep_clean]
  simp [raw]

end FiniteAlgebraicEnvelopes.Compiler.Surface

/- Literal path alphabet and sector parsing for the finite compiler.
   All definitions are independent of the partial program. -/

end OAI
end

section
-- module Solutions.OAIFAE.Paths
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Path alphabet, sectors, cuts, and contextual preparation.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Path

section

variable {C H : Type*}

/-- Parallel nonzero equation sides preserve the complete contextual shape,
    including nonpath status. This also covers all length-decreasing cleanup. -/
theorem shape_context {u v : List (Letter C H)} (h : shape u = shape v)
    (x y : List (Letter C H)) : shape (x++u++y) = shape (x++v++y) := by simp [h]

theorem shape_zero_context (x y : List (Letter C H)) :
    shape (x ++ .zero :: y) = .zero := by simp [typeOf]

theorem shape_append_ne_zero {u v : List (Letter C H)} (h : shape (u++v) ≠ .zero) :
    shape u ≠ .zero ∧ shape v ≠ .zero := by
  constructor <;> intro hz <;> apply h <;> simp [hz]

theorem shape_mem_flatten_ne_zero {cs : List (List (Letter C H))}
    (h : shape cs.flatten ≠ .zero) {c : List (Letter C H)} (hc : c ∈ cs) : shape c ≠ .zero := by
  induction cs with
  | nil => simp at hc
  | cons a cs ih =>
    have hh := shape_append_ne_zero h
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hh.1
    · exact ih hh.2 hc

theorem shape_cut_ne_zero {w : List (Letter C H)} (hw : shape w ≠ .zero)
    {c : List (Letter C H)} (hc : c ∈ cuts w) : shape c ≠ .zero := by
  exact shape_mem_flatten_ne_zero (by simpa using hw) hc

theorem Shape.act_comp : ∀ (a b : Shape) (v : Vertex),
    (a*b).act v = (a.act v).bind b.act := by decide

theorem walk_cons (v : Vertex) (a : Letter C H) (w : List (Letter C H)) :
    walk v (a::w) = ((typeOf a).act v).bind (fun z => walk z w) := by
  exact Shape.act_comp _ _ _

theorem exists_walk {w : List (Letter C H)} (h : shape w ≠ .zero) :
    ∃ v z, walk v w = some z := by
  cases he : shape w with
  | zero => exact (h he).elim
  | unit => exact ⟨.outer,.outer,by simp [walk,he,Shape.act]⟩
  | path a b => exact ⟨a,b,by simp [walk,he,Shape.act]⟩

/-- A sector cannot have any omega except its last letter. -/
def terminalLeave : List (Letter C H) → Prop
  | [] => True
  | .leave::w => w = []
  | _::w => terminalLeave w

theorem terminalLeave_cons {a : Letter C H} (ha : a ≠ .leave) (w : List (Letter C H)) :
    terminalLeave (a::w) ↔ terminalLeave w := by cases a <;> simp_all [terminalLeave]

theorem terminalLeave_glue (a : Letter C H) (ha : a ≠ .leave)
    (cs : List (List (Letter C H))) (h : ∀ c ∈ cs, terminalLeave c) :
    ∀ c ∈ glue [a] cs, terminalLeave c := by
  cases cs with
  | nil => simp [glue,terminalLeave_cons ha,terminalLeave]
  | cons c cs =>
    simp only [glue,List.cons_append,List.nil_append,List.mem_cons]
    intro d hd
    rcases hd with rfl | hd
    · exact (terminalLeave_cons ha c).2 (h c (by simp))
    · exact h d (List.mem_cons_of_mem _ hd)

theorem terminalLeave_cuts (w : List (Letter C H)) : ∀ c ∈ cuts w, terminalLeave c := by
  induction w with
  | nil => simp
  | cons a w ih =>
    by_cases ha : a = .leave
    · subst a
      simp only [cuts_leave,List.mem_cons]
      intro c hc
      rcases hc with rfl | hc
      · rfl
      · exact ih c hc
    · rw [cuts_cons ha]
      exact terminalLeave_glue _ ha _ ih

/-- Once a path is at R, its terminal sector consists only of right loops and
    an optional omega. This includes a headless right end-sector. -/
theorem right_form {w : List (Letter C H)} (hn : terminalLeave w) {v : Vertex}
    (h : walk .right w = some v) :
    ∃ r : List C, ∃ rb : Bool, w = r.map .right ++ (if rb then [.leave] else []) := by
  induction w with
  | nil => exact ⟨[],false,rfl⟩
  | cons a w ih =>
    cases a with
    | zero => simp [walk_cons,typeOf,Shape.act] at h
    | enter => simp [walk_cons,typeOf,Shape.act] at h
    | head q => simp [walk_cons,typeOf,Shape.act] at h
    | left c => simp [walk_cons,typeOf,Shape.act] at h
    | leave =>
      have hw : w = [] := hn
      exact ⟨[],true,by simp [hw]⟩
    | right c =>
      have hw : walk .right w = some v := by simpa [walk_cons,typeOf,Shape.act] using h
      obtain ⟨r,rb,he⟩ := ih hn hw
      exact ⟨c::r,rb,by simp [he]⟩

/-- Starting at L, a sector either has no head and only left loops, or has
    exactly one head followed by a right-only tail. -/
theorem left_form {w : List (Letter C H)} (hn : terminalLeave w) {v : Vertex}
    (h : walk .left w = some v) :
    (∃ l : List C, w = l.map .left) ∨
    (∃ l : List C, ∃ q : H, ∃ r : List C, ∃ rb : Bool,
      w = l.map .left ++ [.head q] ++ r.map .right ++ (if rb then [.leave] else [])) := by
  induction w with
  | nil => exact .inl ⟨[],rfl⟩
  | cons a w ih =>
    cases a with
    | zero => simp [walk_cons,typeOf,Shape.act] at h
    | enter => simp [walk_cons,typeOf,Shape.act] at h
    | leave => simp [walk_cons,typeOf,Shape.act] at h
    | right c => simp [walk_cons,typeOf,Shape.act] at h
    | head q =>
      have hw : walk .right w = some v := by simpa [walk_cons,typeOf,Shape.act] using h
      obtain ⟨r,rb,he⟩ := right_form (w := w) hn hw
      exact .inr ⟨[],q,r,rb,by simp [he]⟩
    | left c =>
      have hw : walk .left w = some v := by simpa [walk_cons,typeOf,Shape.act] using h
      rcases ih hn hw with ⟨l,he⟩ | ⟨l,q,r,rb,he⟩
      · exact .inl ⟨c::l,by simp [he]⟩
      · exact .inr ⟨c::l,q,r,rb,by simp [he]⟩

/-- Every nonzero sector is either literally headless or has the precise
    optional-boundary zipper grammar used by the finite component evaluator. -/
theorem sector_form {w : List (Letter C H)} (hn : terminalLeave w)
    (h : shape w ≠ .zero) : heads w = [] ∨
    ∃ l q r lb rb, w = headed l q r lb rb := by
  obtain ⟨v,z,hv⟩ := exists_walk h
  cases v with
  | right =>
    obtain ⟨r,rb,rfl⟩ := right_form hn hv
    left
    cases rb <;> simp [heads,List.filterMap_map]
  | left =>
    rcases left_form hn hv with ⟨l,rfl⟩ | ⟨l,q,r,rb,rfl⟩
    · left; simp [heads,List.filterMap_map]
    · right; exact ⟨l.reverse,q,r,false,rb,by simp [headed]⟩
  | outer =>
    cases w with
    | nil => exact .inl rfl
    | cons a w =>
      cases a with
      | zero => simp [walk_cons,typeOf,Shape.act] at hv
      | leave => simp [walk_cons,typeOf,Shape.act] at hv
      | head q => simp [walk_cons,typeOf,Shape.act] at hv
      | left c => simp [walk_cons,typeOf,Shape.act] at hv
      | right c => simp [walk_cons,typeOf,Shape.act] at hv
      | enter =>
        have hw : walk .left w = some z := by simpa [walk_cons,typeOf,Shape.act] using hv
        rcases left_form (w := w) hn hw with ⟨l,rfl⟩ | ⟨l,q,r,rb,rfl⟩
        · left; simp [heads,List.filterMap_map]
        · right; exact ⟨l.reverse,q,r,true,rb,by simp [headed]⟩

variable [DecidableEq C] [DecidableEq H]

theorem decode_sound {w : List (Letter C H)} {v : Sector C H} (h : decode w = some v) :
    encode v = w := by
  unfold decode at h
  split at h
  · dsimp only at h
    split at h
    · cases h
      assumption
    · cases h
  · cases h

end

section
open Relation
variable {C H : Type*}

/-- A single literal equation step in arbitrary word context. -/
inductive Context (r : List (Letter C H) → List (Letter C H) → Prop) :
    List (Letter C H) → List (Letter C H) → Prop
  | apply (x y : List (Letter C H)) {a b} (h : r a b) :
      Context r (x++a++y) (x++b++y)

theorem context_context {r : List (Letter C H) → List (Letter C H) → Prop}
    {u v : List (Letter C H)} (h : Context r u v) (x y : List (Letter C H)) :
    Context r (x++u++y) (x++v++y) := by
  cases h with
  | apply a b h =>
    simpa only [List.append_assoc] using (Context.apply (x++a) (b++y) h)

theorem reaches_context {r : List (Letter C H) → List (Letter C H) → Prop}
    {u v : List (Letter C H)} (h : ReflTransGen (Context r) u v) (x y : List (Letter C H)) :
    ReflTransGen (Context r) (x++u++y) (x++v++y) :=
  h.lift (fun w => x++w++y) (fun _ _ hh => context_context hh x y)

theorem Shape.middle_zero : ∀ (a b c : Shape), b ≠ .unit →
    ((a*b)*c = .zero ↔ a*b = .zero ∨ b*c = .zero) := by decide

theorem absorb_zero (w : List (Letter C H)) :
    ReflTransGen (Context ZeroStep) (.zero::w) [.zero] := by
  induction w with
  | nil => exact .refl
  | cons a w ih =>
    apply ReflTransGen.head ?_ ih
    exact Context.apply [] w (ZeroStep.pair .zero a rfl)

/-- Every dirty nonpath, including every occurrence of Omega, has a finite
    zero derivation. No simulation, program call, or confluence is used. -/
theorem zero_reaches {w : List (Letter C H)} (h : shape w = .zero) :
    ReflTransGen (Context ZeroStep) w [.zero] := by
  induction w with
  | nil => cases h
  | cons a w ih =>
    cases w with
    | nil =>
      cases a <;> simp only [shape_singleton,typeOf] at h
      · exact .refl
      all_goals cases h
    | cons b w =>
      have hz : (typeOf a * typeOf b) * shape w = .zero := by
        simpa only [shape_cons,mul_assoc] using h
      rcases (Shape.middle_zero _ _ _ (typeOf_ne_unit b)).mp hz with hp | ht
      · exact ReflTransGen.head (Context.apply [] w (ZeroStep.pair a b hp)) (absorb_zero w)
      · have hh := reaches_context (ih ht) [a] []
        have hh' : ReflTransGen (Context ZeroStep) (a::b::w) [a,.zero] := by simpa using hh
        exact hh'.tail (Context.apply [] [] (ZeroStep.pair a .zero (mul_zero _)))

theorem zeroStep_grade (g : C → ℕ) {u v : List (Letter C H)} (h : ZeroStep u v) :
    grade g v ≤ grade g u := by cases h; simp [grade,letterGrade]

end

section
variable {C H : Type*}

/-- Split an arbitrary left context after its last omega. The finished part
    cannot join the sector containing a subsequently inserted head. -/
theorem split_left_context (x : List (Letter C H)) :
    ∃ p a, x = p++a ∧ (.leave : Letter C H) ∉ a ∧
      (p = [] ∨ ∃ t, p = t++[.leave]) := by
  induction x with
  | nil => exact ⟨[],[],rfl,by simp,.inl rfl⟩
  | cons c x ih =>
    obtain ⟨p,a,rfl,ha,hp⟩ := ih
    rcases hp with rfl | ⟨t,rfl⟩
    · by_cases hc : c = .leave
      · subst c
        exact ⟨[.leave],a,rfl,ha,.inr ⟨[],rfl⟩⟩
      · exact ⟨[],c::a,rfl,by simpa using And.intro (Ne.symm hc) ha,.inl rfl⟩
    · exact ⟨c::(t++[.leave]),a,rfl,ha,.inr ⟨c::t,rfl⟩⟩

/-- One delimiter frame works simultaneously for every nonempty replacement
    with no omega. This lemma makes no path or cleanliness assumption. -/
theorem context_frame (x y : List (Letter C H)) :
    ∃ cs a b ds, (.leave : Letter C H) ∉ a ∧ terminalLeave b ∧
      (∀ u : List (Letter C H), u ≠ [] → .leave ∉ u →
        cuts (x++u++y) = cs ++ (a++u++b)::ds) := by
  obtain ⟨p,a,rfl,ha,hp⟩ := split_left_context x
  have hclosed : ∀ v, cuts (p++v) = cuts p ++ cuts v := by
    intro v
    rcases hp with rfl | ⟨t,rfl⟩
    · rfl
    · simpa only [List.append_assoc,List.singleton_append] using cuts_append_leave t v
  cases hy : cuts y with
  | nil =>
    have hy' : y = [] := by simpa using congrArg List.flatten hy
    subst y
    refine ⟨cuts p,a,[],[],ha,trivial,?_⟩
    intro u hu hn
    simp only [List.append_nil,List.append_assoc]
    rw [hclosed,cuts_append_nonleave a _ ha,cuts_of_noLeave u hn]
    cases u with
    | nil => exact (hu rfl).elim
    | cons c u => simp [glue]
  | cons b ds =>
    have hb : terminalLeave b := terminalLeave_cuts y b (by simp [hy])
    refine ⟨cuts p,a,b,ds,ha,hb,?_⟩
    intro u _ hn
    simp only [List.append_assoc]
    rw [hclosed,cuts_append_nonleave a _ ha,
      cuts_append_nonleave u y hn,hy,glue_assoc]
    simp only [glue,List.append_assoc]

 theorem terminalLeave_append_nonleave (a b : List (Letter C H))
    (ha : .leave ∉ a) (hb : terminalLeave b) : terminalLeave (a++b) := by
  induction a with
  | nil => exact hb
  | cons c a ih =>
    have hc : c ≠ .leave := fun h => ha (by simp [h])
    exact (terminalLeave_cons hc _).2 (ih (fun h => ha (List.mem_cons_of_mem _ h)))

/-- The unique designated head identifies its entire host sector, even when
    the surrounding input is malformed. The only premise is literal pathhood. -/
theorem head_context_form {a b : List (Letter C H)} {q : H}
    (hn : terminalLeave (a++ .head q::b)) (h : shape (a++ .head q::b) ≠ .zero) :
    ∃ (l r : List C) (lb rb : Bool), a = (if lb then [.enter] else []) ++ l.reverse.map .left ∧
      b = r.map .right ++ (if rb then [.leave] else []) := by
  rcases sector_form hn h with hh | ⟨l,z,r,lb,rb,he⟩
  · simp only [heads,List.filterMap_append,List.filterMap_cons] at hh
    simp at hh
  · have hp : (.head q : Letter C H) ∉
        (if lb then [Letter.enter] else []) ++ l.reverse.map .left := by
      cases lb <;> simp
    have hs : (.head q : Letter C H) ∉
        r.map .right ++ (if rb then [Letter.leave] else []) := by
      cases rb <;> simp
    have he' : (if lb then [Letter.enter] else []) ++ l.reverse.map .left ++
        .head z::(r.map .right ++ (if rb then [Letter.leave] else [])) = a++ .head q::b := by
      simpa only [headed,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using he.symm
    obtain ⟨ha,_,hb⟩ := (List.append_cons_inj_of_notMem hp hs).mp he'
    exact ⟨l,r,lb,rb,ha.symm,hb.symm⟩

/-- Extract the containing sector in an arbitrary path context. The same
    surrounding sector list works after any head change, or any added left and
    right loops. No claim that sector boundaries survive arbitrary attachment
    of context is built into the statement. -/
theorem head_frame (x y : List (Letter C H)) (q : H)
    (h : shape (x++[.head q]++y) ≠ .zero) :
    ∃ cs ds l r lb rb, ∀ (q' : H) (ls rs : List C),
      cuts (x++ls.map .left++[.head q']++rs.map .right++y) =
        cs ++ [headed (ls.reverse++l) q' (rs++r) lb rb] ++ ds := by
  obtain ⟨cs,a,b,ds,ha,hb,hframe⟩ := context_frame x y
  have hf := hframe [.head q] (by simp) (by simp)
  have hm : shape (a++ .head q::b) ≠ .zero := by
    apply shape_cut_ne_zero h
    simp only [hf,List.mem_append,List.mem_cons]
    exact .inr (.inl (by simp))
  have ht : terminalLeave (a++ .head q::b) :=
    terminalLeave_append_nonleave a _ ha ((terminalLeave_cons (by simp) b).2 hb)
  obtain ⟨l,r,lb,rb,rfl,rfl⟩ := head_context_form ht hm
  refine ⟨cs,ds,l,r,lb,rb,?_⟩
  intro q' ls rs
  have hh := hframe (ls.map .left++[.head q']++rs.map .right) (by simp) (by simp)
  simpa only [headed,List.reverse_append,List.reverse_reverse,List.map_append,
    List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using hh

 theorem split_right_context (y : List (Letter C H)) :
    ∃ b s, y = b++s ∧ terminalLeave b ∧
      (s = [] ∨ ∃ t, b = t++[.leave]) := by
  induction y with
  | nil => exact ⟨[],[],rfl,trivial,.inl rfl⟩
  | cons c y ih =>
    by_cases hc : c = .leave
    · subst c
      exact ⟨[.leave],y,rfl,rfl,.inr ⟨[],rfl⟩⟩
    · obtain ⟨b,s,rfl,hb,hs⟩ := ih
      refine ⟨c::b,s,rfl,(terminalLeave_cons hc b).2 hb,?_⟩
      rcases hs with rfl | ⟨t,rfl⟩
      · exact .inl rfl
      · exact .inr ⟨c::t,rfl⟩

/-- A two-sided delimiter frame, valid even for replacements which change the
    number of heads or create/delete internal visits to the outer vertex. -/
theorem general_context_frame (x y : List (Letter C H)) :
    ∃ cs a b ds, (.leave : Letter C H) ∉ a ∧ terminalLeave b ∧
      (∀ u, cuts (x++u++y) = cs ++ cuts (a++u++b) ++ ds) := by
  obtain ⟨p,a,rfl,ha,hp⟩ := split_left_context x
  obtain ⟨b,s,rfl,hb,hs⟩ := split_right_context y
  have hclosed : ∀ v, cuts (p++v) = cuts p ++ cuts v := by
    intro v
    rcases hp with rfl | ⟨t,rfl⟩
    · rfl
    · simpa only [List.append_assoc,List.singleton_append] using cuts_append_leave t v
  have hright : ∀ v, cuts (v++b++s) = cuts (v++b) ++ cuts s := by
    intro v
    rcases hs with rfl | ⟨t,rfl⟩
    · simp
    · simpa only [List.append_assoc,List.singleton_append] using cuts_append_leave (v++t) s
  refine ⟨cuts p,a,b,cuts s,ha,hb,?_⟩
  intro u
  rw [show (p++a)++u++(b++s) = p++((a++u)++b++s) by simp [List.append_assoc],
    hclosed,hright]
  simp only [List.append_assoc]

/-- Around a fixed head every path context is exactly an arbitrary prefix of
    finished sectors, an optional alpha and left loops, right loops and an
    optional omega, and an arbitrary suffix of sectors. This uniform literal
    identity is also valid for merge and unmerge replacements. -/
theorem word_frame (x y : List (Letter C H)) (q : H)
    (h : shape (x++[.head q]++y) ≠ .zero) :
    ∃ (cs ds : List (List (Letter C H))) (l r : List C) (lb rb : Bool), ∀ u,
      cuts (x++u++y) = cs ++
        cuts (((if lb then [.enter] else []) ++ l.reverse.map .left) ++ u ++
          (r.map .right ++ (if rb then [.leave] else []))) ++ ds := by
  obtain ⟨cs,a,b,ds,ha,hb,hframe⟩ := general_context_frame x y
  have hf := congrArg List.flatten (hframe [.head q])
  simp only [List.flatten_append,flatten_cuts] at hf
  have hm : shape (a++ .head q::b) ≠ .zero := by
    rw [hf] at h
    have hh := (shape_append_ne_zero h).1
    have hh' := (shape_append_ne_zero hh).2
    simpa using hh'
  have ht : terminalLeave (a++ .head q::b) :=
    terminalLeave_append_nonleave a _ ha ((terminalLeave_cons (by simp) b).2 hb)
  obtain ⟨l,r,lb,rb,rfl,rfl⟩ := head_context_form ht hm
  exact ⟨cs,ds,l,r,lb,rb,hframe⟩

end

section
variable {C H : Type*} [DecidableEq C] [DecidableEq H]

/-- All ordinary compiler rules can be checked on a sector with arbitrary
    extra zipper cells. This theorem transports those checks into arbitrary
    literal word contexts, without a cleanliness or boundary promise. -/
theorem prepare_context_headed (P : Sector C H → List (Sector C H))
    (x y : List (Letter C H)) (l₁ l₂ r₁ r₂ : List C) (q₁ q₂ : H)
    (h : shape (x++headed l₁ q₁ r₁ false false++y) ≠ .zero)
    (hinv : ∀ (l r : List C) (lb rb : Bool),
      P ⟨l₁++l,q₁,r₁++r,lb,rb⟩ = P ⟨l₂++l,q₂,r₂++r,lb,rb⟩) :
    prepare P (x++headed l₁ q₁ r₁ false false++y) =
      prepare P (x++headed l₂ q₂ r₂ false false++y) := by
  have hb : shape (x++[.head q₁]++y) ≠ .zero := by
    simpa only [shape_append,shape_headed,shape_singleton,typeOf,Bool.false_eq_true,ite_false] using h
  obtain ⟨cs,ds,l,r,lb,rb,hframe⟩ := head_frame x y q₁ hb
  have hf₁ := hframe q₁ l₁.reverse r₁
  have hf₂ := hframe q₂ l₂.reverse r₂
  simp only [List.reverse_reverse] at hf₁ hf₂
  have h₁ : cuts (x++headed l₁ q₁ r₁ false false++y) =
      cs++[encode (⟨l₁++l,q₁,r₁++r,lb,rb⟩ : Sector C H)]++ds := by
    simpa only [headed,encode,Bool.false_eq_true,ite_false,List.nil_append,List.append_nil,
      List.append_assoc] using hf₁
  have h₂ : cuts (x++headed l₂ q₂ r₂ false false++y) =
      cs++[encode (⟨l₂++l,q₂,r₂++r,lb,rb⟩ : Sector C H)]++ds := by
    simpa only [headed,encode,Bool.false_eq_true,ite_false,List.nil_append,List.append_nil,
      List.append_assoc] using hf₂
  simp only [prepare,h₁,h₂,prepareChunks_append,prepareChunks_singleton,hinv]

end

section
variable {C H : Type*}

 theorem prefix_end_enter {a : List (Letter C H)} {l : List C} {lb : Bool}
    (h : a++[.enter] = (if lb then [.enter] else []) ++ l.reverse.map .left) :
    a = [] ∧ l = [] ∧ lb = true := by
  cases l with
  | nil =>
    cases lb with
    | false => simp at h
    | true =>
      refine ⟨?_,rfl,rfl⟩
      apply List.append_left_injective [.enter]
      simpa using h
  | cons c l =>
    have hh := congrArg (fun w : List (Letter C H) => w.reverse.head?) h
    cases lb <;> simp [List.reverse_cons,List.reverse_append] at hh

 theorem suffix_begin_leave {b : List (Letter C H)} {r : List C} {rb : Bool}
    (h : .leave::b = r.map .right ++ (if rb then [.leave] else [])) :
    b = [] ∧ r = [] ∧ rb = true := by
  cases r with
  | nil => cases rb <;> simp_all
  | cons c r => simp at h

 theorem left_boundary_frame (x y : List (Letter C H)) (q : H)
    (h : shape (x++[.enter,.head q]++y) ≠ .zero) :
    ∃ (cs ds : List (List (Letter C H))) (r : List C) (rb : Bool), ∀ q' : H,
      cuts (x++[.enter,.head q']++y) = cs++[headed [] q' r true rb]++ds := by
  obtain ⟨cs,a,b,ds,ha,hb,hframe⟩ := context_frame x y
  have hf := hframe [.enter,.head q] (by simp) (by simp)
  have hm : shape ((a++[.enter])++ .head q::b) ≠ .zero := by
    apply shape_cut_ne_zero h
    simp only [hf,List.mem_append,List.mem_cons]
    exact .inr (.inl (by simp))
  have ht : terminalLeave ((a++[.enter])++ .head q::b) := by
    apply terminalLeave_append_nonleave
    · simpa using ha
    · exact (terminalLeave_cons (by simp) b).2 hb
  obtain ⟨l,r,lb,rb,hl,hr⟩ := head_context_form ht hm
  obtain ⟨rfl,rfl,rfl⟩ := prefix_end_enter hl
  subst b
  refine ⟨cs,ds,r,rb,?_⟩
  intro q'
  simpa [headed,List.append_assoc] using hframe [.enter,.head q'] (by simp) (by simp)

 theorem right_boundary_frame (x y : List (Letter C H)) (q : H)
    (h : shape (x++[.head q,.leave]++y) ≠ .zero) :
    ∃ (cs ds : List (List (Letter C H))) (l : List C) (lb : Bool), ∀ q' : H,
      cuts (x++[.head q',.leave]++y) = cs++[headed l q' [] lb true]++ds := by
  obtain ⟨p,a,rfl,ha,hp⟩ := split_left_context x
  have hclosed : ∀ v, cuts (p++v) = cuts p ++ cuts v := by
    intro v
    rcases hp with rfl | ⟨t,rfl⟩
    · rfl
    · simpa only [List.append_assoc,List.singleton_append] using cuts_append_leave t v
  have hf : ∀ q' : H, cuts ((p++a)++[.head q',.leave]++y) =
      cuts p ++ (a++[.head q',.leave])::cuts y := by
    intro q'
    simp only [List.append_assoc,List.cons_append,List.nil_append]
    rw [hclosed,cuts_append_nonleave a _ ha,cuts_cons (by simp),cuts_leave]
    simp [glue]
  have hm : shape (a++ .head q::[.leave]) ≠ .zero := by
    apply shape_cut_ne_zero h
    simp only [hf,List.mem_append,List.mem_cons]
    exact .inr (.inl trivial)
  have ht : terminalLeave (a++ .head q::[.leave]) :=
    terminalLeave_append_nonleave a _ ha (by trivial)
  obtain ⟨l,r,lb,rb,hl,hr⟩ := head_context_form ht hm
  obtain ⟨_,rfl,rfl⟩ := suffix_begin_leave hr
  subst a
  refine ⟨cuts p,cuts y,l,lb,?_⟩
  intro q'
  simpa [headed,List.append_assoc] using hf q'

variable [DecidableEq C] [DecidableEq H]

theorem prepare_context_left_boundary (P : Sector C H → List (Sector C H))
    (x y : List (Letter C H)) (q₁ q₂ : H)
    (h : shape (x++[.enter,.head q₁]++y) ≠ .zero)
    (hinv : ∀ (r : List C) (rb : Bool), P ⟨[],q₁,r,true,rb⟩ = P ⟨[],q₂,r,true,rb⟩) :
    prepare P (x++[.enter,.head q₁]++y) = prepare P (x++[.enter,.head q₂]++y) := by
  obtain ⟨cs,ds,r,rb,hframe⟩ := left_boundary_frame x y q₁ h
  simp only [prepare,hframe,prepareChunks_append]
  change prepareChunks P cs ++ prepareChunks P [encode ⟨[],q₁,r,true,rb⟩] ++ prepareChunks P ds =
    prepareChunks P cs ++ prepareChunks P [encode ⟨[],q₂,r,true,rb⟩] ++ prepareChunks P ds
  rw [prepareChunks_singleton,prepareChunks_singleton,hinv]

theorem prepare_context_right_boundary (P : Sector C H → List (Sector C H))
    (x y : List (Letter C H)) (q₁ q₂ : H)
    (h : shape (x++[.head q₁,.leave]++y) ≠ .zero)
    (hinv : ∀ (l : List C) (lb : Bool), P ⟨l,q₁,[],lb,true⟩ = P ⟨l,q₂,[],lb,true⟩) :
    prepare P (x++[.head q₁,.leave]++y) = prepare P (x++[.head q₂,.leave]++y) := by
  obtain ⟨cs,ds,l,lb,hframe⟩ := right_boundary_frame x y q₁ h
  simp only [prepare,hframe,prepareChunks_append]
  change prepareChunks P cs ++ prepareChunks P [encode ⟨l,q₁,[],lb,true⟩] ++ prepareChunks P ds =
    prepareChunks P cs ++ prepareChunks P [encode ⟨l,q₂,[],lb,true⟩] ++ prepareChunks P ds
  rw [prepareChunks_singleton,prepareChunks_singleton,hinv]

end

variable {C H : Type*}

 theorem cuts_join_headed (l r : List C) (q q' : H) (lb rb : Bool) :
    cuts (headed l q [] lb true ++ headed [] q' r true rb) =
      [headed l q [] lb true,headed [] q' r true rb] := by
  let a := (if lb then [Letter.enter] else []) ++ l.reverse.map .left ++ [Letter.head q]
  have ha : headed l q [] lb true = a++[.leave] := by simp [a,headed]
  rw [ha,List.append_assoc,List.singleton_append,cuts_append_leave,←ha,cuts_headed,cuts_headed]
  rfl

variable [DecidableEq C] [DecidableEq H]

/-- Literal merge invariance in every well-typed context, including incomplete
    and dirty outer sectors. The two visits to the outer vertex are explicit. -/
theorem prepare_context_merge (P : Sector C H → List (Sector C H))
    (x y : List (Letter C H)) (q p : H) (c d : C)
    (h : shape (x++[.head q,.leave,.enter,.head q]++y) ≠ .zero)
    (hinv : ∀ (l r : List C) (lb rb : Bool),
      P ⟨c::l,p,d::r,lb,rb⟩ = P ⟨l,q,[],lb,true⟩ ++ P ⟨[],q,r,true,rb⟩) :
    prepare P (x++[.head q,.leave,.enter,.head q]++y) =
      prepare P (x++[.left c,.head p,.right d]++y) := by
  have hb : shape (x++[.head q]++y) ≠ .zero := by
    simpa only [shape_append,shape_cons,shape_nil,typeOf,mul_unit,path_mul_path,
      ite_true] using h
  obtain ⟨cs,ds,l,r,lb,rb,hframe⟩ := word_frame x y q hb
  have hf₁ : cuts (x++[.head q,.leave,.enter,.head q]++y) =
      cs++[encode ⟨l,q,[],lb,true⟩,encode ⟨[],q,r,true,rb⟩]++ds := by
    rw [hframe]
    have he : ((if lb then [Letter.enter] else [])++l.reverse.map .left) ++
        [.head q,.leave,.enter,.head q] ++ (r.map .right++(if rb then [.leave] else [])) =
        headed l q [] lb true ++ headed [] q r true rb := by
      simp [headed,List.append_assoc]
    rw [he,cuts_join_headed]
    rfl
  have hf₂ : cuts (x++[.left c,.head p,.right d]++y) =
      cs++[encode ⟨c::l,p,d::r,lb,rb⟩]++ds := by
    rw [hframe]
    have he : ((if lb then [Letter.enter] else [])++l.reverse.map .left) ++
        [.left c,.head p,.right d] ++ (r.map .right++(if rb then [.leave] else [])) =
        headed (c::l) p (d::r) lb rb := by
      simp [headed,List.reverse_cons,List.map_append,List.append_assoc]
    rw [he,cuts_headed]
    rfl
  unfold prepare
  rw [hf₁,hf₂]
  simp only [prepareChunks,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,prepareChunk_encode,List.append_nil,hinv,List.map_append,
    List.append_assoc]

end FiniteAlgebraicEnvelopes.Compiler.Path

/- Maximal full-raw-run normalization and its one exceptional equation,
   the finite compiler. Nonraw sectors are opaque separators here. -/

end OAI
end

section
-- module Solutions.OAIFAE.Normalization
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.instPrimcodableSector _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableBaseOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableTagOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Raw-run folds, full word compilation, partial budgets, and bounded normalization.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C S : Type*}

variable {f : List S → List S} {m : ℕ}

 theorem prepend_grade (g : C → ℕ) (h : Budget f m) (a : Item C S) (w : List (Item C S))
    (hm : itemGrade g a + grade g w ≤ m) :
    grade g (prepend f a w) ≤ itemGrade g a + grade g w := by
  cases a with
  | inl c => rfl
  | inr x =>
    cases w with
    | nil => rfl
    | cons b w =>
      cases b with
      | inl c => rfl
      | inr y =>
        have hb : (x++y).length ≤ m := by simp only [grade_cons,itemGrade,List.length_append] at *; omega
        have hl := h.length (x++y) hb
        simp only [prepend,grade_cons,itemGrade,List.length_append] at *
        omega

theorem normalize_grade (g : C → ℕ) (h : Budget f m) (w : List (Item C S))
    (hm : grade g w ≤ m) : grade g (normalize f w) ≤ grade g w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hw : grade g w ≤ m := by simp only [grade_cons] at hm; omega
    have hi := ih hw
    exact (prepend_grade g h a (normalize f w) (by simp only [grade_cons] at hm; omega)).trans
      (by simpa only [grade_cons] using Nat.add_le_add_left hi (itemGrade g a))

theorem prepend_pair (g : C → ℕ) (h : Budget f m) (x y : List S) (w : List (Item C S))
    (hm : x.length + y.length + grade g w ≤ m) :
    prepend f (.inr x) (prepend f (.inr y) w) = prepend f (.inr (f (x++y))) w := by
  cases w with
  | nil => rfl
  | cons a w =>
    cases a with
    | inl c => rfl
    | inr z =>
      simp only [prepend]
      congr 2
      apply triple h x y z
      simp only [grade_cons,itemGrade,List.length_append] at *
      omega

/-- Left contexts commute with equality of folded normal forms, without any
    stability-of-sector-boundaries claim. -/
theorem normalize_left_context {u v : List (Item C S)} (h : normalize f u = normalize f v)
    (a : List (Item C S)) : normalize f (a++u) = normalize f (a++v) := by
  induction a with
  | nil => exact h
  | cons a w ih => simpa only [List.cons_append,normalize_cons] using congrArg (prepend f a) ih

/-- Contextual invariance of pair versus its genuine returned singleton; this
    is the only nontrivial comparison at q_ok--cleanup with entry priority. -/
theorem pair_context (g : C → ℕ) (h : Budget f m) (x y : List S) (a b : List (Item C S))
    (hm : grade g (a ++ .inr x :: .inr y :: b) ≤ m) :
    normalize f (a ++ .inr x :: .inr y :: b) =
      normalize f (a ++ .inr (f (x++y)) :: b) := by
  apply normalize_left_context
  simp only [normalize_cons]
  apply prepend_pair g h
  have hb : grade g b ≤ m := by simp only [grade_append,grade_cons,itemGrade] at hm; omega
  have hi := normalize_grade g h b hb
  simp only [grade_append,grade_cons,itemGrade] at hm
  omega

/-- On a raw run of size at least two this fold is exactly a single application
    to the literal concatenation, as specified by the frozen source. -/
theorem normalize_run (h : Budget f m) (x y : List S) (ws : List (List S))
    (hm : (x++y++ws.flatten).length ≤ m) :
    normalize f (((x::y::ws).map Sum.inr) : List (Item C S)) =
      [.inr (f (x++y++ws.flatten))] := by
  induction ws generalizing x y with
  | nil => simp [prepend]
  | cons z ws ih =>
    have hb : (y++z++ws.flatten).length ≤ m := by
      simp only [List.flatten_cons,List.length_append] at hm ⊢
      omega
    rw [List.map_cons,normalize_cons,ih y z hb]
    simp only [prepend]
    congr 2
    simpa [List.append_assoc] using h.context x (y++z++ws.flatten) []
      (by simpa [List.append_assoc] using hm)

theorem splitRun_stops (w : List (Item C S)) :
    (splitRun w).2 = [] ∨ ∃ c t, (splitRun w).2 = .inl c::t := by
  induction w with
  | nil => exact .inl rfl
  | cons a w ih =>
    cases a with
    | inl c => exact .inr ⟨c,w,rfl⟩
    | inr x => exact ih

theorem prepend_append_separator (a : Item C S) (u v : List (Item C S)) (c : C) :
    prepend f a (u ++ .inl c::v) = prepend f a u ++ .inl c::v := by
  cases a <;> cases u with
  | nil => rfl
  | cons b w => cases b <;> rfl

theorem normalize_append_separator (u v : List (Item C S)) (c : C) :
    normalize f (u ++ .inl c::v) = normalize f u ++ .inl c::normalize f v := by
  induction u with
  | nil => rfl
  | cons a w ih =>
    simp only [List.cons_append,normalize_cons,ih,prepend_append_separator]

/-- Bounded comparison with the fold is a theorem, not an alteration of the
    source algorithm. In particular source calls obey the same grade budget. -/
theorem source_eq_normalize (g : C → ℕ) (h : Budget f m) (w : List (Item C S))
    (hm : grade g w ≤ m) : source f w = normalize f w := by
  cases w with
  | nil => simp [source]
  | cons a w =>
    cases a with
    | inl c =>
      have hb : grade g w ≤ m := by simp only [grade_cons] at hm; omega
      simp only [source,normalize_cons,prepend,source_eq_normalize g h w hb]
    | inr x =>
      obtain ⟨ys,t,he⟩ : ∃ ys t, splitRun w = (ys,t) := ⟨_,_,rfl⟩
      have hj : ys.map (Sum.inr : List S → Item C S) ++ t = w := by
        simpa only [he] using splitRun_join w
      have ht : t.length ≤ w.length := by simpa only [he] using splitRun_length w
      have hs : t = [] ∨ ∃ c u, t = .inl c::u := by simpa only [he] using splitRun_stops w
      have hb : grade g t ≤ m := by
        rw [← hj] at hm
        simp only [grade_cons,grade_append,itemGrade] at hm
        omega
      have hi := source_eq_normalize g h t hb
      rw [source,he]
      dsimp only
      rw [hi,← hj]
      cases ys with
      | nil =>
        rcases hs with rfl | ⟨c,u,rfl⟩ <;> rfl
      | cons y ys =>
        have hl : (x++y++ys.flatten).length ≤ m := by
          rw [← hj] at hm
          simp only [grade_cons,itemGrade,grade_append,grade_raws,List.flatten_cons,
            List.length_cons,List.length_append] at hm ⊢
          omega
        have hr := normalize_run (C := C) h x y ys hl
        rcases hs with rfl | ⟨c,u,rfl⟩
        · simpa only [List.append_nil,normalize_nil,List.map_cons,List.flatten_cons,
            List.append_assoc] using hr.symm
        · rw [← List.cons_append,← List.map_cons,normalize_append_separator,hr]
          simp only [List.flatten_cons,List.append_assoc,normalize_cons,prepend,
            List.singleton_append]
termination_by w.length
decreasing_by
  all_goals simp_all only [List.length_cons]
  all_goals omega

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H B T K : Type*}

namespace Literal
open _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path

 theorem cell_step (table : Table H B T) (q : H) (b : B) (t : T)
    (i : Instruction H T) (h : table.cell q b t = some i)
    (l r : List (B×T)) (lb rb : Bool) :
    Step table
      ⟨inLeft (table.direction q) (b,t)++l,q,inRight (table.direction q) (b,t)++r,lb,rb⟩
      ⟨outLeft (table.direction q) i.cross (b,i.tag)++l,i.head,
        outRight (table.direction q) i.cross (b,i.tag)++r,lb,rb⟩ := by
  cases hd : table.direction q <;> cases hc : i.cross <;>
    simp [Step,step,inLeft,inRight,outLeft,outRight,hd,hc,h]

 theorem rule_shape (table : Table H B T) (m : H → K) {u v : List (Letter (B×T) K)}
    (h : Rule table m u v) : shape u = shape v := by
  cases h with
  | cell => simp
  | left => simp [typeOf]
  | right => simp [typeOf]

variable [DecidableEq B] [DecidableEq T] [DecidableEq K]

/-- Sector invariance for a deterministic table implies literal invariance for
    every cell and boundary equation in every word context. -/
theorem prepare_rule (table : Table H B T) (m : H → K)
    (P : Path.Sector (B×T) K → List (Path.Sector (B×T) K))
    (hinv : ∀ v w, Step table v w → P (literal m v) = P (literal m w))
    {u v : List (Letter (B×T) K)} (h : Rule table m u v)
    (x y : List (Letter (B×T) K)) (hn : shape (x++u++y) ≠ .zero) :
    prepare P (x++u++y) = prepare P (x++v++y) := by
  cases h with
  | cell q b t i hi =>
    apply prepare_context_headed P x y _ _ _ _ _ _ hn
    intro l r lb rb
    exact hinv _ _ (cell_step table q b t i hi l r lb rb)
  | left q q' hd hi =>
    apply prepare_context_left_boundary P x y _ _ hn
    intro r rb
    exact hinv ⟨[],q,r,true,rb⟩ ⟨[],q',r,true,rb⟩ (by simp [Step,step,hd,hi])
  | right q q' hd hi =>
    apply prepare_context_right_boundary P x y _ _ hn
    intro l lb
    exact hinv ⟨l,q,[],lb,true⟩ ⟨l,q',[],lb,true⟩ (by simp [Step,step,hd,hi])

end Literal
end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Word

section
open _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path
variable {S Γ Q : Type*}

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

 theorem ordinary_shape {u v : List (Letter S Γ Q)} (h : Ordinary A M u v) : shape u = shape v := by
  cases h with
  | internal h => exact Scan.Literal.rule_shape _ _ h
  | clean c => cases he : Cleanup.emit c <;> simp [Cleanup.letter,typeOf]
  | raw => simp [typeOf]
  | merge => simp [typeOf]
  | quota => simp [typeOf]
  | entry => simp [typeOf]
  | finish => simp [typeOf]

 theorem rule_shape {u v : List (Letter S Γ Q)} (h : Rule A M u v) : shape u = shape v := by
  cases h with
  | ordinary h => exact ordinary_shape A M h
  | zero h => cases h with | pair a b h => simpa [typeOf] using h
  | exit => simp [typeOf]

variable [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)]

/-- Every ordinary source equation has identical preprocessed sector lists in
    any literal nonzero context. Only the accepting exit needs a program law. -/
theorem preprocess_ordinary {u v : List (Letter S Γ Q)} (h : Ordinary A M u v)
    (x y : List (Letter S Γ Q)) (hn : shape (x++u++y) ≠ .zero) :
    preprocess A M (x++u++y) = preprocess A M (x++v++y) := by
  unfold preprocess
  cases h with
  | raw a =>
    apply Path.prepare_context_headed (sectorPreprocess A M) x y
      [Validator.cell A.blank (.anchor a)] [] [] [Validator.cell A.blank (.anchor a)] .raw .raw hn
    intro l r lb rb
    exact congrArg (fun z => z.map (Scan.literal id))
      (Surface.preprocess_rawStep A M (.slide a l r lb rb))
  | merge =>
    apply Path.prepare_context_merge (sectorPreprocess A M) x y .raw .pending _ _ hn
    intro l r lb rb
    change (Surface.pendingPreprocess A.blank
      ⟨Validator.cell A.blank .cutC::l,.pending,Validator.cell A.blank .cutD::r,lb,rb⟩).map _ = _
    rw [show Validator.cell A.blank .cutC::l =
      List.replicate 0 (Validator.cell A.blank .workspace)++Validator.cell A.blank .cutC::l by rfl,
      Surface.pendingPreprocess_merge]
    rfl
  | quota =>
    apply Path.prepare_context_headed (sectorPreprocess A M) x y
      [Validator.cell A.blank .workspace] [] [Validator.cell A.blank .cutD]
      [Validator.cell A.blank .cutD] .pending .pending hn
    intro l r lb rb
    exact congrArg (fun z => z.map (Scan.literal id))
      (Surface.preprocess_quotaStep A M (.trim l r lb rb))
  | entry =>
    apply Path.prepare_context_headed (sectorPreprocess A M) x y [] []
      [Validator.cell A.blank .cutD] [Validator.cell A.blank .cutD] .pending (.internal .initial) hn
    intro l r lb rb
    exact congrArg (fun z => z.map (Scan.literal id)) (Surface.preprocess_entryStep A M l r lb rb)
  | internal h =>
    apply Scan.Literal.prepare_rule _ _ _ ?_ h x y hn
    intro v w hvw
    exact congrArg (fun z => z.map (Scan.literal id)) (Surface.preprocess_internalStep A M hvw)
  | clean c =>
    have hinv := fun l r lb rb => congrArg (fun z => z.map (Scan.literal id))
      (Surface.preprocess_cleanupStep A M (v := ⟨c::l,.cleanup,r,lb,rb⟩)
        (w := ⟨l,.cleanup,(Cleanup.emit c).toList.map (Cleanup.letter A.blank)++r,lb,rb⟩) rfl)
    have hh := Path.prepare_context_headed (sectorPreprocess A M) x y [c] [] []
      ((Cleanup.emit c).toList.map (Cleanup.letter A.blank)) .cleanup .cleanup
    simpa [Path.headed] using hh (by simpa [Path.headed] using hn) hinv
  | finish =>
    apply Path.prepare_context_left_boundary (sectorPreprocess A M) x y .cleanup .raw hn
    intro r rb
    exact congrArg (fun z => z.map (Scan.literal id))
      (Surface.preprocess_cleanupStep A M (v := ⟨[],.cleanup,r,true,rb⟩)
        (w := ⟨[],.raw,r,true,rb⟩) rfl)

end

section
open Relation
variable {S Γ Q : Type*}

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

 theorem sectorPreprocess_grade (v : Sector S Γ Q) :
    chunksGrade ((sectorPreprocess A M v).map Path.encode) ≤ grade (Path.encode v) := by
  have h := Surface.preprocess_grade A M (Scan.unliteral v)
  have he : Path.encode v = encode (Scan.unliteral v) := by simp [encode]
  rw [he,grade_encode]
  simpa only [chunksGrade,sectorPreprocess,List.map_map,Function.comp_def,
    show (fun x : Surface.Sector S Γ (Control.Head S Q) => grade (Path.encode (Scan.literal id x))) =
      Surface.grade from funext grade_encode,Surface.listGrade] using h

 theorem prepareChunk_grade (w : List (Letter S Γ Q)) :
    chunksGrade (Path.prepareChunk (sectorPreprocess A M) w) ≤ grade w := by
  cases he : Path.decode w with
  | none => simp [Path.prepareChunk,he,chunksGrade]
  | some v =>
    have hw := Path.decode_sound he
    rw [←hw]
    simpa using sectorPreprocess_grade A M v

 theorem prepareChunks_grade (ws : List (List (Letter S Γ Q))) :
    chunksGrade (Path.prepareChunks (sectorPreprocess A M) ws) ≤ chunksGrade ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simpa only [Path.prepareChunks,List.flatMap_cons,chunksGrade_append,
      chunksGrade,List.map_cons,List.sum_cons,List.map_append,List.sum_append] using Nat.add_le_add (prepareChunk_grade A M w) ih

 theorem preprocess_grade (w : List (Letter S Γ Q)) :
    chunksGrade (preprocess A M w) ≤ grade w := by
  have h := prepareChunks_grade A M (Path.cuts w)
  simpa only [preprocess,Path.prepare,← chunksGrade_flatten,Path.flatten_cuts] using h

end

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Surface
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- The exact exceptional comparison. When entry priority changes the answer,
    both boundaries really exist, and a bounded run of the specified machine
    returns the output of cleanup. No program equation is assumed here. -/
theorem exit_alternative
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    (l : Cells S Γ) (lb : Bool) :
    preprocess A M ⟨l,.internal (.machine .ok),[],lb,true⟩ =
      preprocess A M ⟨l,.cleanup,[],lb,true⟩ ∨
    ∃ x y out n c,
      preprocess A M ⟨l,.internal (.machine .ok),[],lb,true⟩ =
        [raw A.blank x,raw A.blank y] ∧
      preprocess A M ⟨l,.cleanup,[],lb,true⟩ = [raw A.blank out] ∧
      ReflTransGen (Simulator.TapeStep M)
        (Simulator.pad A (Simulator.initialTape A M (x++y)) (n+1)) c ∧
      Simulator.Halted A M c ∧ Simulator.Returns A c out := by
  let v : Control.Sector S Γ Q := ⟨l,.machine .ok,[],lb,true⟩
  by_cases he : ∃ w, EqvGen (Scan.Step (Control.table A M)) v w ∧ Control.Entry A.blank w
  · obtain ⟨w,hw,hwe⟩ := he
    obtain ⟨a,ha,rfl⟩ := Control.entry_cases A.blank hwe
    have hc := Control.cfg_connected A M (EqvGen.symm _ _ hw)
    change EqvGen (Compiled.Step A M) (Control.toCfg (Control.validator a))
      (Control.toCfg (Control.machine ⟨l,.ok,[],lb,true⟩)) at hc
    rw [Control.cfg_validator,Control.cfg_machine] at hc
    obtain ⟨x,y,s,n,c,out,result,rfl,_,hr,hh,ho,_,hb,hclean⟩ :=
      Compiled.accepting_entry_sound A M hdecode ha rfl hc
    right
    refine ⟨x,y,out,n,c,?_,?_,hr,hh,ho⟩
    · change internalPreprocess A M v = _
      rw [internalPreprocess_invariant A M hw,
        internalPreprocess_entry A M _ (Control.entry_validator A.blank ha)]
      exact pendingPreprocess_cleanEntry A x y s
    · have hn := cleanupPreprocess_invariant (H := Control.Head S Q) A.blank
        (EqvGen.reflTransGen_le_eqvGen _ _ _ hclean)
      have he : (⟨l,.cleanup,[],lb,true⟩ : Cleanup.Sector S Γ) =
          ⟨result.reverse,.cleanup,[],true,true⟩ := by
        have h₁ := congrArg (fun v : Compiled.MachineSector S Γ Q => v.left) hb
        have h₂ := congrArg (fun v : Compiled.MachineSector S Γ Q => v.leftBoundary) hb
        simp only at h₁ h₂
        subst l; subst lb; rfl
      rw [←he] at hn
      change [cleanupPreprocess A.blank (ofCleanup ⟨l,.cleanup,[],lb,true⟩)] = _
      rw [hn]
      rfl
  · left
    exact internalPreprocess_success A M v ⟨rfl,rfl,rfl⟩ he

end FiniteAlgebraicEnvelopes.Compiler.Surface

namespace FiniteAlgebraicEnvelopes.Compiler.Word
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

theorem normal_eq_fold {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m)
    (w : List (Letter S Γ Q)) (hn : Path.shape w ≠ .zero) (hm : grade w ≤ m) :
    normal A M f w =
      (RawRuns.normalize f ((preprocess A M w).map (classify A.blank))).flatMap (realize A.blank) := by
  rw [normal,ite_eq_right hn,RawRuns.source_eq_normalize grade h]
  exact (by rw [classify_grade]; exact (preprocess_grade A M w).trans hm)

theorem normal_ordinary (f : List S → List S) {u v : List (Letter S Γ Q)}
    (h : Ordinary A M u v) (x y : List (Letter S Γ Q)) :
    normal A M f (x++u++y) = normal A M f (x++v++y) := by
  have hs := Path.shape_context (ordinary_shape A M h) x y
  by_cases hn : Path.shape (x++u++y) = .zero
  · simp only [normal,hn,←hs,ite_eq_left]
  · simp only [normal,hn,←hs,ite_false,preprocess_ordinary A M h x y hn]

theorem normal_zero (f : List S → List S) {u v : List (Letter S Γ Q)}
    (h : Path.ZeroStep u v) (x y : List (Letter S Γ Q)) :
    normal A M f (x++u++y) = normal A M f (x++v++y) := by
  have h₁ : Path.shape (x++u++y) = .zero := by
    cases h with
    | pair a b h => simp only [Path.shape_append,Path.shape_cons,Path.shape_nil,
        Path.mul_unit,h,Path.mul_zero,Path.zero_mul]
  have h₂ := Path.shape_context (rule_shape A M (.zero h)) x y
  simp only [normal,h₁,←h₂,ite_eq_left]

/-- Finite tape realization at a bound. This is a *lemma parameter*, not an
    assumption of either main theorem; the partial-recursive adapter must prove it. -/
def ComputesAt (f : List S → List S) (m : ℕ) : Prop :=
  ∀ w, w.length ≤ m → ∃ c,
    ReflTransGen (Simulator.UnboundedStep A M) (Simulator.initialTape A M w) c ∧
    Simulator.Halted A M c ∧ Simulator.Returns A c (f w)

theorem normal_exit
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (a b : List (Letter S Γ Q))
    (h₁ : grade (a++[.head (.internal (.machine .ok)),.leave]++b) ≤ m)
    (h₂ : grade (a++[.head .cleanup,.leave]++b) ≤ m) :
    normal A M f (a++[.head (.internal (.machine .ok)),.leave]++b) =
      normal A M f (a++[.head .cleanup,.leave]++b) := by
  have hs := Path.shape_context (rule_shape A M .exit) a b
  by_cases hn : Path.shape (a++[.head (.internal (.machine .ok)),.leave]++b) = .zero
  · simp only [normal,hn,←hs,ite_eq_left]
  have hn₂ : Path.shape (a++[.head .cleanup,.leave]++b) ≠ .zero := by rwa [←hs]
  obtain ⟨cs,ds,l,lb,hframe⟩ := Path.right_boundary_frame a b (.internal (.machine .ok)) hn
  have hf : ∀ q : Head S Q, preprocess A M (a++[.head q,.leave]++b) =
      Path.prepareChunks (sectorPreprocess A M) cs ++
      (Surface.preprocess A M ⟨l,q,[],lb,true⟩).map encode ++
      Path.prepareChunks (sectorPreprocess A M) ds := by
    intro q
    simp only [preprocess,Path.prepare,hframe,Path.prepareChunks_append]
    change _ ++ Path.prepareChunks (sectorPreprocess A M) [Path.encode (Scan.literal id ⟨l,q,[],lb,true⟩)] ++ _ = _
    rw [Path.prepareChunks_singleton,sectorPreprocess_literal]
    simp only [List.map_map,Function.comp_def]
    rfl
  rcases Surface.exit_alternative A M hdecode l lb with he | ⟨x,y,out,n,c,hx,hy,hr,hh,ho⟩
  · simp only [normal,ite_eq_right hn,ite_eq_right hn₂,hf,he]
  · let p := (Path.prepareChunks (sectorPreprocess A M) cs).map (classify A.blank)
    let q := (Path.prepareChunks (sectorPreprocess A M) ds).map (classify A.blank)
    have hp : (preprocess A M (a++[.head (.internal (.machine .ok)),.leave]++b)).map
        (classify A.blank) = p ++ .inr x :: .inr y :: q := by
      simp only [hf,hx,List.map_cons,List.map_nil,List.map_append]
      change p ++ [classify A.blank (raw A.blank x),classify A.blank (raw A.blank y)] ++ q = _
      simp [List.append_assoc]
    have hq : (preprocess A M (a++[.head .cleanup,.leave]++b)).map (classify A.blank) =
        p ++ .inr out :: q := by
      simp only [hf,hy,List.map_cons,List.map_nil,List.map_append]
      change p ++ [classify A.blank (raw A.blank out)] ++ q = _
      simp [List.append_assoc]
    have hbound : RawRuns.grade grade (p ++ .inr x :: .inr y :: q) ≤ m := by
      rw [←hp,classify_grade]
      exact (preprocess_grade A M _).trans h₁
    have hlen : (x++y).length ≤ m := by
      simp only [RawRuns.grade_append,RawRuns.grade_cons,RawRuns.itemGrade,List.length_append] at hbound ⊢
      omega
    obtain ⟨d,hd,hdh,hdo⟩ := hcomp (x++y) hlen
    have hout : out = f (x++y) := Simulator.returned_quota_unique A M (n+1) hr hd hh hdh ho hdo
    rw [normal_eq_fold A M h _ hn h₁,normal_eq_fold A M h _ hn₂ h₂,hp,hq,hout]
    exact congrArg (fun z => z.flatMap (realize A.blank)) (RawRuns.pair_context grade h x y p q hbound)

/-- Every literal defining equation is invariant in arbitrary word contexts,
    including dirty and incomplete sectors, within the *unchanged* grade bound. -/
theorem normal_rule
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    {u v : List (Letter S Γ Q)} (hr : Rule A M u v) (a b : List (Letter S Γ Q))
    (h₁ : grade (a++u++b) ≤ m) (h₂ : grade (a++v++b) ≤ m) :
    normal A M f (a++u++b) = normal A M f (a++v++b) := by
  cases hr with
  | zero hr => exact normal_zero A M f hr a b
  | ordinary hr => exact normal_ordinary A M f hr a b
  | exit => exact normal_exit A M hdecode h hcomp a b h₁ h₂

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Path
variable {C H : Type*}

theorem context_headed {R : List (Letter C H) → List (Letter C H) → Prop}
    {l₁ l₂ r₁ r₂ : List C} {q₁ q₂ : H}
    (h : R (headed l₁ q₁ r₁ false false) (headed l₂ q₂ r₂ false false))
    (l r : List C) (lb rb : Bool) :
    Context R (headed (l₁++l) q₁ (r₁++r) lb rb)
      (headed (l₂++l) q₂ (r₂++r) lb rb) := by
  have hh := Context.apply ((if lb then [.enter] else []) ++ l.reverse.map .left)
      (r.map .right ++ (if rb then [.leave] else [])) h
  simp only [headed,Bool.false_eq_true,ite_false,List.nil_append,List.append_nil,
    List.reverse_append,List.map_append,List.append_assoc] at hh ⊢
  exact hh

end FiniteAlgebraicEnvelopes.Compiler.Path

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Literal
open _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path
variable {H B T K : Type*}

theorem encode_step (table : Table H B T) (m : H → K) {v w : Sector H B T}
    (h : Step table v w) :
    Context (Rule table m) (Path.encode (literal m v)) (Path.encode (literal m w)) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  unfold Step step at h
  cases hd : table.direction q <;> simp only [hd] at h
  · cases l with
    | nil =>
      cases lb <;> simp only [Bool.false_eq_true,↓reduceIte] at h
      · contradiction
      · obtain ⟨q',hq,rfl⟩ := Option.map_eq_some_iff.mp h
        have hh := Context.apply [] (r.map .right++(if rb then [.leave] else []))
          (Rule.left (table := table) (m := m) q q' hd hq)
        simp only [Path.encode,literal,headed,List.nil_append,List.append_nil,
          List.map_nil,List.reverse_nil,ite_true,List.singleton_append,List.append_assoc] at hh ⊢
        exact hh
    | cons c l =>
      rcases c with ⟨b,t⟩
      obtain ⟨i,hi,rfl⟩ := Option.map_eq_some_iff.mp h
      have hh := context_headed (Rule.cell (table := table) (m := m) q b t i hi) l r lb rb
      cases hc : i.cross <;>
        simpa [Path.encode,literal,inLeft,inRight,outLeft,outRight,hd,hc] using hh
  · cases r with
    | nil =>
      cases rb <;> simp only [Bool.false_eq_true,↓reduceIte] at h
      · contradiction
      · obtain ⟨q',hq,rfl⟩ := Option.map_eq_some_iff.mp h
        have hh := Context.apply ((if lb then [.enter] else [])++l.reverse.map .left) []
          (Rule.right (table := table) (m := m) q q' hd hq)
        simp only [Path.encode,literal,headed,List.append_nil,
          List.map_nil,ite_true,List.append_assoc] at hh ⊢
        exact hh
    | cons c r =>
      rcases c with ⟨b,t⟩
      obtain ⟨i,hi,rfl⟩ := Option.map_eq_some_iff.mp h
      have hh := context_headed (Rule.cell (table := table) (m := m) q b t i hi) l r lb rb
      cases hc : i.cross <;>
        simpa [Path.encode,literal,inLeft,inRight,outLeft,outRight,hd,hc] using hh

end FiniteAlgebraicEnvelopes.Compiler.Scan.Literal

namespace FiniteAlgebraicEnvelopes.Compiler.Word
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

/-- A literal equation in either direction, used without any grade increase. -/
def Reduce (u v : List (Letter S Γ Q)) : Prop :=
  Path.Context (SymmGen (Rule A M)) u v ∧ grade v ≤ grade u
abbrev Reduces := ReflTransGen (Reduce A M)

theorem reduces_grade {u v : List (Letter S Γ Q)} (h : Reduces A M u v) : grade v ≤ grade u := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact h.2.trans ih

theorem reduce_context {u v : List (Letter S Γ Q)} (h : Reduce A M u v)
    (x y : List (Letter S Γ Q)) : Reduce A M (x++u++y) (x++v++y) := by
  refine ⟨Path.context_context h.1 x y,?_⟩
  simpa only [grade_append] using Nat.add_le_add_right (Nat.add_le_add_left h.2 (grade x)) (grade y)

theorem reduces_context {u v : List (Letter S Γ Q)} (h : Reduces A M u v)
    (x y : List (Letter S Γ Q)) : Reduces A M (x++u++y) (x++v++y) :=
  h.lift (fun w => x++w++y) (fun _ _ hh => reduce_context A M hh x y)

theorem reduces_append {u v x y : List (Letter S Γ Q)}
    (h₁ : Reduces A M u v) (h₂ : Reduces A M x y) : Reduces A M (u++x) (v++y) := by
  have ha : Reduces A M (u++x) (v++x) := by simpa using reduces_context A M h₁ [] x
  have hb : Reduces A M (v++x) (v++y) := by simpa using reduces_context A M h₂ v []
  exact ha.trans hb

variable [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)]

theorem normal_reduce
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    {u v : List (Letter S Γ Q)} (hr : Reduce A M u v) (hm : grade u ≤ m) :
    normal A M f u = normal A M f v := by
  have hv := hr.2.trans hm
  rcases hr with ⟨hr,_⟩
  cases hr with
  | apply x y hr =>
    rcases hr with hr | hr
    · exact normal_rule A M hdecode h hcomp hr x y hm hv
    · exact (normal_rule A M hdecode h hcomp hr x y hv hm).symm

theorem normal_reduces
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    {u v : List (Letter S Γ Q)} (hr : Reduces A M u v) (hm : grade u ≤ m) :
    normal A M f u = normal A M f v := by
  induction hr with
  | refl => rfl
  | tail hp hs ih => exact ih.trans (normal_reduce A M hdecode h hcomp hs ((reduces_grade A M hp).trans hm))

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Path
variable {C H : Type*}

theorem context_mono {R T : List (Letter C H) → List (Letter C H) → Prop}
    {u v : List (Letter C H)} (h : Context R u v) (ht : ∀ a b, R a b → T a b) : Context T u v := by
  cases h with
  | apply x y h => exact .apply x y (ht _ _ h)

open Relation
theorem context_symm {R : List (Letter C H) → List (Letter C H) → Prop}
    {u v : List (Letter C H)} (h : Context (SymmGen R) u v) : Context (SymmGen R) v u := by
  cases h with
  | apply x y h => exact .apply x y (Or.symm h)

end FiniteAlgebraicEnvelopes.Compiler.Path

namespace FiniteAlgebraicEnvelopes.Compiler.Word

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

theorem internal_rule_grade {u v : List (Letter S Γ Q)}
    (h : Scan.Literal.Rule (Control.table A M) Surface.Head.internal u v) : grade u = grade v := by
  cases h with
  | cell q b t i hi =>
    cases hd : (Control.table A M).direction q <;> cases hc : i.cross <;>
      simp [grade,Path.grade_headed,Scan.Literal.inLeft,Scan.Literal.inRight,
        Scan.Literal.outLeft,Scan.Literal.outRight,gradeCell,Nat.add_comm]
  | left => rfl
  | right => rfl

theorem ordinary_grade {u v : List (Letter S Γ Q)} (h : Ordinary A M u v) : grade v ≤ grade u := by
  cases h with
  | internal h => exact (internal_rule_grade A M h).symm.le
  | clean c =>
    have hh := Cleanup.output_grade_le A.blank [c]
    simp only [Cleanup.output_singleton,Cleanup.cellsGrade,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      Nat.add_zero,Function.comp_def] at hh
    simpa [grade,Path.grade,Path.letterGrade,List.map_map,Function.comp_def,gradeCell,Nat.add_comm] using Nat.add_le_add_left hh 1
  | raw | merge | quota | entry | finish =>
    simp [grade,Path.grade,Path.letterGrade,gradeCell,Validator.cell,Cleanup.grade]

theorem rule_grade {u v : List (Letter S Γ Q)} (h : Rule A M u v) : grade v ≤ grade u := by
  cases h with
  | ordinary h => exact ordinary_grade A M h
  | zero h => exact Path.zeroStep_grade gradeCell h
  | exit => rfl

theorem reduce_rule {u v : List (Letter S Γ Q)} (h : Rule A M u v) : Reduce A M u v := by
  refine ⟨?_,rule_grade A M h⟩
  simpa using Path.Context.apply [] [] (Or.inl h : SymmGen (Rule A M) u v)

theorem reduce_rule_reverse {u v : List (Letter S Γ Q)} (h : Rule A M u v)
    (hg : grade u = grade v) : Reduce A M v u := by
  refine ⟨?_,hg.le⟩
  simpa using Path.Context.apply [] [] (Or.inr h : SymmGen (Rule A M) v u)

theorem reduce_internal {v w : Control.Sector S Γ Q} (h : Scan.Step (Control.table A M) v w) :
    Reduce A M (encode (Scan.mapHead Surface.Head.internal v))
      (encode (Scan.mapHead Surface.Head.internal w)) ∧
    Reduce A M (encode (Scan.mapHead Surface.Head.internal w))
      (encode (Scan.mapHead Surface.Head.internal v)) := by
  have hc := Scan.Literal.encode_step (Control.table A M) Surface.Head.internal h
  have hg : grade (encode (Scan.mapHead Surface.Head.internal v)) =
      grade (encode (Scan.mapHead Surface.Head.internal w)) := by
    rw [grade_encode,grade_encode]
    apply Surface.grade_eq_of_skeleton
    simpa using Scan.step_skeleton _ h
  have hf : Path.Context (SymmGen (Rule A M)) (encode (Scan.mapHead Surface.Head.internal v))
      (encode (Scan.mapHead Surface.Head.internal w)) :=
    Path.context_mono hc (fun _ _ hs => .inl (.ordinary (.internal hs)))
  refine ⟨⟨hf,hg.symm.le⟩,⟨?_,hg.le⟩⟩
  exact Path.context_symm hf

theorem reduces_internal {v w : Control.Sector S Γ Q}
    (h : EqvGen (Scan.Step (Control.table A M)) v w) :
    Reduces A M (encode (Scan.mapHead Surface.Head.internal v))
      (encode (Scan.mapHead Surface.Head.internal w)) := by
  have hh : ∀ {v w : Control.Sector S Γ Q}, EqvGen (Scan.Step (Control.table A M)) v w →
      Reduces A M (encode (Scan.mapHead Surface.Head.internal v))
        (encode (Scan.mapHead Surface.Head.internal w)) ∧
      Reduces A M (encode (Scan.mapHead Surface.Head.internal w))
        (encode (Scan.mapHead Surface.Head.internal v)) := by
    intro v w h
    induction h with
    | rel _ _ h => exact ⟨.single (reduce_internal A M h).1,.single (reduce_internal A M h).2⟩
    | refl _ => exact ⟨.refl,.refl⟩
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1,ih₂.2.trans ih₁.2⟩
  exact (hh h).1

theorem reduce_of_context_rule {u v : List (Letter S Γ Q)} (h : Path.Context (Rule A M) u v) :
    Reduce A M u v := by
  refine ⟨Path.context_mono h (fun _ _ hh => .inl hh),?_⟩
  cases h with
  | apply x y h =>
    simp only [grade_append]
    exact Nat.add_le_add_right (Nat.add_le_add_left (rule_grade A M h) _) _

theorem reduce_reverse {u v : List (Letter S Γ Q)} (h : Reduce A M u v)
    (hg : grade u = grade v) : Reduce A M v u := ⟨Path.context_symm h.1,hg.le⟩

theorem reduces_reverse {u v : List (Letter S Γ Q)} (h : Reduces A M u v)
    (hg : grade u = grade v) : Reduces A M v u := by
  induction h with
  | refl => exact .refl
  | @tail v w hp hs ih =>
    have h₁ := reduces_grade A M hp
    have h₂ := hs.2
    have he : grade u = grade v := by omega
    have he' : grade v = grade w := by omega
    exact (ReflTransGen.single (reduce_reverse A M hs he')).trans (ih he)

theorem reduce_headed {l₁ l₂ r₁ r₂ : List (Cell S Γ)} {q₁ q₂ : Head S Q}
    (h : Rule A M (Path.headed l₁ q₁ r₁ false false) (Path.headed l₂ q₂ r₂ false false))
    (l r : List (Cell S Γ)) (lb rb : Bool) :
    Reduce A M (encode ⟨l₁++l,q₁,r₁++r,lb,rb⟩) (encode ⟨l₂++l,q₂,r₂++r,lb,rb⟩) :=
  reduce_of_context_rule A M (Path.context_headed h l r lb rb)

theorem reduce_rawStep {v w : Surface.Sector S Γ (Control.Head S Q)}
    (h : Surface.RawStep A.blank v w) : Reduce A M (encode v) (encode w) := by
  cases h with
  | slide a l r lb rb =>
    apply reduce_headed A M (l₁ := [Validator.cell A.blank (.anchor a)]) (l₂ := [])
      (r₁ := []) (r₂ := [Validator.cell A.blank (.anchor a)]) ?_ l r lb rb
    simpa [Path.headed] using (Rule.ordinary (Ordinary.raw (A := A) (M := M) a))

theorem reduces_rawNormal (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) (encode (Surface.rawNormal A.blank v)) :=
  (Surface.rawNormal_reaches A.blank v).lift encode (fun _ _ h => reduce_rawStep A M h)

theorem reduces_quotaNormal (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) (encode (Surface.quotaNormal A.blank v)) := by
  apply (Surface.quotaNormal_reaches A.blank v).lift encode
  intro v w h
  cases h with
  | trim l r lb rb =>
    apply reduce_headed A M (l₁ := [Validator.cell A.blank .workspace]) (l₂ := [])
      (r₁ := [Validator.cell A.blank .cutD]) (r₂ := [Validator.cell A.blank .cutD]) ?_ l r lb rb
    simpa [Path.headed] using (Rule.ordinary (Ordinary.quota (A := A) (M := M)))

theorem reduce_entry (l r : List (Cell S Γ)) (lb rb : Bool) :
    Reduce A M (encode ⟨l,.pending,Validator.cell A.blank .cutD::r,lb,rb⟩)
      (encode ⟨l,.internal .initial,Validator.cell A.blank .cutD::r,lb,rb⟩) := by
  apply reduce_headed A M (l₁ := []) (l₂ := [])
    (r₁ := [Validator.cell A.blank .cutD]) (r₂ := [Validator.cell A.blank .cutD]) ?_ l r lb rb
  simpa [Path.headed] using (Rule.ordinary (Ordinary.entry (A := A) (M := M)))

theorem reduce_cleanup {v w : Cleanup.Sector S Γ} (h : Cleanup.Step A.blank v w) :
    Reduce A M (encode (Surface.ofCleanup v)) (encode (Surface.ofCleanup w)) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | raw => cases h
  | cleanup =>
    cases l with
    | nil =>
      cases lb with
      | false => cases h
      | true =>
        cases Option.some.inj h
        apply reduce_of_context_rule A M
        have hh := Path.Context.apply [] (r.map .right++(if rb then [.leave] else []))
            (Rule.ordinary (Ordinary.finish (A := A) (M := M)))
        simp only [encode,Scan.literal,Path.encode,Path.headed,Surface.ofCleanup,Scan.mapHead,Surface.cleanupHead,
          List.map_nil,List.reverse_nil,List.nil_append,List.append_nil,ite_true,
          List.singleton_append,List.append_assoc] at hh ⊢
        exact hh
    | cons c l =>
      cases Option.some.inj h
      apply reduce_headed A M (l₁ := [c]) (l₂ := []) (r₁ := [])
        (r₂ := (Cleanup.emit c).toList.map (Cleanup.letter A.blank)) ?_ l r lb rb
      simpa only [Surface.cleanupHead,Path.headed,List.map_nil,List.nil_append,List.map_cons,
        List.reverse_cons,List.reverse_nil,List.append_nil,List.singleton_append,Bool.false_eq_true,ite_false] using
          (Rule.ordinary (Ordinary.clean (A := A) (M := M) c))

theorem reduces_cleanupNormal (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) (encode (Surface.cleanupNormal A.blank v)) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | cleanup =>
    exact (Cleanup.normal_reached A.blank ⟨l,.cleanup,r,lb,rb⟩).lift
      (fun v => encode (Surface.ofCleanup v)) (fun _ _ h => reduce_cleanup A M h)
  | raw | pending | internal _ => exact .refl

theorem reduces_cleanupPreprocess (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) (encode (Surface.cleanupPreprocess A.blank v)) :=
  (reduces_cleanupNormal A M v).trans (reduces_rawNormal A M _)

theorem reduce_unmerge (l r : List (Cell S Γ)) (lb rb : Bool) :
    Reduce A M (encode ⟨Validator.cell A.blank .cutC::l,.pending,Validator.cell A.blank .cutD::r,lb,rb⟩)
      (encode ⟨l,.raw,[],lb,true⟩ ++ encode ⟨[],.raw,r,true,rb⟩) := by
  have hr := reduce_rule_reverse A M (.ordinary .merge) (by
    simp [grade,Path.grade,Path.letterGrade,gradeCell,Validator.cell,Cleanup.grade])
  have hh := reduce_context A M hr ((if lb then [.enter] else [])++l.reverse.map .left)
      (r.map .right++(if rb then [.leave] else []))
  simp only [encode,Scan.literal,Path.encode,Path.headed,List.reverse_cons,List.reverse_nil,
    List.map_cons,List.map_append,List.map_nil,List.append_nil,
    List.singleton_append,ite_true,List.append_assoc] at hh ⊢
  exact hh

theorem reduces_unmerge (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) ((Surface.unmerge A.blank v).flatMap encode) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases l with
  | nil =>
    simp only [Surface.unmerge,List.flatMap_cons,List.flatMap_nil,List.append_nil]; exact .refl
  | cons c l =>
    cases q with
    | raw | cleanup | internal _ =>
      simp only [Surface.unmerge,List.flatMap_cons,List.flatMap_nil,List.append_nil]; exact .refl
    | pending =>
      cases r with
      | nil =>
        simp only [Surface.unmerge,List.flatMap_cons,List.flatMap_nil,List.append_nil]; exact .refl
      | cons d r =>
        by_cases h : c = Validator.cell A.blank .cutC ∧ d = Validator.cell A.blank .cutD
        · rcases h with ⟨rfl,rfl⟩
          have hp := (reduces_rawNormal A M ⟨l,.raw,[],lb,true⟩)
          have hq := (reduces_rawNormal A M ⟨[],.raw,r,true,rb⟩)
          simpa [Surface.unmerge] using
            ((ReflTransGen.single (reduce_unmerge A M l r lb rb)).trans (reduces_append A M hp hq))
        · simpa only [Surface.unmerge,ite_eq_right h,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
            (ReflTransGen.refl (a := encode ⟨c::l,.pending,d::r,lb,rb⟩) : Reduces A M _ _)

theorem reduces_pendingPreprocess (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) ((Surface.pendingPreprocess A.blank v).flatMap encode) :=
  (reduces_quotaNormal A M v).trans (reduces_unmerge A M _)

theorem reduce_exit (l : List (Cell S Γ)) (lb : Bool) :
    Reduce A M (encode ⟨l,.internal (.machine .ok),[],lb,true⟩)
      (encode ⟨l,.cleanup,[],lb,true⟩) := by
  have hh := reduce_context A M (reduce_rule A M .exit) ((if lb then [.enter] else [])++l.reverse.map .left) []
  simp only [encode,Scan.literal,Path.encode,Path.headed,List.map_nil,List.append_nil,
    ite_true,List.append_assoc] at hh ⊢
  exact hh

variable [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)]

theorem reduces_internalPreprocess (v : Control.Sector S Γ Q) :
    Reduces A M (encode (Scan.mapHead Surface.Head.internal v))
      ((Surface.internalPreprocess A M v).flatMap encode) := by
  have hp := reduces_internal A M (Control.representative_connected A M v)
  refine hp.trans ?_
  generalize hw : Control.representative A M v = w at *
  rcases w with ⟨l,q,r,lb,rb⟩
  unfold Surface.internalPreprocess
  rw [hw]
  dsimp only
  by_cases he : Control.Entry A.blank ⟨l,q,r,lb,rb⟩
  · rw [ite_eq_left he]
    rcases he with ⟨rfl,hr⟩
    cases r with
    | nil => cases hr
    | cons c r =>
      cases Option.some.inj hr
      have hh := reduce_entry A M l r lb rb
      have hg : grade (Q := Q) (encode ⟨l,.pending,Validator.cell A.blank .cutD::r,lb,rb⟩) =
          grade (Q := Q) (encode ⟨l,.internal .initial,Validator.cell A.blank .cutD::r,lb,rb⟩) := by
        rw [grade_encode,grade_encode]; rfl
      exact (ReflTransGen.single (reduce_reverse A M hh hg)).trans (reduces_pendingPreprocess A M _)
  · rw [ite_eq_right he]
    by_cases hs : Control.Success ⟨l,q,r,lb,rb⟩
    · rw [ite_eq_left hs]
      rcases hs with ⟨rfl,rfl,rfl⟩
      simpa only [Scan.mapHead,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
        ((ReflTransGen.single (reduce_exit A M l lb)).trans (reduces_cleanupPreprocess A M _))
    · rw [ite_eq_right hs]
      simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
      exact .refl

theorem reduces_sectorPreprocess (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) ((Surface.preprocess A M v).flatMap encode) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | raw =>
    simpa only [Surface.preprocess,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
      reduces_rawNormal A M ⟨l,.raw,r,lb,rb⟩
  | pending => exact reduces_pendingPreprocess A M _
  | cleanup =>
    simpa only [Surface.preprocess,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
      reduces_cleanupPreprocess A M ⟨l,.cleanup,r,lb,rb⟩
  | internal q => exact reduces_internalPreprocess A M ⟨l,q,r,lb,rb⟩

end

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

theorem reduces_prepareChunk (w : List (Letter S Γ Q)) :
    Reduces A M w (Path.prepareChunk (sectorPreprocess A M) w).flatten := by
  cases hd : Path.decode w with
  | none => simp only [Path.prepareChunk,hd,List.flatten_cons,List.flatten_nil,List.append_nil]; exact .refl
  | some v =>
    have hw := Path.decode_sound hd
    subst w
    have hh := reduces_sectorPreprocess A M (Scan.unliteral v)
    simp only [Path.prepareChunk_encode,sectorPreprocess,List.map_map,List.flatMap_def,
      Function.comp_def,encode,Scan.literal_unliteral] at hh ⊢
    exact hh

theorem reduces_prepareChunks (cs : List (List (Letter S Γ Q))) :
    Reduces A M cs.flatten (Path.prepareChunks (sectorPreprocess A M) cs).flatten := by
  induction cs with
  | nil => exact .refl
  | cons c cs ih =>
    simpa only [Path.prepareChunks,List.flatMap_cons,List.flatten_cons,List.flatten_append] using
      reduces_append A M (reduces_prepareChunk A M c) ih

theorem reduces_preprocess (w : List (Letter S Γ Q)) :
    Reduces A M w (preprocess A M w).flatten := by
  simpa only [preprocess,Path.prepare,Path.flatten_cuts] using reduces_prepareChunks A M (Path.cuts w)

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
 theorem reduces_zero {w : List (Letter S Γ Q)} (h : Path.shape w = .zero) :
    Reduces A M w [.zero] := by
  exact ReflTransGen.mono (fun _ _ hs =>
    reduce_of_context_rule A M (Path.context_mono hs (fun _ _ hh => .zero hh))) _ _ (Path.zero_reaches h)

end

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

omit [DecidableEq S] [DecidableEq Γ] in
theorem grade_flatMap_encode (vs : List (Surface.Sector S Γ (Control.Head S Q))) :
    grade (vs.flatMap encode) = Surface.listGrade vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [List.flatMap_cons,grade_append,grade_encode,ih,Surface.listGrade,
      List.map_cons,List.sum_cons]

theorem reduces_rawPair_of_run (x y out : List S)
    (c : Simulator.Tape (S := S) (Γ := Γ) (Q := Q))
    (hrun : ReflTransGen (Simulator.UnboundedStep A M) (Simulator.initialTape A M (x++y)) c)
    (hhalt : Simulator.Halted A M c) (hout : Simulator.Returns A c out)
    (hlen : out.length ≤ x.length+y.length) :
    Reduces A M (raw A.blank x ++ raw A.blank y) (raw A.blank out) := by
  obtain ⟨s,result,hr,hclean⟩ := Compiled.clean_success A M x y out c hrun hhalt hout hlen
  let e : Surface.Sector S Γ (Control.Head S Q) :=
    ⟨(Compiled.cleanEntry A.blank x y s).left,.pending,
      (Compiled.cleanEntry A.blank x y s).right,true,true⟩
  have he : (Surface.pendingPreprocess A.blank e).flatMap encode = raw A.blank x++raw A.blank y := by
    rw [show Surface.pendingPreprocess A.blank e = [Surface.raw A.blank x,Surface.raw A.blank y] from
      Surface.pendingPreprocess_cleanEntry A x y s]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,raw]
  have hp := reduces_pendingPreprocess A M e
  have hg : grade (encode e) = grade ((Surface.pendingPreprocess A.blank e).flatMap encode) := by
    rw [grade_encode,grade_flatMap_encode,Surface.pendingPreprocess_grade]
  have hp' := reduces_reverse A M hp hg
  rw [he] at hp'
  have hentry : Reduce A M (encode e)
      (encode (Scan.mapHead Surface.Head.internal (Control.validator (Compiled.cleanEntry A.blank x y s)))) :=
    reduce_entry A M _ _ true true
  have hrun' := reduces_internal A M (EqvGen.reflTransGen_le_eqvGen _ _ _ (Control.ofCfg_runs A M hr))
  simp only [Control.ofCfg] at hrun'
  have hc : Reduces A M (encode (Surface.ofCleanup ⟨result.reverse,.cleanup,[],true,true⟩))
      (raw A.blank out) := by
    exact hclean.lift (fun v => encode (Surface.ofCleanup v)) (fun _ _ hh => reduce_cleanup A M hh)
  exact hp'.trans ((ReflTransGen.single hentry).trans
    (hrun'.trans ((ReflTransGen.single (reduce_exit A M result.reverse true)).trans hc)))

theorem reduces_rawPair {f : List S → List S} {m : ℕ}
    (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (x y : List S) (hm : (x++y).length ≤ m) :
    Reduces A M (raw A.blank x++raw A.blank y) (raw A.blank (f (x++y))) := by
  obtain ⟨c,hc,hh,ho⟩ := hcomp (x++y) hm
  exact reduces_rawPair_of_run A M x y (f (x++y)) c hc hh ho (by simpa using h.length (x++y) hm)

end

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]

omit [DecidableEq Q] in
 theorem reduces_prepend {f : List S → List S} {m : ℕ}
    (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (a : Item S Γ Q) (w : List (Item S Γ Q))
    (hm : RawRuns.itemGrade grade a + RawRuns.grade grade w ≤ m) :
    Reduces A M (realize A.blank a ++ w.flatMap (realize A.blank))
      ((RawRuns.prepend f a w).flatMap (realize A.blank)) := by
  cases a with
  | inl c => exact .refl
  | inr x =>
    cases w with
    | nil => exact .refl
    | cons a w =>
      cases a with
      | inl c => exact .refl
      | inr y =>
        have hl : (x++y).length ≤ m := by
          simp only [RawRuns.itemGrade,RawRuns.grade_cons,List.length_append] at *
          omega
        have hp := reduces_context A M (reduces_rawPair A M h hcomp x y hl) [] (w.flatMap (realize A.blank))
        simpa only [List.nil_append,List.flatMap_cons,RawRuns.prepend,realize,List.append_assoc] using hp

omit [DecidableEq Q] in
 theorem reduces_rawRuns {f : List S → List S} {m : ℕ}
    (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (w : List (Item S Γ Q)) (hm : RawRuns.grade grade w ≤ m) :
    Reduces A M (w.flatMap (realize A.blank))
      ((RawRuns.normalize f w).flatMap (realize A.blank)) := by
  induction w with
  | nil => exact .refl
  | cons a w ih =>
    have hb : RawRuns.grade grade w ≤ m := by simp only [RawRuns.grade_cons] at hm; omega
    have hp := reduces_append A M (ReflTransGen.refl (a := realize A.blank a)) (ih hb)
    have hg := RawRuns.normalize_grade grade h w hb
    have hh := reduces_prepend A M h hcomp a (RawRuns.normalize f w)
      (by simp only [RawRuns.grade_cons] at hm; omega)
    exact hp.trans hh

variable [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- A literal, grade-nonincreasing derivation to the source's whole-word
    evaluator, not just equality in an assumed quotient. -/
 theorem reduces_normal {f : List S → List S} {m : ℕ}
    (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (w : List (Letter S Γ Q)) (hm : grade w ≤ m) :
    Reduces A M w (normal A M f w) := by
  by_cases hn : Path.shape w = .zero
  · simpa only [normal,ite_eq_left hn] using reduces_zero A M hn
  · rw [normal_eq_fold A M h w hn hm]
    have hp := reduces_preprocess A M w
    have hh := reduces_rawRuns A M h hcomp ((preprocess A M w).map (classify A.blank))
      (by rw [classify_grade]; exact (preprocess_grade A M w).trans hm)
    have hj : ((preprocess A M w).map (classify A.blank)).flatMap (realize A.blank) =
        (preprocess A M w).flatten := by
      simp only [List.flatMap_def,List.map_map,Function.comp_def,realize_classify,List.map_id']
    rw [hj] at hh
    exact hp.trans hh

end

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- The bounded context conclusion uses the nonincreasing literal derivations;
    the attachment need not preserve sector boundaries. -/
theorem normal_context
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    {u v : List (Letter S Γ Q)} (he : normal A M f u = normal A M f v)
    (x y : List (Letter S Γ Q))
    (hu : grade (x++u++y) ≤ m) (hv : grade (x++v++y) ≤ m) :
    normal A M f (x++u++y) = normal A M f (x++v++y) := by
  have hu' : grade u ≤ m := by simp only [grade_append] at hu; omega
  have hv' : grade v ≤ m := by simp only [grade_append] at hv; omega
  have hp := normal_reduces A M hdecode h hcomp
    (reduces_context A M (reduces_normal A M h hcomp u hu') x y) hu
  have hq := normal_reduces A M hdecode h hcomp
    (reduces_context A M (reduces_normal A M h hcomp v hv') x y) hv
  rw [he] at hp
  exact hp.trans hq.symm

end

open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

theorem normal_contains_omega (f : List S → List S) (x y : List (Letter S Γ Q)) :
    normal A M f (x ++ .zero::y) = [.zero] := by
  rw [normal,ite_eq_left (Path.shape_zero_context x y)]

end FiniteAlgebraicEnvelopes.Compiler.Word

/- The actual partial evaluator is a finite plan followed by partial calls.
   Its definition has no budget and does not totalize an undefined program. -/
namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C S : Type*}

theorem plan_total (f : List S → List S) (w : List (Item C S)) :
    (plan w).map (Action.total f) = source f w := by
  cases w with
  | nil => simp [plan,source]
  | cons a w =>
    cases a with
    | inl c => simp only [plan,source,List.map_cons,Action.total,plan_total f w]
    | inr x =>
      have ht := splitRun_length w
      rw [plan,source,List.map_cons,plan_total f (splitRun w).2]
      cases (splitRun w).1 <;> rfl
termination_by w.length
decreasing_by all_goals simp_all only [List.length_cons]; omega

/-- Every program argument is bounded by the grade of the original item list,
    before any output from the program is computed. -/
theorem plan_call_bound (g : C → ℕ) (w : List (Item C S)) {x : List S}
    (hx : Action.call x ∈ plan w) : x.length ≤ grade g w := by
  cases w with
  | nil => simp [plan] at hx
  | cons a w =>
    cases a with
    | inl c =>
      simp only [plan,List.mem_cons] at hx
      rcases hx with he | hx
      · cases he
      ·
        exact (plan_call_bound g w hx).trans (by simp only [grade_cons,itemGrade]; omega)
    | inr y =>
      have ht := splitRun_length w
      have hj := splitRun_join w
      simp only [plan,List.mem_cons] at hx
      rcases hx with he | hx
      · cases hh : (splitRun w).1 with
        | nil => simp only [hh] at he; cases he
        | cons z zs =>
          simp only [hh] at he
          cases he
          rw [←hj]
          simp only [grade_cons,itemGrade,grade_append,grade_raws,hh]
          simp only [List.length_append]
          omega
      · have hp := plan_call_bound g (splitRun w).2 hx
        rw [←hj]
        simp only [grade_cons,itemGrade,grade_append]
        omega
termination_by w.length
decreasing_by all_goals simp_all only [List.length_cons]; omega

theorem execute_total_mem {f : List S → Part (List S)} {t : List S → List S}
    (p : List (Action C S)) (h : ∀ x, Action.call x ∈ p → t x ∈ f x) :
    p.map (Action.total t) ∈ execute f p := by
  induction p with
  | nil => exact Part.mem_some []
  | cons a p ih =>
    have hp := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha : Action.total t a ∈ Action.partial f a := by
      cases a with
      | keep c => exact Part.mem_some _
      | raw x => exact Part.mem_some _
      | call x => exact (Part.mem_map_iff _).mpr ⟨t x,h x (List.mem_cons_self),rfl⟩
    exact Part.mem_bind_iff.mpr ⟨_,ha,(Part.mem_map_iff _).mpr ⟨_,hp,rfl⟩⟩

theorem partialSource_total_mem (g : C → ℕ) {f : List S → Part (List S)} {t : List S → List S}
    (w : List (Item C S)) (h : ∀ x, x.length ≤ grade g w → t x ∈ f x) :
    source t w ∈ partialSource f w := by
  rw [←plan_total t]
  exact execute_total_mem _ (fun x hx => h x (plan_call_bound g w hx))

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

namespace FiniteAlgebraicEnvelopes.Compiler.Word
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- Agreement only needs the values below the *input's* additive grade. -/
theorem partialNormal_total_mem {f : List S → Part (List S)} {t : List S → List S}
    (w : List (Letter S Γ Q)) (h : ∀ x, x.length ≤ grade w → t x ∈ f x) :
    normal A M t w ∈ partialNormal A M f w := by
  unfold normal partialNormal
  split
  · exact Part.mem_some _
  · apply (Part.mem_map_iff _).mpr
    refine ⟨_,RawRuns.partialSource_total_mem grade _ ?_,rfl⟩
    intro x hx
    apply h x
    apply hx.trans
    rw [classify_grade]
    exact preprocess_grade A M w

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler

theorem partValue_mem {S : Type*} {p : Part (List S)} (h : p.Dom) : partValue p ∈ p := by
  simp only [partValue,dite_eq_left h]
  exact Part.get_mem h

theorem PartialBudget.totalize {S : Type*} {f : List S → Part (List S)} {m : ℕ}
    (h : PartialBudget f m) : RawRuns.Budget (fun w => partValue (f w)) m where
  length w hw := h.length w hw _ (partValue_mem (h.total w hw))
  context x w y hw := by
    have hh : w.length ≤ m := by simp only [List.length_append] at hw; omega
    exact congrArg partValue (h.context x w y hw _ (partValue_mem (h.total w hh)))

end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler.Word
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
theorem Realizes.computesAt {f : List S → Part (List S)} (hr : Realizes A M f) {m : ℕ}
    (h : PartialBudget f m) : ComputesAt A M (fun w => partValue (f w)) m := by
  intro w hw
  exact (hr w _).mp (partValue_mem (h.total w hw))

theorem partialNormal_eq_some {f : List S → Part (List S)} {m : ℕ} (h : PartialBudget f m)
    (w : List (Letter S Γ Q)) (hw : grade w ≤ m) :
    partialNormal A M f w = Part.some (normal A M (fun x => partValue (f x)) w) := by
  apply Part.eq_some_iff.mpr
  exact partialNormal_total_mem A M w (fun x hx => partValue_mem (h.total x (hx.trans hw)))

end FiniteAlgebraicEnvelopes.Compiler.Word

end OAI
end

section
-- module Solutions.OAIFAE.Effectivity
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Primitive recursive encodings and effective finite compiler data.
-/

/- Effectivity dependencies for the source compiler and its bounded recursive
   evaluator. No partial function is completed by classical choice. -/

namespace FiniteAlgebraicEnvelopes.Effect
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {α : Type*} [Primcodable α] [DecidableEq α]

omit [Primcodable α] in
 theorem priorityList_toFinset (p q : α → Bool) (s : List α) :
    (priorityList p q s).toFinset =
      Compiler.prioritySet (fun a => p a = true) (fun a => q a = true) s.toFinset := by
  have hp : (s.filter p).isEmpty = true ↔ ¬ (s.toFinset.filter (fun a => p a = true)).Nonempty := by
    simp
  have hq : (s.filter q).isEmpty = true ↔ ¬ (s.toFinset.filter (fun a => q a = true)).Nonempty := by
    simp
  simp only [priorityList,Compiler.prioritySet,hp,hq]
  split_ifs <;> simp_all

end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open FiniteAlgebraicEnvelopes.Effect
variable {H B T : Type*} [Primcodable H] [Primcodable B] [Primcodable T]
  [Fintype H] [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq B] [DecidableEq T]
  [LinearOrder (Sector H B T)]
  (table : Table H B T) (P Q : Sector H B T → Prop) [DecidablePred P] [DecidablePred Q]

omit [Primcodable H] [Primcodable B] [Primcodable T] in
 theorem representative_list (v : Sector H B T) :
    representative table P Q v =
      (priorityList (fun x => decide (P x)) (fun x => decide (Q x)) (componentList table v)).min?.getD v := by
  symm
  apply minList_eq
  rw [priorityList_toFinset]
  have he : (componentList table v).toFinset = literalComponent table v := by
    ext w
    simp only [List.mem_toFinset,mem_componentList,mem_literalComponent]
  simp only [decide_eq_true_eq,he]

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Path
open FiniteAlgebraicEnvelopes.Effect
variable {C H : Type*}

variable [Primcodable C] [Primcodable H]

variable [Fintype C] [Fintype H] [DecidableEq C] [DecidableEq H]
noncomputable instance instPrimcodableShape : Primcodable Shape := finitePrimcodable _

end FiniteAlgebraicEnvelopes.Compiler.Path

end OAI
end

section
-- module Solutions.OAIFAE.Rewriting
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Newman normalization, block coding, canonical representatives, and static tests.
-/

/- Rewriting layer for the self-reference construction.  No assumptions on
   either main theorem are introduced here. -/
namespace FiniteAlgebraicEnvelopes.Bootstrap

section
open Relation

variable {S : Type*}

theorem step_shortlex {r : S → S → Prop} {rules : List (List S × List S)}
    (dec : ∀ p ∈ rules, List.Shortlex r p.2 p.1) {u v : List S}
    (h : Step rules u v) : List.Shortlex r v u := by
  cases h with
  | apply hm x y => exact shortlex_context (dec _ hm) x y

theorem steps_length {r : S → S → Prop} {rules : List (List S × List S)}
    (dec : ∀ p ∈ rules, List.Shortlex r p.2 p.1) {u v : List S}
    (h : Steps rules u v) : v.length ≤ u.length := by
  induction h with
  | refl => rfl
  | tail huv hvw ih =>
    have hh := List.shortlex_def.mp (step_shortlex dec hvw)
    omega

theorem steps_wellFounded {r : S → S → Prop} {rules : List (List S × List S)}
    (wf : WellFounded r) (dec : ∀ p ∈ rules, List.Shortlex r p.2 p.1) :
    WellFounded (flip (Step rules)) :=
  (List.Shortlex.wf wf).mono (fun _ _ h => step_shortlex dec h)

/-- A bounded table sees precisely those rules whose left sides fit the bound. -/
theorem step_stable {rs rt : List (List S × List S)} {k : ℕ}
    (stable : ∀ p, p.1.length ≤ k → (p ∈ rs ↔ p ∈ rt)) {w v : List S}
    (hw : w.length ≤ k) : Step rs w v ↔ Step rt w v := by
  constructor
  · intro h
    cases h with
    | apply hm x y =>
      apply Step.apply ((stable _ (by simp only [List.length_append] at hw; dsimp only; omega)).mp hm)
  · intro h
    cases h with
    | apply hm x y =>
      apply Step.apply ((stable _ (by simp only [List.length_append] at hw; dsimp only; omega)).mpr hm)

variable [DecidableEq S]

theorem rootNext_sound {w v : List S} {rules : List (List S × List S)}
    (h : rootNext w rules = some v) : ∃ u t, (u,t) ∈ rules ∧
      ∃ y, w = u++y ∧ v = t++y := by
  induction rules with
  | nil => simp [rootNext] at h
  | cons p rs ih =>
    rcases p with ⟨u,t⟩
    simp only [rootNext] at h
    split at h
    next he =>
      obtain rfl := Option.some.inj h
      exact ⟨u,t,List.mem_cons_self, w.drop u.length,
        by simpa only [he] using (List.take_append_drop u.length w).symm,rfl⟩
    next he =>
      obtain ⟨u,t,hm,y,hw,hv⟩ := ih h
      exact ⟨u,t,List.mem_cons_of_mem _ hm,y,hw,hv⟩

theorem rootNext_none {w : List S} {rules : List (List S × List S)}
    (h : rootNext w rules = none) {u t y : List S} (hm : (u,t) ∈ rules) : w ≠ u ++ y := by
  induction rules with
  | nil => simp at hm
  | cons p rs ih =>
    rcases p with ⟨a,b⟩
    simp only [rootNext] at h
    split at h
    · simp at h
    next he =>
      rcases List.mem_cons.mp hm with hp | hm
      · cases hp
        intro hw
        exact he (by simp [hw])
      · exact ih h hm

theorem next_sound {rules : List (List S × List S)} {w v : List S}
    (h : next rules w = some v) : Step rules w v := by
  induction w generalizing v with
  | nil =>
      obtain ⟨u,t,hm,y,hw,hv⟩ := rootNext_sound h
      have hh : Step rules (u++y) (t++y) := by
        simpa only [List.nil_append] using Step.apply hm [] y
      rw [← hw,← hv] at hh
      exact hh
  | cons a w ih =>
      simp only [next] at h
      cases hr : rootNext (a::w) rules with
      | some z =>
          simp [hr] at h
          subst z
          obtain ⟨u,t,hm,y,hw,hv⟩ := rootNext_sound hr
          have hh : Step rules (u++y) (t++y) := by
            simpa only [List.nil_append] using Step.apply hm [] y
          rw [← hw,← hv] at hh
          exact hh
      | none =>
          simp only [hr,Option.none_or,Option.map_eq_some_iff] at h
          obtain ⟨z,hz,rfl⟩ := h
          simpa only [List.singleton_append,List.append_nil] using step_context (ih hz) [a] []

theorem next_none_root {rules : List (List S × List S)} {w : List S}
    (h : next rules w = none) : rootNext w rules = none := by
  cases w with
  | nil => exact h
  | cons a w => exact (Option.or_eq_none_iff.mp h).1

theorem next_none_tail {rules : List (List S × List S)} {a : S} {w : List S}
    (h : next rules (a::w) = none) : next rules w = none := by
  exact Option.map_eq_none_iff.mp (Option.or_eq_none_iff.mp h).2

theorem next_none {rules : List (List S × List S)} {w : List S}
    (h : next rules w = none) : Irreducible (Step rules) w := by
  intro v hv
  cases hv with
  | @apply u t hm x y =>
    induction x with
    | nil => exact rootNext_none (next_none_root h) hm rfl
    | cons a x ih => exact ih (next_none_tail h)

/-- Fully specified finite-table reduction; divergence is retained for arbitrary
    (possibly nonterminating) tables. -/
def iteration (s : List (List S × List S) × List S) :
    List S ⊕ (List (List S × List S) × List S) :=
  match next s.1 s.2 with
  | none => .inl s.2
  | some v => .inr (s.1,v)

def evaluate (rules : List (List S × List S)) (w : List S) : Part (List S) :=
  PFun.fix (fun s => Part.some (iteration s)) (rules,w)

 theorem evaluate_sound {rules : List (List S × List S)} {w v : List S}
    (h : v ∈ evaluate rules w) : Steps rules w v ∧ Irreducible (Step rules) v := by
  change v ∈ PFun.fix _ (rules,w) at h
  refine PFun.fixInduction' (C := fun s => Steps s.1 s.2 v ∧ Irreducible (Step s.1) v) h ?_ ?_
  · rintro ⟨rs,a⟩ ha
    simp only [Part.mem_some_iff,iteration] at ha
    cases hn : next rs a with
    | none =>
      simp only [hn,Sum.inl.injEq] at ha
      subst a
      exact ⟨.refl,next_none hn⟩
    | some b => simp [hn] at ha
  · rintro ⟨rs,a⟩ ⟨rt,b⟩ _ hab ih
    simp only [Part.mem_some_iff,iteration] at hab
    cases hn : next rs a with
    | none => simp [hn] at hab
    | some c =>
      simp only [hn,Sum.inr.injEq,Prod.mk.injEq] at hab
      rcases hab with ⟨rfl,rfl⟩
      exact ⟨.head (next_sound hn) ih.1,ih.2⟩

theorem evaluate_total {rules : List (List S × List S)}
    (wf : WellFounded (flip (Step rules))) (w : List S) : (evaluate rules w).Dom := by
  induction w using wf.induction with
  | h w ih =>
    cases hn : next rules w with
    | none =>
      exact Part.dom_iff_mem.mpr ⟨w,PFun.fix_stop (by simp [iteration,hn])⟩
    | some v =>
      obtain ⟨z,hz⟩ := Part.dom_iff_mem.mp (ih v (next_sound hn))
      apply Part.dom_iff_mem.mpr
      refine ⟨z,PFun.mem_fix_iff.mpr (Or.inr ⟨(rules,v),?_,hz⟩)⟩
      simp [iteration,hn]

end

/- The marker/constant-width code used in the self-reference construction.
   A block has its marker only at the start, not at the end. -/

namespace BlockCode
variable {A S : Type*} (C : BlockCode A S)

/-- The chosen generator order is transported from the equal-width blocks. -/
theorem encode_lex {r : A → A → Prop} {s : S → S → Prop}
    (hblock : ∀ a b, r a b → List.Lex s (C.block a) (C.block b))
    {u v : List A} (h : List.Lex r u v) : List.Lex s (C.encode u) (C.encode v) := by
  induction h with
  | nil => exact List.Lex.nil
  | rel hh => exact lex_append_two (hblock _ _ hh) (by simp) _ _
  | @cons a u v hh ih => exact List.Lex.append_left s ih (C.block a)

theorem encode_shortlex {r : A → A → Prop} {s : S → S → Prop}
    (hblock : ∀ a b, r a b → List.Lex s (C.block a) (C.block b))
    {u v : List A} (h : List.Shortlex r u v) : List.Shortlex s (C.encode u) (C.encode v) := by
  rcases List.shortlex_def.mp h with hl | ⟨hl,hlex⟩
  · exact List.Shortlex.of_length_lt (by simpa using Nat.mul_lt_mul_of_pos_left hl (Nat.succ_pos C.width))
  · exact List.Shortlex.of_lex (by simp [hl]) (C.encode_lex hblock hlex)

end BlockCode

namespace Canonical
variable {A Q : Type*} {r : A → A → Prop} (wf : WellFounded r)
variable (q : List A → Q)

theorem least_lt_or_eq [Std.Trichotomous r] (w : List A) :
    List.Shortlex r (least wf q w) w ∨ least wf q w=w := by
  have hh := Std.Trichotomous.trichotomous (r := List.Shortlex r) (least wf q w) w
  by_cases h : List.Shortlex r (least wf q w) w
  · exact Or.inl h
  · exact Or.inr (hh h (least_min wf q le_rfl rfl))

end Canonical

open Relation
variable {S : Type*}

theorem absorbs_mem {rs : List (List S × List S)} {z : S} (hz : Absorbs rs z)
    {w : List S} (hw : z∈w) : Steps rs w [z] := by
  induction w with
  | nil => simp at hw
  | cons a w ih =>
    rcases List.mem_cons.mp hw with rfl | hw
    · exact absorbs_context hz [] w
    · have hh := steps_context (ih hw) [a] []
      have hh' : Steps rs (a::w) [a,z] := by simpa using hh
      exact hh'.trans (.single (by simpa using Step.apply (hz a).2 [] []))

theorem step_preserves_letter {rs : List (List S × List S)} {z : S}
    (hz : ∀ p∈rs, z∈p.1 → z∈p.2) {w v : List S} (hw : z∈w) (h : Step rs w v) : z∈v := by
  cases h with
  | apply hp x y =>
    simp only [List.mem_append] at hw ⊢
    rcases hw with (hx | hu) | hy
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr (hz _ hp hu))
    · exact Or.inr hy

end FiniteAlgebraicEnvelopes.Bootstrap

end OAI
end

section
-- module Solutions.OAIFAE.Selectors
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Literal selector envelopes, rewrite saturation, and zero recognition.
-/

/- Literal selector envelopes from the self-reference construction. -/
namespace FiniteAlgebraicEnvelopes.Bootstrap

section
namespace Envelopes
variable {S : Type*}

/-- Every older selector side of length at most N lies wholly in the body of
    an N-envelope. Its body is checked irreducible when that envelope is chosen. -/
theorem bounded_infix_frame {d l r h : S} {v w : List S} {N : ℕ}
    (hdl : d≠l) (hhr : h≠r) (hhd : h≠d) (hhl : h≠l) (hdr : d≠r)
    (hlen : (d::(v++[h])).length ≤ N)
    (hi : d::(v++[h]) <:+: frame d l r h N w) : d::(v++[h]) <:+: w := by
  have hleft : d::(v++[h]) <:+: w++List.replicate N r++[h] :=
    bounded_strip_left hdl hhd hhl (by simp) hlen (by simpa [frame,List.append_assoc] using hi)
  have hrev : h::(v.reverse++[d]) <:+: h::(List.replicate N r++w.reverse) := by
    simpa [List.reverse_append,List.reverse_cons,List.append_assoc] using hleft.reverse
  have hlen' : (h::(v.reverse++[d])).length ≤ N := by simpa using hlen
  have hh := bounded_strip_left hhr hhd.symm hdr (by simp) hlen' hrev
  simpa [List.reverse_append,List.reverse_cons,List.append_assoc] using hh.reverse

/-- The long header has exactly one occurrence in its own envelope. -/
theorem header_unique {d l r h : S} {N : ℕ} {w x y : List S}
    (hdl : d≠l) (hlr : l≠r) (hlh : l≠h) (hw : w.length < N)
    (he : frame d l r h N w = x++(d::List.replicate N l)++y) : x=[] := by
  cases x with
  | nil => rfl
  | cons a x =>
    have hi : d::List.replicate N l <:+: List.replicate N l++w++List.replicate N r++[h] :=
      ⟨x,y,(List.cons.inj he).2.symm⟩
    have hs : d::List.replicate N l <:+: w++List.replicate N r++[h] :=
      infix_strip_prefix (p := List.replicate N l) (by simp [hdl]) (by simpa only [List.append_assoc] using hi)
    have hn : 0<N := by omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N≠0)
    have hs' : (d::List.replicate k l)++[l] <:+: w++(List.replicate (k+1) r++[h]) := by
      simpa only [List.replicate_succ',List.cons_append,List.append_assoc] using hs
    have hb := infix_strip_suffix (by simp [hlr,hlh]) hs'
    have hh := hb.length_le
    simp only [List.length_append,List.length_cons,List.length_replicate] at hh
    omega

/-- Prefix-comparable same-stage envelopes have equal bodies. -/
theorem prefix_frame {d l r h : S} {N : ℕ} {u v : List S}
    (hhr : h≠r) (_ : u.length<N) (hv : v.length<N)
    (hp : frame d l r h N u <+: frame d l r h N v) : u=v := by
  have ht : u++List.replicate N r++[h] <+: v++List.replicate N r++[h] := by
    apply (List.prefix_self_append_iff (l₃ := d::List.replicate N l)).mp
    simpa only [frame,List.cons_append,List.append_assoc] using hp
  have hle : u.length ≤ v.length := by
    have hh := ht.length_le
    simp only [List.length_append,List.length_replicate,List.length_singleton] at hh
    omega
  have heq : u.length=v.length := by
    by_contra heq
    have hlt : u.length<v.length := by omega
    have h₁ : u.length+N < (u++List.replicate N r++[h]).length := by simp
    have hh := ht.getElem h₁
    have he₁ : (u++List.replicate N r++[h])[u.length+N] = h := by
      rw [List.getElem_append_right (by simp)]
      simp
    have h₂ : u.length+N < (v++List.replicate N r++[h]).length := by simp; omega
    have he₂ : (v++List.replicate N r++[h])[u.length+N]'h₂ = r := by
      rw [List.getElem_append_left (by simp; omega)]
      rw [List.getElem_append_right (by omega)]
      simp
    exact hhr (he₁.symm.trans (hh.trans he₂))
  have he := ht.eq_of_length (by simp [heq])
  exact List.append_cancel_right (List.append_cancel_right he)

/-- Same-stage left sides cannot properly contain one another. -/
theorem infix_frame {d l r h : S} {N : ℕ} {u v x y : List S}
    (hdl : d≠l) (hlr : l≠r) (hlh : l≠h) (hhr : h≠r)
    (hu : u.length<N) (hv : v.length<N)
    (he : frame d l r h N u = x++frame d l r h N v++y) :
    x=[] ∧ u=v ∧ y=[] := by
  have hx : x=[] := header_unique hdl hlr hlh hu
    (y := v++List.replicate N r++[h]++y) (by simpa [frame,List.append_assoc] using he)
  subst x
  have hp : frame d l r h N v <+: frame d l r h N u := ⟨y,by simpa using he.symm⟩
  have hvu := prefix_frame hhr hv hu hp
  subst v
  have hy := congrArg List.length he
  simp only [List.nil_append,List.length_append] at hy
  exact ⟨rfl,rfl,List.length_eq_zero_iff.mp (by omega)⟩

theorem frame_last {d l r h : S} {N : ℕ} {w : List S} :
    (frame d l r h N w).getLast? = some h := by
  change ((d::(List.replicate N l++w++List.replicate N r))++[h]).getLast? = some h
  rw [List.getLast?_append]
  rfl

/-- A suffix ending in h cannot be a short prefix of a fresh header. -/
theorem no_short_overlap {d l r h : S} {N : ℕ} {w m : List S}
    (hhd : h≠d) (hhl : h≠l) (hm : m.getLast? = some h)
    (hpre : m <+: frame d l r h N w) (hlen : m.length ≤ N+1) : False := by
  have hh : h∈m := List.mem_of_getLast? hm
  have hi : h∈d::List.replicate N l :=
    prefix_mem_initial (p := d::List.replicate N l)
      (by simpa [frame,List.append_assoc] using hpre) (by simpa using hlen) hh
  simp [hhd,hhl] at hi

/-- Aligned headers and guards exclude every proper same-stage boundary peak. -/
theorem overlap_frame {d l r h : S} {N : ℕ} {u v p m q : List S}
    (hdl : d≠l) (hlr : l≠r) (hlh : l≠h) (hhr : h≠r) (hhd : h≠d)
    (hu : u.length<N) (hv : v.length<N) (hm : m≠[])
    (he₁ : frame d l r h N u = p++m)
    (he₂ : frame d l r h N v = m++q) : p=[] ∧ u=v ∧ q=[] := by
  have hlast : m.getLast? = some h := by
    have hh := frame_last (d := d) (l := l) (r := r) (h := h) (N := N) (w := u)
    rw [he₁,List.getLast?_append,List.getLast?_eq_some_getLast hm] at hh
    simpa only [List.getLast?_eq_some_getLast hm, Option.some_or] using hh
  have hpre : m <+: frame d l r h N v := ⟨q,he₂.symm⟩
  have hlen : N+1 < m.length := by
    by_contra hh
    exact no_short_overlap hhd hlh.symm hlast hpre (by omega)
  have hh : d::List.replicate N l <+: m := by
    apply List.prefix_of_prefix_length_le
      (l₃ := frame d l r h N v) _ hpre (by simp; omega)
    exact ⟨v++List.replicate N r++[h],by simp [frame,List.append_assoc]⟩
  obtain ⟨t,ht⟩ := hh
  have hp : p=[] := header_unique hdl hlr hlh hu
    (by simpa [← ht,List.append_assoc] using he₁)
  subst p
  have hem : frame d l r h N u=m := by simpa using he₁
  have huv := prefix_frame hhr hu hv (hem.symm ▸ hpre)
  subst v
  have hq := congrArg List.length (he₂.trans (congrArg (·++q) hem.symm))
  simp only [List.length_append] at hq
  exact ⟨rfl,rfl,List.length_eq_zero_iff.mp (by omega)⟩

/-- Different-stage boundary overlaps are excluded by spacing alone; this
    does not depend on which earlier stage passed its irreducibility test. -/
theorem short_long_overlap {d l r h : S} {N M : ℕ} {u v p m q : List S}
    (hhd : h≠d) (hhl : h≠l) (hsmall : (frame d l r h N u).length≤M+1)
    (hm : m≠[]) (he : frame d l r h N u=p++m)
    (hf : frame d l r h M v=m++q) : False := by
  have hlast : m.getLast?=some h := by
    have hh := frame_last (d := d) (l := l) (r := r) (h := h) (N := N) (w := u)
    rw [he,List.getLast?_append,List.getLast?_eq_some_getLast hm] at hh
    simpa only [List.getLast?_eq_some_getLast hm,Option.some_or] using hh
  apply no_short_overlap hhd hhl hlast ⟨q,hf.symm⟩
  have hh := congrArg List.length he
  simp only [List.length_append] at hh
  omega

theorem long_short_overlap {d l r h : S} {N M : ℕ} {u v p m q : List S}
    (hdh : d≠h) (hdr : d≠r) (hsmall : (frame d l r h N v).length≤M+1)
    (hm : m≠[]) (he : frame d l r h M u=p++m)
    (hf : frame d l r h N v=m++q) : False := by
  apply short_long_overlap hdh hdr (u := v.reverse) (v := u.reverse)
    (p := q.reverse) (m := m.reverse) (q := p.reverse)
  · simpa using hsmall
  · simpa using hm
  · simpa using congrArg List.reverse hf
  · simpa using congrArg List.reverse he

/-- General form of code containment: only avoidance of the four envelope
    markers is used, so it applies to either of the two disjoint code types. -/
theorem avoiding_infix_frame {d l r h : S} {N : ℕ} {u w : List S}
    (hn : u≠[]) (hd : d∉u) (hl : l∉u) (hr : r∉u) (hh : h∉u)
    (hi : u <:+: frame d l r h N w) : u <:+: w := by
  have hleft : u <:+: w++List.replicate N r++[h] := by
    cases u with
    | nil => contradiction
    | cons a u =>
      apply infix_strip_prefix (p := d::List.replicate N l) ?_
        (by simpa [frame,List.append_assoc] using hi)
      simp only [List.mem_cons,List.mem_replicate]
      rintro (ha | ⟨_,ha⟩)
      · exact hd (by simp [ha])
      · exact hl (by simp [ha])
  rcases List.eq_nil_or_concat' u with he | ⟨v,b,rfl⟩
  · exact False.elim (hn he)
  · apply infix_strip_suffix (p := List.replicate N r++[h]) ?_
      (by simpa only [List.append_assoc] using hleft)
    simp only [List.mem_append,List.mem_replicate,List.mem_singleton]
    rintro (⟨_,hb⟩ | hb)
    · exact hr (by simp [hb])
    · exact hh (by simp [hb])

/-- A code suffix cannot meet the first envelope marker. -/
theorem avoiding_frame_overlap_left {d l r h : S} {N : ℕ} {u w p m q : List S}
    (hd : d∉u) (hm : m≠[]) (he : u=p++m) (hf : frame d l r h N w=m++q) : False := by
  cases m with
  | nil => contradiction
  | cons a m =>
    have ha : d=a := (List.cons.inj hf).1
    apply hd
    simp [he,ha]

/-- An envelope suffix cannot meet a code prefix because it ends in h. -/
theorem avoiding_frame_overlap_right {d l r h : S} {N : ℕ} {u w p m q : List S}
    (hh : h∉u) (hm : m≠[]) (he : frame d l r h N w=p++m) (hf : u=m++q) : False := by
  exact avoiding_frame_overlap_left (u := u.reverse) (m := m.reverse)
    (p := q.reverse) (q := p.reverse) (d := h) (l := r) (r := l) (h := d)
    (N := N) (w := w.reverse) (by simpa using hh) (by simpa using hm)
    (by simpa using congrArg List.reverse hf)
    (by simpa using congrArg List.reverse he)

end Envelopes

open Relation
variable {S : Type*} {rs : List (List S × List S)}

theorem join_context {u v : List S} (h : Join (Steps rs) u v) (x y : List S) :
    Join (Steps rs) (x++u++y) (x++v++y) := by
  obtain ⟨z,huz,hvz⟩ := h
  exact ⟨x++z++y,steps_context huz x y,steps_context hvz x y⟩

theorem critical_ordered {n : ℕ} (crit : Critical rs n)
    {u u' v v' x y a b : List S} (hu : (u,u')∈rs) (hv : (v,v')∈rs)
    (he : x++u++y=a++v++b) (hlen : (x++u++y).length≤n) (hxa : x.length≤a.length) :
    Join (Steps rs) (x++u'++y) (a++v'++b) := by
  have hp₁ : x <+: x++u++y := ⟨u++y,by simp only [List.append_assoc]⟩
  have hp₂ : a <+: x++u++y := ⟨v++b,by simpa only [List.append_assoc] using he.symm⟩
  obtain ⟨p,hp⟩ := List.prefix_of_prefix_length_le hp₁ hp₂ hxa
  subst a
  have hs : u++y=p++(v++b) :=
    List.append_cancel_left (by simpa only [List.append_assoc] using he)
  rcases List.append_eq_append_iff.mp hs with ⟨t,rfl,hy⟩ | ⟨s,huv,hvb⟩
  · subst y
    refine ⟨x++u'++t++v'++b,?_,?_⟩
    · exact .single (by simpa only [List.append_assoc] using Step.apply hv (x++u'++t) b)
    · exact .single (by simpa only [List.append_assoc] using Step.apply hu x (t++v'++b))
  · rcases List.append_eq_append_iff.mp hvb.symm with ⟨c,hvc,hy⟩ | ⟨c,hsc,hb⟩
    · by_cases hsn : s=[]
      · subst s
        simp only [List.append_nil] at huv
        subst u
        simp only [List.nil_append] at hvc
        subst v
        subst y
        refine ⟨x++u'++v'++b,?_,?_⟩
        · exact .single (by simpa only [List.append_assoc] using Step.apply hv (x++u') b)
        · exact .single (by simpa only [List.append_assoc] using Step.apply hu x (v'++b))
      · have hj := crit.2 u u' v v' hu hv p s c hsn huv hvc
          (by simp only [huv,hy,List.length_append] at hlen; simp only [List.length_append]; omega)
        have hc := join_context hj x b
        simpa only [hy,List.append_assoc] using hc
    · have hj := crit.1 u u' v v' hu hv p c
        (by simp only [huv,hsc,List.append_assoc])
        (by simp only [List.length_append] at hlen; omega)
      have hc := join_context hj x y
      simpa only [hb,List.append_assoc] using hc

theorem step_decompose {a b : List S} (h : Step rs a b) :
    ∃ u v x y, (u,v)∈rs ∧ a=x++u++y ∧ b=x++v++y := by
  cases h with
  | apply h x y => exact ⟨_,_,x,y,h,rfl,rfl⟩

/-- Critical-pair reduction, including disjoint, boundary and containment peaks. -/
theorem critical_localJoin {n : ℕ} (crit : Critical rs n) {w a b : List S}
    (hw : w.length≤n) (ha : Step rs w a) (hb : Step rs w b) : Join (Steps rs) a b := by
  obtain ⟨u,u',x,y,hu,rfl,rfl⟩ := step_decompose ha
  obtain ⟨v,v',a,b,hv,he,rfl⟩ := step_decompose hb
  rcases le_total x.length a.length with h | h
  · exact critical_ordered crit hu hv he hw h
  · obtain ⟨z,haz,hbz⟩ := critical_ordered crit hv hu he.symm (by simpa only [he] using hw) h
    exact ⟨z,hbz,haz⟩

end

section
open Relation Envelopes
namespace Selectors
variable {S : Type*}

namespace Markers
variable (a : Markers S)
theorem z_d : a.zero≠a.d := by have := a.distinct; simpa using (List.pairwise_cons.mp this).1 _ (by simp)
theorem z_l : a.zero≠a.l := by have := a.distinct; simpa using (List.pairwise_cons.mp this).1 _ (by simp)
theorem z_r : a.zero≠a.r := by have := a.distinct; simpa using (List.pairwise_cons.mp this).1 _ (by simp)
theorem z_h : a.zero≠a.h := by have := a.distinct; simpa using (List.pairwise_cons.mp this).1 _ (by simp)
theorem d_l : a.d≠a.l := by have := (List.pairwise_cons.mp a.distinct).2; exact (List.pairwise_cons.mp this).1 _ (by simp)
theorem d_r : a.d≠a.r := by have := (List.pairwise_cons.mp a.distinct).2; exact (List.pairwise_cons.mp this).1 _ (by simp)
theorem d_h : a.d≠a.h := by have := (List.pairwise_cons.mp a.distinct).2; exact (List.pairwise_cons.mp this).1 _ (by simp)
theorem l_r : a.l≠a.r := by have := (List.pairwise_cons.mp (List.pairwise_cons.mp a.distinct).2).2; exact (List.pairwise_cons.mp this).1 _ (by simp)
theorem l_h : a.l≠a.h := by have := (List.pairwise_cons.mp (List.pairwise_cons.mp a.distinct).2).2; exact (List.pairwise_cons.mp this).1 _ (by simp)
theorem r_h : a.r≠a.h := by have := (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp a.distinct).2).2).2; simpa using this

theorem wrap_avoids {N : ℕ} {w : List S} (hw : a.zero∉w) : a.zero∉a.wrap N w := by
  simp [wrap,frame,hw,a.z_d,a.z_l,a.z_r,a.z_h]
end Markers

variable [DecidableEq S] (a : Markers S)

theorem mem_rules {N : ℕ} {ws : List (List S)} {u v : List S} :
    (u,v)∈rules a N ws ↔ ∃ w∈ws, u=a.wrap N w ∧ v=if ws.head?=some w then [] else [a.zero] := by
  simp only [rules,List.mem_map,Prod.mk.injEq]
  aesop

/-- The only possible old left-side shapes at a selector stage. -/
def Old (N : ℕ) (u : List S) : Prop :=
  a.zero∈u ∨
  (u≠[] ∧ a.d∉u ∧ a.l∉u ∧ a.r∉u ∧ a.h∉u) ∨
  ∃ M w, u=a.wrap M w ∧ u.length<N

omit [DecidableEq S] in
theorem no_occurrence {rs : List (List S × List S)} {w u v : List S}
    (hw : Irreducible (Step rs) w) (hp : (u,v)∈rs) (hi : u <:+: w) : False := by
  obtain ⟨x,y,he⟩ := hi
  exact hw _ (he ▸ Step.apply hp x y)

omit [DecidableEq S] in
theorem old_in_new {rs : List (List S × List S)} {N : ℕ} {u v w : List S}
    (hu : Old a N u) (huz : a.zero∉u) (hp : (u,v)∈rs)
    (hw : Irreducible (Step rs) w) (hi : u <:+: a.wrap N w) : False := by
  rcases hu with hz | ⟨hn,hd,hl,hr,hh⟩ | ⟨M,t,rfl,hlen⟩
  · exact huz hz
  · exact no_occurrence hw hp (avoiding_infix_frame hn hd hl hr hh hi)
  · apply no_occurrence hw hp
    apply bounded_infix_frame a.d_l a.r_h.symm a.d_h.symm a.l_h.symm a.d_r
      (by simpa [Markers.wrap,frame,List.append_assoc] using Nat.le_of_lt hlen)
      (by simpa [Markers.wrap,frame,List.append_assoc] using hi)

omit [DecidableEq S] in
theorem new_in_old {N : ℕ} {u w : List S} (hu : Old a N u) (huz : a.zero∉u)
    (hi : a.wrap N w <:+: u) : False := by
  rcases hu with hz | ⟨_,hd,_,_,_⟩ | ⟨M,t,rfl,hlen⟩
  · exact huz hz
  · apply hd
    exact hi.subset (by simp [Markers.wrap,frame])
  · have hh := hi.length_le
    simp only [Markers.wrap,length_frame] at hh hlen
    omega

omit [DecidableEq S] in
theorem old_new_overlap {N : ℕ} {u w p m q : List S} (hu : Old a N u) (huz : a.zero∉u)
    (hm : m≠[]) (he : u=p++m) (hf : a.wrap N w=m++q) : False := by
  rcases hu with hz | ⟨_,hd,_,_,_⟩ | ⟨M,t,rfl,hlen⟩
  · exact huz hz
  · exact avoiding_frame_overlap_left hd hm he hf
  · exact short_long_overlap a.d_h.symm a.l_h.symm (by change (a.wrap M t).length≤N+1; omega) hm he hf

omit [DecidableEq S] in
theorem new_old_overlap {N : ℕ} {u w p m q : List S} (hu : Old a N u) (huz : a.zero∉u)
    (hm : m≠[]) (he : a.wrap N w=p++m) (hf : u=m++q) : False := by
  rcases hu with hz | ⟨_,_,_,_,hh⟩ | ⟨M,t,rfl,hlen⟩
  · exact huz hz
  · exact avoiding_frame_overlap_right hh hm he hf
  · exact long_short_overlap a.d_h a.d_r (by change (a.wrap M t).length≤N+1; omega) hm he hf

omit [DecidableEq S] in
theorem join_mono {rs rt : List (List S × List S)} (ht : ∀ p∈rs,p∈rt)
    {u v : List S} (h : Join (Steps rs) u v) : Join (Steps rt) u v := by
  obtain ⟨w,hu,hv⟩ := h
  exact ⟨w,steps_mono ht hu,steps_mono ht hv⟩

omit [DecidableEq S] in
theorem zero_join {rs : List (List S × List S)}
    (hz : Absorbs rs a.zero) (hp : ∀ p∈rs,a.zero∈p.1 → a.zero∈p.2)
    {w u v : List S} (hw : a.zero∈w) (hu : Step rs w u) (hv : Step rs w v) :
    Join (Steps rs) u v :=
  ⟨[a.zero],absorbs_mem hz (step_preserves_letter hp hw hu),
    absorbs_mem hz (step_preserves_letter hp hw hv)⟩

/-- The actual finite selector extension preserves the entire bounded critical
    condition, not just the disjoint cases. All irreducibility tests are on bodies. -/
theorem critical_extension {rs : List (List S × List S)} {N B : ℕ} {ws : List (List S)}
    (hz : Absorbs rs a.zero) (hp : ∀ p∈rs,a.zero∈p.1 → a.zero∈p.2)
    (hold : ∀ p∈rs,Old a N p.1)
    (hws : ∀ w∈ws, w.length<N ∧ a.zero∉w ∧ Irreducible (Step rs) w)
    (hc : Critical rs B) : Critical (rs++rules a N ws) B := by
  let rt := rs++rules a N ws
  have hinc : ∀ p∈rs,p∈rt := fun _ h => List.mem_append_left _ h
  have hz' : Absorbs rt a.zero := fun b => ⟨hinc _ (hz b).1,hinc _ (hz b).2⟩
  have hp' : ∀ p∈rt,a.zero∈p.1 → a.zero∈p.2 := by
    intro ⟨u,v⟩ ht hu
    rcases List.mem_append.mp ht with ht | ht
    · exact hp _ ht hu
    · obtain ⟨w,hw,rfl,rfl⟩ := (mem_rules a).mp ht
      exact False.elim (a.wrap_avoids (hws w hw).2.1 hu)
  constructor
  · intro u u' v v' hu hv x y he hlen
    by_cases huz : a.zero∈u
    · apply zero_join a hz' hp' huz
      · simpa using Step.apply hu [] []
      · simpa only [he] using Step.apply hv x y
    have hvz : a.zero∉v := fun hh => huz (by simp [he,hh])
    rcases List.mem_append.mp hu with hu | hu <;> rcases List.mem_append.mp hv with hv | hv
    · exact join_mono hinc (hc.1 _ _ _ _ hu hv x y he hlen)
    · obtain ⟨w,hw,rfl,rfl⟩ := (mem_rules a).mp hv
      exact False.elim (new_in_old a (hold _ hu) huz ⟨x,y,he.symm⟩)
    · obtain ⟨w,hw,rfl,rfl⟩ := (mem_rules a).mp hu
      exact False.elim (old_in_new a (hold _ hv) hvz hv (hws w hw).2.2 ⟨x,y,he.symm⟩)
    · obtain ⟨w,hw,rfl,rfl⟩ := (mem_rules a).mp hu
      obtain ⟨t,ht,rfl,rfl⟩ := (mem_rules a).mp hv
      obtain ⟨rfl,rfl,rfl⟩ := infix_frame a.d_l a.l_r a.l_h a.r_h.symm
        (hws w hw).1 (hws t ht).1 he
      exact ⟨_,.refl,by simpa using (ReflTransGen.refl : Steps (rs++rules a N ws) (if ws.head?=some w then [] else [a.zero]) _)⟩
  · intro u u' v v' hu hv p m q hm he hf hlen
    by_cases hwz : a.zero∈p++m++q
    · apply zero_join a hz' hp' hwz
      · simpa only [rt,he,List.append_assoc,List.nil_append] using Step.apply hu [] q
      · simpa only [rt,hf,List.append_assoc,List.append_nil] using Step.apply hv p []
    have huz : a.zero∉u := fun hh => hwz (by simpa only [he,List.mem_append] using Or.inl hh)
    have hvz : a.zero∉v := by
      intro hh
      apply hwz
      simp only [hf,List.mem_append] at hh
      simp only [List.mem_append]
      aesop
    rcases List.mem_append.mp hu with hu | hu <;> rcases List.mem_append.mp hv with hv | hv
    · exact join_mono hinc (hc.2 _ _ _ _ hu hv p m q hm he hf hlen)
    · obtain ⟨w,hw,rfl,rfl⟩ := (mem_rules a).mp hv
      exact False.elim (old_new_overlap a (hold _ hu) huz hm he hf)
    · obtain ⟨w,hw,rfl,rfl⟩ := (mem_rules a).mp hu
      exact False.elim (new_old_overlap a (hold _ hv) hvz hm he hf)
    · obtain ⟨w,hw,rfl,rfl⟩ := (mem_rules a).mp hu
      obtain ⟨t,ht,rfl,rfl⟩ := (mem_rules a).mp hv
      obtain ⟨rfl,rfl,rfl⟩ := overlap_frame a.d_l a.l_r a.l_h a.r_h.symm a.d_h.symm
        (hws w hw).1 (hws t ht).1 hm he hf
      exact ⟨if ws.head?=some w then [] else [a.zero],
        by simpa using (ReflTransGen.refl : Steps (rs++rules a N ws) (if ws.head?=some w then [] else [a.zero]) _),
        by simpa using (ReflTransGen.refl : Steps (rs++rules a N ws) (if ws.head?=some w then [] else [a.zero]) _)⟩

end Selectors
end

section
open Relation
namespace Selectors
variable {S : Type*} [DecidableEq S] (a : Markers S)

variable {a}

theorem allowed_iff {rs : List (List S × List S)} {s : Stage S} :
    allowed rs s = true ↔ ∀ w ∈ s.bodies, Irreducible (Step rs) w := by
  simp only [allowed,List.all_eq_true,Option.isNone_iff_eq_none]
  apply forall₂_congr
  intro w hw
  constructor
  · exact next_none
  · intro h
    cases hn : next rs w with
    | none => rfl
    | some v => exact False.elim (h v (next_sound hn))

omit [DecidableEq S] in
theorem irreducible_bounded {rs rt : List (List S × List S)} {k : ℕ}
    (hh : BoundedEq rs rt k) {w : List S} (hw : w.length ≤ k) :
    Irreducible (Step rs) w ↔ Irreducible (Step rt) w := by
  constructor <;> intro h v hv
  · exact h v ((step_stable hh hw).mpr hv)
  · exact h v ((step_stable hh hw).mp hv)

theorem choose_contains (rs : List (List S × List S)) (s : Stage S) (n : ℕ) :
    ∀ p ∈ rs,p ∈ choose (a:=a) rs s n := by
  intro p hp
  unfold choose
  split
  · exact List.mem_append_left _ hp
  · exact hp

theorem mem_choose {rs : List (List S × List S)} {s : Stage S} {n : ℕ} {p} :
    p ∈ choose (a:=a) rs s n → p ∈ rs ∨ p ∈ rules a s.size s.bodies := by
  unfold choose
  split
  · exact List.mem_append.mp
  · exact Or.inl

theorem choose_bounded {rs rt : List (List S × List S)} {k n : ℕ} {s : Stage S}
    (hkn : k ≤ n) (hh : BoundedEq rs rt k)
    (hbody : ∀ w ∈ s.bodies,w.length<s.size) :
    BoundedEq (choose (a:=a) rs s k) (choose (a:=a) rt s n) k := by
  by_cases hsk : s.size ≤ k
  · have hs : allowed rs s = true ↔ allowed rt s = true := by
      rw [allowed_iff,allowed_iff]
      exact forall₂_congr (fun w hw => irreducible_bounded hh ((Nat.le_of_lt (hbody w hw)).trans hsk))
    intro p hp
    simp only [choose,hsk,hsk.trans hkn,true_and,hs]
    split
    · simp only [List.mem_append,hh p hp]
    · exact hh p hp
  · have hnew : ∀ p ∈ rules a s.size s.bodies, ¬p.1.length ≤ k := by
      intro ⟨u,v⟩ hp hl
      obtain ⟨w,_,rfl,_⟩ := (mem_rules a).mp hp
      simp only [Markers.wrap,Envelopes.length_frame] at hl
      omega
    intro p hp
    have hn : p∉rules a s.size s.bodies := fun hm => hnew _ hm hp
    simp only [choose,hsk,false_and,↓reduceIte]
    split
    · simp only [List.mem_append,hn,or_false,hh p hp]
    · exact hh p hp

theorem process_bounded {base small : List (List S × List S)} {stages : ℕ → Stage S}
    {k n : ℕ} (hkn : k ≤ n) (hh : BoundedEq small base k)
    (hb : ∀ j w, w ∈ (stages j).bodies → w.length<(stages j).size) (j : ℕ) :
    BoundedEq (process (a:=a) small stages k j) (process (a:=a) base stages n j) k := by
  induction j with
  | zero => exact hh
  | succ j ih => exact choose_bounded hkn ih (hb j)

theorem process_members {base : List (List S × List S)} {stages : ℕ → Stage S} {n j : ℕ} {p} :
    p ∈ process (a:=a) base stages n j → p ∈ base ∨ ∃ i<j,p ∈ rules a (stages i).size (stages i).bodies := by
  induction j with
  | zero => exact Or.inl
  | succ j ih =>
    intro hp
    rcases mem_choose hp with hp | hp
    · rcases ih hp with hp | ⟨i,hi,hp⟩
      · exact Or.inl hp
      · exact Or.inr ⟨i,by omega,hp⟩
    · exact Or.inr ⟨j,by omega,hp⟩

theorem process_contains (base : List (List S × List S)) (stages : ℕ → Stage S) (n j : ℕ) :
    ∀ p ∈ base,p ∈ process (a:=a) base stages n j := by
  induction j with
  | zero => exact fun _ h => h
  | succ j ih => exact fun p h => choose_contains _ _ _ p (ih p h)

theorem process_zero {base : List (List S × List S)} {stages : ℕ → Stage S} {n j : ℕ}
    (hb : ∀ p ∈ base,a.zero ∈ p.1 → a.zero ∈ p.2)
    (hz : ∀ i w, w ∈ (stages i).bodies → a.zero∉w) :
    ∀ p ∈ process (a:=a) base stages n j,a.zero ∈ p.1 → a.zero ∈ p.2 := by
  intro ⟨u,v⟩ hp hu
  rcases process_members hp with hp | ⟨i,_,hp⟩
  · exact hb _ hp hu
  · obtain ⟨w,hw,rfl,_⟩ := (mem_rules a).mp hp
    exact False.elim (a.wrap_avoids (hz i w hw) hu)

/-- Full consecutive selector processing preserves critical joins.  The spacing
    is required for *all potential* earlier sides, selected or not. -/
theorem process_critical {base : List (List S × List S)} {stages : ℕ → Stage S} {n : ℕ}
    (hz : Absorbs base a.zero) (hp : ∀ p ∈ base,a.zero ∈ p.1 → a.zero ∈ p.2)
    (hold : ∀ p ∈ base,a.zero ∈ p.1 ∨ (p.1≠[] ∧ a.d∉p.1 ∧ a.l∉p.1 ∧ a.r∉p.1 ∧ a.h∉p.1))
    (hbody : ∀ i w, w ∈ (stages i).bodies → w.length<(stages i).size ∧ a.zero∉w)
    (hspace : ∀ i j, i<j → ∀ w ∈ (stages i).bodies,(a.wrap (stages i).size w).length<(stages j).size)
    (hc : Critical base n) (j : ℕ) : Critical (process (a:=a) base stages n j) n := by
  induction j with
  | zero => exact hc
  | succ j ih =>
    simp only [process,choose]
    split
    next hs =>
      apply critical_extension a
      · intro b
        exact ⟨process_contains _ _ _ _ _ (hz b).1,process_contains _ _ _ _ _ (hz b).2⟩
      · exact process_zero hp (fun i w hw => (hbody i w hw).2)
      · intro ⟨u,v⟩ hu
        rcases process_members hu with hu | ⟨i,hi,hu⟩
        · rcases hold _ hu with hh | hh
          · exact Or.inl hh
          · exact Or.inr (Or.inl hh)
        · obtain ⟨w,hw,rfl,_⟩ := (mem_rules a).mp hu
          exact Or.inr (Or.inr ⟨_,_,rfl,hspace i j hi w hw⟩)
      · intro w hw
        exact ⟨(hbody j w hw).1,(hbody j w hw).2,allowed_iff.mp hs.2 w hw⟩
      · exact ih
    next hs => exact ih

theorem choose_inert {rs : List (List S × List S)} {s : Stage S} {n k : ℕ}
    (hs : k  ≤  s.size) : BoundedEq rs (choose (a:=a) rs s n) k := by
  intro p hp
  constructor
  · exact choose_contains _ _ _ _
  · intro hm
    rcases mem_choose hm with hm | hm
    · exact hm
    · rcases p with ⟨u,v⟩
      obtain ⟨w,_,rfl,_⟩ := (mem_rules a).mp hm
      simp only [Markers.wrap,Envelopes.length_frame] at hp
      omega

theorem process_future {base : List (List S × List S)} {stages : ℕ → Stage S}
    {k n lo hi : ℕ} (hle : lo ≤ hi)
    (hs : ∀ j, lo ≤ j → k ≤ (stages j).size) :
    BoundedEq (process (a:=a) base stages n lo) (process (a:=a) base stages n hi) k := by
  induction hi,hle using Nat.le_induction with
  | base => exact boundedEq_refl _ _
  | succ j hj ih => exact boundedEq_trans ih (choose_inert (hs j hj))

/-- Stability for the literal completed tables, whose number of examined tuples
    varies with the normalization bound. -/
theorem tables_bounded {bases : ℕ → List (List S × List S)} {stages : ℕ → Stage S}
    (hb : ∀ k n, k ≤ n → BoundedEq (bases k) (bases n) k)
    (hlen : ∀ j w, w ∈ (stages j).bodies → w.length<(stages j).size)
    (hsize : ∀ j, j<(stages j).size) {k n : ℕ} (hkn : k ≤ n) :
    BoundedEq (process (a:=a) (bases k) stages k k)
      (process (a:=a) (bases n) stages n n) k :=
  boundedEq_trans (process_bounded hkn (hb k n hkn) hlen k)
    (process_future hkn (fun j hj => hj.trans (Nat.le_of_lt (hsize j))))

theorem rules_decrease {r : S → S → Prop} (s : Stage S) :
    ∀ p ∈ rules a s.size s.bodies, List.Shortlex r p.2 p.1 := by
  intro ⟨u,v⟩ hp
  obtain ⟨w,_,rfl,rfl⟩ := (mem_rules a).mp hp
  apply List.Shortlex.of_length_lt
  simp only [Markers.wrap,Envelopes.length_frame]
  split <;> simp
  omega

theorem process_decrease {r : S → S → Prop} {base : List (List S × List S)}
    (hd : ∀ p ∈ base,List.Shortlex r p.2 p.1) (stages : ℕ → Stage S) (n j : ℕ) :
    ∀ p ∈ process (a:=a) base stages n j,List.Shortlex r p.2 p.1 := by
  intro p hp
  rcases process_members hp with hp | ⟨i,_,hp⟩
  · exact hd p hp
  · exact rules_decrease _ p hp

end Selectors
end

namespace Canonical
variable {A Q : Type*} {r : A → A → Prop} [DecidableEq Q] [DecidableRel (List.Shortlex r)]

def pick (pairs : List (List A × Q)) (w : List A) (q : Q) : List A :=
  pairs.foldl (pickStep (r:=r) q) w

variable (wf : WellFounded r) (q : List A → Q)

theorem pick_class {ps : List (List A × Q)} {w v : List A}
    (hps : ∀ p ∈ ps,p.2=q p.1) (hv : q v=q w) : q (pick (r:=r) ps v (q w))=q w := by
  induction ps generalizing v with
  | nil => exact hv
  | cons p ps ih =>
    simp only [pick,List.foldl_cons]
    apply ih (fun p hp => hps p (List.mem_cons_of_mem _ hp))
    simp only [pickStep]
    split
    next h => exact (hps p (List.mem_cons_self)).symm.trans h.1
    next h => exact hv

theorem pick_least_fixed {ps : List (List A × Q)} {w : List A}
    (hps : ∀ p ∈ ps,p.2=q p.1) :
    pick (r:=r) ps (least wf q w) (q w)=least wf q w := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hh : ¬ (p.2=q w ∧ List.Shortlex r p.1 (least wf q w)) := by
      rintro ⟨hq,hr⟩
      exact least_global_min wf q ((hps p List.mem_cons_self).symm.trans hq) hr
    simp only [pick,List.foldl_cons,pickStep,ite_eq_right hh]
    exact ih (fun p hp => hps p (List.mem_cons_of_mem _ hp))

variable [Std.Trichotomous r]

/-- The finite answer list computes the same least shortlex representative as
    the manuscript, even though it tests every word in the common length ball. -/
theorem pick_eq_least {ps : List (List A × Q)} {w : List A}
    (hps : ∀ p ∈ ps,p.2=q p.1) (hm : (least wf q w,q w) ∈ ps) :
    pick (r:=r) ps w (q w)=least wf q w := by
  obtain ⟨before,after,rfl⟩ := List.mem_iff_append.mp hm
  have hb : ∀ p ∈ before,p.2=q p.1 := fun p hp => hps p (List.mem_append_left _ hp)
  have ha : ∀ p ∈ after,p.2=q p.1 := fun p hp =>
    hps p (List.mem_append_right _ (List.mem_cons_of_mem _ hp))
  have hclass := pick_class (r:=r) q hb (w:=w) rfl
  have hsel : pickStep (r:=r) (q w) (pick (r:=r) before w (q w)) (least wf q w,q w) = least wf q w := by
    unfold pickStep
    simp only [true_and]
    split
    · rfl
    next h =>
      apply Std.Trichotomous.trichotomous (r:=List.Shortlex r)
      · exact least_global_min wf q hclass
      · exact h
  simp only [pick,List.foldl_append,List.foldl_cons]
  change after.foldl (pickStep (r:=r) (q w))
    (pickStep (r:=r) (q w) (pick (r:=r) before w (q w)) (least wf q w,q w)) = _
  rw [hsel]
  exact pick_least_fixed wf q ha

end Canonical

namespace Search

variable {A S Q : Type*} [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [DecidableRel (List.Shortlex r)]

def output (C : BlockCode A S) (z : S) (ps : List (List A × Option Q))
    (p : List A × Option Q) : List S :=
  if p.2=none then [z] else C.encode (Canonical.pick (r:=r) ps p.1 p.2)

def table (C : BlockCode A S) (z : S) (ps : List (List A × Option Q)) : List (List S × List S) :=
  ps.flatMap fun p =>
    if p.1≠[] ∧ output (r:=r) C z ps p≠C.encode p.1 then [(C.encode p.1,output (r:=r) C z ps p)] else []

noncomputable def compute [Fintype A] (C : BlockCode A S) (z : S)
    (q : List A → Part (Option Q)) (n : ℕ) : Part (List (List S × List S)) :=
  (Effect.traverse (fun w => (q w).map (w,·)) (Static.words A n)).map (table (r:=r) C z)

theorem traverse_map {X Y : Type*} (f : X → Part Y) (g : X → Y) (l : List X)
    (h : ∀ x∈l, g x ∈ f x) : l.map g ∈ Effect.traverse f l := by
  induction l with
  | nil => exact Part.mem_some _
  | cons x xs ih =>
    exact Part.mem_bind_iff.mpr ⟨g x,h x List.mem_cons_self,
      (Part.mem_map_iff _).mpr ⟨xs.map g,ih (fun x hx => h x (List.mem_cons_of_mem _ hx)),rfl⟩⟩

variable [Fintype A] [Std.Trichotomous r] (wf : WellFounded r) (q : List A → Option Q)

omit [DecidableEq A] [DecidableEq S] in
 theorem output_full (C : BlockCode A S) (z : S) {n : ℕ} {w : List A} (hw : w.length≤n) :
    output (r:=r) C z ((Static.words A n).map fun v => (v,q v)) (w,q w) = Static.output C wf q z w := by
  have hps : ∀ p∈(Static.words A n).map (fun v => (v,q v)),p.2=q p.1 := by
    intro p hp
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hp
    rfl
  have hm : (Canonical.least wf q w,q w)∈(Static.words A n).map (fun v => (v,q v)) :=
    List.mem_map.mpr ⟨Canonical.least wf q w,(Static.mem_words _ _).mpr
      ((Canonical.least_length wf q w).trans hw),by simp [Canonical.least_class]⟩
  simp only [output,Static.output,Canonical.pick_eq_least wf q hps hm]

omit [DecidableEq A] in
 theorem table_full (C : BlockCode A S) (z : S) (n : ℕ) :
    table (r:=r) C z ((Static.words A n).map fun v => (v,q v))=Static.table C wf q z n := by
  unfold table Static.table
  rw [List.flatMap_map]
  have hh : ∀ w∈Static.words A n,
      (if w≠[] ∧ output (r:=r) C z ((Static.words A n).map fun v => (v,q v)) (w,q w)≠C.encode w
        then [(C.encode w,output (r:=r) C z ((Static.words A n).map fun v => (v,q v)) (w,q w))] else []) =
      (if w≠[] ∧ Static.output C wf q z w≠C.encode w
        then [(C.encode w,Static.output C wf q z w)] else []) := by
    intro w hw
    rw [output_full wf q C z ((Static.mem_words _ _).mp hw)]
  rw [List.flatMap_congr hh]
  have he (l : List (List A)) :
      l.flatMap (fun w => if w≠[] ∧ Static.output C wf q z w≠C.encode w
        then [(C.encode w,Static.output C wf q z w)] else []) =
      (l.filter fun w => w≠[] ∧ Static.output C wf q z w≠C.encode w).map
        (fun w => (C.encode w,Static.output C wf q z w)) := by
    induction l with
    | nil => rfl
    | cons w l ih =>
      by_cases hh : w≠[] ∧ Static.output C wf q z w≠C.encode w
      · simp only [List.flatMap_cons,List.filter_cons,decide_eq_true_eq,ite_eq_left hh,List.map_cons,List.singleton_append,ih]
      · simp only [List.flatMap_cons,List.filter_cons,decide_eq_true_eq,ite_eq_right hh,List.nil_append,ih]
  exact he _

omit [DecidableEq A] in
 theorem compute_full (C : BlockCode A S) (z : S) {f : List A → Part (Option Q)} {n : ℕ}
    (h : ∀ w,w.length≤n → q w ∈ f w) :
    Static.table C wf q z n ∈ compute (r:=r) C z f n := by
  apply (Part.mem_map_iff _).mpr
  refine ⟨(Static.words A n).map (fun w => (w,q w)),?_,table_full wf q C z n⟩
  apply traverse_map
  intro w hw
  exact (Part.mem_map_iff _).mpr ⟨q w,h w ((Static.mem_words _ _).mp hw),rfl⟩

end Search
end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap.Selectors

section
variable {S : Type*} [DecidableEq S] [Primcodable S]

omit [DecidableEq S] [Primcodable S] in
theorem length_le_maxLength {ws : List (List S)} {w : List S} (hw : w∈ws) : w.length ≤ maxLength ws := by
  induction ws with
  | nil => simp at hw
  | cons v vs ih =>
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact le_max_left _ _
    · exact (ih hw).trans (le_max_right _ _)

theorem tuples_valid (z : S) (i : ℕ) :
    tuples z i≠[] ∧ (tuples z i).Nodup ∧ ∀ w∈tuples z i,z∉w := by
  unfold tuples
  dsimp only
  split
  · assumption
  · simp

theorem index_lt_size (z : S) (i : ℕ) : i < sizes z i := by
  cases i with
  | zero => simp [sizes]
  | succ i =>
    have h : i+2 ≤ sizes z (i+1) := (le_max_left _ _).trans (le_max_left _ _)
    omega

 theorem body_lt_size (z : S) (i : ℕ) {w : List S} (hw : w∈tuples z i) : w.length < sizes z i := by
  have hh := length_le_maxLength hw
  cases i with
  | zero => simp only [sizes]; omega
  | succ i =>
    have h : maxLength (tuples z (i+1))+1 ≤ sizes z (i+1) := (le_max_right _ _).trans (le_max_left _ _)
    omega

 theorem sizes_step (z : S) (i : ℕ) : 2*sizes z i+2+maxLength (tuples z i) < sizes z (i+1) := by
  have : 2*sizes z i+3+maxLength (tuples z i) ≤ sizes z (i+1) := le_max_right _ _
  omega

 theorem sizes_strictMono (z : S) : StrictMono (sizes z) := by
  apply strictMono_nat_of_lt_succ
  intro i
  have := sizes_step z i
  omega

 theorem stage_spacing (a : Markers S) {i j : ℕ} (hij : i < j) {w : List S}
    (hw : w∈(stages a.zero i).bodies) :
    (a.wrap (stages a.zero i).size w).length < (stages a.zero j).size := by
  have hw' := length_le_maxLength hw
  have hs := sizes_step a.zero i
  have hj := (sizes_strictMono a.zero).monotone (Nat.succ_le_of_lt hij)
  change sizes a.zero (i+1) ≤ sizes a.zero j at hj
  simp only [Markers.wrap,Envelopes.length_frame,stages]
  change w.length ≤ maxLength (tuples a.zero i) at hw'
  omega

end

end FiniteAlgebraicEnvelopes.Bootstrap.Selectors

end OAI
end

section
-- module Solutions.OAIFAE.Quotients
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical compiler quotients and effective tested classes for word problems.
-/

namespace FiniteAlgebraicEnvelopes.Bootstrap
open Relation

namespace Static
variable {S A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [Std.Trichotomous r]
variable (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (z : S)

omit [DecidableEq A] [DecidableEq Q] in
theorem table_decrease {s : S → S → Prop} (hwidth : 1<C.width+1)
    (hc : ∀ a b, r a b → List.Lex s (C.block a) (C.block b)) (n : ℕ) :
    ∀ p ∈ table C wf q z n,List.Shortlex s p.2 p.1 := by
  intro ⟨u,v⟩ hp
  obtain ⟨w,_,hn,he,rfl,rfl⟩ := (mem_table C wf q z).mp hp
  unfold output
  split
  · apply List.Shortlex.of_length_lt
    simp only [List.length_singleton,C.encode_length]
    have hw : 1 ≤ w.length := by have := List.length_pos_iff.mpr hn; omega
    nlinarith
  · obtain h | h := Canonical.least_lt_or_eq wf q w
    · exact C.encode_shortlex hc h
    · exact False.elim (he (by simp_all [output]))

omit [DecidableEq A] [DecidableEq Q] [Std.Trichotomous r] in
theorem table_bounded {k n : ℕ} (hkn : k ≤ n) :
    Selectors.BoundedEq (table C wf q z (k/(C.width+1))) (table C wf q z (n/(C.width+1))) k := by
  intro ⟨u,v⟩ hu
  simp only [mem_table]
  constructor
  · rintro ⟨w,hw,hn,he,rfl,rfl⟩
    exact ⟨w,hw.trans (Nat.div_le_div_right hkn),hn,he,rfl,rfl⟩
  · rintro ⟨w,hw,hn,he,rfl,rfl⟩
    refine ⟨w,?_,hn,he,rfl,rfl⟩
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr
    simpa only [C.encode_length,Nat.mul_comm] using hu

end Static

namespace Base
variable {S A B Q R : Type*} [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop} [Std.Trichotomous r] [Std.Trichotomous s]
variable (C : BlockCode A S) (D : BlockCode B S) (wf : WellFounded r) (wg : WellFounded s)
  (f : List A → Option Q) (g : List B → Option R) (z : S)

omit [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R] in
/-- All static and absorption critical pairs for the literal two-code base table. -/
theorem critical (hC : z ∉ C.Alphabet) (hD : z ∉ D.Alphabet)
    (hdis : Disjoint C.Alphabet D.Alphabet) {n : ℕ}
    (hf : f [] ≠ none) (hg : g [] ≠ none)
    (hfc : Static.Contextual f (n/(C.width+1))) (hfi : Static.ZeroIdeal f (n/(C.width+1)))
    (hgc : Static.Contextual g (n/(D.width+1))) (hgi : Static.ZeroIdeal g (n/(D.width+1))) :
    Critical (table C D wf wg f g z n) n := by
  let rs := table C D wf wg f g z n
  have hz : Absorbs rs z := absorbs C D wf wg f g z n
  have hp := preserves_zero C D wf wg f g z hC hD n
  have hCt : ∀ p ∈ Static.table C wf f z (n/(C.width+1)),p ∈ rs :=
    fun _ h => (mem_table C D wf wg f g z).mpr (.inr (.inl h))
  have hDt : ∀ p ∈ Static.table D wg g z (n/(D.width+1)),p ∈ rs :=
    fun _ h => (mem_table C D wf wg f g z).mpr (.inr (.inr h))
  have hzero {w u v : List S} (hw : z ∈ w) (hu : Step rs w u) (hv : Step rs w v) :
      Join (Steps rs) u v :=
    ⟨[z],absorbs_mem hz (step_preserves_letter hp hw hu),
      absorbs_mem hz (step_preserves_letter hp hw hv)⟩
  have hnabs {u v : List S} (h : z ∉ u) : (u,v) ∉ absorption z := by
    rintro hh
    obtain ⟨a,ha,_⟩ := (mem_absorption z).mp hh
    rcases ha with rfl | rfl <;> simp at h
  constructor
  · intro u u' v v' hu hv x y he hlen
    by_cases huz : z ∈ u
    · apply hzero huz
      · simpa using Step.apply hu [] []
      · simpa only [he] using Step.apply hv x y
    have hvz : z ∉ v := fun hh => huz (by simp [he,hh])
    have hu' := (mem_table C D wf wg f g z).mp hu
    have hv' := (mem_table C D wf wg f g z).mp hv
    simp only [hnabs huz,hnabs hvz,false_or] at hu' hv'
    rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv'
    · exact Static.critical_containment_bound C wf f z hf hz hCt hfc hfi hu' hv' he hlen
    · obtain ⟨a,_,_,_,rfl,_⟩ := (Static.mem_table C wf f z).mp hu'
      obtain ⟨b,_,hb,_,rfl,_⟩ := (Static.mem_table D wg g z).mp hv'
      exact False.elim (C.disjoint_infix D hdis hb ⟨x,y,he.symm⟩)
    · obtain ⟨a,_,_,_,rfl,_⟩ := (Static.mem_table D wg g z).mp hu'
      obtain ⟨b,_,hb,_,rfl,_⟩ := (Static.mem_table C wf f z).mp hv'
      exact False.elim (D.disjoint_infix C hdis.symm hb ⟨x,y,he.symm⟩)
    · exact Static.critical_containment_bound D wg g z hg hz hDt hgc hgi hu' hv' he hlen
  · intro u u' v v' hu hv p m t hm he hh hlen
    by_cases hwz : z ∈ p++m++t
    · apply hzero hwz
      · simpa only [he,List.nil_append,List.append_assoc] using Step.apply hu [] t
      · simpa only [hh,List.append_nil,List.append_assoc] using Step.apply hv p []
    have huz : z ∉ u := fun h => hwz (by simp [←he,h])
    have hvz : z ∉ v := fun h => hwz (by simpa only [List.append_assoc,←hh,List.mem_append] using Or.inr h)
    have hu' := (mem_table C D wf wg f g z).mp hu
    have hv' := (mem_table C D wf wg f g z).mp hv
    simp only [hnabs huz,hnabs hvz,false_or] at hu' hv'
    rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv'
    · exact Static.critical_overlap_bound C wf f z hf hz hCt hfc hfi hu' hv' hm he hh hlen
    · obtain ⟨a,_,_,_,rfl,_⟩ := (Static.mem_table C wf f z).mp hu'
      obtain ⟨b,_,_,_,rfl,_⟩ := (Static.mem_table D wg g z).mp hv'
      exact False.elim (C.disjoint_overlap D hdis hm he hh)
    · obtain ⟨a,_,_,_,rfl,_⟩ := (Static.mem_table D wg g z).mp hu'
      obtain ⟨b,_,_,_,rfl,_⟩ := (Static.mem_table C wf f z).mp hv'
      exact False.elim (D.disjoint_overlap C hdis.symm hm he hh)
    · exact Static.critical_overlap_bound D wg g z hg hz hDt hgc hgi hu' hv' hm he hh hlen

end Base

open Relation
variable {S : Type*} [DecidableEq S] {r : S → S → Prop}

/-- The actual partial table-first procedure used at the fixed point. -/
def tableNormal (T : ℕ → Part (List (List S × List S))) (w : List S) : Part (List S) :=
  (T w.length).bind (fun rs => evaluate rs w)

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes
namespace Effect
variable {X A B : Type*}

theorem traverse_domain {f : A → Part B} {l : List A} (h : (traverse f l).Dom) :
    ∀ a∈l,(f a).Dom := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨out,ho⟩ := Part.dom_iff_mem.mp h
    obtain ⟨b,hb,ht⟩ := Part.mem_bind_iff.mp ho
    obtain ⟨bs,hbs,_⟩ := (Part.mem_map_iff _).mp ht
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hb.1
    · exact ih hbs.1 x hx

end Effect

namespace Bootstrap
namespace Search
variable {A S Q : Type*} [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [DecidableRel (List.Shortlex r)]

omit [DecidableEq A] [DecidableEq S] [DecidableEq Q] [DecidableRel (List.Shortlex r)] in
theorem value_mem {f : List A → Part (Option Q)} {w : List A} (h : (f w).Dom) : value f w ∈ f w := by
  simp only [value,dite_eq_left h]
  exact Part.get_mem h

variable [Fintype A] [Std.Trichotomous r] (wf : WellFounded r)

omit [DecidableEq A] [Std.Trichotomous r] in
theorem compute_domain (C : BlockCode A S) (z : S) {f : List A → Part (Option Q)} {n : ℕ}
    (hc : (compute (r:=r) C z f n).Dom) : ∀ w,w.length ≤ n → (f w).Dom := by
  obtain ⟨rs,hrs⟩ := Part.dom_iff_mem.mp hc
  obtain ⟨ps,hps,_⟩ := (Part.mem_map_iff _).mp hrs
  have ht := Effect.traverse_domain hps.1
  intro w hw
  have hww := ht w ((Static.mem_words _ _).mpr hw)
  obtain ⟨p,hp⟩ := Part.dom_iff_mem.mp hww
  obtain ⟨v,hv,_⟩ := (Part.mem_map_iff _).mp hp
  exact hv.1

omit [DecidableEq A] in
theorem compute_eq (C : BlockCode A S) (z : S) {f : List A → Part (Option Q)} {n : ℕ}
    {rs : List (List S × List S)} (hc : rs ∈ compute (r:=r) C z f n) :
    rs=Static.table C wf (value f) z n := by
  exact Part.mem_unique hc (compute_full wf (value f) C z
    (fun w hw => value_mem (compute_domain C z hc.1 w hw)))

end Search

namespace Build
variable {S A B Q R : Type*} [Primcodable S] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop}
  [DecidableRel (List.Shortlex r)] [DecidableRel (List.Shortlex s)]
variable (a : Selectors.Markers S) (C : BlockCode A S) (D : BlockCode B S)

noncomputable def bases (f : List A → Part (Option Q)) (g : List B → Part (Option R)) (n : ℕ) :
    Part (List (List S × List S)) :=
  (Search.compute (r:=r) C a.zero f (n/(C.width+1))).bind fun rc =>
    (Search.compute (r:=s) D a.zero g (n/(D.width+1))).map fun rd => Base.absorption a.zero ++ rc ++ rd

noncomputable def tables (f : List A → Part (Option Q)) (g : List B → Part (Option R)) (n : ℕ) :
    Part (List (List S × List S)) :=
  (bases (r:=r) (s:=s) a C D f g n).map fun b =>
    Selectors.process (a:=a) b (Selectors.stages a.zero) n n

variable [Std.Trichotomous r] [Std.Trichotomous s] (wf : WellFounded r) (wg : WellFounded s)

omit [Primcodable S] [DecidableEq A] [DecidableEq B] in
theorem bases_eq {f : List A → Part (Option Q)} {g : List B → Part (Option R)}
    {n : ℕ} {rs : List (List S × List S)} (h : rs ∈ bases (r:=r) (s:=s) a C D f g n) :
    rs=Base.table C D wf wg (Search.value f) (Search.value g) a.zero n := by
  obtain ⟨rc,hrc,ht⟩ := Part.mem_bind_iff.mp h
  obtain ⟨rd,hrd,rfl⟩ := (Part.mem_map_iff _).mp ht
  rw [Search.compute_eq wf C a.zero hrc,Search.compute_eq wg D a.zero hrd]
  rfl

omit [DecidableEq A] [DecidableEq B] in
theorem tables_eq {f : List A → Part (Option Q)} {g : List B → Part (Option R)}
    {n : ℕ} {rs : List (List S × List S)} (h : rs ∈ tables (r:=r) (s:=s) a C D f g n) :
    rs=Selectors.process (a:=a) (Base.table C D wf wg (Search.value f) (Search.value g) a.zero n)
      (Selectors.stages a.zero) n n := by
  obtain ⟨b,hb,rfl⟩ := (Part.mem_map_iff _).mp h
  rw [bases_eq a C D wf wg hb]

end Build

end Bootstrap
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap

section
namespace Base
variable {S A B Q R : Type*} [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop} [Std.Trichotomous r] [Std.Trichotomous s]
variable (C : BlockCode A S) (D : BlockCode B S) (wf : WellFounded r) (wg : WellFounded s)
  (f : List A → Option Q) (g : List B → Option R) (z : S)

omit [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
  [Std.Trichotomous r] [Std.Trichotomous s] in
theorem bounded {k n : ℕ} (hkn : k ≤ n) :
    Selectors.BoundedEq (table C D wf wg f g z k) (table C D wf wg f g z n) k := by
  intro p hp
  rw [mem_table,mem_table]
  exact or_congr Iff.rfl (or_congr (Static.table_bounded C wf f z hkn p hp)
    (Static.table_bounded D wg g z hkn p hp))

omit [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R] in
theorem decrease {t : S → S → Prop} (hcw : 1<C.width+1) (hdw : 1<D.width+1)
    (hc : ∀ a b,r a b → List.Lex t (C.block a) (C.block b))
    (hd : ∀ a b,s a b → List.Lex t (D.block a) (D.block b)) (n : ℕ) :
    ∀ p ∈ table C D wf wg f g z n,List.Shortlex t p.2 p.1 := by
  intro ⟨u,v⟩ hp
  rcases (mem_table C D wf wg f g z).mp hp with hp | hp | hp
  · obtain ⟨a,hu,rfl⟩ := (mem_absorption z).mp hp
    rcases hu with rfl | rfl <;> exact List.Shortlex.of_length_lt (by simp)
  · exact Static.table_decrease C wf f z hcw hc _ _ hp
  · exact Static.table_decrease D wg g z hdw hd _ _ hp

omit [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
  [Std.Trichotomous r] [Std.Trichotomous s] in
theorem shapes (a : Selectors.Markers S)
    (hC : ∀ b∈[a.d,a.l,a.r,a.h],b∉C.Alphabet)
    (hD : ∀ b∈[a.d,a.l,a.r,a.h],b∉D.Alphabet) (n : ℕ) :
    ∀ p ∈ table C D wf wg f g a.zero n,
      a.zero∈p.1 ∨ (p.1≠[] ∧ a.d∉p.1 ∧ a.l∉p.1 ∧ a.r∉p.1 ∧ a.h∉p.1) := by
  intro ⟨u,v⟩ hp
  rcases (mem_table C D wf wg f g a.zero).mp hp with hp | hp | hp
  · obtain ⟨b,hu,_⟩ := (mem_absorption a.zero).mp hp
    rcases hu with rfl | rfl <;> exact Or.inl (by simp)
  · obtain ⟨hn,hs⟩ := Static.table_support C wf f a.zero hp
    exact Or.inr ⟨hn,fun h => hC _ (by simp) (hs _ h),fun h => hC _ (by simp) (hs _ h),
      fun h => hC _ (by simp) (hs _ h),fun h => hC _ (by simp) (hs _ h)⟩
  · obtain ⟨hn,hs⟩ := Static.table_support D wg g a.zero hp
    exact Or.inr ⟨hn,fun h => hD _ (by simp) (hs _ h),fun h => hD _ (by simp) (hs _ h),
      fun h => hD _ (by simp) (hs _ h),fun h => hD _ (by simp) (hs _ h)⟩
end Base

namespace Build
variable {S A B Q R : Type*} [Primcodable S] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop}
  [DecidableRel (List.Shortlex r)] [DecidableRel (List.Shortlex s)]
  [Std.Trichotomous r] [Std.Trichotomous s]
variable (a : Selectors.Markers S) (C : BlockCode A S) (D : BlockCode B S)
  (wf : WellFounded r) (wg : WellFounded s)
variable (f : List A → Part (Option Q)) (g : List B → Part (Option R))

omit [Primcodable S] [DecidableEq A] [DecidableEq B] in
theorem bases_full {n : ℕ}
    (hf : ∀ w,w.length ≤ n/(C.width+1) → (f w).Dom)
    (hg : ∀ w,w.length ≤ n/(D.width+1) → (g w).Dom) :
    Base.table C D wf wg (Search.value f) (Search.value g) a.zero n ∈ bases (r:=r) (s:=s) a C D f g n := by
  refine Part.mem_bind_iff.mpr ⟨_,Search.compute_full wf (Search.value f) C a.zero
    (fun w hw => Search.value_mem (hf w hw)),?_⟩
  exact (Part.mem_map_iff _).mpr ⟨_,Search.compute_full wg (Search.value g) D a.zero
    (fun w hw => Search.value_mem (hg w hw)),rfl⟩

omit [DecidableEq A] [DecidableEq B] in
theorem tables_full {n : ℕ}
    (hf : ∀ w,w.length ≤ n/(C.width+1) → (f w).Dom)
    (hg : ∀ w,w.length ≤ n/(D.width+1) → (g w).Dom) :
    Selectors.process (a:=a) (Base.table C D wf wg (Search.value f) (Search.value g) a.zero n)
      (Selectors.stages a.zero) n n ∈ tables (r:=r) (s:=s) a C D f g n :=
  (Part.mem_map_iff _).mpr ⟨_,bases_full a C D wf wg f g hf hg,rfl⟩

include wf wg in
omit [DecidableEq A] [DecidableEq B] in
theorem good {t : S → S → Prop} (hcw : 1<C.width+1) (hdw : 1<D.width+1)
    (hc : ∀ a b,r a b → List.Lex t (C.block a) (C.block b))
    (hd : ∀ a b,s a b → List.Lex t (D.block a) (D.block b))
    (hC : ∀ b∈[a.zero,a.d,a.l,a.r,a.h],b∉C.Alphabet)
    (hD : ∀ b∈[a.zero,a.d,a.l,a.r,a.h],b∉D.Alphabet)
    (hCD : Disjoint C.Alphabet D.Alphabet) {n : ℕ}
    (hf : ∀ w,w.length ≤ n/(C.width+1) → (f w).Dom)
    (hg : ∀ w,w.length ≤ n/(D.width+1) → (g w).Dom)
    (hf0 : Search.value f []≠none) (hg0 : Search.value g []≠none)
    (hfc : Static.Contextual (Search.value f) (n/(C.width+1)))
    (hfi : Static.ZeroIdeal (Search.value f) (n/(C.width+1)))
    (hgc : Static.Contextual (Search.value g) (n/(D.width+1)))
    (hgi : Static.ZeroIdeal (Search.value g) (n/(D.width+1))) :
    GoodTable (r:=t) (tables (r:=r) (s:=s) a C D f g) n := by
  refine ⟨_,tables_full a C D wf wg f g hf hg,?_,?_⟩
  · exact Selectors.process_decrease
      (Base.decrease C D wf wg (Search.value f) (Search.value g) a.zero hcw hdw hc hd n) _ _ _
  · apply Selectors.process_critical
    · exact Base.absorbs C D wf wg (Search.value f) (Search.value g) a.zero n
    · exact Base.preserves_zero C D wf wg (Search.value f) (Search.value g) a.zero
        (hC _ (by simp)) (hD _ (by simp)) n
    · exact Base.shapes C D wf wg (Search.value f) (Search.value g) a
        (fun b hb => hC b (List.mem_cons_of_mem _ hb))
        (fun b hb => hD b (List.mem_cons_of_mem _ hb)) n
    · intro j w hw
      exact ⟨Selectors.body_lt_size a.zero j hw,(Selectors.tuples_valid a.zero j).2.2 w hw⟩
    · exact fun _ _ hh _ hw => Selectors.stage_spacing a hh hw
    · exact Base.critical C D wf wg (Search.value f) (Search.value g) a.zero
        (hC _ (by simp)) (hD _ (by simp)) hCD hf0 hg0 hfc hfi hgc hgi

end Build

open Relation

end

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes

namespace Bootstrap.Canonical
variable {A Q : Type*} [Fintype A] [Primcodable A]
  {r : A → A → Prop} [DecidableRel (List.Shortlex r)] [Std.Trichotomous r]
  (wf : WellFounded r) (q : List A → Q)

omit [Fintype A] [Primcodable A] [DecidableRel (List.Shortlex r)] in
/-- Equality of computed representatives is exactly equality in the semantic
    quotient, not merely equality of a chosen noncanonical encoding. -/
theorem least_eq_iff {u v : List A} : least wf q u=least wf q v ↔ q u=q v := by
  constructor
  · intro h
    exact (least_class wf q u).symm.trans ((congrArg q h).trans (least_class wf q v))
  · exact least_congr wf q

end Bootstrap.Canonical

end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.WordProblem

local instance instTrichotomousProdFinBoolLetterRel (n : ℕ) : Std.Trichotomous (letterRel n) := ⟨fun a b hab hba => by
  apply Encodable.encode_injective
  change ¬Encodable.encode a<Encodable.encode b at hab
  change ¬Encodable.encode b<Encodable.encode a at hba
  omega⟩

variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)

 theorem testedClass_eq_iff (u v : Word n) : testedClass s u=testedClass s v ↔ evalWord s u=evalWord s v := by
  classical
  exact Bootstrap.Canonical.least_eq_iff _ _

end FiniteAlgebraicEnvelopes.WordProblem

end OAI
end

section
-- module Solutions.OAIFAE.PartialAffine
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Primitive recursive dyadic partial affine monoid and its six-letter presentation.
-/

namespace FiniteAlgebraicEnvelopes.PartialAffine

 theorem testedClass_eq_iff (u v : List Letter) : testedClass u=testedClass v ↔ value u=value v := by
  classical
  exact Bootstrap.Canonical.least_eq_iff _ _

end FiniteAlgebraicEnvelopes.PartialAffine

end OAI
end

section
-- module Solutions.OAIFAE.UniformMachines
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Parameterized effective machine realization and uniform finite data.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode
open Compiler.Simulator ParameterMachine
variable {S Γ Q : Type*}

def encodeCommand (n : ℕ) (c : Command (State Q n) (Bool×Γ)) : Cmd Q Γ :=
  (encode n c.state,c.write,c.move)

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ] (p : S)

 theorem transition_encode (n : ℕ) (q : State Q n) (a : Bool×Γ) :
    transition A M p n (encode n q) a=
      ((machine A M p n).transition q a).map (encodeCommand n) := by
  cases q with
  | start => rfl
  | scan => simp [transition,encode,machine]; split <;> rfl
  | rewind => simp [transition,encode,machine]; split <;> rfl
  | run q => simp [transition,encode,machine,Option.map_map,encodeCommand,Function.comp_def]
  | emit k =>
    have h0 : k.val+3≠0 := by omega
    have h1 : k.val+3≠1 := by omega
    have h2 : k.val+3≠2 := by omega
    simp only [transition,encode,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,Nat.add_sub_cancel,
      ite_eq_left k.isLt,machine]
    split <;> simp_all [encodeCommand,encode]

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

end OAI
end

section
-- module Solutions.OAIFAE.UniformControl
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform validation, simulation, and finite control.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator
open scoped HeadCodec
variable {S Γ Q Q' P : Type*}

def commandMap (f : Q → Q') (c : Command Q Γ) : Command Q' Γ := ⟨f c.state,c.write,c.move⟩

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator
open HeadCodec
variable {S Γ Q Q' : Type*} [DecidableEq Γ]
variable (A : Alphabet S Γ) (M : Machine Q Γ) (N : Machine Q' Γ) (i : Q → Q')
  (hi : N.initial=i M.initial)
  (ht : ∀ q a,N.transition (i q) a=(M.transition q a).map (commandMap i))

theorem table_direction_map (q : Head S Q) :
    (table A N).direction (stateMap i q)=(table A M).direction q := by
  cases q <;> rfl

theorem table_boundary_map (q : Head S Q) :
    (table A N).boundary (stateMap i q)=((table A M).boundary q).map (stateMap i) := by
  cases q <;> try rfl
  case scan r => cases r <;> rfl

include hi ht in
theorem table_cell_map (q : Head S Q) (b : Base S) (a : Tag S Γ) :
    (table A N).cell (stateMap i q) b a=
      ((table A M).cell q b a).map (Scan.mapInstruction (stateMap i)) := by
  cases q with
  | start | ok => rfl
  | rewind r => rfl
  | finish => rfl
  | left q => cases b <;> rfl
  | scan r =>
    cases r <;> cases b <;>
      simp [table,cell,stateMap,Scan.mapInstruction,hi]
    all_goals split <;> simp_all [Scan.mapInstruction,stateMap]
    all_goals split <;> simp_all [Scan.mapInstruction,stateMap,Option.map_map,Function.comp_def]
  | run q =>
    cases b <;> try rfl
    case workspace =>
      simp only [table,cell,stateMap,ht]
      cases h : M.transition q a.work with
      | none => rfl
      | some c =>
        rcases c with ⟨q,g,m⟩
        cases m <;> rfl

end FiniteAlgebraicEnvelopes.Compiler.Simulator

namespace FiniteAlgebraicEnvelopes.Compiler.Control
open HeadCodec
variable {S Γ Q Q' : Type*} [DecidableEq S] [DecidableEq Γ] [Fintype S]
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ) (N : Simulator.Machine Q' Γ)
  (i : Q → Q') (hi : N.initial=i M.initial)
  (ht : ∀ q a,N.transition (i q) a=(M.transition q a).map (commandMap i))

omit [Fintype S] in
theorem table_direction_map (q : Head S Q) :
    (table A N).direction (controlMap i q)=(table A M).direction q := by
  cases q <;> try rfl
  exact Simulator.table_direction_map A M N i _

omit [Fintype S] in
theorem table_boundary_map (q : Head S Q) :
    (table A N).boundary (controlMap i q)=((table A M).boundary q).map (controlMap i) := by
  have hm : controlMap i ∘ validatorHead (S := S)=validatorHead (S := S) := by
    funext q; cases q <;> rfl
  cases q <;> simp only [table,controlMap,toValidator,Option.map_map]
  all_goals try { simp only [hm] }
  case machine q =>
    rw [Simulator.table_boundary_map A M N i]
    simp only [Option.map_map]
    rfl

include hi ht in
omit [Fintype S] in
theorem table_cell_map (q : Head S Q) (b : Base S) (a : Tag S Γ) :
    (table A N).cell (controlMap i q) b a=
      ((table A M).cell q b a).map (Scan.mapInstruction (controlMap i)) := by
  have hm : Scan.mapInstruction (T := Tag S Γ) (controlMap i) ∘
      Scan.mapInstruction (validatorHead (S := S))=Scan.mapInstruction (validatorHead (S := S)) := by
    funext c
    cases c with | mk h t b => cases h <;> rfl
  cases q <;> simp only [table,controlMap,toValidator,Option.map_map]
  all_goals try { simp only [hm] }
  case machine q =>
    rw [Simulator.table_cell_map A M N i hi ht]
    simp only [Option.map_map]
    rfl

omit [DecidableEq S] [DecidableEq Γ] [Fintype S] in
theorem entry_map (blank : Γ) (v : Sector S Γ Q) :
    Entry blank (Scan.mapHead (controlMap i) v) ↔ Entry blank v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> simp [Entry,Scan.mapHead,controlMap]

omit [DecidableEq S] [DecidableEq Γ] [Fintype S] in
theorem success_map (v : Sector S Γ Q) :
    Success (Scan.mapHead (controlMap i) v) ↔ Success v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> simp [Success,Scan.mapHead,controlMap]
  case machine q => cases q <;> simp [stateMap]
end FiniteAlgebraicEnvelopes.Compiler.Control

end OAI
end

section
-- module Solutions.OAIFAE.UniformPaths
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform surface and path normalization with recursive compiler interfaces.
-/

namespace FiniteAlgebraicEnvelopes.Effect.Graph
variable {α β : Type*}
variable (i : α → β) (r : α → α → Bool) (s : β → β → Bool)
variable (h : ∀ a b,s (i a) (i b)=r a b)

include h in
theorem expand_map (u v : List α) : expand s (u.map i) (v.map i)=(expand r u v).map i := by
  simp only [expand,List.map_append,List.any_map]
  rw [List.filter_map]
  simp only [Function.comp_def,h]

include h in
theorem search_map (u : List α) (a : α) (n : ℕ) :
    search s (u.map i) (i a) n=(search r u a n).map i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [search,ih,expand_map i r s h,←search]

include h in
theorem component_map (u : List α) (a : α) :
    component s (u.map i) (i a)=(component r u a).map i := by
  simp only [component,List.length_map,search_map i r s h]

end FiniteAlgebraicEnvelopes.Effect.Graph

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {H H' B T : Type*} [Fintype B] [Fintype T]

theorem sectorList_map (i : H → H') (heads : List H) (n : ℕ) :
    sectorList (B := B) (T := T) (heads.map i) n=
      (sectorList heads n).map (mapHead i) := by
  simp only [sectorList,List.flatMap_map,List.map_flatMap]
  rfl

variable [DecidableEq H] [DecidableEq H'] [DecidableEq B] [DecidableEq T]
omit [DecidableEq H] [DecidableEq H'] [DecidableEq T] in
theorem universeList_map (i : H → H') (heads : List H) (v : Sector H B T) :
    universeList (heads.map i) (mapHead i v)=(universeList heads v).map (mapHead i) := by
  simp only [universeList,mapHead,sectorList_map,List.filter_map,baseSkeleton]
  rfl

variable (i : H → H') (hi : Function.Injective i)
  (t : Table H B T) (u : Table H' B T)
  (hd : ∀ q,u.direction (i q)=t.direction q)
  (hc : ∀ q b a,u.cell (i q) b a=(t.cell q b a).map (mapInstruction i))
  (hb : ∀ q,u.boundary (i q)=(t.boundary q).map i)

omit [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq H'] [DecidableEq B] [DecidableEq T] in
include hd hc hb in
theorem step_map (v : Sector H B T) :
    step u (mapHead i v)=(step t v).map (mapHead i) := by
  apply step_mapHead
  · exact hd _
  · exact hc _
  · exact hb _

omit [Fintype B] [Fintype T] in
include hi hd hc hb in
theorem stepBool_map (v w : Sector H B T) :
    decide (step u (mapHead i v)=some (mapHead i w))=decide (step t v=some w) := by
  rw [step_map i t u hd hc hb]
  have he : (step t v).map (mapHead i)=some (mapHead i w) ↔ step t v=some w := by
    rw [Option.map_eq_some_iff]
    constructor
    · rintro ⟨a,ha,he⟩
      exact (mapHead_injective i hi he) ▸ ha
    · intro he
      exact ⟨w,he,rfl⟩
  simp only [he]

include hi hd hc hb in
theorem componentList_map (heads : List H) (v : Sector H B T) :
    componentList (fun _ : Unit => u) (fun _ => heads.map i) ((),mapHead i v)=
      (componentList (fun _ : Unit => t) (fun _ => heads) ((),v)).map (mapHead i) := by
  rw [componentList,componentList,universeList_map]
  exact component_map _ _ _ (stepBool_map i hi t u hd hc hb) _ _

end FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform

namespace FiniteAlgebraicEnvelopes.Effect.Graph
variable {α : Type*} [DecidableEq α]

theorem expand_ext_universe (r : α → α → Bool) {u v s t : List α}
    (hu : u.toFinset=v.toFinset) (hs : s.toFinset=t.toFinset) :
    (expand r u s).toFinset=(expand r v t).toFinset := by
  have huu : ∀ a,a∈u ↔ a∈v := fun a => by simpa using Finset.ext_iff.mp hu a
  have hss : ∀ a,a∈s ↔ a∈t := fun a => by simpa using Finset.ext_iff.mp hs a
  ext a
  simp only [List.mem_toFinset,mem_expand,huu,hss]

theorem search_ext_universe (r : α → α → Bool) {u v : List α}
    (hu : u.toFinset=v.toFinset) (a : α) (n : ℕ) :
    (search r u a n).toFinset=(search r v a n).toFinset := by
  induction n with
  | zero => rfl
  | succ n ih => exact expand_ext_universe r hu ih

theorem search_add_stable (r : α → α → Bool) {u : List α} {a : α} (ha : a∈u) (k : ℕ) :
    (search r u a (u.length+k)).toFinset=(component r u a).toFinset := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (expand r u (search r u a (u.length+k))).toFinset=(component r u a).toFinset
    rw [expand_ext r u ih]
    exact search_stable r ha

theorem component_ext_universe (r : α → α → Bool) {u v : List α}
    (hu : u.toFinset=v.toFinset) {a : α} (ha : a∈u) :
    (component r u a).toFinset=(component r v a).toFinset := by
  have hv : a∈v := by
    apply List.mem_toFinset.mp
    rw [←hu]
    exact List.mem_toFinset.mpr ha
  rw [←search_add_stable r ha v.length,←search_add_stable r hv u.length,Nat.add_comm v.length]
  exact search_ext_universe r hu a _
end FiniteAlgebraicEnvelopes.Effect.Graph

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform
open FiniteAlgebraicEnvelopes.Effect
variable {P H B T : Type*} [Primcodable P] [Primcodable H] [Primcodable B] [Primcodable T]
  [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq B] [DecidableEq T]

omit [Primcodable H] [Primcodable B] [Primcodable T] in
theorem universeList_ext_support {u v : List H} (h : u.toFinset=v.toFinset) (a : Sector H B T) :
    (universeList u a).toFinset=(universeList v a).toFinset := by
  have hh : ∀ q,q∈u ↔ q∈v := fun q => by simpa using Finset.ext_iff.mp h q
  ext b; simp only [List.mem_toFinset,mem_universeList,hh]

omit [Primcodable P] [Primcodable H] [Primcodable B] [Primcodable T] in
theorem componentList_ext_support (table : P → Table H B T) {u v : P → List H} (p : P)
    (h : (u p).toFinset=(v p).toFinset) (a : Sector H B T) (ha : a.head∈u p) :
    (componentList table u (p,a)).toFinset=(componentList table v (p,a)).toFinset := by
  apply Graph.component_ext_universe _ (universeList_ext_support h a)
  exact mem_universeList _ a a |>.mpr ⟨ha,rfl⟩

end FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform

namespace FiniteAlgebraicEnvelopes.Effect
variable {α β : Type*}

theorem priorityList_map (i : α → β) (p q : α → Bool) (p' q' : β → Bool)
    (hp : ∀ a,p' (i a)=p a) (hq : ∀ a,q' (i a)=q a) (s : List α) :
    priorityList p' q' (s.map i)=(priorityList p q s).map i := by
  have he (f : α → Bool) (g : β → Bool) (h : ∀ a,g (i a)=f a) :
      (s.map i).filter g=(s.filter f).map i := by
    rw [List.filter_map]; simp only [Function.comp_def,h]
  simp only [priorityList,he p p' hp,he q q' hq,List.isEmpty_map]
  split <;> first | rfl | (split <;> rfl)

theorem priorityList_ext [Primcodable α] [DecidableEq α] (p q : α → Bool) {s t : List α}
    (he : s.toFinset=t.toFinset) :
    (priorityList p q s).toFinset=(priorityList p q t).toFinset := by
  simp only [priorityList_toFinset,he]

end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform
open FiniteAlgebraicEnvelopes.Effect
variable {H H' B T : Type*} [Primcodable H] [Primcodable H'] [Primcodable B] [Primcodable T]
  [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq H'] [DecidableEq B] [DecidableEq T]
  [LinearOrder (Sector H B T)] [LinearOrder (Sector H' B T)]

variable (i : H → H') (hi : Function.Injective i)
  (t : Table H B T) (u : Table H' B T)
  (hd : ∀ q,u.direction (i q)=t.direction q)
  (hc : ∀ q b a,u.cell (i q) b a=(t.cell q b a).map (mapInstruction i))
  (hb : ∀ q,u.boundary (i q)=(t.boundary q).map i)
  (ho : Monotone (mapHead (B := B) (T := T) i))
  (entry success : Sector H B T → Bool) (entry' success' : Sector H' B T → Bool)
  (he : ∀ v,entry' (mapHead i v)=entry v) (hs : ∀ v,success' (mapHead i v)=success v)

omit [Primcodable H] [Primcodable H'] [Primcodable B] [Primcodable T] in
include hi hd hc hb ho he hs in
theorem representative_map (heads : List H) (v : Sector H B T) :
    representative (fun _ : Unit => u) (fun _ => heads.map i) entry' success' ((),mapHead i v)=
      mapHead i (representative (fun _ : Unit => t) (fun _ => heads) entry success ((),v)) := by
  unfold representative
  rw [componentList_map i hi t u hd hc hb heads v,priorityList_map _ _ _ _ _ he hs,minList_map _ ho]
  cases (priorityList entry success (componentList (fun _ : Unit => t) (fun _ => heads) ((),v))).min? <;> rfl

variable {P : Type*} [Primcodable P]
omit [Primcodable P] in
theorem representative_ext_support (table : P → Table H B T) {heads heads' : P → List H}
    (p : P) (he : (heads p).toFinset=(heads' p).toFinset)
    (entry success : Sector H B T → Bool) (v : Sector H B T) (hv : v.head∈heads p) :
    representative table heads entry success (p,v)=representative table heads' entry success (p,v) := by
  unfold representative
  rw [minList_ext (priorityList_ext _ _ (componentList_ext_support table p he v hv))]

variable [Fintype H]
omit [Primcodable H] [Primcodable B] [Primcodable T] in
theorem representative_finite (t : Table H B T) (E F : Sector H B T → Prop)
    [DecidablePred E] [DecidablePred F] (v : Sector H B T) :
    representative (fun _ : Unit => t) (fun _ => finiteList H)
      (fun w => decide (E w)) (fun w => decide (F w)) ((),v)=Scan.representative t E F v :=
  (Scan.representative_list t E F v).symm

omit [Primcodable H] in
include hi hd hc hb ho he hs in
theorem representative_finite_map (heads : List H')
    (hh : heads.toFinset=((finiteList H).map i).toFinset) (v : Sector H B T) :
    representative (fun _ : Unit => u) (fun _ => heads) entry' success' ((),mapHead i v)=
      mapHead i (Scan.representative t (fun w => entry w=true) (fun w => success w=true) v) := by
  have hv : (mapHead i v).head∈heads := by
    apply List.mem_toFinset.mp
    rw [hh]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨v.head,mem_finiteList _,rfl⟩)
  rw [representative_ext_support (heads' := fun _ : Unit => (finiteList H).map i) (fun _ : Unit => u) () hh entry' success' _ hv,
    representative_map i hi t u hd hc hb ho entry success entry' success' he hs]
  congr 1
  simpa only [Bool.decide_coe] using
    representative_finite t (fun w => entry w=true) (fun w => success w=true) v

end FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

section
open Compiler Compiler.Simulator Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {S Γ Q : Type*}

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ] (p : S)

theorem coded_initial (n : ℕ) :
    (codedMachine A M p n).initial=encode n (ParameterMachine.machine A M p n).initial := rfl

theorem coded_transition (n : ℕ) (q : State Q n) (a : Bool×Γ) :
    (codedMachine A M p n).transition (encode n q) a=
      ((ParameterMachine.machine A M p n).transition q a).map (commandMap (encode n)) := by
  simp only [codedMachine,transition_encode,Option.map_map]
  rfl

variable [Fintype Q] [Fintype Γ] [Primcodable Q] [Primcodable Γ]

variable {T : Type*} [Fintype T]

omit [Primcodable Q] in
theorem heads_finset [DecidableEq T] [DecidableEq Q] (n : ℕ) :
    (heads (T := T) (Q := Q) n).toFinset=
      ((Scan.finiteList (Compiler.Control.Head T (State Q n))).map (controlMap (encode n))).toFinset := by
  classical
  ext h
  simp only [List.mem_toFinset,mem_heads_iff,List.mem_map,Scan.mem_finiteList,true_and]

end

open Compiler Compiler.Simulator Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {S T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet S Γ) (M : Machine Q Γ) (p : S) (B : Alphabet T (Bool×Γ))

omit [Primcodable Γ] in
theorem codedRepresentative_map (n : ℕ) (v : Compiler.Control.Sector T (Bool×Γ) (State Q n)) :
    letI := finiteOrder (T := T) (Γ := Γ) (Q := Q) n
    codedRepresentative A M p B (n,Scan.mapHead (controlMap (encode n)) v)=
      Scan.mapHead (controlMap (encode n)) (Compiler.Control.representative B (machine A M p n) v) := by
  let : Primcodable (State Q n) := Effect.finitePrimcodable _
  let := Effect.codeOrder (Compiler.Control.Sector T (Bool×Γ) (Control Q))
  let := finiteOrder (T := T) (Γ := Γ) (Q := Q) n
  have h := Scan.Uniform.representative_finite_map
    (controlMap (S := T) (encode n)) (controlMap_injective (encode_injective n))
    (Compiler.Control.table B (machine A M p n)) (Compiler.Control.table B (codedMachine A M p n))
    (Compiler.Control.table_direction_map B (machine A M p n) (codedMachine A M p n) (encode n))
    (Compiler.Control.table_cell_map B (machine A M p n) (codedMachine A M p n) (encode n)
      (coded_initial A M p n) (coded_transition A M p n))
    (Compiler.Control.table_boundary_map B (machine A M p n) (codedMachine A M p n) (encode n))
    (show Monotone (Scan.mapHead (B := Base T) (T := Tag T (Bool×Γ)) (controlMap (encode n))) from
      fun _ _ h => h)
    (fun w => decide (Compiler.Control.Entry B.blank w)) (fun w => decide (Compiler.Control.Success w))
    (fun w => decide (Compiler.Control.Entry B.blank w)) (fun w => decide (Compiler.Control.Success w))
    (fun w => by simp only [Compiler.Control.entry_map])
    (fun w => by simp only [Compiler.Control.success_map])
    (heads n) (heads_finset n) v
  simpa only [codedRepresentative, Compiler.Control.representative,
    Scan.Uniform.representative, Scan.Uniform.componentList,decide_eq_true_eq] using h

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

namespace FiniteAlgebraicEnvelopes.Compiler.Surface
variable {S Γ H H' : Type*}

variable (i : H → H') (blank : Γ) [DecidableEq S] [DecidableEq Γ]

theorem rawSweep_map (l r : Cells S Γ) (lb rb : Bool) :
    rawSweep (H := H') blank l r lb rb=Scan.mapHead (headMap i) (rawSweep (H := H) blank l r lb rb) := by
  induction l generalizing r with
  | nil => rfl
  | cons c l ih =>
    rcases c with ⟨b,t⟩
    cases b <;> simp only [rawSweep]
    case anchor s => split <;> first | exact ih _ | rfl
    all_goals rfl

theorem rawNormal_map (v : Sector S Γ H) :
    rawNormal blank (Scan.mapHead (headMap i) v)=Scan.mapHead (headMap i) (rawNormal blank v) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> first | exact rawSweep_map i blank _ _ _ _ | rfl

theorem quotaNormal_map (v : Sector S Γ H) :
    quotaNormal blank (Scan.mapHead (headMap i) v)=Scan.mapHead (headMap i) (quotaNormal blank v) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> try rfl
  cases r <;> simp only [quotaNormal,Scan.mapHead,headMap]
  all_goals split <;> rfl

theorem unmerge_map (v : Sector S Γ H) :
    unmerge blank (Scan.mapHead (headMap i) v)=
      (unmerge blank v).map (Scan.mapHead (headMap i)) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases l <;> cases q <;> cases r <;> simp only [Scan.mapHead,headMap,unmerge,List.map_cons,List.map_nil]
  split
  · simp only [List.map_cons,List.map_nil]
    refine congrArg₂ (fun (a b : Sector S Γ H') => [a,b]) ?_ ?_
    · exact rawSweep_map (S := S) i blank _ _ _ _
    · exact rawSweep_map (S := S) i blank _ _ _ _
  · rfl

theorem pendingPreprocess_map (v : Sector S Γ H) :
    pendingPreprocess blank (Scan.mapHead (headMap i) v)=
      (pendingPreprocess blank v).map (Scan.mapHead (headMap i)) := by
  simp only [pendingPreprocess,quotaNormal_map,unmerge_map]

omit [DecidableEq S] [DecidableEq Γ] in
theorem ofCleanup_map (v : Cleanup.Sector S Γ) :
    (ofCleanup v : Sector S Γ H')=Scan.mapHead (headMap i) (ofCleanup v : Sector S Γ H) := by
  rcases v with ⟨l,q,r,lb,rb⟩; cases q <;> rfl

omit [DecidableEq S] [DecidableEq Γ] in
theorem cleanupNormal_map (v : Sector S Γ H) :
    cleanupNormal blank (Scan.mapHead (headMap i) v)=Scan.mapHead (headMap i) (cleanupNormal blank v) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> try rfl
  exact ofCleanup_map i _

theorem cleanupPreprocess_map (v : Sector S Γ H) :
    cleanupPreprocess blank (Scan.mapHead (headMap i) v)=Scan.mapHead (headMap i) (cleanupPreprocess blank v) := by
  simp only [cleanupPreprocess,cleanupNormal_map,rawNormal_map]
end FiniteAlgebraicEnvelopes.Compiler.Surface

namespace FiniteAlgebraicEnvelopes.Compiler.Surface.Uniform
open HeadCodec
open scoped HeadCodec
variable {P S Γ Q Q' : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] [DecidableEq Q']
variable (i : Q → Q') (blank : Γ)
  (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)
  (rep' : P × Control.Sector S Γ Q' → Control.Sector S Γ Q')
  (hr : ∀ p v,rep' (p,Scan.mapHead (controlMap i) v)=Scan.mapHead (controlMap i) (rep (p,v)))

omit [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P] in
include hr in
theorem internalPreprocess_map (p : P) (v : Control.Sector S Γ Q) :
    internalPreprocess blank rep' (p,Scan.mapHead (controlMap i) v)=
      (internalPreprocess blank rep (p,v)).map (Scan.mapHead (Surface.headMap (controlMap i))) := by
  simp only [internalPreprocess,hr,Control.entry_map,Control.success_map]
  split
  · exact Surface.pendingPreprocess_map (controlMap i) blank
      (⟨(rep (p,v)).left,.pending,(rep (p,v)).right,(rep (p,v)).leftBoundary,(rep (p,v)).rightBoundary⟩ : Surface.Sector S Γ (Control.Head S Q))
  · split
    · simp only [List.map_cons,List.map_nil]
      congr 1
      exact Surface.cleanupPreprocess_map (controlMap i) blank
        (⟨(rep (p,v)).left,.cleanup,(rep (p,v)).right,(rep (p,v)).leftBoundary,(rep (p,v)).rightBoundary⟩ : Surface.Sector S Γ (Control.Head S Q))
    · rfl

omit [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P] in
include hr in
theorem preprocess_map (p : P) (v : Surface.Sector S Γ (Control.Head S Q)) :
    preprocess blank rep' (p,Scan.mapHead (Surface.headMap (controlMap i)) v)=
      (preprocess blank rep (p,v)).map (Scan.mapHead (Surface.headMap (controlMap i))) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> simp only [preprocess,headMap,Scan.mapHead,List.map_cons,List.map_nil]
  case raw => congr 1; exact Surface.rawNormal_map (controlMap i) blank (⟨l,.raw,r,lb,rb⟩ : Surface.Sector S Γ (Control.Head S Q))
  case pending => exact Surface.pendingPreprocess_map (controlMap i) blank (⟨l,.pending,r,lb,rb⟩ : Surface.Sector S Γ (Control.Head S Q))
  case cleanup => congr 1; exact Surface.cleanupPreprocess_map (controlMap i) blank (⟨l,.cleanup,r,lb,rb⟩ : Surface.Sector S Γ (Control.Head S Q))
  case internal q => exact internalPreprocess_map i blank rep rep' hr p ⟨l,q,r,lb,rb⟩

end FiniteAlgebraicEnvelopes.Compiler.Surface.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler.Path
variable {C H H' : Type*}

variable (i : H → H')

variable [DecidableEq C] [DecidableEq H] [DecidableEq H']
theorem decode_map (hi : Function.Injective i) (w : List (Letter C H)) :
    decode (w.map (mapLetter i))=(decode w).map (mapSector i) := by
  have he (v : Sector C H) : encode (mapSector i v)=w.map (mapLetter i) ↔ encode v=w := by
    rw [encode_map]
    exact List.map_injective_iff.mpr (mapLetter_injective i hi) |>.eq_iff
  unfold decode
  rw [heads_map]
  cases h : heads w with
  | nil => rfl
  | cons q qs =>
    cases qs with
    | cons q' qs => rfl
    | nil =>
      simp only [List.map_cons,List.map_nil,lefts_map,rights_map,enter_mem_map,leave_mem_map]
      let v : Sector C H := ⟨(lefts w).reverse,q,rights w,decide (.enter∈w),decide (.leave∈w)⟩
      change (if encode (mapSector i v) = w.map (mapLetter i) then some (mapSector i v) else none) = _
      simp only [he]
      split <;> rfl

variable (p : Sector C H → List (Sector C H)) (p' : Sector C H' → List (Sector C H'))
  (hp : ∀ v,p' (mapSector i v)=(p v).map (mapSector i))
include hp in
theorem prepareChunk_map (hi : Function.Injective i) (w : List (Letter C H)) :
    prepareChunk p' (w.map (mapLetter i))=(prepareChunk p w).map (List.map (mapLetter i)) := by
  unfold prepareChunk
  rw [decode_map i hi]
  cases h : decode w with
  | none => rfl
  | some v => simp only [Option.map_some,hp,List.map_map,Function.comp_def,encode_map]
include hp in
theorem prepare_map (hi : Function.Injective i) (w : List (Letter C H)) :
    prepare p' (w.map (mapLetter i))=(prepare p w).map (List.map (mapLetter i)) := by
  simp only [prepare,prepareChunks,cuts_map,List.flatMap_map,List.map_flatMap]
  congr 1
  funext a
  exact prepareChunk_map i p p' hp hi a

end FiniteAlgebraicEnvelopes.Compiler.Path

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C D S : Type*} (i : C → D)

def Action.mapKeep : Action C S → Action D S
  | .keep c => .keep (i c)
  | .raw w => .raw w
  | .call w => .call w

theorem splitRun_map (w : List (Item C S)) :
    splitRun (w.map (Sum.map i id))=((splitRun w).1,(splitRun w).2.map (Sum.map i id)) := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp only [List.map_cons,Sum.map_inl,Sum.map_inr,id_eq,splitRun,ih]

theorem plan_map (w : List (Item C S)) :
    plan (w.map (Sum.map i id))=(plan w).map (Action.mapKeep i) := by
  cases w with
  | nil => simp only [List.map_nil,plan]
  | cons a w =>
    cases a with
    | inl c => simp only [List.map_cons,Sum.map_inl,plan,Action.mapKeep,plan_map w]
    | inr x =>
      rw [List.map_cons]
      simp only [Sum.map_inr,id_eq,plan,splitRun_map,List.map_cons,plan_map (splitRun w).2]
      cases (splitRun w).1 <;> rfl
termination_by w.length
decreasing_by all_goals have := splitRun_length w; simp_all only [List.length_cons]; omega

theorem Action.partial_map (f : List S → Part (List S)) (a : Action C S) :
    (a.mapKeep i).partial f=(a.partial f).map (Sum.map i id) := by
  cases a <;> simp only [Action.mapKeep,Action.partial,Part.map_some,Part.map_map,
    Function.comp_def,Sum.map_inl,Sum.map_inr,id_eq]

theorem execute_map (f : List S → Part (List S)) (p : List (Action C S)) :
    execute f (p.map (Action.mapKeep i))=(execute f p).map (List.map (Sum.map i id)) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.map_cons,execute,Action.partial_map,ih,Part.bind_map,Part.map_bind,Part.map_map]
    congr 1

theorem partialSource_map (f : List S → Part (List S)) (w : List (Item C S)) :
    partialSource f (w.map (Sum.map i id))=(partialSource f w).map (List.map (Sum.map i id)) := by
  simp only [partialSource,plan_map,execute_map]

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H H' B T : Type*} (i : H → H')
theorem unliteral_map (v : Path.Sector (B×T) H) :
    unliteral (Path.mapSector i v)=mapHead i (unliteral v) := rfl
theorem literal_map (v : Sector H B T) :
    literal id (mapHead i v)=Path.mapSector i (literal id v) := rfl
end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Word
open HeadCodec
variable {S Γ Q Q' : Type*} (i : Q → Q') (blank : Γ)

variable [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] [DecidableEq Q']
theorem readRaw_map (hi : Function.Injective i) (w : List (Letter S Γ Q)) :
    readRaw blank (w.map (letterMap i))=readRaw blank w := by
  have he : raw blank (rawLetters w)=w.map (letterMap i) ↔ raw blank (rawLetters w)=w := by
    rw [←raw_map i blank]
    exact List.map_injective_iff.mpr (letterMap_injective i hi) |>.eq_iff
  simp only [readRaw,rawLetters_map,he]

theorem classify_map (hi : Function.Injective i) (w : List (Letter S Γ Q)) :
    classify blank (w.map (letterMap i))=Sum.map (List.map (letterMap i)) id (classify blank w) := by
  simp only [classify,readRaw_map i blank hi]
  cases readRaw blank w <;> rfl

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] [DecidableEq Q'] in
theorem realize_map (a : Item S Γ Q) :
    realize blank (Sum.map (List.map (letterMap i)) id a)=(realize blank a).map (letterMap i) := by
  cases a <;> simp only [Sum.map_inl,Sum.map_inr,realize,raw_map,id_eq]
end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Word.Uniform
open HeadCodec
open scoped HeadCodec
variable {P S Γ Q Q' : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] [DecidableEq Q']
variable (i : Q → Q') (blank : Γ)
  (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)
  (rep' : P × Control.Sector S Γ Q' → Control.Sector S Γ Q')
  (hr : ∀ p v,rep' (p,Scan.mapHead (controlMap i) v)=Scan.mapHead (controlMap i) (rep (p,v)))

include hr in
omit [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P] in
theorem sectorPreprocess_map (p : P) (v : Sector S Γ Q) :
    sectorPreprocess blank rep' (p,Path.mapSector (headMap i) v)=
      (sectorPreprocess blank rep (p,v)).map (Path.mapSector (headMap i)) := by
  simp only [sectorPreprocess,Scan.unliteral_map,headMap,
    Surface.Uniform.preprocess_map i blank rep rep' hr,List.map_map,Function.comp_def,Scan.literal_map]

include hr in
omit [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P] in
theorem preprocess_map (hi : Function.Injective i) (p : P) (w : List (Letter S Γ Q)) :
    preprocess blank rep' (p,w.map (letterMap i))=
      (preprocess blank rep (p,w)).map (List.map (letterMap i)) :=
  Path.prepare_map (headMap i) _ _ (sectorPreprocess_map i blank rep rep' hr p)
    (headMap_injective i hi) w

include hr in
omit [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P] in
theorem partialNormal_map (hi : Function.Injective i) (f : P × List S → Part (List S))
    (p : P) (w : List (Letter S Γ Q)) :
    partialNormal blank rep' f (p,w.map (letterMap i))=
      (partialNormal blank rep f (p,w)).map (List.map (letterMap i)) := by
  have hshape : Path.shape (w.map (letterMap i))=Path.shape w := Path.shape_map (headMap i) w
  simp only [partialNormal,hshape]
  split
  · rfl
  · rw [preprocess_map i blank rep rep' hr hi]
    simp only [List.map_map,Function.comp_def,classify_map i blank hi]
    have he := List.map_map (f := classify (Q := Q) (Γ := Γ) blank)
      (g := Sum.map (List.map (letterMap (S := S) (Γ := Γ) i)) (id : List S → List S))
      (l := preprocess blank rep (p,w))
    simp only [Function.comp_def] at he
    rw [←he,RawRuns.partialSource_map]
    simp only [Part.map_map]
    congr 1
    funext l
    simp only [List.flatMap_map,List.map_flatMap,Function.comp_def,realize_map]

end FiniteAlgebraicEnvelopes.Compiler.Word.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler
open HeadCodec
open scoped HeadCodec
variable {P S Γ Q : Type*} [Primcodable P] [Primcodable Q]
  [Fintype S] [Fintype Γ] [Fintype Q]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [LinearOrder (Control.Sector S Γ Q)]
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)

namespace Surface.Uniform
omit [Primcodable P] [Primcodable Q] in
theorem preprocess_specialize (p : P) (v : Surface.Sector S Γ (Control.Head S Q)) :
    preprocess A.blank (fun x : P × Control.Sector S Γ Q => Control.representative A M x.2) (p,v) =
      Surface.preprocess A M v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> rfl
end Surface.Uniform

namespace Word.Uniform
omit [Primcodable P] [Primcodable Q] in
theorem sectorPreprocess_specialize (p : P) (v : Word.Sector S Γ Q) :
    sectorPreprocess A.blank (fun x : P × Control.Sector S Γ Q => Control.representative A M x.2) (p,v) =
      Word.sectorPreprocess A M v := by
  simp only [sectorPreprocess,Surface.Uniform.preprocess_specialize,Word.sectorPreprocess]

omit [Primcodable P] [Primcodable Q] in
theorem preprocess_specialize (p : P) (w : List (Word.Letter S Γ Q)) :
    preprocess A.blank (fun x : P × Control.Sector S Γ Q => Control.representative A M x.2) (p,w) =
      Word.preprocess A M w := by
  simp only [preprocess,sectorPreprocess_specialize,Word.preprocess]

omit [Primcodable P] [Primcodable Q] in
theorem partialNormal_specialize (p : P) (f : List S → Part (List S)) (w : List (Word.Letter S Γ Q)) :
    partialNormal A.blank (fun x : P × Control.Sector S Γ Q => Control.representative A M x.2)
      (fun x => f x.2) (p,w)=Word.partialNormal A M f w := by
  simp only [partialNormal,Word.partialNormal,preprocess_specialize]
end Word.Uniform

end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

section
open Compiler Compiler.Simulator Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {S T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable T] [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet S Γ) (M : Machine Q Γ) (p : S) (B : Alphabet T (Bool×Γ))

omit [Primcodable T] [Primcodable Γ] in
theorem codedNormal_map (n : ℕ) (f : ℕ × List T → Part (List T))
    (w : List (Compiler.Word.Letter T (Bool×Γ) (State Q n))) :
    letI := finiteOrder (T := T) (Γ := Γ) (Q := Q) n
    codedNormal A M p B f (n,w.map (Compiler.Word.letterMap (encode n)))=
      (Compiler.Word.partialNormal B (machine A M p n) (fun u => f (n,u)) w).map
        (List.map (Compiler.Word.letterMap (encode n))) := by
  let : Primcodable (State Q n) := Effect.finitePrimcodable _
  let := finiteOrder (T := T) (Γ := Γ) (Q := Q) n
  have h := Compiler.Word.Uniform.partialNormal_map (P := Unit) (encode n) B.blank
    (fun x => Compiler.Control.representative B (machine A M p n) x.2)
    (fun x => codedRepresentative A M p B (n,x.2))
    (fun _ v => codedRepresentative_map A M p B n v)
    (encode_injective n) (fun x => f (n,x.2)) () w
  rw [Compiler.Word.Uniform.partialNormal_specialize B (machine A M p n) () (fun u => f (n,u)) w] at h
  exact h

end

open Compiler Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

end OAI
end

section
-- module Solutions.OAIFAE.SelfReference
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Controlled shorter-input evaluator calls, fixed points, totality, and tested-class realization.
-/

namespace FiniteAlgebraicEnvelopes.Bootstrap
namespace Projection
variable {A B : Type*}
 theorem left_length (w : List (A ⊕ B)) : (left w).length≤w.length := List.length_filterMap_le _ _
end Projection

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap.Rank
variable {P A B C : Type*} [DecidableEq A]

variable [Primcodable P] [Primcodable A]

 theorem primrec_word : Primrec₂ (word (A:=A)) :=
  Primrec.list_map Primrec.snd (Primrec.list_idxOf.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).to₂

end FiniteAlgebraicEnvelopes.Bootstrap.Rank

namespace FiniteAlgebraicEnvelopes.Bootstrap.Uniform
variable {A S Q : Type*} [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [DecidableRel (List.Shortlex r)]

omit [DecidableEq A] in
 theorem pick_eq_canonical (ps : List (List A × Option Q)) (w : List A) (q : Option Q) :
    pick (fun u v => decide (List.Shortlex r u v)) ps w q=Canonical.pick (r:=r) ps w q := by
  have hh : pickStep (Q:=Q) (fun u v => decide (List.Shortlex r u v))=Canonical.pickStep (r:=r) := by
    funext q w v
    simp only [pickStep,Canonical.pickStep,decide_eq_true_eq]
  simp only [pick,Canonical.pick,hh]

variable [Fintype A] [Std.Trichotomous r] (wf : WellFounded r)
variable (C : BlockCode A S) (z : S) (q : List A → Option Q)
variable (ls : List A) (hls : ∀ a,a∈ls)
include hls

omit [DecidableEq A] [DecidableEq S] [Fintype A] in
 theorem output_full_support {n : ℕ} {w : List A} (hw : w.length≤n) :
    output C.encode (fun u v => decide (List.Shortlex r u v)) z
      ((words ls n).map fun v => (v,q v)) (w,q w)=Static.output C wf q z w := by
  have hps : ∀ p∈(words ls n).map (fun v => (v,q v)),p.2=q p.1 := by
    intro p hp
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hp
    rfl
  have hm : (Canonical.least wf q w,q w)∈(words ls n).map (fun v => (v,q v)) :=
    List.mem_map.mpr ⟨Canonical.least wf q w,(mem_words _ _ _).mpr
      ⟨(Canonical.least_length wf q w).trans hw,fun a _ => hls a⟩,
      by simp only [Canonical.least_class]⟩
  simp only [output,Static.output,pick_eq_canonical,Canonical.pick_eq_least wf q hps hm]

omit [DecidableEq A] in
 theorem table_full_support {n : ℕ} (p : List S × List S) :
    p∈table C.encode (fun u v => decide (List.Shortlex r u v)) z
      ((words ls n).map fun v => (v,q v)) ↔ p∈Static.table C wf q z n := by
  simp only [table,List.flatMap_map,List.mem_flatMap]
  constructor
  · rintro ⟨w,hw,h⟩
    have hlen := ((mem_words _ _ _).mp hw).1
    rw [output_full_support wf C z q ls hls hlen] at h
    split at h
    next hh =>
      obtain rfl := List.mem_singleton.mp h
      exact (Static.mem_table C wf q z).mpr ⟨w,hlen,hh.1,hh.2,rfl,rfl⟩
    next hh => simp at h
  · intro hp
    obtain ⟨w,hlen,hne,hout,ha,hb⟩ := (Static.mem_table C wf q z).mp hp
    refine ⟨w,(mem_words _ _ _).mpr ⟨hlen,fun a _ => hls a⟩,?_⟩
    rw [output_full_support wf C z q ls hls hlen,ite_eq_left ⟨hne,hout⟩]
    exact List.mem_singleton.mpr (Prod.ext ha hb)

omit [DecidableEq A] [Fintype A] [Std.Trichotomous r] hls in
 theorem compute_full_support {f : List A → Part (Option Q)} {n : ℕ}
    (hf : ∀ w,w.length≤n → q w∈f w) :
    table C.encode (fun u v => decide (List.Shortlex r u v)) z
      ((words ls n).map fun v => (v,q v))∈
        compute ls C.encode (fun u v => decide (List.Shortlex r u v)) z f n := by
  apply Part.mem_map
  apply Search.traverse_map
  intro w hw
  exact Part.mem_map _ (hf w ((mem_words _ _ _).mp hw).1)

omit [DecidableEq A] [Fintype A] [Std.Trichotomous r] in
 theorem compute_domain_support {f : List A → Part (Option Q)} {n : ℕ}
    (h : (compute ls C.encode (fun u v => decide (List.Shortlex r u v)) z f n).Dom) :
    ∀ w,w.length≤n → (f w).Dom := by
  obtain ⟨rs,hrs⟩ := Part.dom_iff_mem.mp h
  obtain ⟨ps,hps,_⟩ := (Part.mem_map_iff _).mp hrs
  intro w hw
  have hh := Effect.traverse_domain hps.1 w ((mem_words _ _ _).mpr ⟨hw,fun a _ => hls a⟩)
  obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp hh
  obtain ⟨a,ha,_⟩ := (Part.mem_map_iff _).mp hv
  exact ha.1

omit [DecidableEq A] in
 theorem compute_members_support {f : List A → Part (Option Q)} {n : ℕ}
    {rs : List (List S × List S)}
    (hrs : rs∈compute ls C.encode (fun u v => decide (List.Shortlex r u v)) z f n)
    (p : List S × List S) :
    p∈rs ↔ p∈Static.table C wf (Search.value f) z n := by
  have ht := compute_full_support (r:=r) C z (Search.value f) ls
    (fun w hw => Search.value_mem (compute_domain_support (r:=r) C z ls hls hrs.1 w hw))
  rw [Part.mem_unique hrs ht]
  exact table_full_support wf C z (Search.value f) ls hls p

end FiniteAlgebraicEnvelopes.Bootstrap.Uniform

namespace FiniteAlgebraicEnvelopes.Bootstrap
variable {S : Type*}

 theorem step_rulesEq {rs rt : List (List S × List S)} (h : RulesEq rs rt) : Step rs=Step rt := by
  funext u v
  apply propext
  constructor <;> intro hs
  · cases hs with | apply hp x y => exact Step.apply ((h _).mp hp) x y
  · cases hs with | apply hp x y => exact Step.apply ((h _).mpr hp) x y

 theorem critical_rulesEq {rs rt : List (List S × List S)} (h : RulesEq rs rt) (n : ℕ) :
    Critical rs n ↔ Critical rt n := by
  simp only [Critical,Steps,step_rulesEq h,show ∀ p,p∈rs ↔ p∈rt from h]

namespace Selectors
variable [DecidableEq S] {a : Markers S}
 theorem allowed_rulesEq {rs rt : List (List S × List S)} (h : RulesEq rs rt) (s : Stage S) :
    allowed rs s=allowed rt s := by
  apply Bool.eq_iff_iff.mpr
  simp only [allowed_iff,step_rulesEq h]

 theorem choose_rulesEq {rs rt : List (List S × List S)} (h : RulesEq rs rt) (s : Stage S) (n : ℕ) :
    RulesEq (choose (a:=a) rs s n) (choose (a:=a) rt s n) := by
  intro p
  simp only [choose,allowed_rulesEq h s]
  split
  · simpa only [List.mem_append] using or_congr (h p) (Iff.rfl : p∈rules a s.size s.bodies ↔ p∈rules a s.size s.bodies)
  · exact h p

 theorem process_rulesEq {rs rt : List (List S × List S)} (h : RulesEq rs rt)
    (ss : ℕ → Stage S) (n j : ℕ) :
    RulesEq (process (a:=a) rs ss n j) (process (a:=a) rt ss n j) := by
  induction j with
  | zero => exact h
  | succ j ih => exact choose_rulesEq ih (ss j) n
end Selectors
end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap.Uniform
variable {S A B Q R : Type*} [Primcodable S] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop}
  [DecidableRel (List.Shortlex r)] [DecidableRel (List.Shortlex s)]
  [Std.Trichotomous r] [Std.Trichotomous s]
variable (a : Selectors.Markers S) (C : BlockCode A S) (D : BlockCode B S)
  (wf : WellFounded r) (wg : WellFounded s)
variable (ls : List A) (ms : List B) (hls : ∀ x,x∈ls) (hms : ∀ x,x∈ms)
variable (f : List A → Part (Option Q)) (g : List B → Part (Option R))

include wf wg hls hms in
omit [DecidableEq A] [DecidableEq B] in
 theorem tables_members_support {n : ℕ} {rs : List (List S × List S)}
    (hrs : rs∈fullTables (r:=r) (s:=s) a C D ls ms f g n) :
    RulesEq rs (Selectors.process (a:=a)
      (Base.table C D wf wg (Search.value f) (Search.value g) a.zero n) (Selectors.stages a.zero) n n) := by
  obtain ⟨b,hb,rfl⟩ := (Part.mem_map_iff _).mp hrs
  obtain ⟨rc,hrc,h⟩ := Part.mem_bind_iff.mp hb
  obtain ⟨rd,hrd,rfl⟩ := (Part.mem_map_iff _).mp h
  apply Selectors.process_rulesEq
  intro p
  simp only [List.mem_append,Base.table,
    compute_members_support wf C a.zero ls hls hrc p,
    compute_members_support wg D a.zero ms hms hrd p]

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [Std.Trichotomous r] [Std.Trichotomous s] in
 theorem tables_domain_support {n : ℕ}
    (hf : ∀ w,w.length≤n/(C.width+1) → (f w).Dom)
    (hg : ∀ w,w.length≤n/(D.width+1) → (g w).Dom) :
    (fullTables (r:=r) (s:=s) a C D ls ms f g n).Dom := by
  have hc := compute_full_support (r:=r) C a.zero (Search.value f) ls
    (fun w hw => Search.value_mem (hf w hw))
  have hd := compute_full_support (r:=s) D a.zero (Search.value g) ms
    (fun w hw => Search.value_mem (hg w hw))
  apply Part.dom_iff_mem.mpr
  refine ⟨_,Part.mem_map _ (Part.mem_bind_iff.mpr ⟨_,hc,Part.mem_map _ hd⟩)⟩

include wf wg hls hms in
omit [DecidableEq A] [DecidableEq B] in
 theorem stable_support {k n : ℕ} (hkn : k≤n)
    {rk rn : List (List S × List S)}
    (hk : rk∈fullTables (r:=r) (s:=s) a C D ls ms f g k)
    (hn : rn∈fullTables (r:=r) (s:=s) a C D ls ms f g n) : Selectors.BoundedEq rk rn k := by
  have he := Selectors.tables_bounded (a:=a) (stages:=Selectors.stages a.zero)
    (fun _ _ hh => Base.bounded C D wf wg (Search.value f) (Search.value g) a.zero hh)
    (fun j w hw => Selectors.body_lt_size a.zero j hw) (Selectors.index_lt_size a.zero) hkn
  intro p hp
  exact (tables_members_support a C D wf wg ls ms hls hms f g hk p).trans
    ((he p hp).trans (tables_members_support a C D wf wg ls ms hls hms f g hn p).symm)

include wf wg hls hms in
omit [DecidableEq A] [DecidableEq B] in
 theorem good_support {t : S → S → Prop} (hcw : 1<C.width+1) (hdw : 1<D.width+1)
    (hc : ∀ a b,r a b → List.Lex t (C.block a) (C.block b))
    (hd : ∀ a b,s a b → List.Lex t (D.block a) (D.block b))
    (hC : ∀ b∈[a.zero,a.d,a.l,a.r,a.h],b∉C.Alphabet)
    (hD : ∀ b∈[a.zero,a.d,a.l,a.r,a.h],b∉D.Alphabet)
    (hCD : Disjoint C.Alphabet D.Alphabet) {n : ℕ}
    (hf : ∀ w,w.length≤n/(C.width+1) → (f w).Dom)
    (hg : ∀ w,w.length≤n/(D.width+1) → (g w).Dom)
    (hf0 : Search.value f []≠none) (hg0 : Search.value g []≠none)
    (hfc : Static.Contextual (Search.value f) (n/(C.width+1)))
    (hfi : Static.ZeroIdeal (Search.value f) (n/(C.width+1)))
    (hgc : Static.Contextual (Search.value g) (n/(D.width+1)))
    (hgi : Static.ZeroIdeal (Search.value g) (n/(D.width+1))) :
    GoodTable (r:=t) (fullTables (r:=r) (s:=s) a C D ls ms f g) n := by
  obtain ⟨rt,hrt,hdt,hct⟩ := Build.good a C D wf wg f g hcw hdw hc hd hC hD hCD hf hg hf0 hg0 hfc hfi hgc hgi
  obtain ⟨rs,hrs⟩ := Part.dom_iff_mem.mp (tables_domain_support (r:=r) (s:=s) a C D ls ms f g hf hg)
  have he : RulesEq rs rt := by
    rw [Build.tables_eq a C D wf wg hrt]
    exact tables_members_support a C D wf wg ls ms hls hms f g hrs
  exact ⟨rs,hrs,fun p hp => hdt p ((he p).mp hp),(critical_rulesEq he n).mpr hct⟩

end FiniteAlgebraicEnvelopes.Bootstrap.Uniform

namespace FiniteAlgebraicEnvelopes.Bootstrap

namespace Source
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)

attribute [local instance] OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instDecidableEqXSigma_2
attribute [local instance] OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instFintypeLetterSigmaProdBoolState
omit [Primcodable Γ] in
 theorem stable (n : ℕ) {a b : ℕ} (hab : a≤b) {ra rb : List (List Sigma × List Sigma)}
    (ha : ra∈tables s A M n a) (hb : rb∈tables s A M n b) : Selectors.BoundedEq ra rb a := by
  rw [tables_eq_finite] at ha hb
  exact Uniform.stable_support markers (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (finiteCodeG (Γ:=Γ) (Q:=Q) k n) (wf_relT n) (wf_relG k)
    (finiteLetters n) (zLetters k) (mem_finiteLetters n) (by intro x; simp [zLetters,Static.letters])
    (finiteTest A M n) (testG s n) hab ha hb

omit [Primcodable Γ] in
 theorem good_of_tests (n j : ℕ)
    (hf : ∀ w : List (FiniteY (Γ:=Γ) (Q:=Q) n),w.length≤j/(width (Γ:=Γ) (Q:=Q) k n+1) → (finiteTest A M n w).Dom)
    (hf0 : Search.value (finiteTest A M n) []≠none)
    (hfc : Static.Contextual (Search.value (finiteTest A M n)) (j/(width (Γ:=Γ) (Q:=Q) k n+1)))
    (hfi : Static.ZeroIdeal (Search.value (finiteTest A M n)) (j/(width (Γ:=Γ) (Q:=Q) k n+1)))
    (hg0 : Search.value (testG s n) []≠none)
    (hgc : Static.Contextual (Search.value (testG s n)) (j/(width (Γ:=Γ) (Q:=Q) k n+1)))
    (hgi : Static.ZeroIdeal (Search.value (testG s n)) (j/(width (Γ:=Γ) (Q:=Q) k n+1))) :
    GoodTable (r:=fun u v : Sigma => u<v) (tables s A M n) j := by
  rw [tables_eq_finite]
  apply Uniform.good_support markers (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (finiteCodeG (Γ:=Γ) (Q:=Q) k n) (wf_relT n) (wf_relG k)
    (finiteLetters n) (zLetters k) (mem_finiteLetters n) (by intro x; simp [zLetters,Static.letters])
    (finiteTest A M n) (testG s n)
  · change 1<width (Γ:=Γ) (Q:=Q) k n+1
    unfold width
    omega
  · change 1<width (Γ:=Γ) (Q:=Q) k n+1
    unfold width
    omega
  · exact codeT_order k n
  · exact codeG_order k n
  · exact codeT_avoid k n
  · exact codeG_avoid k n
  · exact codes_disjoint k n
  · exact hf
  · intro w hw; trivial
  · exact hf0
  · exact hg0
  · exact hfc
  · exact hfi
  · exact hgc
  · exact hgi

end Source
end FiniteAlgebraicEnvelopes.Bootstrap

end OAI
end

section
-- module Solutions.OAIFAE.MonoidAlgebras
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite compiler monoids, zero products, both F₂ algebras, and selector constructions.
-/

namespace FiniteAlgebraicEnvelopes
namespace Compiler.Word
variable {S Γ Q : Type*}
 theorem grade_le_twice_length (w : List (Letter S Γ Q)) : grade w≤2*w.length := by
  induction w with
  | nil => simp [grade,Path.grade]
  | cons a w ih =>
    have ha : Path.letterGrade (gradeCell (S:=S) (Γ:=Γ)) a≤2 := by
      cases a <;> simp [Path.letterGrade,gradeCell]
      all_goals rename_i c; cases c.1 <;> simp [Cleanup.grade]
    simpa [grade,Path.grade,List.map_cons,List.sum_cons,Nat.mul_add,Nat.add_comm] using Nat.add_le_add ha ih

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

 theorem normal_zero_context
    (hdecode : ∀ g a, A.output g=some a → g=A.input a)
    {f : List S → Part (List S)} {m : ℕ} (h : PartialBudget f m) (hr : Realizes A M f)
    (a b u : List (Letter S Γ Q)) (hm : grade (a ++ u ++ b) ≤ m)
    (hz : normal A M (fun w => partValue (f w)) u=[.zero]) :
    normal A M (fun w => partValue (f w)) (a++u++b)=[.zero] := by
  have he : normal A M (fun w => partValue (f w)) u=normal A M (fun w => partValue (f w)) [.zero] := by
    simpa using hz
  have hb : grade (a ++ [.zero] ++ b) ≤ m := by
    simp only [grade_append] at *
    have h0 : grade ([.zero] : List (Letter S Γ Q))=0 := rfl
    rw [h0]
    omega
  rw [normal_context A M hdecode h.totalize (Realizes.computesAt A M hr h) he a b hm hb]
  simpa using normal_contains_omega A M (fun w => partValue (f w)) a b
end Compiler.Word

namespace Bootstrap
namespace Projection
variable {A B C D : Type*}
@[simp] theorem left_map (f : A → C) (g : B → D) (w : List (A ⊕ B)) :
    left (w.map (Sum.map f g))=(left w).map f := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a with
    | inl a => exact congrArg (f a :: ·) ih
    | inr b => exact ih
@[simp] theorem right_map (f : A → C) (g : B → D) (w : List (A ⊕ B)) :
    right (w.map (Sum.map f g))=(right w).map g := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a with
    | inl a => exact ih
    | inr b => exact congrArg (g b :: ·) ih
end Projection

namespace ZeroProduct
variable {A C D : Type*} [DecidableEq C]

 theorem contextual (z : C) (f : List A → C) (g : List A → D) (n : ℕ)
    (hf : ∀ a b u v,(a++u++b).length≤n → (a++v++b).length≤n → f u=f v → f (a++u++b)=f (a++v++b))
    (hz : ∀ a b u,(a++u++b).length≤n → f u=z → f (a++u++b)=z)
    (hg : ∀ a b u v,g u=g v → g (a++u++b)=g (a++v++b)) :
    Static.Contextual (test z f g) n := by
  intro a b u v hu hv he
  by_cases huf : f u=z
  · have hvf : f v=z := by
      by_contra hc
      simp [test,huf,hc] at he
    simp only [test,hz a b u hu huf,hz a b v hv hvf,ite_true]
  · have hvf : f v≠z := by
      intro hc
      simp [test,huf,hc] at he
    have hei : f u=f v ∧ g u=g v := by simpa [test,huf,hvf] using he
    simp only [test,hf a b u v hu hv hei.1,hg a b u v hei.2]

 theorem ideal (z : C) (f : List A → C) (g : List A → D) (n : ℕ)
    (hz : ∀ a b u,(a++u++b).length≤n → f u=z → f (a++u++b)=z) :
    Static.ZeroIdeal (test z f g) n := by
  intro a b u hu he
  have hf : f u=z := by simpa [test] using he
  simp only [test,hz a b u hu hf,ite_true]
end ZeroProduct
end Bootstrap

namespace PartialAffine
 theorem value_context {u v : List Letter} (h : value u=value v) (a b : List Letter) :
    value (a++u++b)=value (a++v++b) := by
  simp only [value,List.map_append,List.prod_append] at *
  rw [h]
 theorem testedClass_context {u v : List Letter} (h : testedClass u=testedClass v) (a b : List Letter) :
    testedClass (a++u++b)=testedClass (a++v++b) :=
  (testedClass_eq_iff _ _).mpr (value_context ((testedClass_eq_iff _ _).mp h) a b)
end PartialAffine
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)

local instance instDecidableEqXSigma_3 : DecidableEq (Tested.X Sigma Γ Q) := inferInstance
local instance instLinearOrderSectorSigmaProdBoolState (n : ℕ) : LinearOrder (Compiler.Control.Sector Sigma (Bool×Γ) (ParameterMachine.State Q n)) :=
  finiteOrder (T:=Sigma) (Γ:=Γ) (Q:=Q) n

noncomputable def finiteValue (n : ℕ) (w : List (FiniteY (Γ:=Γ) (Q:=Q) n)) : List (Tested.X Sigma Γ Q) :=
  (Word.normal (terminalAlphabet A) (terminalMachine A M n) (fun w => partValue (raw n w)) (Projection.left w)).map
    (Word.letterMap (encode n))
noncomputable def finiteClass (n : ℕ) (w : List (FiniteY (Γ:=Γ) (Q:=Q) n)) :=
  ZeroProduct.test [.zero] (finiteValue A M n) (fun w => PartialAffine.testedClass (Projection.right w)) w

omit [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q] in
 theorem projection_grade (n : ℕ) (w : List (FiniteY (Γ:=Γ) (Q:=Q) n)) :
    Word.grade (Projection.left w)≤2*w.length :=
  (Word.grade_le_twice_length _).trans (Nat.mul_le_mul_left 2 (Projection.left_length w))

omit [Primcodable Γ] in
 theorem finiteTest_eq (n j : ℕ) (h : PartialBudget (raw n) (2*j))
    (w : List (FiniteY (Γ:=Γ) (Q:=Q) n)) (hw : w.length≤j) :
    finiteTest A M n w=Part.some (finiteClass A M n w) := by
  have hg := (projection_grade n w).trans (Nat.mul_le_mul_left 2 hw)
  simp only [finiteTest,testT,Tested.family,includeY,Projection.left_map,Projection.right_map,List.map_id]
  rw [codedNormal_map,Word.partialNormal_eq_some _ _ h _ hg]
  simp only [Part.map_some,finiteClass,ZeroProduct.test,finiteValue,Tested.combine,
    terminalAlphabet,terminalMachine]
  rfl

omit [Primcodable Γ] in
 theorem finiteValue_zero (n : ℕ) (w : List (FiniteY (Γ:=Γ) (Q:=Q) n)) :
    finiteValue A M n w=[.zero] ↔
      Word.normal (terminalAlphabet A) (terminalMachine A M n) (fun w => partValue (raw n w)) (Projection.left w)=[.zero] := by
  change List.map (Word.letterMap (encode n)) _=List.map (Word.letterMap (encode n)) [.zero] ↔ _
  exact (List.map_injective_iff.mpr (Word.letterMap_injective _ (encode_injective n))).eq_iff

omit [Primcodable Γ] in
 theorem finiteValue_context (n j : ℕ) (h : PartialBudget (raw n) (2*j))
    (hr : Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a,(terminalAlphabet A).output g=some a → g=(terminalAlphabet A).input a)
    (a b u v : List (FiniteY (Γ:=Γ) (Q:=Q) n))
    (hu : (a++u++b).length≤j) (hv : (a++v++b).length≤j)
    (he : finiteValue A M n u=finiteValue A M n v) :
    finiteValue A M n (a++u++b)=finiteValue A M n (a++v++b) := by
  have hh := List.map_injective_iff.mpr (Word.letterMap_injective (encode n) (encode_injective n)) he
  have hgu := (projection_grade n (a++u++b)).trans (Nat.mul_le_mul_left 2 hu)
  have hgv := (projection_grade n (a++v++b)).trans (Nat.mul_le_mul_left 2 hv)
  simp only [Projection.left_append] at hgu hgv
  simp only [finiteValue,Projection.left_append]
  congr 1
  exact Word.normal_context (terminalAlphabet A) (terminalMachine A M n) hd h.totalize
    (Word.Realizes.computesAt _ _ hr h) hh _ _ hgu hgv

omit [Primcodable Γ] in
 theorem finiteValue_ideal (n j : ℕ) (h : PartialBudget (raw n) (2*j))
    (hr : Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a,(terminalAlphabet A).output g=some a → g=(terminalAlphabet A).input a)
    (a b u : List (FiniteY (Γ:=Γ) (Q:=Q) n)) (hu : (a++u++b).length≤j)
    (he : finiteValue A M n u=[.zero]) : finiteValue A M n (a++u++b)=[.zero] := by
  apply (finiteValue_zero A M n _).mpr
  have hh := (finiteValue_zero A M n u).mp he
  have hgu := (projection_grade n (a++u++b)).trans (Nat.mul_le_mul_left 2 hu)
  simp only [Projection.left_append] at hgu ⊢
  exact Word.normal_zero_context (terminalAlphabet A) (terminalMachine A M n) hd h hr _ _ _ hgu hh

omit [Primcodable Γ] in
 theorem finiteClass_context (n j : ℕ) (h : PartialBudget (raw n) (2*j))
    (hr : Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a,(terminalAlphabet A).output g=some a → g=(terminalAlphabet A).input a) :
    Static.Contextual (finiteClass A M n) j := by
  apply ZeroProduct.contextual
  · exact finiteValue_context A M n j h hr hd
  · exact finiteValue_ideal A M n j h hr hd
  · intro a b u v he
    simpa only [Projection.right_append] using PartialAffine.testedClass_context he (Projection.right a) (Projection.right b)

omit [Primcodable Γ] in
 theorem finiteClass_ideal (n j : ℕ) (h : PartialBudget (raw n) (2*j))
    (hr : Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a,(terminalAlphabet A).output g=some a → g=(terminalAlphabet A).input a) :
    Static.ZeroIdeal (finiteClass A M n) j :=
  ZeroProduct.ideal _ _ _ _ (finiteValue_ideal A M n j h hr hd)

omit [Primcodable Γ] in
 theorem finiteClass_nil (n : ℕ) : finiteClass A M n []≠none := by
  simp [finiteClass,ZeroProduct.test,finiteValue,Projection.left]

omit [Primcodable Γ] in
 theorem search_value_eq (n j : ℕ) (h : PartialBudget (raw n) (2*j))
    (w : List (FiniteY (Γ:=Γ) (Q:=Q) n)) (hw : w.length≤j) :
    Search.value (finiteTest A M n) w=finiteClass A M n w := by
  have hh := finiteTest_eq A M n j h w hw
  have hd : (finiteTest A M n w).Dom := by rw [hh]; trivial
  have hm := Search.value_mem hd
  simpa only [hh,Part.mem_some_iff] using hm

omit [Primcodable Γ] in
 theorem tests_bounded (n j : ℕ) (h : PartialBudget (raw n) (2*j))
    (hr : Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a,(terminalAlphabet A).output g=some a → g=(terminalAlphabet A).input a) :
    (∀ w : List (FiniteY (Γ:=Γ) (Q:=Q) n),w.length≤j → (finiteTest A M n w).Dom) ∧
      Search.value (finiteTest A M n) []≠none ∧
      Static.Contextual (Search.value (finiteTest A M n)) j ∧
      Static.ZeroIdeal (Search.value (finiteTest A M n)) j := by
  refine ⟨fun w hw => ?_,?_,?_,?_⟩
  · rw [finiteTest_eq A M n j h w hw]; trivial
  · rw [search_value_eq A M n j h [] (by simp)]
    exact finiteClass_nil A M n
  · intro a b u v hu hv he
    have hul : u.length≤j := by simp only [List.length_append] at hu; omega
    have hvl : v.length≤j := by simp only [List.length_append] at hv; omega
    rw [search_value_eq A M n j h u hul,search_value_eq A M n j h v hvl] at he
    rw [search_value_eq A M n j h _ hu,search_value_eq A M n j h _ hv]
    exact finiteClass_context A M n j h hr hd a b u v hu hv he
  · intro a b u hu he
    have hul : u.length≤j := by simp only [List.length_append] at hu; omega
    rw [search_value_eq A M n j h u hul] at he
    rw [search_value_eq A M n j h _ hu]
    exact finiteClass_ideal A M n j h hr hd a b u hu he

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes

namespace Bootstrap
namespace Static
variable {A Q : Type*} (q : List A → Option Q)
 theorem contextual_zero : Contextual q 0 := by
  intro a b u v hu hv he
  have ha : a=[] := by simpa using (show a.length=0 from by simp only [List.length_append] at hu; omega)
  have hb : b=[] := by simpa using (show b.length=0 from by simp only [List.length_append] at hu; omega)
  simpa [ha,hb] using he
 theorem zeroIdeal_zero : ZeroIdeal q 0 := by
  intro a b u hu he
  have ha : a=[] := by simpa using (show a.length=0 from by simp only [List.length_append] at hu; omega)
  have hb : b=[] := by simpa using (show b.length=0 from by simp only [List.length_append] at hu; omega)
  simpa [ha,hb] using he
end Static

namespace Source
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)

local instance instLinearOrderSectorSigmaProdBoolState_1_rcde1e2_1 (n : ℕ) : LinearOrder (Compiler.Control.Sector Sigma (Bool×Γ) (ParameterMachine.State Q n)) :=
  finiteOrder (T:=Sigma) (Γ:=Γ) (Q:=Q) n
omit [Primcodable Γ] in
 theorem finiteTest_nil (n : ℕ) : finiteTest A M n []=Part.some (finiteClass A M n []) := by
  simp only [finiteTest,testT,Tested.family,includeY,List.map_nil,Projection.left]
  have hh := codedNormal_map A M (.inr ()) (terminalAlphabet A) n (fun p => raw p.1 p.2) ([] : List (Word.Letter Sigma (Bool×Γ) (ParameterMachine.State Q n)))
  simp only [List.map_nil,Word.partialNormal_nil,Part.map_some] at hh
  simp only [List.filterMap_nil]
  rw [hh]
  simp [finiteClass,ZeroProduct.test,finiteValue,Projection.left,Projection.right,Tested.combine]

omit [Primcodable Γ] in
 theorem finite_search_nil (n : ℕ) : Search.value (finiteTest A M n) []=finiteClass A M n [] := by
  have hd : (finiteTest A M n []).Dom := by rw [finiteTest_nil]; trivial
  simpa only [finiteTest_nil,Part.mem_some_iff] using Search.value_mem hd

omit [Primcodable Γ] in
 theorem tests_zero (n : ℕ) :
    (∀ w : List (FiniteY (Γ:=Γ) (Q:=Q) n),w.length≤0 → (finiteTest A M n w).Dom) ∧
      Search.value (finiteTest A M n) []≠none ∧
      Static.Contextual (Search.value (finiteTest A M n)) 0 ∧
      Static.ZeroIdeal (Search.value (finiteTest A M n)) 0 := by
  refine ⟨?_,?_,Static.contextual_zero _,Static.zeroIdeal_zero _⟩
  · intro w hw
    have hw : w=[] := by simpa using hw
    subst w
    rw [finiteTest_nil]; trivial
  · rw [finite_search_nil]
    exact finiteClass_nil A M n

variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
 theorem group_search_value (n : ℕ) (w : List (Z k)) :
    Search.value (testG s n) w=some (WordProblem.testedClass s w) := by
  have hm := Search.value_mem (f:=testG s n) (w:=w) (show (testG s n w).Dom from True.intro)
  simpa only [testG,Part.mem_some_iff] using hm

 theorem group_tests (n j : ℕ) :
    Search.value (testG s n) []≠none ∧
      Static.Contextual (Search.value (testG s n)) j ∧
      Static.ZeroIdeal (Search.value (testG s n)) j := by
  refine ⟨by simp [group_search_value],?_,?_⟩
  · intro a b u v hu hv he
    simp only [group_search_value,Option.some.injEq] at he ⊢
    apply (WordProblem.testedClass_eq_iff s _ _).mpr
    have hh := (WordProblem.testedClass_eq_iff s _ _).mp he
    simp only [WordProblem.evalWord_append]
    rw [hh]
  · intro a b u hu he
    simp only [group_search_value,Option.some_ne_none] at he

end Source
end Bootstrap
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

section
open Compiler Compiler.Simulator MachineRealization
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)

omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem quota_smaller (k n j : ℕ) (hj : 0<j) :
    2*(j/(width (Γ:=Γ) (Q:=Q) k n+1))<j := by
  have hd : 3≤width (Γ:=Γ) (Q:=Q) k n+1 := by unfold width; omega
  have hp := Nat.mul_le_mul_right (j/(width (Γ:=Γ) (Q:=Q) k n+1)) hd
  have hq := Nat.div_mul_le_self j (width (Γ:=Γ) (Q:=Q) k n+1)
  rw [Nat.mul_comm (width (Γ:=Γ) (Q:=Q) k n+1)] at hp
  omega

end

section
open Compiler Compiler.Simulator MachineRealization

attribute [instance] Family.finiteΓ Family.finiteQ Family.decΓ Family.decQ Family.codeΓ Family.codeQ

end

open Compiler Compiler.Simulator MachineRealization
open scoped Compiler.HeadCodec

end FiniteAlgebraicEnvelopes.Bootstrap.Source

end

end OAI
end


