-- Prove2me | Definitions.Def_OAIQ18Pg009
-- name    : OAIQ18Pg009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T16:03:28.402584+00:00
-- url     : https://prove2.me/theorems/23b394a8-e09f-4e6c-8ccb-29e0b14deb97
-- title:
--   Definitions bundle OAIQ18Pg009 of the split of OpenAI, An infinite finitely presented periodic group
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SourceBurnside.thm_main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented periodic group*, OpenAI Math Release, September 23, 2026, result family 247, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 316 declarations of OpenAI's Lean: 92 definitions, 2 inductive types or structures, 1 instance and 221 theorems. The definitions and types are `OAI.SourceBurnside.ConcreteSource.R`, `OAI.SourceBurnside.ConcreteSource.augmentation`, `OAI.SourceBurnside.ConcreteSource.evalOne`, `OAI.SourceBurnside.ConcreteSource.evalZero`, `OAI.SourceBurnside.ConcreteSource.gradedElement`, `OAI.SourceBurnside.ConcreteSource.groundElement`, `OAI.SourceBurnside.ConcreteSource.height`, `OAI.SourceBurnside.ConcreteSource.machine`, `OAI.SourceBurnside.DropPadding.program`, `OAI.SourceBurnside.FiniteSteinbergPresentation.equiv`, `OAI.SourceBurnside.FiniteTable.AcquiredPrefix`, `OAI.SourceBurnside.FiniteTable.AcquiredPrefix.boundaryCell`, `OAI.SourceBurnside.FiniteTable.AcquiredPrefix.boundaryWord`, `OAI.SourceBurnside.FiniteTable.AcquiredPrefix.first`, `OAI.SourceBurnside.FiniteTable.AcquiredPrefix.idleWord`, `OAI.SourceBurnside.FiniteTable.AcquiredPrefix.last`, `OAI.SourceBurnside.FiniteTable.Cell.CheckerSafe`, `OAI.SourceBurnside.FiniteTable.Cell.Cut`, `OAI.SourceBurnside.FiniteTable.Cell.blockRank`, `OAI.SourceBurnside.FiniteTable.Cell.geometryRank`, `OAI.SourceBurnside.FiniteTable.Cell.geometrySignature`, `OAI.SourceBurnside.FiniteTable.Cell.paletteRank`, `OAI.SourceBurnside.FiniteTable.Cell.paletteSignature`, `OAI.SourceBurnside.FiniteTable.Codec.Reach`, `OAI.SourceBurnside.FiniteTable.Codec.Step`, `OAI.SourceBurnside.FiniteTable.Codec.Survives`, `OAI.SourceBurnside.FiniteTable.Codec.algebraTable`, `OAI.SourceBurnside.FiniteTable.Codec.boundedWords`, `OAI.SourceBurnside.FiniteTable.Codec.eligibleFields`, `OAI.SourceBurnside.FiniteTable.Codec.fields`, `OAI.SourceBurnside.FiniteTable.Codec.letter`, `OAI.SourceBurnside.FiniteTable.Codec.noncolor`, `OAI.SourceBurnside.FiniteTable.Codec.rawCut`, `OAI.SourceBurnside.FiniteTable.Codec.rawToken`, `OAI.SourceBurnside.FiniteTable.Component.headIndex`, `OAI.SourceBurnside.FiniteTable.Component.partialRegion`, `OAI.SourceBurnside.FiniteTable.Component.word`, `OAI.SourceBurnside.FiniteTable.EndsStop`, `OAI.SourceBurnside.FiniteTable.GeomRel`, `OAI.SourceBurnside.FiniteTable.Reach` and 54 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/PeriodicGroups, in whole or in part: `PeriodicGroups_Algebra_HierarchyGrowth`, `PeriodicGroups_Algebra_MatrixTests`, `PeriodicGroups_Algebra_WordAlgebra`, `PeriodicGroups_Machines_Compilation`, `PeriodicGroups_Machines_InputEncoding`, `PeriodicGroups_Machines_ProgramAssembly`, `PeriodicGroups_Machines_ProgramFixedPoint`, `PeriodicGroups_Machines_StackCompression`, `PeriodicGroups_Machines_TimedExecution`, `PeriodicGroups_Machines_UniversalInput`, `PeriodicGroups_Rules_BoundaryCell`, `PeriodicGroups_Rules_DataWords`, `PeriodicGroups_Rules_GeometricRelations`, `PeriodicGroups_Rules_HeadTour`, `PeriodicGroups_Rules_PrefixRewriting`, `PeriodicGroups_Rules_TableEncoding`, `PeriodicGroups_Rules_TemplateHierarchy`, `PeriodicGroups_Rules_Transactions`, `PeriodicGroups_Rules_WordComponents`, `PeriodicGroups_Rules_WordRewriting`, `PeriodicGroups_Steinberg_BandFactorization`, `PeriodicGroups_Steinberg_CoefficientQuotients`.
--
--   **Imports.** It imports the published bundle `Def_PeriodicGroup`; the bundles `OAIQ18Pg005`, `OAIQ18Pg006` and `OAIQ18Pg007` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ18Pg012`; the statements `OAI.SourceBurnside.ConcreteSource.matrix_nil_kernel`, `OAI.SourceBurnside.ConcreteSource.matrix_periodic`, `OAI.SourceBurnside.ConcreteSource.steinberg_infinite` and `OAI.SourceBurnside.SourceMachine.MachineHierarchy.matrixNilKernel`; the proof of `OAI.SourceBurnside.ConcreteSource.matrix_nil_kernel`.
-- source:
--   OpenAI, An infinite finitely presented periodic group, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 247; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/PeriodicGroups at commit adc7f12

import Mathlib
import Definitions.Def_PeriodicGroup
import Definitions.Def_OAIQ18Pg005
import Definitions.Def_OAIQ18Pg006
import Definitions.Def_OAIQ18Pg007

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_HeadTour
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest _root_.OAI.SourceBurnside.FiniteTable.instDecidableCellCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.FiniteTable
open LocalSyntax
open LocalSyntax.Skeleton

variable {q : ℕ} [NeZero q]

lemma replacement_symm (S : Schedule q) (dataSize : ℕ) (v w : List (Cell q)) :
    Replacement S dataSize v w ↔ Replacement S dataSize w v := by
  simp only [Replacement,List.mem_append,or_imp,forall_and]
  constructor <;> rintro ⟨⟨hv,hw⟩, hh⟩
  · refine ⟨⟨hw,hv⟩,?_⟩
    rcases hh with ⟨a,b,rfl,rfl,hh⟩ | ⟨a,b,a',b',rfl,rfl,hh⟩
    · exact Or.inl ⟨b,a,rfl,rfl,hh.symm⟩
    · exact Or.inr ⟨a',b',a,b,rfl,rfl,hh.symm⟩
  · refine ⟨⟨hw,hv⟩,?_⟩
    rcases hh with ⟨a,b,rfl,rfl,hh⟩ | ⟨a,b,a',b',rfl,rfl,hh⟩
    · exact Or.inl ⟨b,a,rfl,rfl,hh.symm⟩
    · exact Or.inr ⟨a',b',a,b,rfl,rfl,hh.symm⟩

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_TableEncoding
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAdmissible _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideEndpoint _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHead _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideInternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLeftExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideRightExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideStructural _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest _root_.OAI.SourceBurnside.FiniteTable.instDecidableCellCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.FiniteTable
open LocalSyntax
open LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q]

lemma unary_transaction_context {S : Schedule q} {a b : Cell q} (h : Unary S a b)
    (p s : List (Skeleton q 10)) :
    Closed (p ++ a.skeleton :: s) ↔ Closed (p ++ b.skeleton :: s) := by
  cases h with
  | create c side hc =>
    exact (closed_idle_metadata p s c.skeleton defaultMeta).trans
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append,Cell.boundary,Cell.full,Cell.wing,Cell.idle,Cell.pos] using
        (Skeleton.replacement_context (Skeleton.Replacement.create c.skeleton hc) p s))
  | finish_acquisition c side hc =>
    simpa only [List.append_assoc,List.cons_append,List.nil_append,Cell.boundary,Cell.full,Cell.wing,Cell.idle,Cell.pos] using
      (Skeleton.replacement_context (Skeleton.Replacement.finish c.skeleton hc) p s)
  | _ => exact Iff.rfl

theorem replacement_transaction_context {S : Schedule q} {d : ℕ} {v w : List (Cell q)}
    (h : Replacement S d v w) (p s : List (Cell q)) :
    Closed ((p ++ v ++ s).map Cell.skeleton) ↔
      Closed ((p ++ w ++ s).map Cell.skeleton) := by
  rcases h.2 with ⟨a,b,rfl,rfl,hh⟩ | ⟨a,b,a',b',rfl,rfl,hh⟩
  · simp only [List.map_append,List.map_cons,List.append_assoc,List.cons_append,List.nil_append]
    exact hh.elim (fun h => unary_transaction_context h _ _)
      (fun h => (unary_transaction_context h _ _).symm)
  · simp only [List.map_append,List.map_cons,List.append_assoc,List.cons_append,List.nil_append]
    exact hh.elim (fun h => binary_transaction_context h _ _)
      (fun h => (binary_transaction_context h _ _).symm)

end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable
open LocalSyntax
variable {q : ℕ} [NeZero q]

lemma unary_checker_context {S : Schedule q} {a b : Cell q} (h : Unary S a b)
    (p s : List (Cell q)) :
    List.IsChain CheckerPair (p ++ a :: s) ↔ List.IsChain CheckerPair (p ++ b :: s) := by
  apply chain_replace_one
  · intro c; cases h <;> exact Iff.rfl
  · intro c; cases h <;> exact Iff.rfl

theorem replacement_checker_context {S : Schedule q} {d : ℕ} {v w : List (Cell q)}
    (h : Replacement S d v w) (p s : List (Cell q)) :
    List.IsChain CheckerPair (p ++ v ++ s) ↔ List.IsChain CheckerPair (p ++ w ++ s) := by
  rcases h.2 with ⟨a,b,rfl,rfl,hh⟩ | ⟨a,b,a',b',rfl,rfl,hh⟩
  · simp only [List.append_assoc,List.cons_append,List.nil_append]
    exact hh.elim (fun h => unary_checker_context h _ _)
      (fun h => (unary_checker_context h _ _).symm)
  · simp only [List.append_assoc,List.cons_append,List.nil_append]
    exact hh.elim (fun h => binary_checker_context h _ _)
      (fun h => (binary_checker_context h _ _).symm)

theorem replacement_syntax_context {S : Schedule q} {d : ℕ} {v w : List (Cell q)}
    (h : Replacement S d v w) (p s : List (Cell q)) :
    Syntax S d (p ++ v ++ s) ↔ Syntax S d (p ++ w ++ s) := by
  have hv : ∀ c ∈ v, c.Format S d := fun c hc => h.1 c (List.mem_append_left _ hc)
  have hw : ∀ c ∈ w, c.Format S d := fun c hc => h.1 c (List.mem_append_right _ hc)
  unfold Syntax
  rw [replacement_transaction_context h, replacement_checker_context h]
  simp only [List.forall_mem_append]
  tauto

def Step (S : Schedule q) (d : ℕ) (v w : List (Cell q)) : Prop :=
  ∃ p s a b, v=p++a++s ∧ w=p++b++s ∧ Replacement S d a b

abbrev Reach (S : Schedule q) (d : ℕ) := Relation.ReflTransGen (Step S d)

theorem reach_syntax {S : Schedule q} {d : ℕ} {v w : List (Cell q)}
    (h : Reach S d v w) (hv : Syntax S d v) : Syntax S d w := by
  induction h with
  | refl => exact hv
  | tail h e ih =>
    rcases e with ⟨p,s,a,b,rfl,rfl,he⟩
    exact (replacement_syntax_context he p s).mp ih

end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

lemma step_symm {v w : List (Cell q)} (h : Step S d v w) : Step S d w v := by
  rcases h with ⟨p,s,a,b,hv,hw,hh⟩
  exact ⟨p,s,b,a,hw,hv,(replacement_symm S d a b).mp hh⟩

lemma step_context {v w : List (Cell q)} (h : Step S d v w) (p s : List (Cell q)) :
    Step S d (p++v++s) (p++w++s) := by
  rcases h with ⟨l,r,a,b,rfl,rfl,hh⟩
  exact ⟨p++l,r++s,a,b,by simp only [List.append_assoc],
    by simp only [List.append_assoc],hh⟩

lemma reach_context {v w : List (Cell q)} (h : Reach S d v w) (p s : List (Cell q)) :
    Reach S d (p++v++s) (p++w++s) := by
  induction h with
  | refl => exact .refl
  | tail h e ih => exact ih.tail (step_context e p s)

end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable.Codec
open LocalSyntax

lemma decodeWord_encode {h : ℕ} (hh : 4≤h) (w : List (Cell (2^h))) :
    decodeWord (by omega) (w.map encode)=some w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [decodeWord,decode_encode hh,ih]

lemma binaryZero_encode {h : ℕ} (hh : 4≤h) (a b : Cell (2^h)) :
    binaryZero (by omega) (encode a) (encode b) ↔ BinaryZero a b := by
  simp [binaryZero,decode_encode hh]
lemma replacement_encode {h : ℕ} (hh : 4≤h) (S : Schedule (2^h)) (d : ℕ)
    (v w : List (Cell (2^h))) :
    replacement (by omega) S d (v.map encode) (w.map encode) ↔ Replacement S d v w := by
  simp [replacement,decodeWord_encode hh]

end SourceBurnside.FiniteTable.Codec

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_Transactions
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideEndpoint _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLastOK _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalettePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest _root_.OAI.SourceBurnside.FiniteTable.instDecidableCellCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

section LocalEdits
variable {N : ℕ} {α : Type*}

lemma step_one_ofFn (f g : Fin N → Cell q) (i : Fin N)
    (hf : ∀ j, j ≠ i → f j = g j) (hr : Replacement S d [f i] [g i]) :
    Step S d (List.ofFn f) (List.ofFn g) := by
  refine ⟨(List.ofFn f).take i.val,(List.ofFn f).drop (i.val+1),[f i],[g i],
    ofFn_split_one f i,?_,hr⟩
  have hp := ofFn_take_congr f g i.val (fun j hj => hf j (by intro he; subst j; omega))
  have hs := ofFn_drop_congr f g (i.val+1) (fun j hj => hf j (by intro he; subst j; omega))
  rw [hp,hs]
  exact ofFn_split_one g i

lemma step_two_ofFn (f g : Fin N → Cell q) (i j : Fin N) (hij : i.val+1=j.val)
    (hf : ∀ k, k ≠ i → k ≠ j → f k = g k)
    (hr : Replacement S d [f i,f j] [g i,g j]) :
    Step S d (List.ofFn f) (List.ofFn g) := by
  refine ⟨(List.ofFn f).take i.val,(List.ofFn f).drop (j.val+1),[f i,f j],[g i,g j],
    ofFn_split_two f i j hij,?_,hr⟩
  have hp := ofFn_take_congr f g i.val (fun k hk => hf k
    (by intro he; subst k; omega) (by intro he; subst k; omega))
  have hs := ofFn_drop_congr f g (j.val+1) (fun k hk => hf k
    (by intro he; subst k; omega) (by intro he; subst k; omega))
  rw [hp,hs]
  exact ofFn_split_two g i j hij
end LocalEdits

namespace Region
variable (R : Region q d) (S : Schedule q)

lemma step_unary {s t : HeadTour.FullState (S.count R.task).val R.size}
    (hs : R.SideOK S s) (ht : R.SideOK S t) (hp : R.position S s=R.position S t)
    (he : Unary S
      ((R.cell (R.position S s)).full s.side (R.clause S s) (R.phase S s) s.reg)
      ((R.cell (R.position S t)).full t.side (R.clause S t) (R.phase S t) t.reg)) :
    Step S d (R.realize S s) (R.realize S t) := by
  apply step_one_ofFn (R.realizeCell S s) (R.realizeCell S t) (R.position S s)
  · exact fun i hi => R.realizeCell_eq_off_head S s t hp i hi
  · refine ⟨?_,Or.inl ⟨_,_,rfl,rfl,Or.inl ?_⟩⟩
    · intro c hc
      simp only [List.singleton_append,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl
      · exact R.realizeCell_format S s hs _
      · exact R.realizeCell_format S t ht _
    · rw [R.realize_head, hp,R.realize_head]
      simpa only [hp] using he

lemma step_adjacent {s t : HeadTour.FullState (S.count R.task).val R.size}
    (hs : R.SideOK S s) (ht : R.SideOK S t)
    (i j : Fin R.size) (hij : i.val+1=j.val)
    (hps : R.position S s=i ∨ R.position S s=j)
    (hpt : R.position S t=i ∨ R.position S t=j)
    (he : Binary S (R.realizeCell S s i) (R.realizeCell S s j)
      (R.realizeCell S t i) (R.realizeCell S t j)) :
    Step S d (R.realize S s) (R.realize S t) := by
  apply step_two_ofFn (R.realizeCell S s) (R.realizeCell S t) i j hij
  · exact R.realizeCell_eq_off_adjacent S s t i j hij hps hpt
  · refine ⟨?_,Or.inr ⟨_,_,_,_,rfl,rfl,Or.inl he⟩⟩
    intro c hc
    simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact R.realizeCell_format S s hs _
    · exact R.realizeCell_format S s hs _
    · exact R.realizeCell_format S t ht _
    · exact R.realizeCell_format S t ht _

lemma tour_realize_step (j : Fin (S.count R.task).val) {s t : HeadTour.State R.size}
    (he : ((R.plan S).payload j).Edge s t)
    (hs : R.SideOK S (HeadTour.atClause j s)) :
    Step S d (R.realize S (HeadTour.atClause j s))
      (R.realize S (HeadTour.atClause j t)) := by
  have ht := (R.edge_side S (.tour j he)).mp hs
  cases he with
  | enter r b =>
    apply R.step_unary S hs ht rfl
    exact Unary.read_enter (R.cell R.last) b (R.clauseIndex S j) r R.last_last
  | read_turn r b =>
    apply R.step_unary S hs ht rfl
    exact Unary.read_turn (R.cell R.first) b (R.clauseIndex S j) r R.first_first
  | read_exit r b =>
    apply R.step_unary S hs ht rfl
    exact Unary.read_exit (R.cell R.last) b (R.clauseIndex S j) r R.last_last
  | gate r b hg =>
    apply R.step_unary S hs ht rfl
    have hg' : (S.clause (R.cell R.last).metadata.task (R.clauseIndex S j)).truth r = true := by
      rw [R.task_eq]
      exact hg
    exact Unary.gate (R.cell R.last) b (R.clauseIndex S j) r R.last_last hg'
  | undo_enter r b =>
    apply R.step_unary S hs ht rfl
    exact Unary.undo_enter (R.cell R.last) b (R.clauseIndex S j) r R.last_last
  | undo_turn r b =>
    apply R.step_unary S hs ht rfl
    exact Unary.undo_turn (R.cell R.first) b (R.clauseIndex S j) r R.first_first
  | undo_exit r b =>
    apply R.step_unary S hs ht rfl
    exact Unary.undo_exit (R.cell R.last) b (R.clauseIndex S j) r R.last_last
  | read_left p z hp r b =>
    apply R.step_adjacent S hs ht z p hp (Or.inr rfl) (Or.inl rfl)
    have hz : z.val < p.val := by omega
    simpa [realizeCell,position,phase,clause,controlPosition,controlPhase,HeadTour.atClause,
      hz,not_lt_of_gt hz,plan,R.task_eq] using
      Binary.read_left (R.cell z) (R.cell p) b (R.clauseIndex S j) r (R.adjacent_pair z p hp)
  | read_right p z hp r b =>
    apply R.step_adjacent S hs ht p z hp (Or.inl rfl) (Or.inr rfl)
    have hz : p.val < z.val := by omega
    simpa [realizeCell,position,phase,clause,controlPosition,controlPhase,HeadTour.atClause,
      hz,not_lt_of_gt hz] using
      Binary.read_right (R.cell p) (R.cell z) b (R.clauseIndex S j) r (R.adjacent_pair p z hp)
  | undo_left p z hp r b =>
    apply R.step_adjacent S hs ht z p hp (Or.inr rfl) (Or.inl rfl)
    have hz : z.val < p.val := by omega
    simpa [realizeCell,position,phase,clause,controlPosition,controlPhase,HeadTour.atClause,
      hz,not_lt_of_gt hz] using
      Binary.undo_left (R.cell z) (R.cell p) b (R.clauseIndex S j) r (R.adjacent_pair z p hp)
  | undo_right p z hp r b =>
    apply R.step_adjacent S hs ht p z hp (Or.inl rfl) (Or.inr rfl)
    have hz : p.val < z.val := by omega
    simpa [realizeCell,position,phase,clause,controlPosition,controlPhase,HeadTour.atClause,
      hz,not_lt_of_gt hz,plan,R.task_eq] using
      Binary.undo_right (R.cell p) (R.cell z) b (R.clauseIndex S j) r (R.adjacent_pair p z hp)

lemma edge_realize_step {s t : HeadTour.FullState (S.count R.task).val R.size}
    (he : (R.plan S).Edge s t) (hs : R.SideOK S s) :
    Step S d (R.realize S s) (R.realize S t) := by
  have ht := (R.edge_side S he).mp hs
  cases he with
  | tour j h => exact R.tour_realize_step S j h hs
  | next i j hij b =>
    apply R.step_unary S hs ht rfl
    exact Unary.next (R.cell R.last) b (R.clauseIndex S i) (R.clauseIndex S j) hij R.last_last
  | done b =>
    apply R.step_unary S hs ht rfl
    apply Unary.success _ _ _ _ R.last_last
    change (R.clauseIndex S (R.plan S).last).val+1=(S.count (R.cell R.last).metadata.task).val
    rw [R.task_eq]
    have hc := S.positive R.task
    dsimp [clauseIndex,HeadTour.Plan.last]
    omega
  | flip b hz =>
    apply R.step_unary S hs ht rfl
    apply Unary.pivot _ _ R.last_last
    have he : (R.cell R.last).metadata.zeroTask=R.task.zeroTask := congrArg Task.zeroTask (R.task_eq R.last)
    rw [he]
    exact hz

lemma realize_reach {s t : HeadTour.FullState (S.count R.task).val R.size}
    (h : (R.plan S).Reach s t) (hs : R.SideOK S s) :
    Reach S d (R.realize S s) (R.realize S t) := by
  induction h with
  | refl => exact .refl
  | tail h e ih =>
    have hm := R.reach_side S h hs
    apply ih.tail
    rcases e with e | e
    · exact R.edge_realize_step S e hm
    · exact step_symm (R.edge_realize_step S e ((R.edge_side S e).mpr hm))

theorem literal_rollback (s : HeadTour.FullState (S.count R.task).val R.size)
    (hs : R.SideOK S s) :
    Reach S d (R.realize S s)
      (R.realize S (HeadTour.atClause (R.plan S).first ⟨.acquisition,0,s.side⟩)) ∨
    ∃ w p a z, Reach S d (R.realize S s) w ∧ w=p++[a]++z ∧ Zero S d [a] := by
  rcases (R.plan S).rollback s with h | ⟨t,h,hz⟩
  · exact Or.inl (R.realize_reach S h hs)
  · right
    refine ⟨R.realize S t,(R.realize S t).take (R.position S t).val,
      R.realizeCell S t (R.position S t),(R.realize S t).drop ((R.position S t).val+1),
      R.realize_reach S h hs,ofFn_split_one _ _,?_⟩
    exact Or.inl ⟨_,rfl,Or.inr (Or.inl (R.realize_semanticZero S t (Or.inl hz)))⟩

end Region

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_WordComponents
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideEndpoint _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q N : ℕ} [NeZero q]

lemma Unary.shape {S : Schedule q} {a b : Cell q} (hu : Unary S a b) :
    a.shape=b.shape := by
  cases hu <;> rfl

lemma replacement_shape {S : Schedule q} {d : ℕ} {v w : List (Cell q)}
    (hr : Replacement S d v w) : v.map Cell.shape=w.map Cell.shape := by
  rcases hr.2 with ⟨a,b,rfl,rfl,h⟩ | ⟨a,b,a',b',rfl,rfl,h⟩
  · rcases h with h | h
    · simpa using h.shape
    · simpa using h.shape.symm
  · rcases h with h | h
    · simp only [List.map_cons,List.map_nil,h.shape.1,h.shape.2]
    · simp only [List.map_cons,List.map_nil,←h.shape.1,←h.shape.2]

lemma step_shape {S : Schedule q} {d : ℕ} {v w : List (Cell q)}
    (hr : Step S d v w) : v.map Cell.shape=w.map Cell.shape := by
  obtain ⟨p,s,v,w,rfl,rfl,hr⟩ := hr
  simp only [List.map_append,replacement_shape hr]

lemma reach_shape {S : Schedule q} {d : ℕ} {v w : List (Cell q)}
    (hr : Reach S d v w) : v.map Cell.shape=w.map Cell.shape := by
  induction hr with
  | refl => rfl
  | tail hr he ih => exact ih.trans (step_shape he)

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_UniversalInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.UniversalInput
open StackMachine UniversalStack
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K]

variable (src dst : K) (hne : src≠dst)
include hne

lemma parse_packet_first (p : Packet K) (u todo : List Bool)
    (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    exec (machine src dst) (config src dst first u (packetWord p++todo) f b pc)
      (width K)=config src dst (packetState p) u todo f b pc := by
  simpa only [first,Nat.sub_zero,List.drop_zero] using
    parse_packet src dst hne p ⟨0,width_pos⟩ (fun _ => false) (by intro j hj;change j.val < 0 at hj;omega) u todo f b pc

lemma parse_code (P : List (UniversalStack.Token K)) (u todo : List Bool)
    (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    exec (machine src dst) (config src dst first u (binaryCode P++todo) f b pc)
      ((width K+1)*P.length+width K)=
      config src dst (.universal .reset) u todo f (b++P) pc := by
  induction P generalizing b with
  | nil => simpa only [binaryCode,List.map_nil,List.nil_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.length_nil,Nat.mul_zero,Nat.zero_add,packetState] using
      parse_packet_first src dst hne none u todo f b pc
  | cons a P ih =>
    have hc : binaryCode (a::P)=packetWord (some a)++binaryCode P := by
      simp [binaryCode]
    rw [hc,List.append_assoc,List.length_cons,
      show (width K+1)*(P.length+1)+width K=
        width K+(1+((width K+1)*P.length+width K)) by ring,
      exec_from,parse_packet_first src dst hne]
    change exec (machine src dst) (config src dst (.emit a) u (binaryCode P++todo) f b pc) _=_
    rw [exec_from,exec_one,emit_token src dst,ih]
    simp

end
end SourceBurnside.UniversalInput

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_Compilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.RawHeader
open Structured Structured.Program Structured.Binary
lemma program_run (h l : ℕ) (z : Bool) (data : List Bool) :
    Run program (store (request h l z data) [] [] [])
      (7*(InitialFormula.binSize h+InitialFormula.binSize l)+14)
      (store data (InitialFormula.bin h) (InitialFormula.bin l) [z]) := by
  have h1 := height_run (InitialFormula.bin h) (InitialFormula.enc l++z::data) [] []
  have h2 := arity_run (InitialFormula.bin l) (z::data) (InitialFormula.bin h) []
  have h3 := task_run z data (InitialFormula.bin h) (InitialFormula.bin l)
  have hh (n : ℕ) : UniversalInput.header (InitialFormula.bin n)=InitialFormula.enc n := by simp [UniversalInput.header,InitialFormula.enc]
  simp only [hh,InitialFormula.bin_length] at h1 h2
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 h3)
  convert H using 1 <;> first | rfl | simp [request,List.append_assoc] | omega
end SourceBurnside.RawHeader

namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type*} [DecidableEq K]

def inflate (src dst : K) (n : ℕ) : Program K := .loop src (fun _ => pushes dst n)
lemma inflate_run (src dst : K) (hne : src≠dst) (n : ℕ) (r : Store K) :
    Run (inflate src dst n) r ((n+2)*(r src).length+1)
      (Function.update (Function.update r src []) dst (r dst++List.replicate (n*(r src).length) false)) := by
  generalize hv : r src=v
  induction v using List.reverseRecOn generalizing r with
  | nil =>
    have he : Function.update (Function.update r src []) dst (r dst++List.replicate (n*0) false)=r := by
      simp [←hv]
    rw [List.length_nil,he]
    simpa [inflate] using Run.loop_nil r src (fun _ => pushes dst n) hv
  | append_singleton v b ih =>
    let s := Function.update r src v
    let t := Function.update s dst (s dst++List.replicate n false)
    have ht : t src=v := by simp [t,s,hne]
    have hh := ih t ht
    have H := Run.loop_cons r src (fun _ => pushes dst n) v b t _ (n+1) ((n+2)*v.length+1) hv
      (pushes_run dst n s) hh
    have he : Function.update (Function.update t src []) dst (t dst++List.replicate (n*v.length) false)=
        Function.update (Function.update r src []) dst (r dst++List.replicate (n*(v++[b]).length) false) := by
      funext k
      by_cases hd : k=dst
      · subst k
        simp [t,s,Ne.symm hne,List.append_assoc,Nat.mul_add,Nat.add_comm]
      · by_cases hs : k=src
        · subst k;simp [hd]
        · simp [t,s,hd,hs]
    rw [he] at H
    convert H using 1 <;> first | rfl | simp [List.length_append,Nat.mul_add];omega
end SourceBurnside.Structured.Binary

namespace SourceBurnside.DropPadding
open Structured Structured.Program Structured.Binary
def program : Program K := .loop 0 (fun _ => step)
lemma program_run (xs : List Bool) (n : ℕ) :
    Run program (store xs (xs.length+n)) (3*xs.length+1) (store [] n) := by
  induction xs using List.reverseRecOn with
  | nil => simpa [program] using Run.loop_nil (store [] n) (0:K) (fun _ => step) rfl
  | append_singleton xs b ih =>
    have he0 : Function.update (store (xs++[b]) ((xs++[b]).length+n)) 0 xs=store xs (xs.length+n+1) := by
      funext i;fin_cases i <;> simp [store,Nat.add_assoc,Nat.add_comm]
    have he1 : Function.update (store xs (xs.length+n+1)) 1 (List.replicate (xs.length+n) false)=store xs (xs.length+n) := by
      funext i;fin_cases i <;> simp [store]
    have hs : store xs (xs.length+n+1) 1=List.replicate (xs.length+n) false++[false] := by
      change List.replicate ((xs.length+n)+1) false=_
      rw [List.replicate_add];rfl
    have hb : Run step (store xs (xs.length+n+1)) 2 (store xs (xs.length+n)) := by
      refine Run.pop _ _ _ 1 _ ?_
      simp only [hs,List.dropLast_concat,he1]
      exact Run.skip _
    have H := Run.loop_cons (store (xs++[b]) ((xs++[b]).length+n)) (0:K) (fun _ => step) xs b
      (store xs (xs.length+n)) (store [] n) 2 (3*xs.length+1) rfl (by rw [he0];exact hb) ih
    convert H using 1 <;> first | rfl | simp;omega
end SourceBurnside.DropPadding

namespace SourceBurnside.PadRegister
open Structured Structured.Program Structured.Binary
def program : Program K := .seq (copy 1 2 3) (.seq (copy 0 4 3)
  (.seq (DropPadding.program.relabel dropSlots) (copy 0 2 3)))
lemma program_run (xs : List Bool) (n : ℕ) (hn : xs.length≤n) :
    Run program (store xs n [] []) (5*n+13*xs.length+7)
      (store xs n (List.replicate (n-xs.length) false++xs) []) := by
  have h1 := copy_run (1:K) 2 3 (by decide) (by decide) (by decide) (store xs n [] []) (by rfl)
  have he1 : Function.update (store xs n [] []) 2 ((store xs n [] [] 2)++(store xs n [] [] 1))=
      store xs n (List.replicate n false) [] := by
    funext i;fin_cases i <;> simp [store]
  rw [he1] at h1
  have hl1 : (store xs n [] [] 1).length=n := by simp [store]
  rw [hl1] at h1
  have h2 := copy_run (0:K) 4 3 (by decide) (by decide) (by decide) (store xs n (List.replicate n false) []) (by rfl)
  have he2 : Function.update (store xs n (List.replicate n false) []) 4
      ((store xs n (List.replicate n false) [] 4)++(store xs n (List.replicate n false) [] 0))=
      store xs n (List.replicate n false) xs := by
    funext i;fin_cases i <;> simp [store]
  rw [he2] at h2
  have h3 : Run (DropPadding.program.relabel dropSlots) (store xs n (List.replicate n false) xs)
      (3*xs.length+1) (store xs n (List.replicate (n-xs.length) false) []) := by
    refine (DropPadding.program_run xs (n-xs.length)).relabel_to dropSlots dropSlots_injective _ _ ?_ ?_ ?_
    · intro i;fin_cases i
      · rfl
      · simp [DropPadding.store,dropSlots,store,Nat.add_sub_of_le hn]
    · intro i;fin_cases i <;> rfl
    · intro i hi;fin_cases i
      · rfl
      · rfl
      · exact False.elim (hi 1 rfl)
      · rfl
      · exact False.elim (hi 0 rfl)
  have h4 := copy_run (0:K) 2 3 (by decide) (by decide) (by decide)
    (store xs n (List.replicate (n-xs.length) false) []) (by rfl)
  have he4 : Function.update (store xs n (List.replicate (n-xs.length) false) []) 2
      ((store xs n (List.replicate (n-xs.length) false) [] 2)++(store xs n (List.replicate (n-xs.length) false) [] 0))=
      store xs n (List.replicate (n-xs.length) false++xs) [] := by
    funext i;fin_cases i <;> simp [store]
  rw [he4] at h4
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 (Run.seq _ _ _ _ _ _ _ h3 h4))
  convert H using 1 <;> first | rfl | simp only [store,Matrix.cons_val_zero];omega
end SourceBurnside.PadRegister

namespace SourceBurnside.WrappedInput
open StackMachine UniversalStack
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K]

variable (src dst : K) (hne : src≠dst)
include hne

theorem specialize_trace (t v x : List Bool) :
    exec (machine src dst) (config src dst .header [] (envelope (specialize t v) x) [] [] 0)
      (4*InitialFormula.binSize (specialize t v).length+3)=
      config src dst .header [] (envelope t (InitialFormula.enc v.length++v++x)) [] [] 0 := by
  rw [show 4*InitialFormula.binSize (specialize t v).length+3=
    (4*(InitialFormula.bin (specialize t v).length).length+2)+1 by rw [InitialFormula.bin_length],
    exec_from]
  unfold envelope
  rw [enc_header,List.append_assoc,header_all src dst hne,exec_one]
  simp only [specialize,List.cons_append]
  rw [marker_true src dst hne]
  simp only [List.append_assoc]

lemma plain_trace (P : List (UniversalStack.Token K)) (x : List Bool) :
    exec (machine src dst) (config src dst .header [] (envelope (plain P) x) [] [] 0)
      ((4*InitialFormula.binSize (plain P).length+3)+((UniversalInput.width K+1)*P.length+
        UniversalInput.width K)+(2*P.length+1))=
      config src dst (.inner (.universal .pick)) [] x P [] 0 := by
  rw [exec_from (machine src dst) _ _ (2*P.length+1),
    exec_from (machine src dst) _ _ ((UniversalInput.width K+1)*P.length+UniversalInput.width K),
    show 4*InitialFormula.binSize (plain P).length+3=(4*(InitialFormula.bin (plain P).length).length+2)+1 by
      rw [InitialFormula.bin_length],
    exec_from (machine src dst) _ (4*(InitialFormula.bin (plain P).length).length+2) 1]
  unfold envelope
  rw [enc_header,List.append_assoc,header_all src dst hne,exec_one]
  simp only [plain,List.cons_append]
  rw [marker_false src dst hne]
  change exec (machine src dst) (exec (machine src dst)
    (liftConfig (UniversalInput.config src dst UniversalInput.first [] (UniversalInput.binaryCode P++x) [] [] 0)) _) _=_
  rw [lift_exec,UniversalInput.parse_code src dst hne,List.nil_append,lift_exec,
    UniversalInput.reset_code src dst]
  rfl

theorem raw_specialize_trace (t v x : List Bool) :
    exec (machine src dst) (config src dst .reverse (envelope (specialize t v) x) [] [] [] 0)
      ((2*(envelope (specialize t v) x).length+1)+(4*InitialFormula.binSize (specialize t v).length+3))=
      config src dst .header [] (envelope t (InitialFormula.enc v.length++v++x)) [] [] 0 := by
  rw [exec_from,reverse_all src dst hne,List.append_nil,specialize_trace src dst hne]

end
end SourceBurnside.WrappedInput

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_InputEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.TwoInputQuote
open Structured Structured.Program Structured.Binary
lemma quote_run (v todo : List Bool) :
    Run quote (store todo (InitialFormula.bin v.length) v 0 [])
      (14*v.length+28*InitialFormula.binSize v.length+21)
      (store todo (InitialFormula.bin v.length) v 0 (WrappedInput.specialize v v).reverse) := by
  have H := Run.seq _ _ _ _ _ _ _ (qstage_run v (InitialFormula.bin v.length) [] todo)
    (Run.seq _ _ _ _ _ _ _ (qstage_run v (InitialFormula.bin v.length)
      ([]++(UniversalInput.header (InitialFormula.bin v.length)++v).reverse) todo)
      (qpush_run v (InitialFormula.bin v.length)
        (([]++(UniversalInput.header (InitialFormula.bin v.length)++v).reverse)++
          (UniversalInput.header (InitialFormula.bin v.length)++v).reverse) todo true))
  convert H using 1 <;> first | rfl | simp only [InitialFormula.bin_length];omega |
    simp only [WrappedInput.specialize,List.reverse_cons,List.reverse_append,List.append_assoc,
      List.nil_append,WrappedInput.enc_header]

theorem program_run (v todo : List Bool) :
    ∃t,t≤(7*v.length+47)*InitialFormula.binSize v.length+17*v.length+32 ∧
      Run program (store (InitialFormula.enc v.length++v++todo) [] [] 0 []) t
        (store todo (InitialFormula.bin v.length) v 0 (WrappedInput.specialize v v).reverse) := by
  obtain ⟨t,ht,h3⟩ := makeUnary_run v.length (v++todo)
  have h1 := readHeader_run v.length (v++todo)
  have h2 := reverseBin_run (InitialFormula.bin v.length) (v++todo)
  rw [InitialFormula.bin_length] at h2
  have h4 := takeCode_run v todo (InitialFormula.bin v.length)
  have h5 := quote_run v todo
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2
    (Run.seq _ _ _ _ _ _ _ h3 (Run.seq _ _ _ _ _ _ _ h4 h5)))
  refine ⟨(7*InitialFormula.binSize v.length+6)+((7*InitialFormula.binSize v.length+3)+
    (t+((3*v.length+1)+(14*v.length+28*InitialFormula.binSize v.length+21)))),?_,?_⟩
  · nlinarith [ht]
  · simpa only [program,List.append_assoc] using H
end SourceBurnside.TwoInputQuote

namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type*} [DecidableEq K]
def copyInflate (src dst tmp aux : K) (c : ℕ) : Program K :=
  .seq (copy src tmp aux) (inflate tmp dst c)
lemma copyInflate_run (src dst tmp aux : K) (c : ℕ)
    (hst : src≠tmp) (hsa : src≠aux) (hta : tmp≠aux) (htd : tmp≠dst)
    (r : Store K) (ht : r tmp=[]) (ha : r aux=[]) :
    Run (copyInflate src dst tmp aux c) r ((c+7)*(r src).length+3)
      (Function.update r dst (r dst++List.replicate (c*(r src).length) false)) := by
  have h1 := copy_run src tmp aux hst hsa hta r ha
  simp only [ht,List.nil_append] at h1
  have h2 := inflate_run tmp dst htd c (Function.update r tmp (r src))
  have he : Function.update (Function.update (Function.update r tmp (r src)) tmp []) dst
      ((Function.update r tmp (r src)) dst++List.replicate (c*((Function.update r tmp (r src)) tmp).length) false)=
      Function.update r dst (r dst++List.replicate (c*(r src).length) false) := by
    funext i
    by_cases hd : i=dst
    · subst i;simp [Ne.symm htd]
    · by_cases hj : i=tmp
      · subst i;simp [htd,ht]
      · simp [hd,hj]
  rw [he] at h2
  simp only [Function.update_self] at h2
  have H := Run.seq _ _ _ _ _ _ _ h1 h2
  convert H using 1 <;> first | rfl | ring
end SourceBurnside.Structured.Binary

namespace SourceBurnside.RawPadSeed
open Structured Structured.Program Structured.Binary
def step {r : ℕ} (i : Fin r) (c : ℕ) : Program (K r) :=
  copyInflate (.inl i) (.inr 0) (.inr 1) (.inr 2) c
lemma step_run {r : ℕ} (i : Fin r) (c : ℕ) (v : Fin r → List Bool) (n : ℕ) :
    Run (step i c) (store v n) ((c+7)*(v i).length+3) (store v (n+c*(v i).length)) := by
  have H := copyInflate_run (.inl i : K r) (.inr 0) (.inr 1) (.inr 2) c
    (by simp) (by simp) (by simp) (by simp) (store v n) rfl rfl
  convert H using 1 <;> try rfl
  funext j
  cases j with
  | inl j => simp [store]
  | inr j => fin_cases j <;> simp [store]
def steps {r : ℕ} : List (Fin r × ℕ) → Program (K r)
  | [] => .skip
  | (i,c)::rest => .seq (step i c) (steps rest)
def added {r : ℕ} (v : Fin r → List Bool) : List (Fin r × ℕ) → ℕ
  | [] => 0
  | (i,c)::rest => c*(v i).length+added v rest
def time {r : ℕ} (v : Fin r → List Bool) : List (Fin r × ℕ) → ℕ
  | [] => 1
  | (i,c)::rest => (c+7)*(v i).length+3+time v rest
lemma steps_run {r : ℕ} (items : List (Fin r × ℕ)) (v : Fin r → List Bool) (n : ℕ) :
    Run (steps items) (store v n) (time v items) (store v (n+added v items)) := by
  induction items generalizing n with
  | nil => simpa [steps,time,added] using Run.skip (store v n)
  | cons ic rest ih =>
    rcases ic with ⟨i,c⟩
    have H := Run.seq _ _ _ _ _ _ _ (step_run i c v n) (ih (n+c*(v i).length))
    simpa only [steps,time,added,Nat.add_assoc] using H

def program {r : ℕ} (items : List (Fin r × ℕ)) (offset : ℕ) : Program (K r) :=
  .seq (pushes (.inr 0) offset) (steps items)
lemma program_run {r : ℕ} (items : List (Fin r × ℕ)) (offset : ℕ) (v : Fin r → List Bool) :
    Run (program items offset) (store v 0) (offset+1+time v items)
      (store v (offset+added v items)) := by
  have H := pushes_run (.inr 0 : K r) offset (store v 0)
  have he : Function.update (store v 0) (.inr 0) (store v 0 (.inr 0)++List.replicate offset false)=store v offset := by
    funext i
    cases i with
    | inl i => simp [store]
    | inr i => fin_cases i <;> simp [store]
  rw [he] at H
  exact Run.seq _ _ _ _ _ _ _ H (steps_run items v offset)
end SourceBurnside.RawPadSeed

namespace SourceBurnside.PackFamily
open Structured Structured.Program
def step {r : ℕ} (i : Fin r) : Program (K r) := PadRegister.program.relabel (slots i)
lemma step_run {r : ℕ} (i : Fin r) (v out : Fin r → List Bool) (n : ℕ)
    (hlen : (v i).length≤n) (he : out i=[]) :
    Run (step i) (store v out n) (5*n+13*(v i).length+7)
      (store v (Function.update out i (pad (v i) n)) n) := by
  refine (PadRegister.program_run (v i) n hlen).relabel_to (slots i) (slots_injective i) _ _ ?_ ?_ ?_
  · intro j;fin_cases j <;> simp [slots,store,PadRegister.store,he]
  · intro j;fin_cases j <;> simp [slots,store,PadRegister.store,pad]
  · intro j hj
    cases j with
    | inl j =>
      cases j with
      | inl k => rfl
      | inr k =>
        have hk : k≠i := by intro h;subst k;exact hj 2 rfl
        simp [store,hk]
    | inr j => fin_cases j <;> rfl
def program {r : ℕ} : List (Fin r) → Program (K r)
  | [] => .skip
  | i::rest => .seq (step i) (program rest)
def time {r : ℕ} (v : Fin r → List Bool) (n : ℕ) : List (Fin r) → ℕ
  | [] => 1
  | i::rest => (5*n+13*(v i).length+7)+time v n rest
lemma program_run {r : ℕ} (items : List (Fin r)) (hd : items.Nodup)
    (v out : Fin r → List Bool) (n : ℕ) (hlen : ∀i∈items,(v i).length≤n)
    (he : ∀i∈items,out i=[]) :
    Run (program items) (store v out n) (time v n items) (store v (outputs v out n items) n) := by
  induction items generalizing out with
  | nil =>
    have h0 : outputs v out n []=out := by funext i;simp only [outputs,List.not_mem_nil,↓reduceIte]
    rw [h0]
    exact Run.skip _
  | cons i rest ih =>
    have hdi := List.nodup_cons.mp hd
    let next := Function.update out i (pad (v i) n)
    have hrest := ih hdi.2 next (by intro k hk;exact hlen k (by simp [hk])) (by
      intro k hk
      have hki : k≠i := by intro h;subst k;exact hdi.1 hk
      simp [next,hki,he k (by simp [hk])])
    have heq : outputs v next n rest=outputs v out n (i::rest) := by
      funext k
      by_cases hk : k=i
      · subst k;simp [outputs,next,hdi.1]
      · simp [outputs,next,hk]
    rw [heq] at hrest
    exact Run.seq _ _ _ _ _ _ _ (step_run i v out n (hlen i (by simp)) (he i (by simp))) hrest

theorem all_run {r : ℕ} (v : Fin r → List Bool) (n : ℕ) (hlen : ∀i,(v i).length≤n) :
    Run (program (List.finRange r)) (store v (fun _ => []) n)
      (time v n (List.finRange r)) (store v (fun i => pad (v i) n) n) := by
  have H := program_run (List.finRange r) (List.nodup_finRange r) v (fun _ => []) n
    (by intro i _;exact hlen i) (by simp)
  have he : outputs v (fun _ => []) n (List.finRange r)=(fun i => pad (v i) n) := by
    funext i;simp only [outputs,List.mem_finRange,↓reduceIte]
  rwa [he] at H
lemma time_le {r : ℕ} (items : List (Fin r)) (v : Fin r → List Bool) (n : ℕ)
    (hlen : ∀i∈items,(v i).length≤n) : time v n items≤ items.length*(18*n+7)+1 := by
  induction items with
  | nil => simp [time]
  | cons i rest ih =>
    have h0 := hlen i (by simp)
    have h1 := ih (by intro j hj;exact hlen j (by simp [hj]))
    simp only [time,List.length_cons]
    nlinarith
end SourceBurnside.PackFamily

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_ProgramAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.RawNumberPrep
open Structured Structured.Program Structured.Binary
lemma header_run (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) :
    Run readHeader (store (before code (RawHeader.request h l z data)) 0 [] [])
      (7*(InitialFormula.binSize h+InitialFormula.binSize l)+14)
      (store (parsed code h l z data) 0 [] []) := by
  refine (RawHeader.program_run h l z data).relabel_to headerSlots headerSlots_injective _ _ ?_ ?_ ?_
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i hi
    cases i with
    | inl i =>
      fin_cases i
      · rfl
      · exact False.elim (hi 2 rfl)
      · exact False.elim (hi 4 rfl)
      · exact False.elim (hi 5 rfl)
      · exact False.elim (hi 0 rfl)
      · rfl
    | inr i => fin_cases i <;> rfl
def seed (W D : ℕ) : Program K :=
  (RawPadSeed.program (items W D) (offset W D)).relabel seedSlots
lemma seed_run (W D : ℕ) (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) :
    Run (seed W D) (store (raw code h l z data) 0 [] [])
      (offset W D+1+RawPadSeed.time (raw code h l z data) (items W D))
      (store (raw code h l z data) (width W D h code data (InitialFormula.bin l)) [] []) := by
  have hn : offset W D+RawPadSeed.added (raw code h l z data) (items W D)=
      width W D h code data (InitialFormula.bin l) := by
    simp only [offset,items,RawPadSeed.added,raw,Matrix.cons_val_zero,
      List.length_reverse,width,RawLocalBody.limit]
    dsimp
    simp only [List.length_reverse,List.length_replicate]
    ring
  have H := RawPadSeed.program_run (items W D) (offset W D) (raw code h l z data)
  rw [hn] at H
  refine H.relabel_to seedSlots seedSlots_injective _ _ ?_ ?_ ?_
  · intro i;cases i with
    | inl i => rfl
    | inr i => fin_cases i <;> rfl
  · intro i;cases i with
    | inl i => rfl
    | inr i => fin_cases i <;> rfl
  · intro i hi;cases i with
    | inl i => rfl
    | inr i =>
      fin_cases i
      all_goals first | rfl | exact False.elim (hi (.inr 0) rfl)

def program (W D : ℕ) : Program K :=
  .seq readHeader (.seq makeUnary (.seq (seed W D) (.seq (count false) (count true))))

theorem program_run (W D : ℕ) (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) :
    let v := raw code h l z data
    let n := width W D h code data (InitialFormula.bin l)
    ∃t,t≤7*(InitialFormula.binSize h+InitialFormula.binSize l)+14+
        ((7*h+12)*InitialFormula.binSize h+4)+
        (offset W D+1+RawPadSeed.time v (items W D))+
        ((13*n+13)*(code.length+data.length)+24*n+16) ∧
      Run (program W D) (store (before code (RawHeader.request h l z data)) 0 [] []) t
        (store v n (CountLength.countBits code.reverse n) (CountLength.countBits data.reverse n)) := by
  dsimp only
  let v := raw code h l z data
  let n := width W D h code data (InitialFormula.bin l)
  obtain ⟨tu,hu,Hu⟩ := unary_run code h l z data
  obtain ⟨tc,hc,Hc⟩ := count_run false v n []
  obtain ⟨td,hd,Hd⟩ := count_run true v n (CountLength.countBits (v 0) n)
  simp only [Bool.false_eq_true,ite_false,ite_true] at hc hd Hc Hd
  have hc0 : (v 0).length=code.length := by simp [v,raw]
  have hd0 : (v 4).length=data.length := by simp [v,raw]
  rw [hc0] at hc
  rw [hd0] at hd
  have H := Run.seq _ _ _ _ _ _ _ (header_run code h l z data)
    (Run.seq _ _ _ _ _ _ _ Hu (Run.seq _ _ _ _ _ _ _ (seed_run W D code h l z data)
      (Run.seq _ _ _ _ _ _ _ Hc Hd)))
  refine ⟨(7*(InitialFormula.binSize h+InitialFormula.binSize l)+14)+
    (tu+((offset W D+1+RawPadSeed.time v (items W D))+(tc+td))),?_,?_⟩
  · nlinarith
  · exact H
end SourceBurnside.RawNumberPrep

namespace SourceBurnside.RawPreparedInputs
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
open FiniteTable.Codec
lemma bound_limits (D h l : ℕ) (code data : List Bool) :
    h+1≤bound D h code data l+1 ∧ code.length≤bound D h code data l+1 ∧
    data.length≤bound D h code data l+1 ∧ InitialFormula.binSize l≤bound D h code data l+1 := by
  unfold bound RawLocalBody.limit
  constructor
  · nlinarith
  · omega
lemma semantic_bounded (D h l : ℕ) (code : List Bool) (z : Bool) (data : List Bool) :
    ∀i,semantic code h l z data i<2^(bound D h code data l+1) := by
  have hb := bound_limits D h l code data
  have hlt : l<2^(InitialFormula.binSize l) := by
    have H := Add.value_lt (InitialFormula.bin l).reverse
    simpa only [InitialFormula.bin_value,List.length_reverse,InitialFormula.bin_length] using H
  have hp : 1<2^(bound D h code data l+1) := Nat.one_lt_two_pow (by omega : bound D h code data l+1≠0)
  intro i;fin_cases i
  · exact (binaryValue_lt code).trans_le (Nat.pow_le_pow_right (by omega) hb.2.1)
  · exact hb.2.1.trans_lt Nat.lt_two_pow_self
  · exact (by omega : h<bound D h code data l+1).trans Nat.lt_two_pow_self
  · exact hlt.trans_le (Nat.pow_le_pow_right (by omega) hb.2.2.2)
  · change CellRepr.boolean z<_;cases z <;> simp only [CellRepr.boolean,Bool.false_eq_true,ite_false,ite_true] <;> omega
  · exact (binaryValue_lt data).trans_le (Nat.pow_le_pow_right (by omega) hb.2.2.1)
  · exact hb.2.2.1.trans_lt Nat.lt_two_pow_self
lemma inputs_lengths (D h l n : ℕ) (code : List Bool) (z : Bool) (data : List Bool)
    (hn : bound D h code data l+1≤n) : ∀i,(inputs n code h l z data i).length≤n := by
  have hb := bound_limits D h l code data
  intro i;fin_cases i
  · simpa [inputs] using hb.2.1.trans hn
  · simp [inputs,CountLength.countBits_length]
  · change (InitialFormula.bin h).length≤n
    rw [InitialFormula.bin_length]
    exact (InitialFormula.binSize_le_self h).trans (hb.1.trans hn)
  · simpa [inputs,InitialFormula.bin_length] using hb.2.2.2.trans hn
  · simp [inputs];omega
  · simpa [inputs] using hb.2.2.1.trans hn
  · simp [inputs,CountLength.countBits_length]
lemma inputs_values (D h l n : ℕ) (code : List Bool) (z : Bool) (data : List Bool)
    (hn : bound D h code data l+1≤n) : values (inputs n code h l z data)=semantic code h l z data := by
  have hb := bound_limits D h l code data
  have hc : code.reverse.length<2^n := by
    simpa only [List.length_reverse] using (hb.2.1.trans hn).trans_lt Nat.lt_two_pow_self
  have hd : data.reverse.length<2^n := by
    simpa only [List.length_reverse] using (hb.2.2.1.trans hn).trans_lt Nat.lt_two_pow_self
  funext i;fin_cases i
  · simpa [inputs,values,semantic,List.reverse_reverse] using (binaryValue_eq code).symm
  · simpa [inputs,values,semantic] using CountLength.countBits_value code.reverse n hc
  · simpa [inputs,values,semantic] using InitialFormula.bin_value h
  · simpa [inputs,values,semantic] using InitialFormula.bin_value l
  · cases z <;> rfl
  · simpa [inputs,values,semantic,List.reverse_reverse] using (binaryValue_eq data).symm
  · simpa [inputs,values,semantic] using CountLength.countBits_value data.reverse n hd
lemma packed_lengths (D h l n : ℕ) (code : List Bool) (z : Bool) (data : List Bool)
    (hn : bound D h code data l+1≤n) : ∀i,(packed n code h l z data i).length=n := by
  intro i;exact PadRegister.result_length _ n (inputs_lengths D h l n code z data hn i)
lemma packed_values (D h l n : ℕ) (code : List Bool) (z : Bool) (data : List Bool)
    (hn : bound D h code data l+1≤n) : values (packed n code h l z data)=semantic code h l z data := by
  rw [←inputs_values D h l n code z data hn]
  funext i;exact PadRegister.result_value _ _
end SourceBurnside.RawPreparedInputs

namespace SourceBurnside.RawAssembler
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
def pack : Program K := (PackFamily.program (List.finRange 7)).relabel packSlots
lemma pack_run (D h l n : ℕ) (code : List Bool) (z : Bool) (data : List Bool)
    (hn : RawPreparedInputs.bound D h code data l+1≤n) :
    let r := RawNumberPrep.store (RawNumberPrep.raw code h l z data) n
      (CountLength.countBits code.reverse n) (CountLength.countBits data.reverse n)
    Run pack (store r (fun _ => []))
      (PackFamily.time (RawPreparedInputs.inputs n code h l z data) n (List.finRange 7))
      (store r (RawPreparedInputs.packed n code h l z data)) := by
  dsimp only
  have H := PackFamily.all_run (RawPreparedInputs.inputs n code h l z data) n
    (RawPreparedInputs.inputs_lengths D h l n code z data hn)
  refine H.relabel_to packSlots packSlots_injective _ _ ?_ ?_ ?_
  · intro j;cases j with
    | inl j => cases j with
      | inl i => exact RawPreparedInputs.agrees_inputs n code h l z data i
      | inr i => rfl
    | inr i => fin_cases i <;> rfl
  · intro j;cases j with
    | inl j => cases j with
      | inl i => exact RawPreparedInputs.agrees_inputs n code h l z data i
      | inr i => rfl
    | inr i => fin_cases i <;> rfl
  · intro j hj;cases j with
    | inl j => rfl
    | inr j => exact False.elim (hj (.inl (.inr j)) rfl)
def program (W D : ℕ) : Program K := .seq ((RawNumberPrep.program W D).relabel Sum.inl) pack
lemma time_bound (W D h l : ℕ) (code data : List Bool) :
    let v := RawNumberPrep.raw code h l false data
    let Q := h+code.length+data.length+InitialFormula.binSize l+1
    RawNumberPrep.offset W D+1+RawPadSeed.time v (RawNumberPrep.items W D) ≤
      (W*(10000*(D+20)+33)+100)*(Q+1) := by
  dsimp
  simp only [RawNumberPrep.offset,RawPadSeed.time,RawNumberPrep.items,RawNumberPrep.raw]
  dsimp
  simp only [List.length_reverse,List.length_replicate,InitialFormula.bin_length]
  let C := W*(10000*(D+20)+33)+100
  have h0 : W*(10000*(D+20))+7≤C := by dsimp [C];nlinarith
  have h1 : W+7≤C := by dsimp [C];nlinarith
  have h2 := Nat.mul_le_mul_right h h0
  have h3 := Nat.mul_le_mul_right code.length h1
  have h4 := Nat.mul_le_mul_right data.length h1
  have h5 := Nat.mul_le_mul_right (InitialFormula.binSize l) h1
  change _ ≤ C*(h+code.length+data.length+InitialFormula.binSize l+1+1)
  dsimp [C] at h2 h3 h4 h5 ⊢
  nlinarith

theorem program_run (W D : ℕ) (hW : 0<W) (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) :
    let n := RawNumberPrep.width W D h code data (InitialFormula.bin l)
    let r := RawNumberPrep.store (RawNumberPrep.raw code h l z data) n
      (CountLength.countBits code.reverse n) (CountLength.countBits data.reverse n)
    ∃t,t≤7*(InitialFormula.binSize h+InitialFormula.binSize l)+14+
        ((7*h+12)*InitialFormula.binSize h+4)+
        (RawNumberPrep.offset W D+1+RawPadSeed.time (RawNumberPrep.raw code h l z data) (RawNumberPrep.items W D))+
        ((13*n+13)*(code.length+data.length)+24*n+16)+(7*(18*n+7)+1) ∧
      Run (program W D)
        (store (RawNumberPrep.store (RawNumberPrep.before code (RawHeader.request h l z data)) 0 [] []) (fun _ => [])) t
        (store r (RawPreparedInputs.packed n code h l z data)) := by
  dsimp only
  let n := RawNumberPrep.width W D h code data (InitialFormula.bin l)
  have hn : RawPreparedInputs.bound D h code data l+1≤n := by
    dsimp [n,RawNumberPrep.width,RawPreparedInputs.bound]
    rw [InitialFormula.bin_length]
    nlinarith
  obtain ⟨t,ht,H⟩ := RawNumberPrep.program_run W D code h l z data
  have H0 := H.extend_left (fun _ : Fin 7 => [])
  have H1 := pack_run D h l n code z data hn
  have htime := PackFamily.time_le (List.finRange 7) (RawPreparedInputs.inputs n code h l z data) n
    (by intro i _;exact RawPreparedInputs.inputs_lengths D h l n code z data hn i)
  simp only [List.length_finRange] at htime
  refine ⟨t+PackFamily.time (RawPreparedInputs.inputs n code h l z data) n (List.finRange 7),by omega,?_⟩
  exact Run.seq _ _ _ _ _ _ _ H0 H1
end SourceBurnside.RawAssembler

namespace SourceBurnside.RawCompiled
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
variable {f : (Fin 7 → ℕ) → ℕ} {Pre : ℕ → (Fin 7 → ℕ) → Prop}
def slots (R : Realizer f Pre) : Fin 7 ⊕ R.W → K R
  | .inl i => .inl (.inr i)
  | .inr w => .inr w
lemma slots_injective (R : Realizer f Pre) : Function.Injective (slots R) := by
  intro x y h;cases x <;> cases y <;> simp_all [slots]
def before (R : Realizer f Pre) (code request : List Bool) : Store (K R) :=
  Sum.elim (RawAssembler.store (RawNumberPrep.store (RawNumberPrep.before code request) 0 [] []) (fun _ => [])) (fun _ => [])
def prepared (R : Realizer f Pre) (n : ℕ) (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) : Store (K R) :=
  Sum.elim (RawAssembler.store
    (RawNumberPrep.store (RawNumberPrep.raw code h l z data) n
      (CountLength.countBits code.reverse n) (CountLength.countBits data.reverse n))
    (RawPreparedInputs.packed n code h l z data)) (fun _ => [])
def program (R : Realizer f Pre) (W D : ℕ) : Program (K R) :=
  .seq ((RawAssembler.program W D).relabel Sum.inl) (R.program.relabel (slots R))
lemma body_lift (R : Realizer f Pre) {n t : ℕ} {code : List Bool} {h l : ℕ} {z : Bool} {data y : List Bool}
    (H : Run R.program (input (RawPreparedInputs.packed n code h l z data)) t
      (result (RawPreparedInputs.packed n code h l z data) R.out y)) :
    Run (R.program.relabel (slots R)) (prepared R n code h l z data) t
      (Function.update (prepared R n code h l z data) (.inr R.out) y) := by
  have hi : Agrees (slots R) (input (RawPreparedInputs.packed n code h l z data)) (prepared R n code h l z data) := by
    intro i;cases i <;> rfl
  exact H.relabel_to (slots R) (slots_injective R) _ _ hi
    (agrees_update (slots R) (slots_injective R) _ _ hi (.inr R.out) y)
    (outside_update (slots R) _ (.inr R.out) y)
def setupBound (W D h l : ℕ) (code data : List Bool) : ℕ :=
  let n := RawNumberPrep.width W D h code data (InitialFormula.bin l)
  7*(InitialFormula.binSize h+InitialFormula.binSize l)+14+
    ((7*h+12)*InitialFormula.binSize h+4)+
    (RawNumberPrep.offset W D+1+RawPadSeed.time (RawNumberPrep.raw code h l false data) (RawNumberPrep.items W D))+
    ((13*n+13)*(code.length+data.length)+24*n+16)+(7*(18*n+7)+1)
lemma setup_tag_independent (W D h l : ℕ) (code data : List Bool) (z : Bool) :
    RawPadSeed.time (RawNumberPrep.raw code h l z data) (RawNumberPrep.items W D)=
      RawPadSeed.time (RawNumberPrep.raw code h l false data) (RawNumberPrep.items W D) := rfl

theorem generic_trace (e : Formula (Fin 7)) (D : ℕ)
    (hE : ∀code h l z data,e.Exponents (RawPreparedInputs.bound D h code data l)
      (RawPreparedInputs.semantic code h l z data)) :
    ∃R : Realizer e.totalize.eval (fun n v => e.totalize.Safe n v),
      ∀(code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool),
        let n := RawNumberPrep.width e.weight D h code data (InitialFormula.bin l)
        ∃t y,t ≤ setupBound e.weight D h l code data+R.coefficient*(n+1)^2 ∧ y.length=n ∧
          Add.value y.reverse=e.eval (RawPreparedInputs.semantic code h l z data) ∧
          Run (program R e.weight D) (before R code (RawHeader.request h l z data)) t
            (Function.update (prepared R n code h l z data) (.inr R.out) y) := by
  obtain ⟨R,hR⟩ := timed_total (0:Fin 7) e
  refine ⟨R,?_⟩
  intro code h l z data
  let M := RawPreparedInputs.bound D h code data l
  let n := RawNumberPrep.width e.weight D h code data (InitialFormula.bin l)
  have hn0 : n=e.weight*(M+1) := by simp only [n,M,RawNumberPrep.width,RawPreparedInputs.bound,InitialFormula.bin_length]
  have hn : M+1≤n := by rw [hn0];have := e.weight_pos;nlinarith
  have hv := RawPreparedInputs.packed_values D h l n code z data hn
  have hl := RawPreparedInputs.packed_lengths D h l n code z data hn
  obtain ⟨tb,y,hb,hy,hyv,HB⟩ := hR M (RawPreparedInputs.packed n code h l z data) (fun i => (hl i).trans hn0)
    (by rw [hv];exact RawPreparedInputs.semantic_bounded D h l code z data)
    (by rw [hv];exact hE code h l z data)
  rw [←hn0] at hb hy
  rw [hv] at hyv
  obtain ⟨ta,ha,HA⟩ := RawAssembler.program_run e.weight D e.weight_pos code h l z data
  have has : ta ≤ setupBound e.weight D h l code data := by
    simpa only [setup_tag_independent,setupBound] using ha
  have H0 := HA.extend_left (fun _ : R.W => [])
  have H1 := body_lift R HB
  exact ⟨ta+tb,y,Nat.add_le_add has hb,hy,hyv,Run.seq _ _ _ _ _ _ _ H0 H1⟩
end SourceBurnside.RawCompiled

namespace SourceBurnside.RawPolynomial
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
lemma size_bounds (h l : ℕ) (code data : List Bool) :
    1 ≤ size h l code data ∧ h+1 ≤ size h l code data ∧
    InitialFormula.binSize h ≤ size h l code data ∧ InitialFormula.binSize l ≤ size h l code data ∧
    code.length+data.length ≤ size h l code data := by
  have := InitialFormula.binSize_le_self h
  unfold size;omega
lemma width_le (W D h l : ℕ) (code data : List Bool) :
    RawNumberPrep.width W D h code data (InitialFormula.bin l) ≤ factor W D*size h l code data := by
  have H := size_bounds h l code data
  have Hh := Nat.mul_le_mul_left (10000*(D+20)) H.2.1
  have Hp : code.length+data.length+InitialFormula.binSize l+33 ≤ 33*size h l code data := by
    unfold size;nlinarith
  unfold RawNumberPrep.width RawLocalBody.limit
  rw [InitialFormula.bin_length]
  unfold factor
  calc
    _  ≤  W*((10000*(D+20)+33)*size h l code data) := Nat.mul_le_mul_left W (by nlinarith)
    _ = _ := by ring
lemma setup_le (W D h l : ℕ) (code data : List Bool) :
    RawCompiled.setupBound W D h l code data  ≤
      (200*factor W D+1000)*(size h l code data+1)^2 := by
  let B := size h l code data+1
  let N := factor W D
  let n := RawNumberPrep.width W D h code data (InitialFormula.bin l)
  have HS := size_bounds h l code data
  have hB : 1 ≤ B := by dsimp [B];omega
  have hh : h ≤ B := by dsimp [B];omega
  have hbh : InitialFormula.binSize h ≤ B := by dsimp [B];omega
  have hbl : InitialFormula.binSize l ≤ B := by dsimp [B];omega
  have hcd : code.length+data.length ≤ B := by dsimp [B];omega
  have hn : n ≤ N*B := (width_le W D h l code data).trans (Nat.mul_le_mul_left _ (by omega))
  have h1 : 7*(InitialFormula.binSize h+InitialFormula.binSize l)+14 ≤ 28*B^2 :=
    linear_square hB (by omega)
  have h2m := squash (show 7*h+12 ≤ 19*B by omega) hbh
  have h4 : 4 ≤ 4*B^2 := by have := linear_square hB (show 4 ≤ 4*B by omega);omega
  have h2 : (7*h+12)*InitialFormula.binSize h+4 ≤ 23*B^2 := by omega
  have ht := RawAssembler.time_bound W D h l code data
  have h3 : RawNumberPrep.offset W D+1+RawPadSeed.time
      (RawNumberPrep.raw code h l false data) (RawNumberPrep.items W D) ≤ (N+100)*B^2 :=
    linear_square hB ht
  have hc1 := squash (show 13*n+13 ≤ (13*N+13)*B by nlinarith) hcd
  have hc2 : 24*n+16 ≤ (24*N+16)*B^2 := linear_square hB (by nlinarith)
  have hcount : (13*n+13)*(code.length+data.length)+24*n+16 ≤ (37*N+29)*B^2 := by
    nlinarith only [hc1,hc2]
  have hpack : 7*(18*n+7)+1 ≤ (126*N+50)*B^2 := linear_square hB (by nlinarith)
  change _  ≤  (200*N+1000)*B^2
  unfold RawCompiled.setupBound
  change 7*(InitialFormula.binSize h+InitialFormula.binSize l)+14+
    ((7*h+12)*InitialFormula.binSize h+4)+
    (RawNumberPrep.offset W D+1+RawPadSeed.time (RawNumberPrep.raw code h l false data) (RawNumberPrep.items W D))+
    ((13*n+13)*(code.length+data.length)+24*n+16)+(7*(18*n+7)+1) ≤ _
  nlinarith only [h1,h2,h3,hcount,hpack]
lemma body_le (W D h l c : ℕ) (code data : List Bool) :
    c*(RawNumberPrep.width W D h code data (InitialFormula.bin l)+1)^2 ≤
      (c*(factor W D+1)^2)*(size h l code data+1)^2 := by
  have hn := width_le W D h l code data
  have H : RawNumberPrep.width W D h code data (InitialFormula.bin l)+1 ≤
      (factor W D+1)*(size h l code data+1) := by nlinarith
  calc
    _  ≤  c*((factor W D+1)*(size h l code data+1))^2 := Nat.mul_le_mul_left c (Nat.pow_le_pow_left H 2)
    _ = _ := by ring
end SourceBurnside.RawPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_StackCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.TwoInputBody
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
variable {f : (Fin 7 → ℕ) → ℕ} {Pre : ℕ → (Fin 7 → ℕ) → Prop}
abbrev K (R : Realizer f Pre) := Fin 7 ⊕ RawCompiled.K R
def codeSlot (R : Realizer f Pre) : K R := .inr (.inl (.inl (.inl 0)))
def requestSlot (R : Realizer f Pre) : K R := .inr (.inl (.inl (.inl 4)))
def source (R : Realizer f Pre) : K R := .inl 0
def start (R : Realizer f Pre) (x : List Bool) : Store (K R) := Function.update (fun _ => []) (source R) x.reverse
def transfer (R : Realizer f Pre) : Program (K R) := .seq (copy (.inl 6) (codeSlot R) (.inl 4))
  (copy (.inl 0) (requestSlot R) (.inl 4))
def program (R : Realizer f Pre) (W D : ℕ) : Program (K R) :=
  .seq (TwoInputQuote.program.relabel Sum.inl) (.seq (transfer R) ((RawCompiled.program R W D).relabel Sum.inr))
lemma start_eq (R : Realizer f Pre) (x : List Bool) :
    start R x=Sum.elim (TwoInputQuote.store x [] [] 0 []) (fun _ => []) := by
  funext j;cases j with
  | inl j => fin_cases j <;> simp [-Sum.update_elim_inr, -Sum.elim_update_right, start,source,TwoInputQuote.store]
  | inr j => simp [-Sum.update_elim_inr, -Sum.elim_update_right, start,source]
lemma update_ready (R : Realizer f Pre) (r : Fin 7 → List Bool) (code request : List Bool) :
    Function.update (Function.update (Sum.elim r (fun _ => [])) (codeSlot R) code.reverse)
      (requestSlot R) request.reverse=Sum.elim r (RawCompiled.before R code request) := by
  funext j;cases j with
  | inl j => simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot,requestSlot]
  | inr j => cases j with
    | inr j => simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot,requestSlot,RawCompiled.before]
    | inl j => cases j with
      | inr j => simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot,requestSlot,RawCompiled.before,RawAssembler.store]
      | inl j => cases j with
        | inr j => fin_cases j <;> simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot,requestSlot,RawCompiled.before,RawAssembler.store,RawNumberPrep.store]
        | inl j => fin_cases j <;> simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot,requestSlot,RawCompiled.before,RawAssembler.store,RawNumberPrep.store,RawNumberPrep.before]
lemma transfer_run (R : Realizer f Pre) (v request : List Bool) :
    let q := TwoInputQuote.store request (InitialFormula.bin v.length) v 0 (WrappedInput.specialize v v).reverse
    Run (transfer R) (Sum.elim q (fun _ => []))
      (5*(WrappedInput.specialize v v).length+2+(5*request.length+2))
      (Sum.elim q (RawCompiled.before R (WrappedInput.specialize v v) request)) := by
  dsimp only
  let r := Sum.elim (TwoInputQuote.store request (InitialFormula.bin v.length) v 0 (WrappedInput.specialize v v).reverse)
    (fun _ : RawCompiled.K R => [])
  have H1 := copy_run (.inl 6 : K R) (codeSlot R) (.inl 4)
    (by simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot]) (by simp) (by simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot]) r rfl
  have H2 := copy_run (.inl 0 : K R) (requestSlot R) (.inl 4)
    (by simp [-Sum.update_elim_inr, -Sum.elim_update_right, requestSlot]) (by simp) (by simp [-Sum.update_elim_inr, -Sum.elim_update_right, requestSlot])
    (Function.update r (codeSlot R) (WrappedInput.specialize v v).reverse) (by simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot,r,TwoInputQuote.store])
  change Run (copy (.inl 6 : K R) (codeSlot R) (.inl 4)) r
    (5*(WrappedInput.specialize v v).reverse.length+2)
    (Function.update r (codeSlot R) (WrappedInput.specialize v v).reverse) at H1
  rw [List.length_reverse] at H1
  have HC : codeSlot R≠requestSlot R := by simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot,requestSlot]
  have hreq : (Function.update r (codeSlot R) (WrappedInput.specialize v v).reverse) (requestSlot R)=[] := by
    rw [Function.update_of_ne (Ne.symm HC)]
    rfl
  have hsrc : (Function.update r (codeSlot R) (WrappedInput.specialize v v).reverse) (.inl 0)=request.reverse := by
    simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot,r,TwoInputQuote.store]
  rw [hreq,hsrc,List.nil_append,List.length_reverse] at H2
  have H := Run.seq _ _ _ _ _ _ _ H1 H2
  rw [update_ready] at H
  exact H

theorem trace (e : Formula (Fin 7)) (D : ℕ)
    (hE : ∀code h l z data,e.Exponents (RawPreparedInputs.bound D h code data l)
      (RawPreparedInputs.semantic code h l z data)) :
    ∃R : Realizer e.totalize.eval (fun n v => e.totalize.Safe n v),
      ∀(v : List Bool) (h l : ℕ) (z : Bool) (data : List Bool),
        let code := WrappedInput.specialize v v
        let request := RawHeader.request h l z data
        let n := RawNumberPrep.width e.weight D h code data (InitialFormula.bin l)
        let q := TwoInputQuote.store request (InitialFormula.bin v.length) v 0 code.reverse
        ∃t y,t ≤ (7*v.length+47)*InitialFormula.binSize v.length+17*v.length+32+
            (5*code.length+2+(5*request.length+2))+
            (RawCompiled.setupBound e.weight D h l code data+R.coefficient*(n+1)^2) ∧
          y.length=n ∧ Add.value y.reverse=e.eval (RawPreparedInputs.semantic code h l z data) ∧
          Run (program R e.weight D) (start R (InitialFormula.enc v.length++v++request)) t
            (Sum.elim q (Function.update (RawCompiled.prepared R n code h l z data) (.inr R.out) y)) := by
  obtain ⟨R,hR⟩ := RawCompiled.generic_trace e D hE
  refine ⟨R,?_⟩
  intro v h l z data
  obtain ⟨tb,y,hb,hy,hyv,HB⟩ := hR (WrappedInput.specialize v v) h l z data
  obtain ⟨ta,ha,HA⟩ := TwoInputQuote.program_run v (RawHeader.request h l z data)
  have H0 := HA.extend_left (fun _ : RawCompiled.K R => [])
  rw [←start_eq] at H0
  have H1 := transfer_run R v (RawHeader.request h l z data)
  have H2 := HB.extend_right (TwoInputQuote.store (RawHeader.request h l z data)
    (InitialFormula.bin v.length) v 0 (WrappedInput.specialize v v).reverse)
  refine ⟨ta+((5*(WrappedInput.specialize v v).length+2+(5*(RawHeader.request h l z data).length+2))+tb),y,?_,hy,hyv,?_⟩
  · have H := Nat.add_le_add ha (Nat.add_le_add_left hb (5*(WrappedInput.specialize v v).length+2+(5*(RawHeader.request h l z data).length+2)))
    simpa only [Nat.add_assoc] using H
  · exact Run.seq _ _ _ _ _ _ _ H0 (Run.seq _ _ _ _ _ _ _ H1 H2)
end SourceBurnside.TwoInputBody

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_ProgramFixedPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.LiteralCompiler
noncomputable section
open StackMachine Structured Structured.Program FixedArity
variable {A : Type*} [DecidableEq A] {m : ℕ}
lemma header_trace (e : Option A ≃ Fin m) {P : Program A} (j out : A) (x : List Bool)
    {n : ℕ} {s : Store A} (h : Run P (CompactProgram.inputStore j x) n s) :
    ∃ t r front back, t ≤ loaderTime (tokens e P j out)+(runTime e P j out x n+1)*(5*(tokens e P j out).length+3) ∧
      exec (WrappedInput.machine src dst)
        (WrappedInput.config src dst .header [] (WrappedInput.envelope (code e P j out) x) [] [] 0) t=
        WrappedInput.liftConfig (UniversalInput.liftConfig
          (UniversalStack.config (.stopped ((s out).getLast?.getD false)) r front back 0)) := by
  obtain ⟨t,r,front,back,ht,H⟩ := compiled_trace e j out x h
  have HL := WrappedInput.plain_trace src dst distinct (tokens e P j out) x
  refine ⟨loaderTime (tokens e P j out)+t,r,front,back,Nat.add_le_add_left ht _,?_⟩
  rw [UniversalStack.exec_from]
  change exec (WrappedInput.machine src dst) (exec (WrappedInput.machine src dst)
    (WrappedInput.config src dst .header [] (WrappedInput.envelope (WrappedInput.plain (tokens e P j out)) x) [] [] 0)
      (loaderTime (tokens e P j out))) t=_
  dsimp only [loaderTime]
  rw [HL]
  change exec (WrappedInput.machine src dst) (WrappedInput.liftConfig (UniversalInput.liftConfig
    (UniversalStack.config .pick (UniversalInput.inputRegs src dst [] x) (tokens e P j out) [] 0))) t=_
  rw [WrappedInput.lift_exec,UniversalInput.lift_exec src dst,H]
lemma specialized_trace (e : Option A ≃ Fin m) {P : Program A} (j out : A) (v x : List Bool)
    {n : ℕ} {s : Store A} (h : Run P (CompactProgram.inputStore j (InitialFormula.enc v.length++v++x)) n s) :
    ∃ t r front back,
      t ≤ (2*(WrappedInput.envelope (WrappedInput.specialize (code e P j out) v) x).length+1)+
        (4*InitialFormula.binSize (WrappedInput.specialize (code e P j out) v).length+3)+
        (loaderTime (tokens e P j out)+(runTime e P j out (InitialFormula.enc v.length++v++x) n+1)*
          (5*(tokens e P j out).length+3)) ∧
      exec (WrappedInput.machine src dst)
        (WrappedInput.config src dst .reverse (WrappedInput.envelope (WrappedInput.specialize (code e P j out) v) x) [] [] [] 0) t=
        WrappedInput.liftConfig (UniversalInput.liftConfig
          (UniversalStack.config (.stopped ((s out).getLast?.getD false)) r front back 0)) := by
  obtain ⟨t,r,front,back,ht,H⟩ := header_trace e j out (InitialFormula.enc v.length++v++x) h
  let s0 := (2*(WrappedInput.envelope (WrappedInput.specialize (code e P j out) v) x).length+1)+
    (4*InitialFormula.binSize (WrappedInput.specialize (code e P j out) v).length+3)
  refine ⟨s0+t,r,front,back,Nat.add_le_add_left ht s0,?_⟩
  rw [UniversalStack.exec_from,WrappedInput.raw_specialize_trace src dst distinct]
  exact H
end
end SourceBurnside.LiteralCompiler

namespace SourceBurnside.RawTimeBound
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
open PolynomialAccounting
def quoteCost (v : List Bool) := (7*v.length+47)*InitialFormula.binSize v.length+17*v.length+32
def inputCoefficient (v : List Bool) := 2*InitialFormula.binSize v.length+1+v.length+7
def coefficient (W D c : ℕ) (v : List Bool) :=
  let a := WrappedInput.specialize v v
  quoteCost v+5*a.length+39+
    (200*RawPolynomial.factor W D+1000+c*(RawPolynomial.factor W D+1)^2)*(a.length+3)^2
lemma request_length (h l : ℕ) (data : List Bool) (z : Bool) :
    (RawHeader.request h l z data).length ≤ 7*size h l data := by
  have hh := InitialFormula.binSize_le_self h
  have hl := InitialFormula.binSize_le_self l
  simp only [RawHeader.request,List.length_append,List.length_cons,InitialFormula.enc_length]
  unfold size;omega
lemma twoinput_length (h l : ℕ) (data v : List Bool) (z : Bool) :
    (InitialFormula.enc v.length++v++RawHeader.request h l z data).length ≤ inputCoefficient v*size h l data := by
  have hh := request_length h l data z
  have hs := positive h l data
  simp only [List.length_append,InitialFormula.enc_length]
  have H := Nat.mul_le_mul_left (2*InitialFormula.binSize v.length+1+v.length) hs
  unfold inputCoefficient
  nlinarith
lemma envelope_length (h l : ℕ) (data a : List Bool) (z : Bool) :
    (WrappedInput.envelope a (RawHeader.request h l z data)).length ≤ inputCoefficient a*size h l data :=
  twoinput_length h l data a z
lemma arithmetic_size (h l : ℕ) (data a : List Bool) :
    RawPolynomial.size h l a data+1 ≤ (a.length+3)*size h l data := by
  have hl := InitialFormula.binSize_le_self l
  have hs := positive h l data
  have H := Nat.mul_le_mul_left (a.length+2) hs
  unfold RawPolynomial.size size at *
  nlinarith
lemma trace_bound (W D c h l : ℕ) (z : Bool) (data v : List Bool) :
    (7*v.length+47)*InitialFormula.binSize v.length+17*v.length+32+
      (5*(WrappedInput.specialize v v).length+2+(5*(RawHeader.request h l z data).length+2))+
      (RawCompiled.setupBound W D h l (WrappedInput.specialize v v) data+
        c*(RawNumberPrep.width W D h (WrappedInput.specialize v v) data (InitialFormula.bin l)+1)^2) ≤
      coefficient W D c v*(size h l data)^2 := by
  let a := WrappedInput.specialize v v
  let S := size h l data
  have hs : 1 ≤ S := positive h l data
  have hs2 : 1 ≤ S^2 := (powers S hs).1
  have hsq : S ≤ S^2 := (powers S hs).2.1
  have hreq : (RawHeader.request h l z data).length ≤ 7*S^2 :=
    (request_length h l data z).trans (Nat.mul_le_mul_left 7 hsq)
  have hsz := arithmetic_size h l data a
  have hsz2 : (RawPolynomial.size h l a data+1)^2 ≤ (a.length+3)^2*S^2 := by
    calc _ ≤ ((a.length+3)*S)^2 := Nat.pow_le_pow_left hsz 2
         _ = _ := by ring
  have hsetup := RawPolynomial.setup_le W D h l a data
  have hbody := RawPolynomial.body_le W D h l c a data
  have hab : RawCompiled.setupBound W D h l a data+
      c*(RawNumberPrep.width W D h a data (InitialFormula.bin l)+1)^2 ≤
      (200*RawPolynomial.factor W D+1000+c*(RawPolynomial.factor W D+1)^2)*
        (RawPolynomial.size h l a data+1)^2 := by nlinarith only [hsetup,hbody]
  have hscale := Nat.mul_le_mul_left (200*RawPolynomial.factor W D+1000+c*(RawPolynomial.factor W D+1)^2) hsz2
  have hconst := Nat.mul_le_mul_left (quoteCost v+5*a.length+4) hs2
  change quoteCost v+(5*a.length+2+(5*(RawHeader.request h l z data).length+2))+_ ≤ _
  change _ ≤ (quoteCost v+5*a.length+39+(200*RawPolynomial.factor W D+1000+c*(RawPolynomial.factor W D+1)^2)*(a.length+3)^2)*S^2
  nlinarith only [hab,hscale,hconst,hreq]
end SourceBurnside.RawTimeBound

namespace SourceBurnside.RawFixedPoint
noncomputable section
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
theorem constructTimed (e : Formula (Fin 7)) (D : ℕ)
    (hE : ∀code h l z data,e.Exponents (RawPreparedInputs.bound D h code data l)
      (RawPreparedInputs.semantic code h l z data)) (hBool : ∀v,e.eval v ≤ 1) :
    ∃(t : List Bool) (C : ℕ), ∀(h l : ℕ) (z : Bool) (data : List Bool),
      ∃(N : ℕ) (b : Bool), ∃r front back,
        N ≤ C*(RawTimeBound.size h l data)^4 ∧
        Add.bit b=e.eval (RawPreparedInputs.semantic (WrappedInput.specialize t t) h l z data) ∧
        StackMachine.exec (WrappedInput.machine LiteralCompiler.src LiteralCompiler.dst)
          (WrappedInput.config LiteralCompiler.src LiteralCompiler.dst .reverse
            (WrappedInput.envelope (WrappedInput.specialize t t) (RawHeader.request h l z data)) [] [] [] 0) N=
          WrappedInput.liftConfig (UniversalInput.liftConfig
            (UniversalStack.config (.stopped b) r front back 0)) := by
  obtain ⟨R,hR⟩ := TwoInputBody.trace e D hE
  let K := TwoInputBody.K R
  let : Fintype K := Fintype.ofFinite K
  let p := TwoInputBody.program R e.weight D
  let j := TwoInputBody.source R
  let out : K := .inr (.inr R.out)
  let f := Fintype.equivFin (Option K)
  let t := LiteralCompiler.code f p j out
  let C := LiteralCompiler.coefficient (Fintype.card (Option K))
    (RawTimeBound.coefficient e.weight D R.coefficient t)
    (RawTimeBound.inputCoefficient t) (RawTimeBound.inputCoefficient (WrappedInput.specialize t t))
    (WrappedInput.specialize t t) (LiteralCompiler.tokens f p j out)
  refine ⟨t,C,?_⟩
  intro h l z data
  obtain ⟨n,y,hn,hy,hyv,H⟩ := hR t h l z data
  have HH : Run p (CompactProgram.inputStore j (InitialFormula.enc t.length++t++RawHeader.request h l z data)) n
      (Sum.elim (TwoInputQuote.store (RawHeader.request h l z data) (InitialFormula.bin t.length) t 0
        (WrappedInput.specialize t t).reverse)
      (Function.update (RawCompiled.prepared R (RawNumberPrep.width e.weight D h (WrappedInput.specialize t t) data
        (InitialFormula.bin l)) (WrappedInput.specialize t t) h l z data) (.inr R.out) y)) := H
  obtain ⟨N,r,front,back,hN,HC⟩ := LiteralCompiler.specialized_trace f j out t (RawHeader.request h l z data) HH
  have hout : (Sum.elim (TwoInputQuote.store (RawHeader.request h l z data) (InitialFormula.bin t.length) t 0
        (WrappedInput.specialize t t).reverse)
      (Function.update (RawCompiled.prepared R (RawNumberPrep.width e.weight D h (WrappedInput.specialize t t) data
        (InitialFormula.bin l)) (WrappedInput.specialize t t) h l z data) (.inr R.out) y)) out=y := by
    simp [out]
  rw [hout] at HC
  have hnn := hn.trans (RawTimeBound.trace_bound e.weight D R.coefficient h l z data t)
  have htime := LiteralCompiler.specialized_bound f p j out t (RawHeader.request h l z data)
    n (RawTimeBound.size h l data) (RawTimeBound.coefficient e.weight D R.coefficient t)
    (RawTimeBound.inputCoefficient t) (RawTimeBound.inputCoefficient (WrappedInput.specialize t t))
    (RawTimeBound.positive h l data) (RawTimeBound.twoinput_length h l data t z)
    (RawTimeBound.envelope_length h l data (WrappedInput.specialize t t) z) hnn
  refine ⟨N,y.getLast?.getD false,r,front,back,hN.trans htime,?_,HC⟩
  rw [FixedArity.output_bit,hyv,Nat.mod_eq_of_lt]
  have := hBool (RawPreparedInputs.semantic (WrappedInput.specialize t t) h l z data)
  omega
end
end SourceBurnside.RawFixedPoint

namespace SourceBurnside.TimedTape
noncomputable section
open StackMachine Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
lemma construct (e : Formula (Fin 7)) (D : ℕ)
    (hE : ∀code h l z data,e.Exponents (RawPreparedInputs.bound D h code data l)
      (RawPreparedInputs.semantic code h l z data)) (hBool : ∀v,e.eval v ≤ 1) :
    ∃(t : List Bool) (C : ℕ), ∀(h l : ℕ) (z : Bool) (data : List Bool),
      ∃(N : ℕ) (b : Bool),
        N ≤ C*(RawTimeBound.size h l data)^8 ∧
        Add.bit b=e.eval (RawPreparedInputs.semantic (WrappedInput.specialize t t) h l z data) ∧
        ∀T≥N,(OneTape.run δ (StackMachine.encode
          (start (WrappedInput.envelope (WrappedInput.specialize t t) (RawHeader.request h l z data)))) T).cell 0=output b := by
  obtain ⟨t,C,hC⟩ := RawFixedPoint.constructTimed e D hE hBool
  refine ⟨t,C*(2*(RawTimeBound.inputCoefficient (WrappedInput.specialize t t)+C)+3),?_⟩
  intro h l z data
  obtain ⟨N,b,r,front,back,hN,hb,HC⟩ := hC h l z data
  let X := WrappedInput.envelope (WrappedInput.specialize t t) (RawHeader.request h l z data)
  change StackMachine.exec machine (start X) N=finish b r front back at HC
  refine ⟨StackMachine.clock machine (start X) N,b,?_,hb,?_⟩
  · have H := StackMachine.clock_bound machine (start X) X.length N (start_length X)
    exact H.trans (PolynomialAccounting.oneTape_bound X.length N C
      (RawTimeBound.inputCoefficient (WrappedInput.specialize t t)) (RawTimeBound.size h l data)
      (RawTimeBound.positive h l data) (RawTimeBound.envelope_length h l data (WrappedInput.specialize t t) z) hN)
  · intro T hT
    have ht := StackMachine.compile_finish machine (start X) N T
      (by rw [HC];exact finish_halt b r front back) hT
    rw [HC] at ht
    change (OneTape.run (StackMachine.compile machine) (StackMachine.encode (start X)) T).cell 0=output b
    rw [ht,finish_output]
lemma source_predicate (β g D : ℕ) (c : Tableau.Circuit (3*β) g)
    (out : Fin β → Tableau.Wire (3*β+g)) (bl ini acc : Fin β → Bool)
    (encoding : Bool → Fin β → Bool) :
    ∃(t : List Bool) (C : ℕ), ∀(h l : ℕ) (z : Bool) (data : List Bool),
      ∃(N : ℕ) (b : Bool),
        N ≤ C*(RawTimeBound.size h l data)^8 ∧
        Add.bit b=(RawFit.body β g D c out bl ini acc encoding).eval
          (RawPreparedInputs.semantic (WrappedInput.specialize t t) h l z data) ∧
        ∀T≥N,(OneTape.run δ (StackMachine.encode
          (start (WrappedInput.envelope (WrappedInput.specialize t t) (RawHeader.request h l z data)))) T).cell 0=output b :=
  construct _ D (RawFixedPoint.body_exponents β g D c out bl ini acc encoding)
    (RawFixedPoint.body_boolean β g D c out bl ini acc encoding)
end
end SourceBurnside.TimedTape

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Machines_TimedExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

namespace SourceBurnside.SourceMachine
noncomputable section
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
open TimedTape

theorem timed_selfpoint (D : ℕ) (_hD : 2≤D) :
    ∃(t : List Bool) (h0 : ℕ), 0<h0 ∧ ∀h≥h0,
      RawFit.Fits β g D h (WrappedInput.specialize t t).length ∧
      ∀(l : ℕ), l≤10 → ∀(z : Bool) (data : List Bool), data.length≤200000*(D*h) →
        ∃b : Bool,
          Add.bit b=(body D).eval (RawPreparedInputs.semantic (WrappedInput.specialize t t) (D*h) l z data) ∧
          (OneTape.run δ (StackMachine.encode (start
            (WrappedInput.envelope (WrappedInput.specialize t t) (RawHeader.request (D*h) l z data))))
            (2^(h/5)-1)).cell 0=output b := by
  obtain ⟨t,C,hC⟩ := TimedTape.source_predicate β g D localCircuit.circuit localCircuit.output
    blankBits initialBits acceptBits bitEncoding
  let A := 200001*D+11
  obtain ⟨u,hu⟩ := ExponentialThreshold.scaled (C*A^8) 8 5 (by omega)
  obtain ⟨v,hv⟩ := RawFit.eventually_fits β g D (WrappedInput.specialize t t).length
  refine ⟨t,max 1 (max u v),by omega,?_⟩
  intro h hh
  have h1 : 1≤h := by omega
  have hU : u≤h := by omega
  have hV : v≤h := by omega
  refine ⟨hv h hV,?_⟩
  intro l hl z data hd
  obtain ⟨N,b,hN,hb,HC⟩ := hC (D*h) l z data
  refine ⟨b,hb,HC _ ?_⟩
  have hsz : RawTimeBound.size (D*h) l data ≤ A*h := by
    have H := Nat.mul_le_mul_left 11 h1
    unfold RawTimeBound.size A
    nlinarith only [H,hl,hd]
  have hn : N < 2^(h/5) := by
    calc
      N ≤ C*(RawTimeBound.size (D*h) l data)^8 := hN
      _ ≤ C*(A*h)^8 := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hsz 8)
      _ = C*A^8*h^8 := by ring
      _ < 2^(h/5) := hu h hU
  omega
end
end SourceBurnside.SourceMachine

namespace SourceBurnside.SourceMachine
noncomputable section

open TimedTape Addressable Structured Structured.Binary

theorem tableau_selfpoint (D : ℕ) (hD : 2≤D) :
    ∃(t : List Bool) (h0 : ℕ) (h0pos : 0<h0), ∀(h : ℕ) (hh : h0≤h),
      ∃fit : RawFit.Fits β g D h (WrappedInput.specialize t t).length,
      ∀(l : ℕ) (hl : 0<l) (hl10 : l≤10) (z : Bool) (data : DataAddress (2^h)→Bool),
      let a := WrappedInput.specialize t t
      let hd : 0<10000*(D*h) := by exact Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (lt_of_lt_of_le h0pos hh))
      let raw := candidateBits data z hd fit.2.2.2.1 hl hl10
      let input := addressedInput (InitialFormula.sourceInput a (D*h) l z hd fit.2.2.2.1 hl hl10)
      (∃ cert : Fin (2^h)→Bool, ∀i,
        ((layout h a.length D fit).clauseAt localCircuit.circuit localCircuit.output
          (input.initialBits coding (2^(h/5))) blankBits acceptBits i).Holds
            (Layout.assemble data cert)) ↔
      (body D).eval (RawPreparedInputs.semantic a (D*h) l z raw)=1 := by
  obtain ⟨t,h0,h0pos,H⟩ := timed_selfpoint D hD
  refine ⟨t,h0,h0pos,?_⟩
  intro h hh
  obtain ⟨fit,ht⟩ := H h hh
  refine ⟨fit,?_⟩
  intro l hl hl10 z data
  dsimp only
  let a := WrappedInput.specialize t t
  have hd : 0<10000*(D*h) := by exact Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (lt_of_lt_of_le h0pos hh))
  let raw := candidateBits data z hd fit.2.2.2.1 hl hl10
  let input := addressedInput (InitialFormula.sourceInput a (D*h) l z hd fit.2.2.2.1 hl hl10)
  let : NeZero (2^h) := ⟨pow_ne_zero h (by omega)⟩
  obtain ⟨b,hb,HC⟩ := ht l hl10 z raw (candidate_length_le data z hd fit.2.2.2.1 hl hl10)
  have HM := input.certificate_machine_iff coding δ localCircuit (2^(h/5)) (Nat.pow_pos (by omega))
    (input_short a h D l z fit hd hl hl10) (layout h a.length D fit) rfl (output true) data
  change (∃cert : Fin (2^h)→Bool, ∀i,
    ((layout h a.length D fit).clauseAt localCircuit.circuit localCircuit.output
      (input.initialBits coding (2^(h/5))) blankBits acceptBits i).Holds
      (Layout.assemble data cert)) ↔ (body D).eval (RawPreparedInputs.semantic a (D*h) l z raw)=1
  simp only [blankBits,acceptBits]
  rw [HM]
  change (OneTape.run δ (input.config (Layout.assemble data (fun _ => false))) (2^(h/5)-1)).cell 0=_ ↔ _
  have hcfg := source_config a data z hd fit.2.2.2.1 hl hl10
  change input.config _=_ at hcfg
  rw [hcfg,HC,TimedTape.output_injective.eq_iff,←hb]
  cases b <;> decide
end
end SourceBurnside.SourceMachine

namespace SourceBurnside.SourceMachine
noncomputable section

open TimedTape Addressable LocalSyntax FiniteTable FiniteTable.Codec

theorem fixed_table_certificate (D : ℕ) (hD : 2≤D) :
    ∃(t : List Bool) (h0 : ℕ) (h0pos : 4≤h0), ∀(h : ℕ) (hh : h0≤h),
      let a := WrappedInput.specialize t t
      ∃(fit : RawFit.Fits β g D h a.length) (fitnext : RawFit.Fits β g D (D*h) a.length),
      ∀(task : Task) (data : DataAddress (2^h)→Bool),
      let hd : 0<10000*(D*h) := by exact Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (by omega))
      let hdnext : 0<10000*(D*(D*h)) := by exact Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
      (∃cert : Fin (2^h)→Bool, ∀i,
        ((layout h a.length D fit).clauseAt localCircuit.circuit localCircuit.output
          (sourceInitial a fit hd task) blankBits acceptBits i).Holds (Layout.assemble data cert)) ↔
      entry (by nlinarith : 0<D*h) (sourceSchedule a fitnext hdnext) (10000*(D*(D*h))) task.zeroTask
        (List.ofFn (candidateWord (l:=task.arity.val+1) data fit.2.2.2.1 (by have := task.arity.isLt;omega) false))
        (if task.zeroTask then [] else List.ofFn
          (candidateWord (l:=task.arity.val+1) data fit.2.2.2.1 (by have := task.arity.isLt;omega) true))=true := by
  obtain ⟨t,u,hu,H⟩ := tableau_selfpoint D hD
  refine ⟨t,max 4 u,by omega,?_⟩
  intro h hh
  have h4 : 4≤h := by omega
  have huh : u≤h := by omega
  have hnext : u≤D*h := by nlinarith
  obtain ⟨fit,ht⟩ := H h huh
  obtain ⟨fitnext,_⟩ := H (D*h) hnext
  refine ⟨fit,fitnext,?_⟩
  intro task data
  dsimp only
  let a := WrappedInput.specialize t t
  have hd : 0<10000*(D*h) := by positivity
  have hdnext : 0<10000*(D*(D*h)) := by positivity
  have hl : 0<task.arity.val+1 := by omega
  have hl10 : task.arity.val+1≤10 := by have := task.arity.isLt;omega
  have Hb := ht (task.arity.val+1) hl hl10 task.zeroTask data
  have He := candidate_entry (by nlinarith : 4≤D*h) a data task.zeroTask hd fit.2.2.2.1 hl hl10 fitnext hdnext
  rw [sourceInitial_input]
  exact Hb.trans He
end
end SourceBurnside.SourceMachine

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_WordRewriting
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAdmissible _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideEndpoint _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHead _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideInternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLastOK _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLeftExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalettePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideRightExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideStructural _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

def Survives (S : Schedule q) (d : ℕ) (w : List (Cell q)) : Prop :=
  ∀ p z s, Reach S d w (p ++ z ++ s) → ¬ Zero S d z

lemma Survives.of_reach {v w : List (Cell q)} (hv : Survives S d v)
    (h : Reach S d v w) : Survives S d w := by
  intro p z s hz
  exact hv p z s (h.trans hz)

lemma Survives.infix {v w : List (Cell q)} (hw : Survives S d w)
    (hi : v <:+: w) : Survives S d v := by
  obtain ⟨a,b,rfl⟩ := hi
  intro p z s hr hz
  have hh := reach_context hr a b
  apply hw (a++p) z (s++b) _ hz
  simpa only [List.append_assoc] using hh

lemma Survives.not_zero {w : List (Cell q)} (hw : Survives S d w) : ¬ Zero S d w := by
  exact hw [] w [] (by simpa using (Relation.ReflTransGen.refl : Reach S d w w))

lemma Survives.format {w : List (Cell q)} (hw : Survives S d w) {a : Cell q}
    (ha : a ∈ w) : a.Format S d := by
  obtain ⟨p,s,rfl⟩ := List.append_of_mem ha
  by_contra h
  exact hw p [a] s (by simpa using (Relation.ReflTransGen.refl : Reach S d (p ++ a :: s) (p ++ a :: s))) (Or.inl ⟨a,rfl,Or.inl h⟩)

lemma Survives.pair {w : List (Cell q)} (hw : Survives S d w) {a b : Cell q}
    (hab : [a,b] <:+: w) : Pair a b := by
  by_contra h
  exact (hw.infix hab).not_zero (Or.inr ⟨a,b,rfl,Or.inl h⟩)

lemma Survives.chain {w : List (Cell q)} (hw : Survives S d w) : w.IsChain Pair := by
  induction w with
  | nil => simp
  | cons a w ih =>
    cases w with
    | nil => simp
    | cons b w =>
      apply List.isChain_cons_cons.mpr
      constructor
      · exact hw.pair ⟨[],w,by simp⟩
      · exact ih (hw.infix ⟨[a],[],by simp⟩)

namespace Cell

def paletteRank (c : Cell q) : ℕ := c.transactionRank + c.checkerRank

omit [NeZero q] in
lemma paletteRank_lt (c : Cell q) : c.paletteRank < 6 := by
  unfold paletteRank transactionRank checkerRank
  cases c.marker <;> cases c.checker <;> simp

lemma not_first_of_palette (c : Cell q) (hc : c.isPalette) : ¬c.skeleton.first := by
  obtain ⟨x,hx⟩ := hc
  change c.skeleton.pos = .palette x at hx
  simp [Skeleton.first, hx]

omit [NeZero q] in
lemma not_last_of_palette (c : Cell q) (hc : c.isPalette) : ¬c.skeleton.last := by
  obtain ⟨x,hx⟩ := hc
  change c.skeleton.pos = .palette x at hx
  simp [Skeleton.last, hx]
end Cell

lemma palette_marker_pair {a b : Cell q} (ha : a.isPalette) (hb : b.isPalette)
    (hp : Pair a b) :
    (a.marker = .idle ∧ b.marker = .idle) ∨
    (a.marker = .left ∧ (b.marker = .left ∨ b.marker = .boundary ∨ b.marker = .full)) ∨
    (a.marker = .boundary ∧ b.marker = .idle) ∨
    (a.marker = .full ∧ b.marker = .right) ∨
    (a.marker = .right ∧ b.marker = .right) := by
  have haf := a.not_first_of_palette ha
  have hal := a.not_last_of_palette ha
  have hbf := b.not_first_of_palette hb
  have hbl := b.not_last_of_palette hb
  have hh := hp.1.2
  simp only [Skeleton.rightExternal, Skeleton.leftExternal, Skeleton.acceptsRight,
    Skeleton.acceptsLeft, hal, hbf, and_false, or_false] at hh
  cases hma : a.marker <;> cases hmb : b.marker <;>
    simp_all only [Cell.marker, reduceCtorEq, and_self, or_self,
      or_true, or_false, true_and, and_true, false_and, and_false,
      not_true_eq_false, not_false_eq_true, ite_true, ite_false]

lemma palette_rank_nondecreasing {a b : Cell q} (ha : a.isPalette) (hb : b.isPalette)
    (hp : Pair a b) :
    a.transactionRank ≤ b.transactionRank ∧ a.checkerRank ≤ b.checkerRank := by
  constructor
  · have hh := palette_marker_pair ha hb hp
    rcases hh with ⟨h,h'⟩ | ⟨h,hh⟩ | ⟨h,h'⟩ | ⟨h,h'⟩ | ⟨h,h'⟩
    all_goals try {simp [Cell.transactionRank,h,h']}
    rcases hh with h' | h' | h' <;> simp [Cell.transactionRank,h,h']
  · have hh := hp.2.1 ⟨ha,hb⟩
    generalize hca : a.checker = ca at hh
    generalize hcb : b.checker = cb at hh
    cases hh <;> simp [Cell.checkerRank,hca,hcb]

lemma palette_equal_markerRank {a b : Cell q} (ha : a.isPalette) (hb : b.isPalette)
    (hp : Pair a b) (he : a.transactionRank = b.transactionRank) :
    a.marker = b.marker ∧ (a.marker = .idle ∨ a.marker = .left ∨ a.marker = .right) := by
  have hh := palette_marker_pair ha hb hp
  rcases hh with ⟨h,h'⟩ | ⟨h,h'|h'|h'⟩ | ⟨h,h'⟩ | ⟨h,h'⟩ | ⟨h,h'⟩ <;>
    simp_all [Cell.transactionRank]

omit [NeZero q] in
lemma palette_equal_checkerRank {a b : Cell q} (ha : a.isPalette) (hb : b.isPalette)
    (hp : Pair a b) (he : a.checkerRank = b.checkerRank) :
    a.checker = b.checker ∧ ∀ x, a.checker ≠ .head x := by
  have hh := hp.2.1 ⟨ha,hb⟩
  generalize hca : a.checker = ca at hh
  generalize hcb : b.checker = cb at hh
  cases hh <;> simp_all [Cell.checkerRank]

omit [NeZero q] in
lemma palette_internal_metadata {a b : Cell q} (ha : a.isPalette)
    (hi : Internal a.skeleton b.skeleton) : a.metadata = b.metadata := by
  obtain ⟨x,hx⟩ := ha
  change a.skeleton.pos = .palette x at hx
  rcases hi with ⟨har,ht,hbl,_,_⟩
  simp only [hx, reduceCtorEq, ite_false] at hbl
  change a.skeleton.metadata = b.skeleton.metadata
  generalize hma : a.skeleton.metadata = ma at har ht hbl ⊢
  generalize hmb : b.skeleton.metadata = mb at har ht hbl ⊢
  cases ma with | mk ar ta bl =>
    cases mb with | mk ar' ta' bl' =>
      simp only at har ht hbl
      subst ar'; subst ta'
      congr 1
      exact Fin.ext hbl

lemma palette_equal_metadata {a b : Cell q} (ha : a.isPalette) (_hb : b.isPalette)
    (hfa : a.Format S d) (hfb : b.Format S d) (hp : Pair a b)
    (he : a.marker = b.marker) (hn : a.marker = .idle ∨ a.marker = .left ∨ a.marker = .right) :
    a.metadata = b.metadata := by
  rcases hn with hi | hn
  · exact (hfa.2.2.2.2.1 hi).1.trans ((hfb.2.2.2.2.1 (he ▸ hi)).1.symm)
  · rcases hp.1.2 with hh | hh
    · have hal := a.not_last_of_palette ha
      have hh := hh.1
      rcases hn with hn | hn <;>
        simp_all [Skeleton.rightExternal,Cell.marker]
    · exact palette_internal_metadata ha hh.2.2.2.2

lemma palette_equal_rank {a b : Cell q} (ha : a.isPalette) (hb : b.isPalette)
    (hfa : a.Format S d) (hfb : b.Format S d) (hp : Pair a b)
    (hr : a.paletteRank = b.paletteRank) :
    a.eraseColor = b.eraseColor ∧ a.HeadFree ∧ b.HeadFree := by
  have hm := palette_rank_nondecreasing ha hb hp
  have htr : a.transactionRank = b.transactionRank := by
    unfold Cell.paletteRank at hr; omega
  have hcr : a.checkerRank = b.checkerRank := by
    unfold Cell.paletteRank at hr; omega
  obtain ⟨hem,hnm⟩ := palette_equal_markerRank ha hb hp htr
  obtain ⟨hec,hnc⟩ := palette_equal_checkerRank ha hb hp hcr
  have hmeta := palette_equal_metadata ha hb hfa hfb hp hem hnm
  have hna : ¬a.isCore := by
    obtain ⟨x,hx⟩ := ha
    rintro ⟨p,hp⟩; rw [hx] at hp; cases hp
  have hnb : ¬b.isCore := by
    obtain ⟨x,hx⟩ := hb
    rintro ⟨p,hp⟩; rw [hx] at hp; cases hp
  obtain ⟨hda,hca⟩ := hfa.2.2.2.1 hna
  obtain ⟨hdb,hcb⟩ := hfb.2.2.2.1 hnb
  have hhead (c : Cell q) (hf : c.Format S d)
      (hn : c.marker = .idle ∨ c.marker = .left ∨ c.marker = .right) :
      c.head = defaultHead := by
    rcases hn with hi | hn
    · exact (hf.2.2.2.2.1 hi).2.1
    · exact hf.2.2.2.2.2.1 hn
  have hha := hhead a hfa hnm
  have hhb := hhead b hfb (hem ▸ hnm)
  have hnon : ¬IsHead a.skeleton := by
    change ¬(a.marker = .boundary ∨ a.marker = .full)
    rcases hnm with h | h | h <;> simp [h]
  have hnon' : ¬IsHead b.skeleton := by
    change ¬(b.marker = .boundary ∨ b.marker = .full)
    change ¬(a.marker = .boundary ∨ a.marker = .full) at hnon
    simpa only [←hem] using hnon
  refine ⟨?_, ⟨hnon,hnc⟩, ⟨hnon',?_⟩⟩
  · cases a with | mk ska cha da ca hea =>
      cases b with | mk skb chb db cb heb =>
        cases ska; cases skb
        simp_all [Cell.eraseColor,Cell.setColor,Cell.marker,Cell.metadata]
  · simpa only [←hec] using hnc

lemma replacement_swap_of_same_fields {a b : Cell q} (ha : a.isPalette) (hb : b.isPalette)
    (hfa : a.Format S d) (hfb : b.Format S d) (he : a.eraseColor = b.eraseColor)
    (hf : a.HeadFree) (hf' : b.HeadFree) : Replacement S d [a,b] [b,a] := by
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hb
  have hset : a.setColor y = b := by
    have hh := congrArg (fun c : Cell q => c.setColor y) he
    simpa only [Cell.eraseColor,Cell.setColor_setColor,b.setColor_of_palette hy] using hh
  refine ⟨?_,Or.inr ⟨a,b,b,a,rfl,rfl,Or.inl (.swap a b x y hx hy hset hf hf')⟩⟩
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rintro c ((rfl|rfl)|(rfl|rfl)) <;> assumption

lemma Survives.palette_rank_chain {w : List (Cell q)} (hw : Survives S d w)
    (hp : ∀ a ∈ w, a.isPalette) :
    (w.map Cell.paletteRank).IsChain (· ≤ ·) := by
  exact (List.isChain_map Cell.paletteRank).mpr (hw.chain.imp_of_mem_imp (by
    intro a b ha hb hab
    have hh := palette_rank_nondecreasing (hp a ha) (hp b hb) hab
    exact Nat.add_le_add hh.1 hh.2))

lemma Survives.palette_rank_head_le {a b : Cell q} {w : List (Cell q)}
    (hw : Survives S d (a::w)) (hp : ∀ c ∈ a::w, c.isPalette) (hb : b ∈ w) :
    a.paletteRank ≤ b.paletteRank := by
  have hh := hw.palette_rank_chain hp
  exact hh.rel_cons (List.mem_map_of_mem hb)

lemma Survives.palette_no_collision {a b : Cell q} (p : List (Cell q))
    (hw : Survives S d (a :: p ++ [b]))
    (hp : ∀ c ∈ a :: p ++ [b], c.isPalette)
    (hr : a.paletteRank = b.paletteRank) (hc : a.color = b.color) : False := by
  induction p with
  | nil =>
    obtain ⟨x,hx⟩ := hp a (by simp)
    obtain ⟨y,hy⟩ := hp b (by simp)
    have hxy : x = y := by simpa only [Cell.color,hx,hy] using hc
    subst y
    apply hw.not_zero
    exact Or.inr ⟨a,b,rfl,Or.inr (Or.inl ⟨x,hx,hy⟩)⟩
  | cons c p ih =>
    have hac : a.paletteRank ≤ c.paletteRank :=
      hw.palette_rank_head_le hp (by simp)
    have hwt : Survives S d (c :: p ++ [b]) := hw.infix ⟨[a],[],by simp⟩
    have hpt : ∀ v ∈ c :: p ++ [b], v.isPalette := fun v hv => hp v (List.mem_cons_of_mem a hv)
    have hcb : c.paletteRank ≤ b.paletteRank :=
      hwt.palette_rank_head_le hpt (by simp)
    have hac' : a.paletteRank = c.paletteRank := by omega
    have hab : Pair a c := hw.pair ⟨[],p++[b],by simp⟩
    have ha := hp a (by simp)
    have hcp := hp c (by simp)
    obtain ⟨he,hf,hf'⟩ := palette_equal_rank ha hcp
      (hw.format (by simp)) (hw.format (by simp)) hab hac'
    have hrep := replacement_swap_of_same_fields ha hcp
      (hw.format (by simp)) (hw.format (by simp)) he hf hf'
    have hstep : Step S d (a :: c :: p ++ [b]) (c :: a :: p ++ [b]) :=
      ⟨[],p++[b],[a,c],[c,a],by simp,by simp,hrep⟩
    have hnew := hw.of_reach (Relation.ReflTransGen.single hstep)
    apply ih (hnew.infix ⟨[c],[],by simp⟩)
    intro v hv
    apply hp v
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hv ⊢
    tauto

namespace Cell
def paletteSignature (c : Cell q) : Fin 6 × Fin q :=
  (⟨c.paletteRank,c.paletteRank_lt⟩,c.color)

omit [NeZero q] in
lemma paletteRank_setColor (c : Cell q) (x : Fin q) :
    (c.setColor x).paletteRank = c.paletteRank := rfl

lemma paletteRank_eq_of_eraseColor_eq {a b : Cell q} (he : a.eraseColor = b.eraseColor) :
    a.paletteRank = b.paletteRank := by
  simpa only [eraseColor,paletteRank_setColor] using congrArg paletteRank he
end Cell

theorem eligible_run_distinct {w : List (Cell q)} (hw : Survives S d w)
    (hp : ∀ a ∈ w, a.isPalette)
    (he : ∀ a ∈ w, ∀ b ∈ w, a.eraseColor = b.eraseColor) : (w.map Cell.color).Nodup := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih (hw.infix ⟨[a],[],by simp⟩)
      (fun c hc => hp c (List.mem_cons_of_mem a hc))
      (fun c hc e he' => he c (List.mem_cons_of_mem a hc) e (List.mem_cons_of_mem a he'))⟩
    intro hh
    obtain ⟨b,hb,hc⟩ := List.mem_map.mp hh
    have hr := Cell.paletteRank_eq_of_eraseColor_eq (he a (by simp) b (by simp [hb]))
    obtain ⟨p,s,rfl⟩ := List.append_of_mem hb
    have hs : Survives S d (a :: p ++ [b]) := hw.infix ⟨[],s,by simp [List.append_assoc]⟩
    apply hs.palette_no_collision p _ hr hc.symm
    intro c hc
    apply hp c
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hc ⊢
    tauto

namespace Cell

def Cut (c : Cell q) : Prop :=
  c.pos = .core 0 ∧ (c.marker = .idle ∨ c.metadata.block.val = 0)

def blockRank (c : Cell q) : ℕ := if c.marker = .idle then 10 else c.metadata.block.val

def geometryRank (c : Cell q) : ℕ := (q+2)*c.blockRank + c.positionRank

lemma cut_of_first {c : Cell q} (hf : c.skeleton.first) : c.Cut := by
  rcases hf with ⟨hb,p,hp,hv⟩
  have hp0 : p = 0 := Fin.ext hv
  exact ⟨hp0 ▸ hp,Or.inr hb⟩

omit [NeZero q] in
lemma blockRank_lt (c : Cell q) : c.blockRank < 11 := by
  have h₁ := c.metadata.arity.isLt
  have h₂ := c.metadata.block.isLt
  unfold blockRank
  split_ifs <;> omega

omit [NeZero q] in
lemma blockRank_lt_ten {c : Cell q} (h : c.marker ≠ .idle) : c.blockRank < 10 := by
  have h₁ := c.metadata.arity.isLt
  have h₂ := c.metadata.block.isLt
  simp only [blockRank,ite_eq_right h]
  omega

omit [NeZero q] in
lemma positionRank_lt (c : Cell q) : c.positionRank < q+2 := by
  unfold positionRank
  cases c.pos with
  | core p => have := p.isLt; dsimp only; omega
  | palette a => dsimp only; omega
  | stop => dsimp only; omega

end Cell

lemma pair_noCut_external_idle {b : Cell q} (hb : ¬b.Cut)
    (he : b.skeleton.leftExternal) : b.marker = .idle := by
  rcases he with he | ⟨_,he⟩
  · exact he
  · exact (hb (Cell.cut_of_first he)).elim

omit [NeZero q] in
lemma pair_internal_nonidle {a b : Cell q}
    (ha : ¬a.skeleton.rightExternal) (hb : ¬b.skeleton.leftExternal) :
    a.marker ≠ .idle ∧ b.marker ≠ .idle := by
  constructor
  · intro h; exact ha (Or.inl h)
  · intro h; exact hb (Or.inl h)

lemma pair_noCut_blockRank {a b : Cell q} (hp : Pair a b) (hb : ¬b.Cut) :
    a.blockRank ≤ b.blockRank := by
  rcases hp.1.2 with he | hi
  · have hb' := pair_noCut_external_idle hb he.2
    have := a.blockRank_lt
    simp only [Cell.blockRank,hb',ite_eq_left] at *
    omega
  · obtain ⟨ha',hb'⟩ := pair_internal_nonidle hi.1 hi.2.1
    have hbl := hi.2.2.2.2.2.2.1
    simp only [Cell.blockRank,ite_eq_right ha',ite_eq_right hb',Cell.metadata]
    split_ifs at hbl <;> omega

lemma pair_noCut_stop_core {a b : Cell q} {p : Fin q} (hp : Pair a b) (hb : ¬b.Cut)
    (ha : a.pos = .stop) (hpos : b.pos = .core p) : a.blockRank < b.blockRank := by
  have hp0 : p=0 := by
    have hh := hp.1.1
    change a.skeleton.pos = .stop at ha
    change b.skeleton.pos = .core p at hpos
    simp only [Structural,ha,hpos] at hh
    exact Fin.ext hh
  rcases hp.1.2 with he | hi
  · have hb' := pair_noCut_external_idle hb he.2
    exact (hb ⟨hp0 ▸ hpos,Or.inl hb'⟩).elim
  · obtain ⟨ha',hb'⟩ := pair_internal_nonidle hi.1 hi.2.1
    have hbl := hi.2.2.2.2.2.2.1
    change a.skeleton.pos = .stop at ha
    simp only [ha,ite_eq_left] at hbl
    simp only [Cell.blockRank,ite_eq_right ha',ite_eq_right hb',Cell.metadata]
    omega

lemma pair_noCut_geometry {a b : Cell q} (hp : Pair a b) (hb : ¬b.Cut) :
    a.geometryRank ≤ b.geometryRank ∧
      (a.geometryRank = b.geometryRank → a.isPalette ∧ b.isPalette) := by
  have hr := pair_noCut_blockRank hp hb
  have haL := a.positionRank_lt
  have hbL := b.positionRank_lt
  by_cases hlt : a.blockRank < b.blockRank
  · have hh : a.geometryRank < b.geometryRank := by
      unfold Cell.geometryRank; nlinarith
    exact ⟨hh.le,fun he => (Nat.ne_of_lt hh he).elim⟩
  have heq : a.blockRank = b.blockRank := by omega
  have hstr := hp.1.1
  generalize hpa : a.pos = pa
  generalize hpb : b.pos = pb
  change (match a.pos,b.pos with
    | .core p,.core r => p.val+1=r.val
    | .core p,.palette _ => p.val+1=q
    | .palette _,.palette _ => True
    | .palette _,.stop => True
    | .stop,.core r => r.val=0
    | _,_ => False) at hstr
  rw [hpa,hpb] at hstr
  cases pa <;> cases pb <;> simp only at hstr
  · simp only [Cell.geometryRank,Cell.positionRank,hpa,hpb,heq]
    omega
  · simp only [Cell.geometryRank,Cell.positionRank,hpa,hpb,heq]
    omega
  · exact ⟨by simp [Cell.geometryRank,Cell.positionRank,hpa,hpb,heq],
      fun _ => ⟨⟨_,hpa⟩,⟨_,hpb⟩⟩⟩
  · simp only [Cell.geometryRank,Cell.positionRank,hpa,hpb,heq]
    omega
  · have hh := pair_noCut_stop_core hp hb hpa hpb
    omega

lemma Survives.geometry_rank_chain {w : List (Cell q)} (hw : Survives S d w)
    (hn : ∀ a ∈ w, ¬a.Cut) : (w.map Cell.geometryRank).IsChain (· ≤ ·) := by
  exact (List.isChain_map Cell.geometryRank).mpr (hw.chain.imp_of_mem_imp (by
    intro a b ha hb hab
    exact (pair_noCut_geometry hab (hn b hb)).1))

lemma Survives.geometry_rank_head_le {a b : Cell q} {w : List (Cell q)}
    (hw : Survives S d (a::w)) (hn : ∀ c ∈ a::w, ¬c.Cut) (hb : b∈w) :
    a.geometryRank ≤ b.geometryRank :=
  (hw.geometry_rank_chain hn).rel_cons (List.mem_map_of_mem hb)

lemma Survives.palette_of_geometry_collision {a b : Cell q} (p : List (Cell q))
    (hw : Survives S d (a::p++[b])) (hn : ∀ c ∈ a::p++[b], ¬c.Cut)
    (hr : a.geometryRank = b.geometryRank) : ∀ c ∈ a::p++[b], c.isPalette := by
  induction p generalizing a with
  | nil =>
    have hp := (pair_noCut_geometry (hw.pair ⟨[],[],by simp⟩) (hn b (by simp))).2 hr
    simpa only [List.nil_append,List.cons_append,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] using hp
  | cons c p ih =>
    have hac : a.geometryRank ≤ c.geometryRank := hw.geometry_rank_head_le hn (by simp)
    have hwt : Survives S d (c::p++[b]) := hw.infix ⟨[a],[],by simp⟩
    have hnt : ∀ v ∈ c::p++[b], ¬v.Cut := fun v hv => hn v (List.mem_cons_of_mem a hv)
    have hcb : c.geometryRank ≤ b.geometryRank := hwt.geometry_rank_head_le hnt (by simp)
    have hac' : a.geometryRank = c.geometryRank := by omega
    have hcb' : c.geometryRank = b.geometryRank := by omega
    have hp := (pair_noCut_geometry (hw.pair ⟨[],p++[b],by simp⟩) (hn c (by simp))).2 hac'
    have ht := ih (a := c) hwt hnt hcb'
    intro v hv
    change v∈a::(c::p++[b]) at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hp.1
    · exact ht v hv

namespace Cell

def geometrySignature (c : Cell q) : GeometrySignature q :=
  (⟨c.blockRank,c.blockRank_lt⟩,match c.pos with
  | .core p => .inl p
  | .palette _ => .inr (.inl c.paletteSignature)
  | .stop => .inr (.inr ()))

lemma geometrySignature_geometry (c : Cell q) :
    c.geometrySignature.geometry = c.geometryRank := by
  unfold geometrySignature GeometrySignature.geometry geometryRank positionRank
  cases c.pos <;> rfl

lemma geometryRank_eq_of_signature_eq {a b : Cell q} (he : a.geometrySignature=b.geometrySignature) :
    a.geometryRank=b.geometryRank := by
  simpa only [geometrySignature_geometry] using congrArg GeometrySignature.geometry he

lemma paletteSignature_eq_of_geometrySignature_eq {a b : Cell q}
    (ha : a.isPalette) (hb : b.isPalette) (he : a.geometrySignature=b.geometrySignature) :
    a.paletteSignature=b.paletteSignature := by
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hb
  have hh := congrArg Prod.snd he
  simpa only [geometrySignature,hx,hy,Sum.inr.injEq,Sum.inl.injEq] using hh
end Cell

lemma Survives.geometry_signature_nodup {w : List (Cell q)} (hw : Survives S d w)
    (hn : ∀ c ∈ w, ¬c.Cut) : (w.map Cell.geometrySignature).Nodup := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih (hw.infix ⟨[a],[],by simp⟩)
      (fun c hc => hn c (List.mem_cons_of_mem a hc))⟩
    intro hh
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hh
    have hr := Cell.geometryRank_eq_of_signature_eq he.symm
    obtain ⟨p,s,rfl⟩ := List.append_of_mem hb
    have hs : Survives S d (a::p++[b]) := hw.infix ⟨[],s,by simp [List.append_assoc]⟩
    have hn' : ∀ c ∈ a::p++[b], ¬c.Cut := by
      intro c hc
      apply hn c
      simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hc ⊢
      tauto
    have hp := hs.palette_of_geometry_collision p hn' hr
    have hpSig := Cell.paletteSignature_eq_of_geometrySignature_eq
      (hp a (by simp)) (hp b (by simp)) he.symm
    have hrr := congrArg (fun x : Fin 6 × Fin q => x.1.val) hpSig
    have hcc := congrArg (fun x : Fin 6 × Fin q => x.2) hpSig
    exact hs.palette_no_collision p hp hrr hcc

lemma Survives.cut_free_length {w : List (Cell q)} (hw : Survives S d w)
    (hn : ∀ c ∈ w, ¬c.Cut) : w.length ≤ 77*q+11 := by
  have hh := (hw.geometry_signature_nodup hn).length_le_card
  simp only [List.length_map,Cell.GeometrySignature,Fintype.card_prod,Fintype.card_sum,
    Fintype.card_fin,Fintype.card_unit] at hh
  calc
    w.length ≤ 11*(q+(6*q+1)) := hh
    _ = 77*q+11 := by ring

theorem cut_free_fragment_bound {w : List (Cell q)} (hw : Survives S d w)
    (hn : ∀ c ∈ w.tail, ¬c.Cut) : w.length ≤ (10+2)*(17*q+3) := by
  cases w with
  | nil => simp
  | cons a w =>
    have hwt := hw.infix (show w <:+: a::w from ⟨[a],[],by simp⟩)
    have hh := hwt.cut_free_length hn
    simp only [List.length_cons]
    omega

lemma canonicalCell_format (bits : Fin d → ZMod 2) (p : Position q) :
    (canonicalCell bits p).Format S d := by
  cases p with
  | core r =>
    simp [Cell.Format,canonicalCell,Cell.pos,Cell.marker,Cell.metadata,Cell.isPalette,
      Cell.isCore,Skeleton.Admissible,Skeleton.IsHead]
    intro hd
    funext side
    simp [Nat.not_lt_of_ge hd]
  | palette x =>
    simp [Cell.Format,canonicalCell,Cell.pos,Cell.marker,Cell.metadata,Cell.isPalette,
      Cell.isCore,Skeleton.Admissible,Skeleton.IsHead]
    rfl
  | stop =>
    simp [Cell.Format,canonicalCell,Cell.pos,Cell.marker,Cell.metadata,Cell.isPalette,
      Cell.isCore,Skeleton.Admissible,Skeleton.IsHead]
    rfl

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_BoundaryCell
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAdmissible _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideEndpoint _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHead _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideInternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLastOK _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLeftExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalettePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideRightExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideStructural _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q]
namespace Cell
lemma idle_format (c : Cell q) (S : Schedule q) (s : Bool) (hc : c.PayloadFormat d) :
    (c.idle s).Format S d := by
  dsimp [PayloadFormat,Cell.isPalette,Cell.isCore,Cell.pos] at hc
  simp only [Format,idle,marker,metadata,pos,isPalette,isCore,Skeleton.Admissible,
    Skeleton.IsHead]
  simp only [reduceCtorEq,false_implies,or_self,and_true,true_implies,true_and]
  refine ⟨hc.1,?_,?_,rfl⟩
  · intro p hp hd
    have he := hc.2.1 p hp hd
    funext b
    simp [he]
  · intro hp
    have he := (hc.2.2 hp).1
    exact (by funext b; simp [he])

lemma boundary_format (c : Cell q) (S : Schedule q) (s : Bool) (hc : c.PayloadFormat d)
    (hs : c.metadata.zeroTask=true → s=false) : (c.boundary s).Format S d := by
  dsimp [PayloadFormat,Cell.isPalette,Cell.isCore,Cell.pos] at hc
  simp only [Format,boundary,marker,metadata,pos,isPalette,isCore,Skeleton.Admissible,
    Skeleton.IsHead,Skeleton.mark]
  simpa only [reduceCtorEq,false_implies,true_implies,or_true,true_or,and_true,true_and,
    implies_true,defaultHead,false_or] using ⟨hc.1,hc.2.1,hc.2.2,hs⟩
end Cell

namespace Region
variable (R : Region q d) (S : Schedule q)

def boundaryCell (cursor : Fin R.size) (s : Bool) (i : Fin R.size) : Cell q :=
  if i < cursor then (R.cell i).wing .left else
    if i=cursor then (R.cell i).boundary s else (R.cell i).idle s

def boundaryWord (cursor : Fin R.size) (s : Bool) : List (Cell q) :=
  List.ofFn (R.boundaryCell cursor s)

def idleWord (s : Bool) : List (Cell q) := List.ofFn (fun i => (R.cell i).idle s)

lemma boundaryCell_format (cursor : Fin R.size) (s : Bool)
    (hs : R.task.zeroTask=true → s=false) (i : Fin R.size) :
    (R.boundaryCell cursor s i).Format S d := by
  unfold boundaryCell
  split
  · rename_i hi
    let state : HeadTour.FullState (S.count R.task).val R.size :=
      HeadTour.atClause (R.plan S).first ⟨.readLeft cursor,0,s⟩
    have hh := R.realizeCell_format S state hs i
    simpa [state,realizeCell,position,controlPosition,HeadTour.atClause,hi] using hh
  · split
    · apply Cell.boundary_format _ S s (R.payload_format i)
      intro ht
      exact hs ((congrArg Task.zeroTask (R.task_eq i)).symm.trans ht)
    · exact Cell.idle_format _ S s (R.payload_format i)

lemma boundaryCell_cursor (cursor : Fin R.size) (s : Bool) :
    R.boundaryCell cursor s cursor=(R.cell cursor).boundary s := by simp [boundaryCell]

omit [NeZero q] in
lemma acquisition_pair (i j : Fin R.size) (hij : i.val+1=j.val) :
    Skeleton.Pair ((R.cell i).skeleton.mark .left) ((R.cell j).skeleton.mark .boundary) := by
  obtain ⟨hstr,hi⟩ := R.adjacent i j hij
  refine ⟨hstr,Or.inr ?_⟩
  simp only [Skeleton.rightExternal,Skeleton.leftExternal,Skeleton.mark_marker,
    Skeleton.mark_last,Skeleton.mark_first,Skeleton.acceptsRight,Skeleton.acceptsLeft,
    Skeleton.internal_mark_left,Skeleton.internal_mark_right]
  simpa using And.intro hi.2.2.2.1 hi

lemma release_step (i j : Fin R.size) (hij : i.val+1=j.val) (s : Bool)
    (hs : R.task.zeroTask=true → s=false) :
    Step S d (R.boundaryWord j s) (R.boundaryWord i s) := by
  unfold boundaryWord
  apply step_two_ofFn _ _ i j hij
  · intro z hzi hzj
    have hi : z < i ↔ z < j := by
      have hzine : z.val≠i.val := fun h => hzi (Fin.ext h)
      have hzjne : z.val≠j.val := fun h => hzj (Fin.ext h)
      simp only [Fin.lt_def]
      omega
    simp only [boundaryCell,hi,hzi,hzj,ite_false]
  · have hij' : i < j := by simp only [Fin.lt_def]; omega
    have hji : ¬ j < i := by omega
    have hne : j≠i := by omega
    refine ⟨?_,Or.inr ⟨_,_,_,_,rfl,rfl,Or.inr ?_⟩⟩
    · intro c hc
      simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl <;> apply R.boundaryCell_format S _ s hs
    · simpa only [boundaryCell,hij',hji,hne,ne_eq,hne,ite_true,ite_false,lt_self_iff_false]
        using Binary.acquire (S:=S) (R.cell i) (R.cell j) s (R.acquisition_pair i j hij)

lemma remove_first (s : Bool) (hs : R.task.zeroTask=true → s=false) :
    Step S d (R.boundaryWord R.first s) (R.idleWord s) := by
  unfold boundaryWord idleWord
  apply step_one_ofFn _ _ R.first
  · intro i hi
    have hlt : ¬ i < R.first := by change ¬ i.val < 0; omega
    simp [boundaryCell,hlt,hi]
  · refine ⟨?_,Or.inl ⟨_,_,rfl,rfl,Or.inr ?_⟩⟩
    · intro c hc
      simp only [List.singleton_append,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl
      · exact R.boundaryCell_format S _ s hs _
      · exact Cell.idle_format _ S s (R.payload_format _)
    · rw [R.boundaryCell_cursor]
      exact Unary.create _ _ R.first_first

theorem release (cursor : Fin R.size) (s : Bool) (hs : R.task.zeroTask=true → s=false) :
    Reach S d (R.boundaryWord cursor s) (R.idleWord s) := by
  generalize he : cursor.val=n
  induction n generalizing cursor with
  | zero =>
    have hx : cursor=R.first := Fin.ext he
    subst cursor
    exact Relation.ReflTransGen.single (R.remove_first S s hs)
  | succ n ih =>
    let i : Fin R.size := ⟨n,by omega⟩
    have he' : i.val+1=cursor.val := by dsimp [i]; omega
    exact (Relation.ReflTransGen.single (R.release_step S i cursor he' s hs)).trans
      (ih i rfl)

lemma unfinish (s : Bool) (hs : R.task.zeroTask=true → s=false) :
    Step S d (R.realize S (HeadTour.atClause (R.plan S).first ⟨.acquisition,0,s⟩))
      (R.boundaryWord R.last s) := by
  unfold realize boundaryWord
  apply step_one_ofFn _ _ R.last
  · intro i hi
    have hil : i<R.last := by
      have hh := i.isLt
      have hn : i.val≠R.last.val := fun h => hi (Fin.ext h)
      dsimp [last] at *
      exact show i.val<R.size-1 by omega
    simp [realizeCell,position,controlPosition,HeadTour.atClause,boundaryCell,hil]
  · refine ⟨?_,Or.inl ⟨_,_,rfl,rfl,Or.inr ?_⟩⟩
    · intro c hc
      simp only [List.singleton_append,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl
      · exact R.realizeCell_format S _ hs _
      · exact R.boundaryCell_format S _ s hs _
    · rw [R.boundaryCell_cursor]
      simpa [realizeCell,position,controlPosition,HeadTour.atClause,phase,controlPhase,
        clause,clauseIndex,HeadTour.Plan.first]
        using Unary.finish_acquisition (S:=S) (R.cell R.last) s R.last_last

theorem literal_rollback_release (s : HeadTour.FullState (S.count R.task).val R.size)
    (hs : R.SideOK S s) :
    Reach S d (R.realize S s) (R.idleWord s.side) ∨
      ∃ w p a z, Reach S d (R.realize S s) w ∧ w=p++[a]++z ∧ Zero S d [a] := by
  rcases R.literal_rollback S s hs with hh | hz
  · left
    exact hh.trans ((Relation.ReflTransGen.single (R.unfinish S s.side hs)).trans
      (R.release S R.last s.side hs))
  · exact Or.inr hz

def actualState (h : Fin R.size) (hf : (R.cell h).Format S d)
    (hm : (R.cell h).marker=.full) : HeadTour.FullState (S.count R.task).val R.size :=
  let c := R.cell h
  { ctrl := if hp : c.head.phase=.success then .success else
      let j : Fin (S.count R.task).val := ⟨c.head.clause.val,by
        have hb := (hf.2.2.2.2.2.2.2.2 hm).2.1 hp
        rwa [R.task_eq h] at hb⟩
      .clause j (match c.head.phase with
        | .acquisition => .acquisition
        | .readLeft => .readLeft h
        | .readRight => .readRight h
        | .beforeGate => .beforeGate
        | .afterGate => .afterGate
        | .undoLeft => .undoLeft h
        | .undoRight => .undoRight h
        | .finish => .finish
        | .success => .finish)
    reg := c.head.reg
    side := c.head.side }

lemma actualState_side (h : Fin R.size) (hf : (R.cell h).Format S d)
    (hm : (R.cell h).marker=.full) :
    R.SideOK S (R.actualState S h hf hm) := by
  intro ht
  apply hf.2.2.2.2.2.2.2.1 (Or.inr hm)
  exact (congrArg Task.zeroTask (R.task_eq h)).trans ht

lemma actualState_position (h : Fin R.size) (hf : (R.cell h).Format S d)
    (hm : (R.cell h).marker=.full) :
    R.position S (R.actualState S h hf hm)=h := by
  have hend : Cell.endpoint (R.cell h).head.phase → R.last=h := by
    intro he
    have hh := (R.last_iff h).mp ((hf.2.2.2.2.2.2.2.2 hm).2.2 he)
    apply Fin.ext
    dsimp [last]
    omega
  cases hp : (R.cell h).head.phase <;>
    simp_all [actualState,position,controlPosition,Cell.endpoint]

lemma actualState_phase (h : Fin R.size) (hf : (R.cell h).Format S d)
    (hm : (R.cell h).marker=.full) :
    R.phase S (R.actualState S h hf hm)=(R.cell h).head.phase := by
  cases hp : (R.cell h).head.phase <;> simp [actualState,hp,phase,controlPhase]

lemma actualState_clause (h : Fin R.size) (hf : (R.cell h).Format S d)
    (hm : (R.cell h).marker=.full) :
    R.clause S (R.actualState S h hf hm)=(R.cell h).head.clause := by
  by_cases hp : (R.cell h).head.phase=.success
  · simp only [actualState,hp,dite_eq_left,clause]
    exact ((hf.2.2.2.2.2.2.2.2 hm).1 hp).symm
  · simp [actualState,hp,clause,clauseIndex]

lemma actualState_realize (h : Fin R.size) (hf : ∀ i, (R.cell i).Format S d)
    (hm : (R.cell h).marker=.full)
    (hl : ∀ i < h, (R.cell i).marker=.left) (hr : ∀ i, h < i → (R.cell i).marker=.right) :
    R.realize S (R.actualState S h (hf h) hm)=List.ofFn R.cell := by
  unfold realize
  apply congrArg List.ofFn
  funext i
  simp only [realizeCell,R.actualState_position S h (hf h) hm]
  split
  · rename_i hi
    have hmi := hl i hi
    have hh := (hf i).2.2.2.2.2.1 (Or.inl hmi)
    cases he : R.cell i with
    | mk sk ch da ce hd =>
      cases sk
      simp_all [Cell.marker,Cell.wing,Skeleton.mark]
  · rename_i hi
    split
    · rename_i hi'
      have hmi := hr i hi'
      have hh := (hf i).2.2.2.2.2.1 (Or.inr hmi)
      cases he : R.cell i with
      | mk sk ch da ce hd =>
        cases sk
        simp_all [Cell.marker,Cell.wing,Skeleton.mark]
    · rename_i hi'
      have hei : i=h := Fin.ext (by omega)
      subst i
      rw [R.actualState_clause,R.actualState_phase]
      change (R.cell h).full (R.cell h).head.side (R.cell h).head.clause
        (R.cell h).head.phase (R.cell h).head.reg=R.cell h
      cases he : R.cell h with
      | mk sk ch da ce hd =>
        cases sk
        cases hd
        simp_all [Cell.marker,Cell.full,Skeleton.mark]

theorem actual_rollback_release (h : Fin R.size) (hf : ∀ i, (R.cell i).Format S d)
    (hm : (R.cell h).marker=.full)
    (hl : ∀ i < h, (R.cell i).marker=.left) (hr : ∀ i, h < i → (R.cell i).marker=.right) :
    Reach S d (List.ofFn R.cell) (R.idleWord (R.cell h).head.side) ∨
      ∃ w p a z, Reach S d (List.ofFn R.cell) w ∧ w=p++[a]++z ∧ Zero S d [a] := by
  have hh := R.literal_rollback_release S (R.actualState S h (hf h) hm)
    (R.actualState_side S h (hf h) hm)
  rwa [R.actualState_realize S h hf hm hl hr] at hh

end Region
end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q d N : ℕ} [NeZero q] {S : Schedule q}

omit [NeZero q] in
lemma Coherent.left_wing {f : Fin N → Cell q} (hf : Coherent f) {i h : Fin N}
    (hh : (f h).skeleton.IsHead) (hih : i.val<h.val) (hc : SameRegion f i h) :
    (f i).marker=.left := by
  cases hm : (f i).marker with
  | left => rfl
  | idle => exact (hf.region_locked hh hc hm).elim
  | boundary => exact (hc.right_barrier hih (Or.inr (Or.inl hm))).elim
  | full =>
    have he := hf.unique_head (Or.inr hm) hh hc
    have := congrArg Fin.val he
    omega
  | right =>
    have he := hf.right_wing (Or.inr hm) hih hc
    rcases hh with hh | hh
    · change (f h).marker=.boundary at hh
      rw [he] at hh
      cases hh
    · change (f h).marker=.full at hh
      rw [he] at hh
      cases hh

namespace Component
variable (f : Fin N → Cell q) (i : Fin N)
noncomputable def headIndex : Fin (size f i) :=
  ⟨i.val-(left f i).val,by
    have := left_le_self f i
    have := self_le_right f i
    dsimp [size]
    omega⟩
omit [NeZero q] in
lemma offset_headIndex : offset f i (headIndex f i)=i := by
  apply Fin.ext
  have := left_le_self f i
  dsimp [offset,headIndex]
  omega

omit [NeZero q] in
lemma before_head (hf : Coherent f) (hi : (f i).skeleton.IsHead)
    (j : Fin (size f i)) (hj : j<headIndex f i) : (f (offset f i j)).marker=.left := by
  apply hf.left_wing hi _ (connected_offset f i j).symm
  have := left_le_self f i
  change j.val < i.val-(left f i).val at hj
  change (left f i).val + j.val < i.val
  omega

omit [NeZero q] in
lemma after_head (hf : Coherent f) (hi : (f i).marker=.full)
    (j : Fin (size f i)) (hj : headIndex f i<j) : (f (offset f i j)).marker=.right := by
  apply hf.right_wing (Or.inl hi) _ (connected_offset f i j)
  have := left_le_self f i
  change i.val-(left f i).val < j.val at hj
  change i.val < (left f i).val + j.val
  omega

theorem actual_rollback_release (hs : Syntax S d (List.ofFn f)) (hi : (f i).marker=.full) :
    Reach S d (List.ofFn (region f i hs hi).cell)
      ((region f i hs hi).idleWord (f i).head.side) ∨
      ∃ w p a z, Reach S d (List.ofFn (region f i hs hi).cell) w ∧
        w=p++[a]++z ∧ Zero S d [a] := by
  have hm : ((region f i hs hi).cell (headIndex f i)).marker=.full := by
    change (f (offset f i (headIndex f i))).marker=.full
    rw [offset_headIndex]
    exact hi
  have hh := (region f i hs hi).actual_rollback_release S (headIndex f i)
    (fun j => hs.2.2 _ (List.mem_ofFn.mpr ⟨offset f i j,rfl⟩)) hm
    (before_head f i (Verification.coherent_of_syntax S hs) (Or.inr hi))
    (after_head f i (Verification.coherent_of_syntax S hs) hi)
  have he : (region f i hs hi).cell (headIndex f i)=f i := by
    change f (offset f i (headIndex f i))=f i
    rw [offset_headIndex]
  rwa [he] at hh

end Component
end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q] {S : Schedule q}
namespace Cell
lemma setChecker_format (c : Cell q) (a : Palette.Check (Fin q)) (hp : c.isPalette) :
    (c.setChecker a).Format S d ↔ c.Format S d := by
  simp [Format,setChecker,isPalette,isCore,pos,marker,metadata] at hp ⊢
  obtain ⟨x,hx⟩ := hp
  simp [hx]
end Cell

omit [NeZero q] in
lemma checkerIdle_eq {w : List (Cell q)} (h : ∀ a∈w, a.checker=.idle) : checkerIdle w=w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [checkerIdle_cons,←h a (by simp),Cell.setChecker_self,ih]
    exact fun b hb => h b (by simp [hb])

lemma checker_create_step (a b : Cell q) (p x : Fin q) (ha : a.pos=.core p)
    (hp : p.val+1=q) (hb : b.isPalette) (hfa : a.Format S d) (hfb : b.Format S d) :
    Step S d [a,b.setChecker .idle] [a,b.setChecker (.head x)] := by
  refine ⟨[],[],[a,b.setChecker .idle],[a,b.setChecker (.head x)],rfl,rfl,?_,Or.inr ⟨_,_,_,_,rfl,rfl,Or.inl ?_⟩⟩
  · intro c hc
    simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl
    · exact hfa
    · exact (b.setChecker_format _ hb).mpr hfb
    · exact hfa
    · exact (b.setChecker_format _ hb).mpr hfb
  · exact Binary.checker_create a b p x ha hp hb

lemma checker_advance_step (a b : Cell q) (x : Fin q) (ha : a.isPalette)
    (hb : b.isPalette) (hn : a.color≠x) (hfa : a.Format S d) (hfb : b.Format S d) :
    Step S d [a.setChecker (.head x),b.setChecker .idle]
      [a.setChecker (.passed x),b.setChecker (.head x)] := by
  obtain ⟨v,hv⟩ := ha
  refine ⟨[],[],[a.setChecker (.head x),b.setChecker .idle],
    [a.setChecker (.passed x),b.setChecker (.head x)],rfl,rfl,?_,
    Or.inr ⟨_,_,_,_,rfl,rfl,Or.inl ?_⟩⟩
  · intro c hc
    simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl
    · exact (a.setChecker_format _ ⟨v,hv⟩).mpr hfa
    · exact (b.setChecker_format _ hb).mpr hfb
    · exact (a.setChecker_format _ ⟨v,hv⟩).mpr hfa
    · exact (b.setChecker_format _ hb).mpr hfb
  · exact Binary.checker_advance a b v x hv hb (by simpa [Cell.color,hv] using hn)

lemma checker_rollback_head (c : Cell q) (p : List (Cell q)) (a : Cell q)
    (s : List (Cell q)) (x t : Fin q) (hc : c.pos=.core t) (ht : t.val+1=q)
    (hfc : c.Format S d)
    (hf : ∀ b∈p++a::s, b.Format S d) (hpal : ∀ b∈p++a::s, b.isPalette)
    (hp : ∀ b∈p, b.checker=.passed x) (hn : ∀ b∈p, b.color≠x)
    (hs : ∀ b∈s, b.checker=.idle) :
    Reach S d (c::(p++a.setChecker (.head x)::s)) (c::checkerIdle (p++a::s)) := by
  induction p using List.reverseRecOn generalizing a s with
  | nil =>
    have st := step_symm (checker_create_step c a t x hc ht
      (hpal a (by simp)) hfc (hf a (by simp)))
    have he := step_context st [] s
    simpa only [List.nil_append,List.cons_append,List.nil_append,checkerIdle_cons,
      checkerIdle_eq hs] using Relation.ReflTransGen.single he
  | append_singleton p b ih =>
    have hb := hp b (by simp)
    have hb' := hn b (by simp)
    have hpb : b.isPalette := hpal b (by simp)
    have hpa : a.isPalette := hpal a (by simp)
    have hfb : b.Format S d := hf b (by simp)
    have hfa : a.Format S d := hf a (by simp)
    have hbp : b.setChecker (.passed x)=b := by rw [←hb,Cell.setChecker_self]
    have st := step_context (step_symm (checker_advance_step b a x hpb hpa hb' hfb hfa))
      (c::p) s
    have rest := ih b (a.setChecker .idle::s)
      (by intro z hz; simp only [List.mem_append,List.mem_cons] at hz; rcases hz with hz|rfl|hz
          · exact hf z (by simp [hz])
          · exact hfb
          · rcases hz with rfl|hz
            · exact (a.setChecker_format _ hpa).mpr hfa
            · exact hf z (by simp [hz]))
      (by intro z hz; simp only [List.mem_append,List.mem_cons] at hz; rcases hz with hz|rfl|hz
          · exact hpal z (by simp [hz])
          · exact hpb
          · rcases hz with rfl|hz
            · exact hpa
            · exact hpal z (by simp [hz]))
      (fun z hz => hp z (by simp [hz])) (fun z hz => hn z (by simp [hz]))
      (by simp only [List.forall_mem_cons,Cell.setChecker_checker]; exact ⟨True.intro,hs⟩)
    have he : checkerIdle (p++b::a.setChecker .idle::s)=checkerIdle ((p++[b])++a::s) := by
      simp [List.append_assoc]
    rw [he] at rest
    apply Relation.ReflTransGen.head _ rest
    simpa only [List.cons_append,List.append_assoc,List.nil_append,hbp] using st

def asChecker (c : Cell q) : Palette.Cell (Fin q) (Cell q) := ⟨c.color,c.checker,c⟩
lemma checker_pattern (w : List (Cell q))
    (hc : w.IsChain (fun a b => Palette.Pair a.checker b.checker))
    (hl : ∀ a∈w.getLast?, Palette.LastOK a.checker) :
    (∀ a∈w, a.checker=.idle) ∨
    ∃ p a s x, w=p++a::s ∧ a.checker=.head x ∧
      (∀ b∈p, b.checker=.passed x) ∧ (∀ b∈s, b.checker=.idle) := by
  have ht : Palette.Syntax (w.map asChecker) := by
    constructor
    · simpa [List.isChain_map,asChecker] using hc
    · intro a ha
      simp only [List.getLast?_map,Option.mem_def,Option.map_eq_some_iff] at ha
      obtain ⟨b,hb,rfl⟩ := ha
      exact hl b hb
  have hcheck : ∀ a∈w.map asChecker, a.aux.checker=a.check := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    rfl
  rcases Palette.syntax_form (w.map asChecker) ht with hi|⟨p,a,s,x,he,ha,hp,hs⟩
  · left; intro a ha
    exact hi (asChecker a) (List.mem_map.mpr ⟨a,ha,rfl⟩)
  · have he' := congrArg (List.map Palette.Cell.aux) he
    simp only [List.map_map,Function.comp_def,asChecker,List.map_append,
      List.map_cons] at he'
    have he'' : w=p.map Palette.Cell.aux++a.aux::s.map Palette.Cell.aux := by simpa using he'
    refine Or.inr ⟨p.map Palette.Cell.aux,a.aux,s.map Palette.Cell.aux,x,he'',?_,?_,?_⟩
    · rw [hcheck a (by rw[he]; simp),ha]
    · intro b hb
      obtain ⟨e,he',rfl⟩ := List.mem_map.mp hb
      exact (hcheck e (by rw[he]; simp [he'])).trans (hp e he')
    · intro b hb
      obtain ⟨e,he',rfl⟩ := List.mem_map.mp hb
      exact (hcheck e (by rw[he]; simp [he'])).trans (hs e he')

theorem Survives.checker_rollback {c z : Cell q} {w : List (Cell q)} {t : Fin q}
    (hw : Survives S d (c::w++[z])) (hc : c.pos=.core t) (ht : t.val+1=q)
    (hz : z.pos=.stop) (hp : ∀ a∈w, a.isPalette) :
    Reach S d (c::w++[z]) (c::checkerIdle w++[z]) := by
  have hv : Survives S d w := hw.infix ⟨[c],[z],rfl⟩
  have hchain : w.IsChain (fun a b => Palette.Pair a.checker b.checker) := by
    exact hv.chain.imp_of_mem_imp (fun a b ha hb hab => hab.2.1 ⟨hp a ha,hp b hb⟩)
  have hlast : ∀ a∈w.getLast?, Palette.LastOK a.checker := by
    intro a ha
    obtain ⟨p,rfl⟩ := List.getLast?_eq_some_iff.mp ha
    exact (hw.pair ⟨c::p,[],by simp⟩).2.2 ⟨hp a (by simp),hz⟩
  rcases checker_pattern w hchain hlast with hi|⟨p,a,s,x,rfl,ha,hp',hs⟩
  · rw [checkerIdle_eq hi]
  · have hn : ∀ b∈p, b.color≠x := by
      intro b hb he
      have hbx : b.pos=.palette x := by
        obtain ⟨y,hy⟩ := hp b (by simp [hb])
        have hyx : y=x := by simpa [Cell.color,hy] using he
        simpa [hyx] using hy
      have hzero : Zero S d [b] := Or.inl ⟨b,rfl,Or.inr (Or.inr ⟨x,hbx,hp' b hb⟩)⟩
      exact (hv.infix ((List.singleton_infix_iff _ _).mpr (by simp [hb]))).not_zero hzero
    have hh := checker_rollback_head c p a s x t hc ht
      (hw.format (by simp)) (fun b hb => hv.format hb) hp hp' hn hs
    have hea : a.setChecker (.head x)=a := by rw [←ha,Cell.setChecker_self]
    simpa only [List.nil_append,List.cons_append,hea] using reach_context hh [] [z]

lemma checker_seek_missing (c : Cell q) (p : List (Cell q)) (a : Cell q)
    (s : List (Cell q)) (z : Cell q) (x : Fin q) (hz : z.pos=.stop)
    (hf : ∀ b∈a::s, b.Format S d) (hp : ∀ b∈a::s, b.isPalette)
    (ha : a.color≠x) (hs : ∀ b∈s, b.checker=.idle) (hn : ∀ b∈s, b.color≠x) :
    ∃ v l u r, Reach S d (c::p++a.setChecker (.head x)::s++[z]) v ∧
      v=l++u++r ∧ Zero S d u := by
  induction s generalizing p a with
  | nil =>
    obtain ⟨y,hy⟩ := hp a (by simp)
    refine ⟨_,c::p,[a.setChecker (.head x),z],[],.refl,by simp,
      Or.inr ⟨a.setChecker (.head x),z,rfl,Or.inr (Or.inr ?_)⟩⟩
    exact ⟨y,x,hy,rfl,hz,by simpa [Cell.color,hy] using ha⟩
  | cons b s ih =>
    have hpb := hp b (by simp)
    have hpa := hp a (by simp)
    have hfb := hf b (by simp)
    have hfa := hf a (by simp)
    have hb : b.setChecker .idle=b := by rw [←hs b (by simp),Cell.setChecker_self]
    have st := step_context (checker_advance_step a b x hpa hpb ha hfa hfb) (c::p) (s++[z])
    obtain ⟨v,l,u,r,hr,he,hzero⟩ := ih (p++[a.setChecker (.passed x)]) b
      (fun e he => hf e (by simp [he])) (fun e he => hp e (by simp [he]))
      (hn b (by simp)) (fun e he => hs e (by simp [he])) (fun e he => hn e (by simp [he]))
    refine ⟨v,l,u,r,.head ?_ hr,he,hzero⟩
    simpa only [List.cons_append,List.nil_append,List.append_assoc,hb] using st

lemma Survives.idle_palette_all_colors {c z : Cell q} {w : List (Cell q)} {t : Fin q}
    (hw : Survives S d (c::w++[z])) (hc : c.pos=.core t) (ht : t.val+1=q)
    (hz : z.pos=.stop) (hwn : w≠[]) (hp : ∀ a∈w, a.isPalette)
    (hi : ∀ a∈w, a.checker=.idle) : ∀ x, x∈w.map Cell.color := by
  intro x
  by_contra hmiss
  have hn : ∀ a∈w, a.color≠x := by
    intro a ha hx
    exact hmiss (List.mem_map.mpr ⟨a,ha,hx⟩)
  cases w with
  | nil => exact hwn rfl
  | cons a s =>
    have haa : a.setChecker .idle=a := by rw [←hi a (by simp),Cell.setChecker_self]
    have st := step_context (checker_create_step c a t x hc ht
      (hp a (by simp)) (hw.format (by simp)) (hw.format (by simp))) [] (s++[z])
    obtain ⟨v,l,u,r,hr,he,hzero⟩ := checker_seek_missing c [] a s z x hz
      (fun b hb => hw.format (by
        simp only [List.mem_cons] at hb
        simp only [List.mem_cons,List.mem_append]
        tauto)) hp (hn a (by simp))
      (fun b hb => hi b (by simp [hb])) (fun b hb => hn b (by simp [hb]))
    apply hw l u r _ hzero
    rw [←he]
    apply Relation.ReflTransGen.head _ hr
    simpa only [List.nil_append,List.cons_append,haa] using st

namespace Cell
lemma palette_idle_canonical (c : Cell q) (bits : Fin d → ZMod 2) (hc : c.Format S d)
    (hp : c.isPalette) (hm : c.marker=.idle) (hi : c.checker=.idle) :
    c=canonicalCell bits (.palette c.color) := by
  obtain ⟨x,hx⟩ := hp
  have hc' := hc.2.2.2.1 (by simp [isCore,hx])
  have hm' := hc.2.2.2.2.1 hm
  have hmeta := hm'.1
  have hhead := hm'.2.1
  have hd := hc'.1
  have hz := hc'.2
  have hsk : c.skeleton=⟨.palette x,.idle,defaultMeta⟩ := by
    cases c with
    | mk sk ch dat cert head => cases sk; simp_all [marker,pos,metadata]
  cases c with
  | mk sk ch dat cert head =>
    dsimp only [Cell.checker] at hi
    simp_all [canonicalCell,color,pos]
    rfl
end Cell

lemma canonical_palette_swap (bits : Fin d → ZMod 2) (a b : Fin q) :
    Replacement S d [canonicalCell bits (.palette a),canonicalCell bits (.palette b)]
      [canonicalCell bits (.palette b),canonicalCell bits (.palette a)] := by
  apply replacement_swap_of_same_fields
  · exact ⟨a,rfl⟩
  · exact ⟨b,rfl⟩
  · exact canonicalCell_format bits _
  · exact canonicalCell_format bits _
  · rfl
  · simp [Cell.HeadFree,canonicalCell,Skeleton.IsHead]
  · simp [Cell.HeadFree,canonicalCell,Skeleton.IsHead]

def canonicalPalette (bits : Fin d → ZMod 2) (w : List (Fin q)) : List (Cell q) :=
  w.map (fun x => canonicalCell bits (.palette x))

lemma canonicalPalette_perm (bits : Fin d → ZMod 2) {v w : List (Fin q)} (h : v.Perm w) :
    Reach S d (canonicalPalette bits v) (canonicalPalette bits w) := by
  induction h with
  | nil => exact .refl
  | cons a h ih =>
    simpa only [canonicalPalette,List.map_cons,List.singleton_append,List.append_nil] using
      reach_context ih [canonicalCell bits (.palette a)] []
  | swap a b w =>
    exact .single ⟨[],canonicalPalette bits w,
      [canonicalCell bits (.palette b),canonicalCell bits (.palette a)],
      [canonicalCell bits (.palette a),canonicalCell bits (.palette b)],rfl,rfl,
      canonical_palette_swap bits b a⟩
  | trans _ _ ih ih' => exact ih.trans ih'

theorem Survives.idle_palette_normalize {c z : Cell q} {w : List (Cell q)} {t : Fin q}
    (hw : Survives S d (c::w++[z])) (hc : c.pos=.core t) (ht : t.val+1=q)
    (hz : z.pos=.stop) (hwn : w≠[]) (hp : ∀ a∈w, a.isPalette)
    (hm : ∀ a∈w, a.marker=.idle) (hi : ∀ a∈w, a.checker=.idle)
    (bits : Fin d → ZMod 2) :
    w.length=q ∧ Reach S d w (canonicalPalette bits (List.finRange q)) := by
  have hv : Survives S d w := hw.infix ⟨[c],[z],rfl⟩
  have he : w=canonicalPalette bits (w.map Cell.color) := by
    unfold canonicalPalette
    rw [List.map_map]
    calc
      w = w.map id := (List.map_id w).symm
      _ = _ := List.map_congr_left (fun a ha =>
        a.palette_idle_canonical bits (hv.format ha) (hp a ha) (hm a ha) (hi a ha))
  have hfields : ∀ a∈w,∀ b∈w,a.eraseColor=b.eraseColor := by
    intro a ha b hb
    rw [a.palette_idle_canonical bits (hv.format ha) (hp a ha) (hm a ha) (hi a ha),
      b.palette_idle_canonical bits (hv.format hb) (hp b hb) (hm b hb) (hi b hb)]
    rfl
  have hnd := eligible_run_distinct hv hp hfields
  have hall := hw.idle_palette_all_colors hc ht hz hwn hp hi
  have hperm : (w.map Cell.color).Perm (List.finRange q) :=
    (List.perm_ext_iff_of_nodup hnd (List.nodup_finRange q)).mpr (by simp [hall])
  have hlen := hperm.length_eq
  refine ⟨by simpa using hlen,?_⟩
  rw [he]
  exact canonicalPalette_perm bits hperm
end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_PrefixRewriting
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAdmissible _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideEndpoint _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHead _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideInternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLastOK _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLeftExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalettePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideRightExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideStructural _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable
section
open LocalSyntax LocalSyntax.Skeleton
variable {q d N : ℕ} [NeZero q]
namespace Cell
lemma left_format (c : Cell q) (S : Schedule q) (hc : c.PayloadFormat d)
    (hl : ¬c.skeleton.last) : (c.wing .left).Format S d := by
  dsimp [PayloadFormat,Cell.isPalette,Cell.isCore,Cell.pos] at hc
  simp only [Format,wing,marker,metadata,pos,isPalette,isCore,Skeleton.Admissible,
    Skeleton.IsHead,Skeleton.mark]
  simpa only [reduceCtorEq,false_implies,true_implies,or_self,and_true,true_and,
    implies_true,defaultHead,Skeleton.last] using And.intro hl (And.intro hc.1 (And.intro hc.2.1 hc.2.2))
end Cell

structure AcquiredPrefix (q d : ℕ) where
  size : ℕ
  positive : 0 < size
  cell : Fin size → Cell q
  first_iff : ∀ i, (cell i).skeleton.first ↔ i.val=0
  adjacent : ∀ i j, i.val+1=j.val →
    Skeleton.Structural (cell i).skeleton (cell j).skeleton ∧
      Skeleton.Internal (cell i).skeleton (cell j).skeleton
  payload_format : ∀ i, (cell i).PayloadFormat d

namespace AcquiredPrefix
variable (R : AcquiredPrefix q d) (S : Schedule q)
def first : Fin R.size := ⟨0,R.positive⟩
def last : Fin R.size := ⟨R.size-1,by have := R.positive; omega⟩
omit [NeZero q] in
lemma first_first : (R.cell R.first).skeleton.first := (R.first_iff _).mpr rfl

def boundaryCell (cursor : Fin R.size) (s : Bool) (i : Fin R.size) : Cell q :=
  if i < cursor then (R.cell i).wing .left else
    if i=cursor then (R.cell i).boundary s else (R.cell i).idle s

def boundaryWord (cursor : Fin R.size) (s : Bool) : List (Cell q) :=
  List.ofFn (R.boundaryCell cursor s)
def idleWord (s : Bool) : List (Cell q) := List.ofFn (fun i => (R.cell i).idle s)

lemma boundaryCell_format (cursor : Fin R.size) (s : Bool)
    (hs : ∀ i, (R.cell i).metadata.zeroTask=true → s=false) (i : Fin R.size) :
    (R.boundaryCell cursor s i).Format S d := by
  unfold boundaryCell
  split
  · rename_i hi
    apply Cell.left_format _ S (R.payload_format i)
    let j : Fin R.size := ⟨i.val+1,by have := cursor.isLt; change i.val < cursor.val at hi; omega⟩
    exact (R.adjacent i j rfl).2.2.2.2.2
  · split
    · exact Cell.boundary_format _ S s (R.payload_format i) (hs i)
    · exact Cell.idle_format _ S s (R.payload_format i)

lemma boundaryCell_cursor (cursor : Fin R.size) (s : Bool) :
    R.boundaryCell cursor s cursor=(R.cell cursor).boundary s := by simp [boundaryCell]

omit [NeZero q] in
lemma acquisition_pair (i j : Fin R.size) (hij : i.val+1=j.val) :
    Skeleton.Pair ((R.cell i).skeleton.mark .left) ((R.cell j).skeleton.mark .boundary) := by
  obtain ⟨hstr,hi⟩ := R.adjacent i j hij
  refine ⟨hstr,Or.inr ?_⟩
  simp only [Skeleton.rightExternal,Skeleton.leftExternal,Skeleton.mark_marker,
    Skeleton.mark_last,Skeleton.mark_first,Skeleton.acceptsRight,Skeleton.acceptsLeft,
    Skeleton.internal_mark_left,Skeleton.internal_mark_right]
  simpa using And.intro hi.2.2.2.1 hi

lemma release_step (i j : Fin R.size) (hij : i.val+1=j.val) (s : Bool)
    (hs : ∀ i, (R.cell i).metadata.zeroTask=true → s=false) :
    Step S d (R.boundaryWord j s) (R.boundaryWord i s) := by
  unfold boundaryWord
  apply step_two_ofFn _ _ i j hij
  · intro z hzi hzj
    have hi : z < i ↔ z < j := by
      have hzine : z.val≠i.val := fun h => hzi (Fin.ext h)
      have hzjne : z.val≠j.val := fun h => hzj (Fin.ext h)
      simp only [Fin.lt_def]
      omega
    simp only [boundaryCell,hi,hzi,hzj,ite_false]
  · have hij' : i < j := by simp only [Fin.lt_def]; omega
    have hji : ¬ j < i := by omega
    have hne : j≠i := by omega
    refine ⟨?_,Or.inr ⟨_,_,_,_,rfl,rfl,Or.inr ?_⟩⟩
    · intro c hc
      simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl <;> apply R.boundaryCell_format S _ s hs
    · simpa only [boundaryCell,hij',hji,hne,ne_eq,hne,ite_true,ite_false,lt_self_iff_false]
        using Binary.acquire (S:=S) (R.cell i) (R.cell j) s (R.acquisition_pair i j hij)

lemma remove_first (s : Bool) (hs : ∀ i, (R.cell i).metadata.zeroTask=true → s=false) :
    Step S d (R.boundaryWord R.first s) (R.idleWord s) := by
  unfold boundaryWord idleWord
  apply step_one_ofFn _ _ R.first
  · intro i hi
    have hlt : ¬ i < R.first := by change ¬ i.val < 0; omega
    simp [boundaryCell,hlt,hi]
  · refine ⟨?_,Or.inl ⟨_,_,rfl,rfl,Or.inr ?_⟩⟩
    · intro c hc
      simp only [List.singleton_append,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl
      · exact R.boundaryCell_format S _ s hs _
      · exact Cell.idle_format _ S s (R.payload_format _)
    · rw [R.boundaryCell_cursor]
      exact Unary.create _ _ R.first_first

theorem release (cursor : Fin R.size) (s : Bool) (hs : ∀ i, (R.cell i).metadata.zeroTask=true → s=false) :
    Reach S d (R.boundaryWord cursor s) (R.idleWord s) := by
  generalize he : cursor.val=n
  induction n generalizing cursor with
  | zero =>
    have hx : cursor=R.first := Fin.ext he
    subst cursor
    exact Relation.ReflTransGen.single (R.remove_first S s hs)
  | succ n ih =>
    let i : Fin R.size := ⟨n,by omega⟩
    have he' : i.val+1=cursor.val := by dsimp [i]; omega
    exact (Relation.ReflTransGen.single (R.release_step S i cursor he' s hs)).trans
      (ih i rfl)

end AcquiredPrefix

namespace Cell
lemma wing_self {S : Schedule q} (c : Cell q) (m : Marker) (hf : c.Format S d)
    (hm : c.marker=m) (hw : m=.left ∨ m=.right) : c.wing m=c := by
  have hd := hf.2.2.2.2.2.1 (by rwa [hm])
  cases c with
  | mk sk ch da ce hd' =>
    cases sk
    simp_all [wing,Skeleton.mark,marker]

lemma boundary_self {S : Schedule q} (c : Cell q) (hf : c.Format S d)
    (hm : c.marker=.boundary) : c.boundary c.head.side=c := by
  have hd := hf.2.2.2.2.2.2.1 hm
  cases c with
  | mk sk ch da ce hd' =>
    cases sk
    cases hd'
    simp_all [boundary,defaultHead,Skeleton.mark,marker]

end Cell

namespace Component
variable (f : Fin N → Cell q) (i : Fin N)
omit [NeZero q] in
lemma boundary_right (hi : (f i).marker=.boundary) : right f i=i := by
  apply le_antisymm
  · by_contra hh
    have hn : i.val<(right f i).val := by omega
    exact (connected_right f i).right_barrier hn (Or.inr (Or.inl hi))
  · exact self_le_right f i

noncomputable def partialRegion {S : Schedule q} (hs : Syntax S d (List.ofFn f))
    (hi : (f i).marker=.boundary) : AcquiredPrefix q d where
  size := size f i
  positive := size_pos f i
  cell := fun j => f (offset f i j)
  first_iff := offset_first_iff f i (Verification.coherent_of_syntax S hs)
    (exterior_of_syntax hs) (Or.inl hi)
  adjacent j k hj := ⟨(Verification.coherent_of_syntax S hs _ _ (offset_adjacent f i j k hj)).1,
    offset_internal f i (Verification.coherent_of_syntax S hs) j k hj⟩
  payload_format j := by
    have hh : (f (offset f i j)).Format S d := hs.2.2 _ (List.mem_ofFn.mpr ⟨offset f i j,rfl⟩)
    exact ⟨hh.2.1,hh.2.2.1,hh.2.2.2.1⟩

lemma headIndex_prefix_last {S : Schedule q} (hs : Syntax S d (List.ofFn f))
    (hi : (f i).marker=.boundary) : headIndex f i=(partialRegion f i hs hi).last := by
  have h := boundary_right f i hi
  have hl := left_le_self f i
  apply Fin.ext
  change i.val-(left f i).val=size f i-1
  dsimp [size]
  rw [h]
  omega

theorem actual_partial_release {S : Schedule q} (hs : Syntax S d (List.ofFn f))
    (hi : (f i).marker=.boundary) :
    Reach S d (List.ofFn (partialRegion f i hs hi).cell)
      ((partialRegion f i hs hi).idleWord (f i).head.side) := by
  let P := partialRegion f i hs hi
  have hf (j : Fin P.size) : (P.cell j).Format S d :=
    hs.2.2 _ (List.mem_ofFn.mpr ⟨offset f i j,rfl⟩)
  have hh : P.cell (headIndex f i)=f i := by
    change f (offset f i (headIndex f i))=f i
    rw [offset_headIndex]
  have he : P.boundaryWord (headIndex f i) (f i).head.side=List.ofFn P.cell := by
    dsimp only [P,partialRegion,AcquiredPrefix.boundaryWord,AcquiredPrefix.boundaryCell]
    apply congrArg List.ofFn
    funext j
    unfold AcquiredPrefix.boundaryCell
    dsimp only
    split
    · apply Cell.wing_self _ _ (hf j)
        (before_head f i (Verification.coherent_of_syntax S hs) (Or.inl hi) j ‹_›) (Or.inl rfl)
    · rename_i hj
      have hle : j≤headIndex f i := by
        rw [headIndex_prefix_last f i hs hi]
        change j.val ≤ size f i - 1
        have hjlt : j.val < size f i := j.isLt
        omega
      have hje : j=headIndex f i := le_antisymm hle (le_of_not_gt hj)
      subst j
      rw [ite_eq_left rfl,offset_headIndex]
      exact Cell.boundary_self _ (hs.2.2 _ (List.mem_ofFn.mpr ⟨i,rfl⟩)) hi
  rw [←he]
  apply P.release S
  intro j hj
  have ht := SameRegion.task (Verification.coherent_of_syntax S hs) (connected_offset f i j).symm
  have hz : (P.cell j).metadata.zeroTask=(f i).metadata.zeroTask := congrArg Task.zeroTask ht
  apply (hs.2.2 _ (List.mem_ofFn.mpr ⟨i,rfl⟩)).2.2.2.2.2.2.2.1 (Or.inl hi)
  exact hz.symm.trans hj
end Component
end

section
open LocalSyntax LocalSyntax.Skeleton
variable {q d N : ℕ} [NeZero q] {S : Schedule q}

omit [NeZero q] in
lemma lockedCount_eq_zero (w : List (Cell q)) : lockedCount w=0 ↔ ∀ c∈w,c.marker=.idle := by
  simp [lockedCount,List.countP_eq_zero]
omit [NeZero q] in
lemma lockedCount_pos (w : List (Cell q)) : 0<lockedCount w ↔ ∃ c∈w,c.marker≠.idle := by
  simp [lockedCount,List.countP_pos_iff]

namespace Component
variable (f : Fin N → Cell q) (i : Fin N)
noncomputable def word : List (Cell q) := List.ofFn (fun j => f (offset f i j))

omit [NeZero q] in
lemma word_slice : word f i=((List.ofFn f).drop (left f i).val).take (size f i) := by
  have hs : size f i≤N-(left f i).val := by
    have := (right f i).isLt
    dsimp [size]
    omega
  apply List.ext_getElem
  · simp only [word,List.length_ofFn,List.length_take,List.length_drop,min_eq_left hs]
  · intro n hn hn'
    simp only [word,List.getElem_ofFn,List.getElem_take,List.getElem_drop]
    apply congrArg f
    apply Fin.ext
    rfl

omit [NeZero q] in
lemma word_split : List.ofFn f=
    (List.ofFn f).take (left f i).val++word f i++(List.ofFn f).drop ((right f i).val+1) := by
  have he : (left f i).val+size f i=(right f i).val+1 := by
    have := left_le_right f i
    dsimp [size]
    omega
  rw [word_slice]
  rw [show (right f i).val+1=(left f i).val+size f i from he.symm]
  rw [←List.drop_drop,List.append_assoc,List.take_append_drop,List.take_append_drop]

omit [NeZero q] in
lemma word_infix : word f i <:+: List.ofFn f := by
  exact ⟨_,_,(word_split f i).symm⟩

omit [NeZero q] in
lemma word_head_mem : f i∈word f i := by
  exact List.mem_ofFn.mpr ⟨headIndex f i,congrArg f (offset_headIndex f i)⟩

omit [NeZero q] in
lemma word_locked_pos (hi : (f i).skeleton.IsHead) : 0<lockedCount (word f i) := by
  apply (lockedCount_pos _).mpr
  refine ⟨f i,word_head_mem f i,?_⟩
  rcases hi with hi|hi <;> change (f i).marker=_ at hi <;> rw [hi] <;> decide

theorem normalize (hs : Syntax S d (List.ofFn f)) (hw : Survives S d (List.ofFn f))
    (hi : (f i).skeleton.IsHead) :
    ∃ v, Reach S d (word f i) v ∧ lockedCount v=0 := by
  rcases hi with hi|hi
  · let P := partialRegion f i hs hi
    refine ⟨P.idleWord (f i).head.side,actual_partial_release f i hs hi,?_⟩
    apply (lockedCount_eq_zero _).mpr
    intro c hc
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
    rfl
  · let R := region f i hs hi
    have hh := actual_rollback_release f i hs hi
    rcases hh with hh | ⟨w,p,a,s,hh,he,hz⟩
    · refine ⟨R.idleWord (f i).head.side,hh,?_⟩
      apply (lockedCount_eq_zero _).mpr
      intro c hc
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
      rfl
    · have hsurv := hw.infix (word_infix f i)
      exact (hsurv p [a] s (by simpa only [he,word,region] using hh) hz).elim
end Component

theorem Survives.transactions_idle {w : List (Cell q)} (hw : Survives S d w)
    (hs : Syntax S d w) : ∃ v, Reach S d w v ∧ ∀c∈v,c.marker=.idle := by
  generalize hk : lockedCount w=n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hn : lockedCount w=0
    · exact ⟨w,.refl,(lockedCount_eq_zero w).mp hn⟩
    · obtain ⟨c,hc,hnc⟩ := (lockedCount_pos w).mp (Nat.pos_of_ne_zero hn)
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hc
      let f : Fin w.length → Cell q := w.get
      have hf : List.ofFn f=w := List.ofFn_get w
      have hsf : Syntax S d (List.ofFn f) := by rwa [hf]
      have hwf : Survives S d (List.ofFn f) := by rwa [hf]
      have hi' : (f i).marker≠.idle := by change (w.get i).marker≠.idle; rwa [hi]
      obtain ⟨h,_,hhead⟩ := (Verification.coherent_of_syntax S hsf).owner
        (exterior_of_syntax hsf) i hi'
      obtain ⟨v,hv,hvc⟩ := Component.normalize f h hsf hwf hhead
      let p := (List.ofFn f).take (Component.left f h).val
      let s := (List.ofFn f).drop ((Component.right f h).val+1)
      have he : w=p++Component.word f h++s := hf.symm.trans (Component.word_split f h)
      have hr : Reach S d w (p++v++s) := by rw [he]; exact reach_context hv p s
      have hpos := Component.word_locked_pos f h hhead
      have hless : lockedCount (p++v++s)<n := by
        rw [←hk,he]
        simp only [lockedCount_append,hvc]
        omega
      obtain ⟨z,hz,hzi⟩ := ih (lockedCount (p++v++s)) hless
        (hw.of_reach hr) (reach_syntax hr hs) rfl
      exact ⟨z,hr.trans hz,hzi⟩
end

open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q] {S : Schedule q}

abbrev StructuralChain (w : List (Cell q)) :=
  w.IsChain (fun a b => Skeleton.Structural a.skeleton b.skeleton)

def EndsStop (w : List (Cell q)) : Prop := ∀c∈w.getLast?,c.pos=.stop

omit [NeZero q] in
lemma endsStop_cons_tail {c b : Cell q} {w : List (Cell q)}
    (h : EndsStop (c::b::w)) : EndsStop (b::w) := by
  simpa [EndsStop] using h

omit [NeZero q] in
lemma scan_core (w : List (Cell q)) (c : Cell q) (p : Fin q)
    (hc : c.pos=.core p) (hchain : StructuralChain (c::w)) (hlast : EndsStop (c::w)) :
    ∃ cores b s, c::w=cores++b::s ∧
      cores.map Cell.pos=((List.finRange q).drop p.val).map Position.core ∧ b.isPalette := by
  induction w generalizing c p with
  | nil =>
    have hz := hlast c (by simp)
    rw [hc] at hz
    cases hz
  | cons b w ih =>
    obtain ⟨hcb,hbw⟩ := List.isChain_cons_cons.mp hchain
    have hlast' := endsStop_cons_tail hlast
    change c.skeleton.pos=.core p at hc
    cases hp : b.pos with
    | core r =>
      change b.skeleton.pos=.core r at hp
      have hn : p.val+1=r.val := by simpa only [Skeleton.Structural,hc,hp] using hcb
      obtain ⟨cores,z,s,he,hcores,hz⟩ := ih b r hp hbw hlast'
      refine ⟨c::cores,z,s,by simp only [List.cons_append,he],?_,hz⟩
      rw [coreRange_cons p,List.map_cons,List.map_cons]
      rw [show c.pos=.core p from hc,hcores,hn]
    | palette x =>
      change b.skeleton.pos=.palette x at hp
      have hn : p.val+1=q := by simpa only [Skeleton.Structural,hc,hp] using hcb
      refine ⟨[c],b,w,rfl,?_,⟨x,hp⟩⟩
      have hdrop : (List.finRange q).drop q=[] := List.drop_eq_nil_iff.mpr (by simp)
      rw [coreRange_cons p,hn,hdrop]
      simp only [List.map_cons,List.map_nil]
      exact congrArg (fun z => [z]) hc
    | stop =>
      change b.skeleton.pos=.stop at hp
      simp only [Skeleton.Structural,hc,hp] at hcb

structure StructuralBlock (q : ℕ) where
  cores : List (Cell q)
  core_positions : cores.map Cell.pos=(List.finRange q).map Position.core
  palette : List (Cell q)
  palette_nonempty : palette≠[]
  palette_positions : ∀c∈palette,c.isPalette
  stop : Cell q
  stop_position : stop.pos=.stop
namespace StructuralBlock
variable (B : StructuralBlock q)
def word : List (Cell q) := B.cores++B.palette++[B.stop]
omit [NeZero q] in
lemma cores_length : B.cores.length=q := by
  have h := congrArg List.length B.core_positions
  simpa using h
omit [NeZero q] in
lemma word_nonempty : B.word≠[] := by
  simp [word]
end StructuralBlock

omit [NeZero q] in
lemma endsStop_suffix (p w : List (Cell q)) (h : EndsStop (p++w)) : EndsStop w := by
  intro a ha
  apply h a
  change (p++w).getLast?=some a
  change w.getLast?=some a at ha
  rw [List.getLast?_append,ha]
  rfl

def StartsCore (w : List (Cell q)) : Prop := ∀c∈w.head?,c.pos=.core (0 : Fin q)

namespace StructuralBlock
variable (B : StructuralBlock q)
omit [NeZero q] in
lemma last_stop : B.word.getLast?=some B.stop := by simp [word]

lemma starts_after {w : List (Cell q)} (hc : StructuralChain (B.word++w)) : StartsCore w := by
  intro a ha
  have h := (List.isChain_append.mp hc).2.2 B.stop (by rw [B.last_stop]; rfl) a ha
  have hz : B.stop.skeleton.pos=.stop := B.stop_position
  cases hp : a.pos with
  | core p =>
    change a.skeleton.pos=.core p at hp
    have h0 : p.val=0 := by simpa only [Skeleton.Structural,hz,hp] using h
    have hp0 : p=(0 : Fin q) := Fin.ext (by simpa using h0)
    exact congrArg Position.core hp0
  | palette x =>
    change a.skeleton.pos=.palette x at hp
    simp only [Skeleton.Structural,hz,hp] at h
  | stop =>
    change a.skeleton.pos=.stop at hp
    simp only [Skeleton.Structural,hz,hp] at h
end StructuralBlock

namespace Cell
lemma stop_idle_canonical (c : Cell q) (bits : Fin d → ZMod 2)
    (hf : c.Format S d) (hp : c.pos=.stop) (hm : c.marker=.idle) :
    c=canonicalCell bits .stop := by
  have hch := hf.2.1 (by simp [isPalette,hp])
  have hc' := hf.2.2.2.1 (by simp [isCore,hp])
  have hm' := hf.2.2.2.2.1 hm
  have hmeta := hm'.1
  have hhead := hm'.2.1
  have hd := hc'.1
  have hz := hc'.2
  have hsk : c.skeleton=⟨.stop,.idle,defaultMeta⟩ := by
    cases c with
    | mk sk ch dat cert head => cases sk; simp_all [marker,pos,metadata]
  cases c with
  | mk sk ch dat cert head =>
    simp_all [canonicalCell]
    rfl

lemma core_idle_canonical (c : Cell q) (bits : Fin d → ZMod 2) (p : Fin q)
    (hf : c.Format S d) (hp : c.pos=.core p) (hm : c.marker=.idle)
    (hb : ∀ h:p.val<d,c.data false=bits ⟨p.val,h⟩) :
    c=canonicalCell bits (.core p) := by
  have hch := hf.2.1 (by simp [isPalette,hp])
  have hm' := hf.2.2.2.2.1 hm
  have hmeta := hm'.1
  have hhead := hm'.2.1
  have hz := hm'.2.2.2
  have hd : c.data=(canonicalCell bits (.core p)).data := by
    funext side
    cases side with
    | true => exact hm'.2.2.1
    | false =>
      dsimp only [canonicalCell]
      by_cases h : p.val<d
      · simpa [h] using hb h
      · have hd := hf.2.2.1 p hp (Nat.le_of_not_gt h)
        simpa [h] using congrFun hd false
  have hsk : c.skeleton=⟨.core p,.idle,defaultMeta⟩ := by
    cases c with
    | mk sk ch dat cert head => cases sk; simp_all [marker,pos,metadata]
  cases c with
  | mk sk ch dat cert head =>
    simp_all [canonicalCell]
end Cell

namespace StructuralBlock
section
variable (B : StructuralBlock q)
def coreCell (i : Fin q) : Cell q := B.cores.get ⟨i.val,by rw [B.cores_length]; exact i.isLt⟩
omit [NeZero q] in
lemma coreCell_mem (i : Fin q) : B.coreCell i∈B.cores := List.get_mem _ _
omit [NeZero q] in
lemma coreCell_position (i : Fin q) : (B.coreCell i).pos=.core i := by
  have he := congrArg (fun l => l[i.val]?) B.core_positions
  simpa [List.getElem?_map,List.getElem?_eq_getElem,i.isLt,B.cores_length,coreCell,
    List.get_eq_getElem] using he

def bits (hd : d≤q) : Fin d → ZMod 2 :=
  fun j => (B.coreCell ⟨j.val,lt_of_lt_of_le j.isLt hd⟩).data false

lemma cores_canonical (hd : d≤q) (hf : ∀c∈B.cores,c.Format S d)
    (hm : ∀c∈B.cores,c.marker=.idle) :
    B.cores=(List.finRange q).map (fun p => canonicalCell (B.bits hd) (.core p)) := by
  apply List.ext_getElem (by simp [B.cores_length])
  intro i hi hi'
  let p : Fin q := ⟨i,by simpa [B.cores_length] using hi⟩
  have hc := Cell.core_idle_canonical (B.coreCell p) (B.bits hd) p
    (hf _ (B.coreCell_mem p)) (B.coreCell_position p) (hm _ (B.coreCell_mem p))
    (by intro h; rfl)
  simpa [coreCell,p,List.get_eq_getElem] using hc
end

variable (B : StructuralBlock q)
lemma core_ends : ∃ p c, B.cores=p++[c] ∧
    c.pos=.core (⟨q-1,Nat.sub_lt (NeZero.pos q) (by decide)⟩ : Fin q) := by
  let last : Fin q := ⟨q-1,Nat.sub_lt (NeZero.pos q) (by decide)⟩
  have he : B.cores.getLast?.map Cell.pos=some (.core last) := by
    rw [←List.getLast?_map,B.core_positions,List.getLast?_map,finRange_last]
    rfl
  obtain ⟨c,hc,hp⟩ := Option.map_eq_some_iff.mp he
  obtain ⟨p,hpc⟩ := List.getLast?_eq_some_iff.mp hc
  exact ⟨p,c,hpc,hp⟩

theorem normalize_idle (hd : d≤q) (hw : Survives S d B.word)
    (hm : ∀c∈B.word,c.marker=.idle) :
    Reach S d B.word (canonicalBlock (B.bits hd)) := by
  obtain ⟨p,c,hcores,hcp⟩ := B.core_ends
  have ht : q-1+1=q := by have := NeZero.pos q; omega
  have hwpal : Survives S d (c::B.palette++[B.stop]) :=
    hw.infix ⟨p,[],by simp [word,hcores,List.append_assoc]⟩
  have hroll := hwpal.checker_rollback hcp ht B.stop_position B.palette_positions
  have hpali : ∀a∈checkerIdle B.palette,a.isPalette := by
    simpa [checkerIdle] using B.palette_positions
  have hmi : ∀a∈checkerIdle B.palette,a.marker=.idle := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact hm b (by simp [word,hb])
  have hci : ∀a∈checkerIdle B.palette,a.checker=.idle := by simp [checkerIdle]
  have hpn : checkerIdle B.palette≠[] := by simpa [checkerIdle] using B.palette_nonempty
  obtain ⟨_,hpal⟩ := (hwpal.of_reach hroll).idle_palette_normalize hcp ht B.stop_position
    hpn hpali hmi hci (B.bits hd)
  have hr1 : Reach S d B.word (B.cores++checkerIdle B.palette++[B.stop]) := by
    simpa [word,hcores,List.append_assoc] using reach_context hroll p []
  have hr2 := reach_context hpal B.cores [B.stop]
  have hcanc := B.cores_canonical hd
    (fun c hc => hw.format (by simp [word,hc])) (fun c hc => hm c (by simp [word,hc]))
  have hstop := Cell.stop_idle_canonical B.stop (B.bits hd)
    (hw.format (by simp [word])) B.stop_position (hm _ (by simp [word]))
  have hfinal : B.cores++canonicalPalette (B.bits hd) (List.finRange q)++[B.stop]=
      canonicalBlock (B.bits hd) := by
    rw [hcanc,hstop]
    rfl
  rw [hfinal] at hr2
  exact hr1.trans hr2
end StructuralBlock

theorem idle_blocks_normalize (hd : d≤q) (bs : List (StructuralBlock q))
    (hw : Survives S d (bs.flatMap StructuralBlock.word))
    (hm : ∀c∈bs.flatMap StructuralBlock.word,c.marker=.idle) :
    Reach S d (bs.flatMap StructuralBlock.word) (encodeWord (bs.map (fun B => B.bits hd))) := by
  induction bs with
  | nil => exact .refl
  | cons B bs ih =>
    have hB : Survives S d B.word := hw.infix ⟨[],bs.flatMap StructuralBlock.word,by simp⟩
    have hbs : Survives S d (bs.flatMap StructuralBlock.word) := hw.infix ⟨B.word,[],by simp⟩
    have hmark : ∀c∈B.word,c.marker=.idle := fun c hc => hm c (by simp [hc])
    have hmarkbs : ∀c∈bs.flatMap StructuralBlock.word,c.marker=.idle :=
      fun c hc => hm c (by simp [hc])
    have h1 := reach_context (B.normalize_idle hd hB hmark) [] (bs.flatMap StructuralBlock.word)
    have h2 := reach_context (ih hbs hmarkbs) (canonicalBlock (B.bits hd)) []
    exact (by simpa [encodeWord,List.flatMap_cons] using h1.trans (by simpa [encodeWord] using h2))
end SourceBurnside.FiniteTable

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_GeometricRelations
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAdmissible _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideEndpoint _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHead _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideInternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLastOK _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLeftExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalettePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideRightExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideStructural _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable
section
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q] {S : Schedule q}

lemma startsCore_shape {v w : List (Cell q)} (he : v.map Cell.shape=w.map Cell.shape)
    (hv : StartsCore v) : StartsCore w := by
  have h : ∀s∈(v.map Cell.shape).head?,s=.core (0 : Fin q) := by
    simpa [List.head?_map,StartsCore] using hv
  rw [he] at h
  simpa [List.head?_map,StartsCore] using h

omit [NeZero q] in
lemma endsStop_shape {v w : List (Cell q)} (he : v.map Cell.shape=w.map Cell.shape)
    (hv : EndsStop v) : EndsStop w := by
  have h : ∀s∈(v.map Cell.shape).getLast?,s=.stop := by
    simpa [List.getLast?_map,EndsStop] using hv
  rw [he] at h
  simpa [List.getLast?_map,EndsStop] using h

lemma Cell.cut_leftExternal {c : Cell q} (hc : c.Cut) (hf : c.Format S d) :
    c.skeleton.leftExternal := by
  rcases hc.2 with hi|hb
  · exact Or.inl hi
  · have hfirst : c.skeleton.first := ⟨hb,0,hc.1,rfl⟩
    exact Or.inr ⟨fun hr => hf.1.1 hr hfirst,hfirst⟩

lemma pair_before_core_zero {a b : Cell q} (hp : Pair a b)
    (hb : b.pos=.core (0 : Fin q)) : a.pos=.stop := by
  have h := hp.1.1
  change b.skeleton.pos=.core (0 : Fin q) at hb
  cases ha : a.pos with
  | core p =>
    change a.skeleton.pos=.core p at ha
    simp only [Skeleton.Structural,ha,hb,Fin.val_zero] at h
    omega
  | palette x =>
    change a.skeleton.pos=.palette x at ha
    simp only [Skeleton.Structural,ha,hb] at h
  | stop => rfl

lemma Survives.before_cut_end {w : List (Cell q)} {b : Cell q}
    (hw : Survives S d (w++[b])) (hb : b.Cut) :
    EndsStop w ∧ ∀a∈w.getLast?,a.skeleton.rightExternal := by
  have hbext := Cell.cut_leftExternal hb (hw.format (by simp))
  have hedge := (List.isChain_append.mp hw.chain).2.2
  constructor
  · intro a ha
    exact pair_before_core_zero (hedge a ha b (by simp)) hb.1
  · intro a ha
    rcases (hedge a ha b (by simp)).1.2 with he|hi
    · exact he.1
    · exact (hi.2.1 hbext).elim

end

section
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q] {S : Schedule q}

def GeomRel (a b : Cell q) : Prop := a.geometryRank≤b.geometryRank ∧
  (a.geometryRank=b.geometryRank → a.isPalette ∧ b.isPalette)

instance instTransCellGeomRel : Trans (GeomRel (q:=q)) GeomRel GeomRel where
  trans := by
    intro a b c hab hbc
    have habL := hab.1
    have hbcL := hbc.1
    refine ⟨habL.trans hbcL,?_⟩
    intro he
    have hab' : a.geometryRank=b.geometryRank := by omega
    have hbc' : b.geometryRank=c.geometryRank := by omega
    exact ⟨(hab.2 hab').1,(hbc.2 hbc').2⟩

lemma Survives.geom_rel {w : List (Cell q)} (hw : Survives S d w)
    (hn : ∀c∈w.tail,¬c.Cut) : w.Pairwise GeomRel := by
  suffices w.IsChain GeomRel from this.pairwise
  induction w with
  | nil => simp
  | cons a w ih =>
    cases w with
    | nil => simp
    | cons b w =>
      refine List.isChain_cons_cons.mpr ⟨?_,?_⟩
      · exact pair_noCut_geometry (hw.pair ⟨[],w,by simp⟩) (hn b (by simp))
      · exact ih (hw.infix ⟨[a],[],by simp⟩) (fun c hc => hn c (List.mem_cons_of_mem b hc))

lemma Survives.beginning_ranks {w : List (Cell q)} (hw : Survives S d w)
    (hn : ∀c∈w.tail,¬c.Cut) : ((beginnings w).map Cell.blockRank).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  apply ((hw.geom_rel hn).filter _).imp_of_mem
  intro a b ha hb hab
  have hpa : a.pos=.core (0 : Fin q) := by simpa [beginnings] using (List.mem_filter.mp ha).2
  have hpb : b.pos=.core (0 : Fin q) := by simpa [beginnings] using (List.mem_filter.mp hb).2
  have hne : a.geometryRank≠b.geometryRank := by
    intro he
    obtain ⟨x,hx⟩ := (hab.2 he).1
    rw [hpa] at hx
    cases hx
  have hlt : a.geometryRank<b.geometryRank := lt_of_le_of_ne hab.1 hne
  simpa [Cell.geometryRank,Cell.positionRank,hpa,hpb] using hlt

lemma Survives.beginning_count_bound {w : List (Cell q)} (hw : Survives S d w)
    (hn : ∀c∈w.tail,¬c.Cut) : firstCoreCount w≤10 := by
  have hb : ∀c∈(beginnings w).tail,c.blockRank<10 := by
    intro c hc
    have hc' : c∈w.tail := by
      cases w with
      | nil => simp [beginnings] at hc
      | cons a w =>
        by_cases ha : a.pos=.core (0 : Fin q)
        · exact (by simpa [beginnings,ha] using hc : c∈w ∧ c.pos=.core (0 : Fin q)).1
        · have hct : c∈(beginnings w).tail := by simpa [beginnings,ha] using hc
          exact (List.mem_filter.mp (List.mem_of_mem_tail hct)).1
    have hp : c.pos=.core (0 : Fin q) := (of_decide_eq_true (List.mem_filter.mp
      (List.mem_of_mem_tail hc)).2)
    have hm : c.marker≠.idle := fun hm => hn c hc' ⟨hp,Or.inl hm⟩
    exact c.blockRank_lt_ten hm
  have hh := rank_list_bound (hw.beginning_ranks hn) (by simpa [←List.map_tail] using hb)
  simpa [firstCoreCount] using hh

lemma firstCoreCount_shape (w : List (Cell q)) : firstCoreCount w=
    (w.map Cell.shape).countP (fun s => decide (s=.core (0 : Fin q))) := by
  rw [firstCoreCount_eq,List.countP_map]
  apply congrArg (fun f => w.countP f)
  funext c
  cases hp : c.pos <;> simp [Cell.shape,hp]

@[simp] lemma firstCoreCount_block (bits : Fin d → ZMod 2) :
    firstCoreCount (canonicalBlock (q:=q) bits)=1 := by
  simp only [firstCoreCount,beginnings,canonicalBlock,List.filter_append,
    List.filter_map,List.length_append,List.length_map]
  simp [canonicalCell,Function.comp_def,Cell.pos,List.filter_eq,
    List.count_eq_one_of_mem (List.nodup_finRange q) (List.mem_finRange (0 : Fin q))]

@[simp] lemma firstCoreCount_encode (u : List (Fin d → ZMod 2)) :
    firstCoreCount (encodeWord (q:=q) u)=u.length := by
  induction u with
  | nil => simp [firstCoreCount,beginnings,encodeWord]
  | cons a u ih => simpa [encodeWord,Nat.add_comm] using ih
end

open LocalSyntax LocalSyntax.Skeleton
end SourceBurnside.FiniteTable

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_DataWords
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLastOK _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalettePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable

section
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q]
namespace Cell
def CheckerSafe (c : Cell q) : Prop := ∀x, c.pos=.palette x → c.checker≠.passed x
end Cell

end

open LocalSyntax LocalSyntax.Skeleton
end SourceBurnside.FiniteTable

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_TemplateHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.FiniteTable.Codec
open LocalSyntax
variable {h d : ℕ}
def Step (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) (v w : List (Raw h)) : Prop :=
  ∃ p s a b, v=p++a++s ∧ w=p++b++s ∧ replacement hh S d a b
abbrev Reach (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) := Relation.ReflTransGen (Step hh S d)
def Survives (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) (w : List (Raw h)) : Prop :=
  ∀p z s, Reach hh S d w (p++z++s) → ¬zero hh S d z
lemma step_encode (hh : 4≤h) {S : Schedule (2^h)} {v w : List (Cell (2^h))}
    (he : FiniteTable.Step S d v w) : Step (by omega) S d (v.map encode) (w.map encode) := by
  obtain ⟨p,s,a,b,rfl,rfl,he⟩ := he
  exact ⟨p.map encode,s.map encode,a.map encode,b.map encode,by simp,by simp,
    (replacement_encode hh S d a b).mpr he⟩
lemma reach_encode (hh : 4≤h) {S : Schedule (2^h)} {v w : List (Cell (2^h))}
    (he : FiniteTable.Reach S d v w) : Reach (by omega) S d (v.map encode) (w.map encode) := by
  induction he with
  | refl => exact .refl
  | tail h e ih => exact ih.tail (step_encode hh e)
end SourceBurnside.FiniteTable.Codec

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable
variable {q H h D : ℕ} [NeZero q]

def embedding (h D : ℕ) (w : List (Codec.Raw (D*h))) : List (Codec.Raw h) :=
  (encodeWord (q:=2^h) (w.map scalars)).map Codec.encode

end
end SourceBurnside.SourceMachine

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable

def hierarchy (D : ℕ) (hD : 2≤D) : MachineHierarchy D hD := Classical.choice (by
  obtain ⟨t,h0,h0pos,H⟩ := fixed_table_certificate D hD
  refine ⟨{ program := t
            threshold := h0
            threshold_four := h0pos
            fits := fun h hh => Classical.choose (H h hh)
            certifies := ?_ }⟩
  intro h hh task data
  obtain ⟨fit,fitnext,hcert⟩ := H h hh
  exact hcert task data)
namespace MachineHierarchy
variable {D : ℕ} {hD : 2≤D} (A : MachineHierarchy D hD)
def code := WrappedInput.specialize A.program A.program
lemma data_pos {h : ℕ} (hh : A.threshold≤h) : 0<10000*(D*h) := by nlinarith [A.threshold_four]
lemma height_pos {h : ℕ} (hh : A.threshold≤h) : 0<h := by have := A.threshold_four;omega
def schedule (h : ℕ) (hh : A.threshold≤h) : Schedule (2^h) :=
  sourceSchedule A.code (A.fits h hh) (A.data_pos hh)
end MachineHierarchy
end
end SourceBurnside.SourceMachine

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable
@[simp] lemma embedding_length (h D : ℕ) (w : List (Codec.Raw (D*h))) :
    (embedding h D w).length=(2*2^h+1)*w.length := by
  simp [embedding]
end
end SourceBurnside.SourceMachine

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_WordAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.FiniteTable.Codec
open LocalSyntax
variable {h d : ℕ} {hh : 0<h} {S : Schedule (2^h)}

def algebraTable (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) : WordAlgebra.Table (Raw h) where
  rep := fun v w => replacement hh S d v.toList w.toList
  zero := {w | zero hh S d w.toList}
lemma algebraTable_homogeneous (hh4 : 4≤h) : (algebraTable hh S d).Homogeneous := by
  intro v w he
  exact (replacement_lengths hh4 S d v.toList w.toList he).1
end SourceBurnside.FiniteTable.Codec
namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open FiniteTable
variable {D : ℕ} {hD : 2≤D} (A : MachineHierarchy D hD)
def table (h : ℕ) (hh : A.threshold≤h) :=
  Codec.algebraTable (A.height_pos hh) (A.schedule h hh) (10000*(D*h))

abbrev Algebra (K : Type*) [Ring K] (h : ℕ) (hh : A.threshold≤h) := (A.table h hh).Algebra (K:=K)

end
end SourceBurnside.SourceMachine.MachineHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_HierarchyGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
noncomputable section
open Classical LocalSyntax Cuts
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

def Token (S : Schedule q) (d : ℕ) (t : List (Cell q)) : Prop :=
  Cuts.Interval Cell.Cut t ∧ ∃b, b.Cut ∧ Survives S d (t++[b])
lemma token_length_le {t : List (Cell q)} (ht : Token S d t) : t.length≤fragmentBound q := by
  obtain ⟨⟨a,w,rfl,_,hn⟩,b,_,hw⟩ := ht
  exact cut_free_fragment_bound (hw.infix ⟨[],[b],by simp⟩) hn
lemma finite_tokens : {t : List (Cell q) | Token S d t}.Finite :=
  (List.finite_length_le (Cell q) (fragmentBound q)).subset (fun _ h => token_length_le h)
end
end SourceBurnside.FiniteTable
namespace SourceBurnside.FiniteTable.Codec
noncomputable section
open Classical LocalSyntax
variable {h d : ℕ} {hh : 0<h} {S : Schedule (2^h)}

def rawCut (hh : 0<h) (a : Raw h) : Prop := ∃c,decode hh a=some c ∧ c.Cut

def noncolor (c : Cell (2^h)) : Cell (2^h) := if c.isPalette then c.eraseColor else c
def fields (hh : 0<h) (a : Raw h) := (decode hh a).map noncolor
def eligibleFields (t : Option (Cell (2^h))) : Prop := ∃c,t=some c ∧ c.isPalette ∧ c.HeadFree

def rawToken (_hh : 0<h) (S : Schedule (2^h)) (d : ℕ) (t : List (Raw h)) : Prop :=
  ∃u : List (Cell (2^h)),FiniteTable.Token S d u ∧ t=u.map encode
lemma finite_rawTokens : {t : List (Raw h)|rawToken hh S d t}.Finite := by
  apply ((finite_tokens (S:=S) (d:=d)).image (List.map encode)).subset
  rintro t ⟨u,hu,rfl⟩
  exact ⟨u,hu,rfl⟩

end
end SourceBurnside.FiniteTable.Codec

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_MatrixTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable.Codec
noncomputable section
open Classical LocalSyntax
variable {h d : ℕ} {hh : 0<h} {S : Schedule (2^h)}
variable {K : Type*} [Ring K]
def letter (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) (a : Raw h) :
    (algebraTable hh S d).Algebra (K:=K) := (algebraTable hh S d).word (FreeMonoid.ofList [a])
end
end SourceBurnside.FiniteTable.Codec

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_CoefficientQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside
namespace FiniteSteinbergPresentation
open MonomialCompletion
variable {n : ℕ} {α : Type u}

 theorem toSteinberg_seed (p : Root n) (w : List α) (hw : w.length ≤ 2) :
    toSteinberg (seed.g p w : Group n α) = Steinberg.x p (monomial w) := by
  rw [seed_short p ⟨w, hw⟩, toSteinberg_of]

 theorem toSteinberg_word (hn : 5 ≤ n) (p : Root n) (w : List α) :
    toSteinberg (word seed hn p w : Group n α) = Steinberg.x p (monomial w) := by
  induction w generalizing p with
  | nil => rw [word_short _ _ _ _ (by simp), toSteinberg_seed _ _ (by simp)]
  | cons a v ih =>
    by_cases hv : v.length ≤ 1
    · rw [word_short _ _ _ _ (by simp only [List.length_cons]; omega),
        toSteinberg_seed _ _ (by simp only [List.length_cons]; omega)]
    · rw [word_long _ _ _ _ _ (by omega), map_bracket,
        word_short _ _ _ _ (by simp), toSteinberg_seed _ _ (by simp), ih,
        Steinberg.x_mul p.row (middle hn p) p.col
          (middle_ne_row hn p).symm (middle_ne_col hn p) p.ne]
      exact congrArg (Steinberg.x p) (monomial_append [a] v).symm

 theorem toSteinberg_poly (hn : 5 ≤ n) (p : Root n) (f : Polynomial α) :
    toSteinberg (poly seed hn p f : Group n α) = Steinberg.x p f := by
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [poly_add, map_mul, hf, hg, Steinberg.x_add]
  | single w a =>
    rcases zmod_two_cases a with rfl | rfl
    · simp
    · rw [poly_single, toSteinberg_word]
      rfl

 theorem from_to (hn : 5 ≤ n) :
    (fromSteinberg (α := α) hn).comp toSteinberg = MonoidHom.id (Group n α) := by
  apply PresentedGroup.ext
  rintro ⟨p, w⟩
  simp only [MonoidHom.comp_apply, toSteinberg_of, fromSteinberg_x, MonoidHom.id_apply]
  change poly seed hn p (MonoidAlgebra.single (FreeMonoid.ofList w.val) 1) = _
  rw [poly_single]
  change word seed hn p w.val = _
  rw [word_short _ _ _ _ w.property]
  exact seed_short p w

 theorem to_from (hn : 5 ≤ n) :
    toSteinberg.comp (fromSteinberg (α := α) hn) = MonoidHom.id (Steinberg n (Polynomial α)) := by
  apply Steinberg.hom_ext
  intro p f
  simp only [MonoidHom.comp_apply, fromSteinberg_x, toSteinberg_poly, MonoidHom.id_apply]

noncomputable def equiv (hn : 5 ≤ n) : Group n α ≃* Steinberg n (Polynomial α) where
  toFun := toSteinberg
  invFun := fromSteinberg hn
  left_inv a := DFunLike.congr_fun (from_to hn) a
  right_inv a := DFunLike.congr_fun (to_from hn) a
  map_mul' := toSteinberg.map_mul

end FiniteSteinbergPresentation

end SourceBurnside

namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open Classical FiniteTable
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
variable {h : ℕ} (hh : A.threshold ≤ h)
lemma table_homogeneous : (A.table h hh).Homogeneous :=
  Codec.algebraTable_homogeneous (A.threshold_four.trans hh)
lemma table_zero_nonempty : ∀z∈(A.table h hh).zero,z≠1 := by
  intro z hz he
  have hn := (Codec.zero_lengths (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) z.toList hz).1
  simp [he] at hn

def augmentation (K : Type) [CommRing K] : A.Algebra K h hh →ₐ[K] K :=
  (A.table h hh).augmentation (A.table_homogeneous hh) (A.table_zero_nonempty hh)
end
end SourceBurnside.SourceMachine.MachineHierarchy

namespace SourceBurnside.FiniteTable.Codec
noncomputable section
open Classical WordAlgebra
variable {h d : ℕ} {hh : 0<h} {S : Schedule (2^h)}
def boundedWords (h n : ℕ) : Set (FreeMonoid (Raw h)) :=
  Set.range (fun v : Σ m : Fin (n+1), Fin m.val → Raw h => FreeMonoid.ofList (List.ofFn v.2))
end
end SourceBurnside.FiniteTable.Codec

namespace SourceBurnside.ConcreteSource
noncomputable section

def machine := SourceMachine.hierarchy dilation dilation_two
def height := machine.threshold

abbrev R := machine.Algebra (ZMod 2) height (by rfl)
def augmentation : R →ₐ[ZMod 2] ZMod 2 := machine.augmentation (by rfl) (ZMod 2)
end
end SourceBurnside.ConcreteSource

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_BandFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.WordAlgebra.Table
noncomputable section
variable {α K : Type*} [CommRing K] (T : Table α) (hh : T.Homogeneous)

def gradingRingHom : @RingHom (T.Algebra (K:=K)) (_root_.Polynomial (T.Algebra (K:=K)))
    (inferInstance : Ring (T.Algebra (K:=K))).toNonAssocSemiring
    (inferInstance : Ring (_root_.Polynomial (T.Algebra (K:=K)))).toNonAssocSemiring where
  toFun := T.gradingHom hh
  map_zero' := map_zero _
  map_one' := map_one _
  map_add' := map_add _
  map_mul' := map_mul _
def gradedElement {n : ℕ} (u : Steinberg n (T.Algebra (K:=K))) :
    Steinberg n (_root_.Polynomial (T.Algebra (K:=K))) :=
  Steinberg.map (T.gradingRingHom hh) u
end
end SourceBurnside.WordAlgebra.Table

namespace SourceBurnside.ConcreteSource
noncomputable section

def evalZero : Polynomial R →ₐ[ZMod 2] R := (machine.table height (by rfl)).evalZero
def evalOne : Polynomial R →ₐ[ZMod 2] R := (machine.table height (by rfl)).evalOne
def gradedElement {n : ℕ} (u : Steinberg n R) : Steinberg n (Polynomial R) :=
  (machine.table height (by rfl)).gradedElement (machine.table_homogeneous (by rfl)) u
def groundElement {n : ℕ} (u : Steinberg n R) : Steinberg n (ZMod 2) := Steinberg.map augmentation.toRingHom u
end
end SourceBurnside.ConcreteSource

end

end OAI
end


