-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
-- name    : QMAPerfectCompleteness_Proof_DynamicBlockCompiler
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:05:18.168893+00:00
-- url     : https://prove2.me/theorems/e98d5c37-6d56-451c-b56a-43cbc5df9ae9
-- title:
--   Coherent selection of certificate index ranges
-- statement:
--   Defines clean reversible programs that compare the index with certificate-dependent binary thresholds and compute the branch-selection tags. The dynamic range layout separates comparison, tag combination and uncomputation, preserving the certificate and arithmetic data.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, Section 3.3, the coherent-certificate verifier and controlled block construction. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/DynamicBlockCompiler.lean, retained declaration span lines 11–145.

/- Generated from Solutions.DynamicBlockCompiler by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockClockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockImplements
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockStateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockTaggedActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition
namespace QMAPerfectCompleteness.Main.BlockTransport
end QMAPerfectCompleteness.Main.BlockTransport
namespace QMAPerfectCompleteness.Main.BlockHistoryCoordinates
end QMAPerfectCompleteness.Main.BlockHistoryCoordinates
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
end QMAPerfectCompleteness.Main.BlockHadamardCoordinates



/-! Dynamic range predicates for a coherent certificate, using three linear reversible comparators. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
namespace QMAPerfectCompleteness.Main.DynamicBlockCompiler
open BlockCompiler BooleanCircuits ReversibleGadgets VariableComparison ComparisonCircuits

/-- Three source pairs may share borrow workspace; all persistent tags lie outside them. -/
structure RangeLayout (n r : ℕ) where
  tags : Fin 6 ↪ Fin n
  comparators : Fin 3 → (Fin (3*r+2) ↪ Fin n)
  disjoint : ∀ t i j, tags t ≠ comparators i j

namespace RangeLayout
variable {n r : ℕ} (L : RangeLayout n r)

def Clean (x : Basis n) : Prop := ∀ i, VariableEquality.Clean (L.comparators i) x

def bit (i : Fin 3) (x : Basis n) : Bool :=
  VariableEquality.comparisonBit (L.comparators i) x

lemma bit_update_tag (i : Fin 3) (x : Basis n) (t : Fin 6) (b : Bool) :
    L.bit i (Function.update x (L.tags t) b) = L.bit i x :=
  VariableEquality.comparisonBit_update _ _ _ _ (L.disjoint t i)

lemma clean_update_tag (x : Basis n) (hx : L.Clean x) (t : Fin 6) (b : Bool) :
    L.Clean (Function.update x (L.tags t) b) := by
  intro i
  constructor
  · intro j
    rw [Function.update_of_ne (show carryWire (L.comparators i) j ≠ L.tags t from (L.disjoint t i _).symm)]
    exact (hx i).1 j
  · rw [Function.update_of_ne (show tempWire (L.comparators i) ≠ L.tags t from (L.disjoint t i _).symm)]
    exact (hx i).2

def compareAction (i : Fin 3) (x : Basis n) : Basis n :=
  Function.update x (L.tags ⟨i.val,by have := i.isLt; omega⟩)
    (xor (x (L.tags ⟨i.val,by have := i.isLt; omega⟩)) (L.bit i x))

noncomputable def compareProgram (i : Fin 3) : CleanProgram n L.Clean where
  gates := comparatorGates (L.comparators i) (L.tags ⟨i.val,by have := i.isLt; omega⟩)
    (L.disjoint _ i)
  action := L.compareAction i
  sound y x hx := comparatorGates_matrix _ _ _ y x (hx i).1 (hx i).2
  preserves x hx := L.clean_update_tag x hx _ _

/-- Flip c by !a∧b, using exactly three literal G₂ gates. -/
def andNotCommands (a b c : Fin 6) (hac : a ≠ c) (hbc : b ≠ c) : List (Command n) :=
  [.flip (L.tags a), .conj (L.tags a) (L.tags b) (L.tags c) (L.tags.injective.ne hac)
    (L.tags.injective.ne hbc), .flip (L.tags a)]

def andNotAction (a b c : Fin 6) (x : Basis n) : Basis n :=
  Function.update x (L.tags c) (xor (x (L.tags c)) ((!x (L.tags a)) && x (L.tags b)))

lemma andNotCommands_eval (a b c : Fin 6) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x : Basis n) : eval (L.andNotCommands a b c hac hbc) x = L.andNotAction a b c x := by
  funext w
  have hab' := L.tags.injective.ne hab
  have hac' := L.tags.injective.ne hac
  have hbc' := L.tags.injective.ne hbc
  by_cases hwa : w = L.tags a
  · subst w
    simp [andNotCommands,eval,evalCommand,andNotAction,hab',hac',hbc',Ne.symm hab',Ne.symm hac',Ne.symm hbc']
  · by_cases hwc : w = L.tags c
    · subst w
      simp [andNotCommands,eval,evalCommand,andNotAction,hab',hac',hbc',Ne.symm hab',Ne.symm hac',Ne.symm hbc']
    · simp [andNotCommands,eval,evalCommand,andNotAction,hwa,hwc,hab',hac',hbc']

noncomputable def andNotProgram (a b c : Fin 6) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    CleanProgram n L.Clean where
  gates := compile (L.andNotCommands a b c hac hbc)
  action := L.andNotAction a b c
  sound y x _ := by
    rw [compile_matrix]
    change (if y = eval (L.andNotCommands a b c hac hbc) x then (1 : ℂ) else 0) = _
    rw [L.andNotCommands_eval a b c hab hac hbc]
  preserves x hx := L.clean_update_tag x hx c _

noncomputable def program : CleanProgram n L.Clean :=
  (((((L.compareProgram 0).append (L.compareProgram 1)).append (L.compareProgram 2)).append
    (L.andNotProgram 0 1 3 (by decide) (by decide) (by decide))).append
    (L.andNotProgram 1 2 4 (by decide) (by decide) (by decide))).append
    (L.andNotProgram 0 2 5 (by decide) (by decide) (by decide))

noncomputable abbrev action : Basis n → Basis n := L.program.action
noncomputable def gates : List (Instr gatesG2 n) := L.program.gates

def truth (x : Basis n) : Fin 6 → Bool :=
  ![L.bit 0 x,L.bit 1 x,L.bit 2 x,(!L.bit 0 x && L.bit 1 x),
    (!L.bit 1 x && L.bit 2 x),(!L.bit 0 x && L.bit 2 x)]











lemma compareAction_involutive (i : Fin 3) : Function.Involutive (L.compareAction i) := by
  intro x
  simp only [compareAction,L.bit_update_tag,Function.update_self,Function.update_idem]
  simp

lemma andNotAction_involutive (a b c : Fin 6) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Involutive (L.andNotAction a b c) := by
  intro x
  simp only [andNotAction,Function.update_self,Function.update_idem,
    Function.update_of_ne (L.tags.injective.ne hac),Function.update_of_ne (L.tags.injective.ne hbc)]
  simp

noncomputable def undoProgram : CleanProgram n L.Clean :=
  ((((((L.andNotProgram 0 2 5 (by decide) (by decide) (by decide)).reverseOfInvolution
    (L.andNotAction_involutive 0 2 5 (by decide) (by decide))).append
    ((L.andNotProgram 1 2 4 (by decide) (by decide) (by decide)).reverseOfInvolution
      (L.andNotAction_involutive 1 2 4 (by decide) (by decide)))).append
    ((L.andNotProgram 0 1 3 (by decide) (by decide) (by decide)).reverseOfInvolution
      (L.andNotAction_involutive 0 1 3 (by decide) (by decide)))).append
    ((L.compareProgram 2).reverseOfInvolution (L.compareAction_involutive 2))).append
    ((L.compareProgram 1).reverseOfInvolution (L.compareAction_involutive 1))).append
    ((L.compareProgram 0).reverseOfInvolution (L.compareAction_involutive 0))

noncomputable abbrev undoAction : Basis n → Basis n := L.undoProgram.action



















end RangeLayout


end QMAPerfectCompleteness.Main.DynamicBlockCompiler


