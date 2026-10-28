-- Prove2me | Definitions.Def_OAIQ076M001
-- name    : OAIQ076M001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T08:59:58.943063+00:00
-- url     : https://prove2.me/theorems/cd52eeda-d29c-4961-b2e7-298642e1f766
-- title:
--   Definitions bundle OAIQ076M001 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 541 declarations of OpenAI's Lean: 286 definitions, 21 inductive types or structures, 2 instances and 232 theorems. The definitions and types are `OAI.MinUncut.Costed.AExpr`, `OAI.MinUncut.Costed.AExpr.eval`, `OAI.MinUncut.Costed.AExpr.lookup`, `OAI.MinUncut.Costed.AExpr.lookupValue`, `OAI.MinUncut.Costed.AExpr.pow`, `OAI.MinUncut.Costed.AExpr.sum`, `OAI.MinUncut.Costed.Arena.Init.bExpr`, `OAI.MinUncut.Costed.Arena.Init.cExpr`, `OAI.MinUncut.Costed.Arena.Init.canvasBase`, `OAI.MinUncut.Costed.Arena.Init.canvasEnv`, `OAI.MinUncut.Costed.Arena.Init.canvasPc`, `OAI.MinUncut.Costed.Arena.Init.canvasTotal`, `OAI.MinUncut.Costed.Arena.Init.canvasWords`, `OAI.MinUncut.Costed.Arena.Init.countExpr`, `OAI.MinUncut.Costed.Arena.Init.countRows`, `OAI.MinUncut.Costed.Arena.Init.dataPointer`, `OAI.MinUncut.Costed.Arena.Init.iExpr`, `OAI.MinUncut.Costed.Arena.Init.isData`, `OAI.MinUncut.Costed.Arena.Init.lExpr`, `OAI.MinUncut.Costed.Arena.Init.lengthExpr`, `OAI.MinUncut.Costed.Arena.Init.mExpr`, `OAI.MinUncut.Costed.Arena.Init.pointerExpr`, `OAI.MinUncut.Costed.Arena.Init.rawCell`, `OAI.MinUncut.Costed.Arena.Init.rawData`, `OAI.MinUncut.Costed.Arena.Init.restExpr`, `OAI.MinUncut.Costed.Arena.Init.rowExpressions`, `OAI.MinUncut.Costed.Arena.Init.sizeExpr`, `OAI.MinUncut.Costed.Arena.PolyProgram.safeIterate`, `OAI.MinUncut.Costed.Arena.maximum`, `OAI.MinUncut.Costed.Blocks.block`, `OAI.MinUncut.Costed.Blocks.emitted`, `OAI.MinUncut.Costed.Blocks.extractor`, `OAI.MinUncut.Costed.Blocks.retained`, `OAI.MinUncut.Costed.Blocks.source`, `OAI.MinUncut.Costed.Blocks.step`, `OAI.MinUncut.Costed.CodeRun`, `OAI.MinUncut.Costed.Division.step`, `OAI.MinUncut.Costed.PolyProgram`, `OAI.MinUncut.Costed.PolyProgram.add`, `OAI.MinUncut.Costed.PolyProgram.addOf` and 267 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Encoding_FormulaEncoding`, `MinUncut_Encoding_GameDecoder`, `MinUncut_Encoding_Serialization`, `MinUncut_Encoding_SignatureEncoding`, `MinUncut_Encoding_ThreeBitTest`, `MinUncut_Estimates_CodeComputability`, `MinUncut_Estimates_CodeIteration`, `MinUncut_Estimates_ExpressionOutput`, `MinUncut_Estimates_F2`, `MinUncut_Estimates_FiberPrefix`, `MinUncut_Estimates_IntegralExpect`, `MinUncut_Estimates_IterationMagnitude`, `MinUncut_Estimates_OuterRemainder`, `MinUncut_Estimates_PolynomialRecursor`, `MinUncut_Estimates_ReversePrefixProgram`, `MinUncut_Estimates_TemplateExpressions`, `MinUncut_Games_FiniteNoise`, `MinUncut_Games_OuterQuestions`, `MinUncut_Games_Sampling`, `MinUncut_Games_Target`, `MinUncut_Games_TotalVariation`, `MinUncut_Machines_MachineCompare`, `MinUncut_Machines_MachineTransducer`, `MinUncut_Machines_MachineUnaryAdd`, `MinUncut_Machines_MachineUnaryCounter`, `MinUncut_Machines_Runtime`, `MinUncut_Machines_RuntimeModel`, `MinUncut_PCP_AddressArithmetic`, `MinUncut_PCP_ClauseLookup`, `MinUncut_PCP_ClauseVerifier`, `MinUncut_PCP_ContextLoad`, `MinUncut_PCP_ContextPrepare`, `MinUncut_PCP_Folding`, `MinUncut_PCP_Game`, `MinUncut_PCP_HeaderAccumulate`, `MinUncut_PCP_HeaderCounts`, `MinUncut_PCP_HonestTest`, `MinUncut_PCP_Occurrences`, `MinUncut_PCP_Walsh`, `MinUncut_Search_ArithmeticExpression`, `MinUncut_Search_BlockEnumeration`, `MinUncut_Search_CodeArithmetic`, `MinUncut_Search_PolynomialArithmetic`, `MinUncut_Search_TemplateArithmetic`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M006`, `OAIQ076M007`, `OAIQ076M008`, `OAIQ076M009`, `OAIQ076M010`, `OAIQ076M011`, `OAIQ076M012` and `OAIQ076M013`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_Target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Target

structure Literal («variables» : Nat) where
  variableIndex : Fin «variables»
  positive : Bool
  deriving DecidableEq

abbrev Clause («variables» : Nat) := Vector (Literal «variables») 3

structure Formula where
  «variables» : Nat
  clauses : List (Clause «variables»)

end MinUncutGames.Foundations.Target

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Walsh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.Hastad

open scoped BigOperators
open Finset

abbrev Cube (I : Type*) := I → Bool

def bitSign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem bitSign_sq (b : Bool) : bitSign b ^ 2 = 1 := by
  cases b <;> norm_num [bitSign]

def cubeXor {I : Type*} (x y : Cube I) : Cube I := fun i => x i ^^ y i

def walsh {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) : ℝ :=
  ∏ i, bitSign (s i && x i)

@[simp] theorem walsh_sq {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x ^ 2 = 1 := by
  simp [walsh, ← Finset.prod_pow]

end MinUncutGames.Foundations.Hastad

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_ThreeBitTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def thirdQuery (π : J → I) (f : Cube I) (g μ : Cube J) : Cube J :=
  cubeXor g (cubeXor (fun y => f (π y)) μ)

end MinUncutGames.Foundations.Hastad

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Folding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncutGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

def cubeFlip (f : Cube I) : Cube I := fun i => !(f i)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem cubeFlip_cubeFlip (f : Cube I) : cubeFlip (cubeFlip f) = f := by
  funext i
  simp [cubeFlip]

def representative (i₀ : I) (f : Cube I) : Cube I :=
  if f i₀ then cubeFlip f else f

omit [Fintype I] [DecidableEq I] in
theorem representative_at (i₀ : I) (f : Cube I) :
    representative i₀ f i₀ = false := by
  cases hf : f i₀ <;> simp [representative, cubeFlip, hf]

abbrev HalfCube (i₀ : I) := {f : Cube I // f i₀ = false}

def canonicalInput (i₀ : I) (f : Cube I) : HalfCube i₀ :=
  ⟨representative i₀ f, representative_at i₀ f⟩

def foldedAnswer (i₀ : I) (table : HalfCube i₀ → Bool) (f : Cube I) : Bool :=
  table (canonicalInput i₀ f) ^^ f i₀

def coordinateMask (i : I) : Cube I := fun j => decide (j = i)

def cubeToggle (i : I) (f : Cube I) : Cube I :=
  cubeXor f (coordinateMask i)

omit [Fintype I] in
@[simp] theorem cubeToggle_twice (i : I) (f : Cube I) :
    cubeToggle i (cubeToggle i f) = f := by
  funext j
  change ((f j ^^ coordinateMask i j) ^^ coordinateMask i j) = f j
  cases f j <;> cases coordinateMask i j <;> rfl

def restrictQuery (valid : I → Bool) (f : Cube I) :
    Cube {i : I // valid i = true} := fun i => f i.val

def conditionedFoldedAnswer (valid : I → Bool) (i₀ : {i : I // valid i = true})
    (table : HalfCube i₀ → Bool) (f : Cube I) : Bool :=
  foldedAnswer i₀ table (restrictQuery valid f)

end MinUncutGames.Foundations.Hastad

end
namespace MinUncutGames.Reduction.CloneGap

variable {α β : Type*} {Name : Type}

structure Equation (Name : Type) where
  first : Name
  second : Name
  third : Name
  rhs : Bool

end MinUncutGames.Reduction.CloneGap

namespace MinUncutGames.Foundations.Hastad.FoldedEquation

open MinUncutGames.Reduction.CloneGap
open scoped BigOperators

variable {I J : Type}

abbrev Address (i₀ : I) (j₀ : J) := HalfCube i₀ ⊕ HalfCube j₀

def rhsCorrection (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (μ : Cube J) : Bool := f i₀ ^^ f (π j₀) ^^ μ j₀

def equation (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (g μ : Cube J) : Equation (Address i₀ j₀) where
  first := .inl (canonicalInput i₀ f)
  second := .inr (canonicalInput j₀ g)
  third := .inr (canonicalInput j₀ (thirdQuery π f g μ))
  rhs := rhsCorrection π i₀ j₀ f μ

def conditionedEquation (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (f : Cube I) (g μ : Cube J) : Equation (Address i₀ j₀) :=
  equation (fun j => π j.val) i₀ j₀ f (restrictQuery valid g) (restrictQuery valid μ)

end MinUncutGames.Foundations.Hastad.FoldedEquation

namespace MinUncutGames.Foundations.Hastad

open MinUncutGames.Reduction.CloneGap
open scoped BigOperators

def mapEquation {Name Name' : Type} (rename : Name → Name')
    (e : Equation Name) : Equation Name' where
  first := rename e.first
  second := rename e.second
  third := rename e.third
  rhs := e.rhs

namespace EmptyContext

variable {I : Type}

abbrev Address (i₀ : I) := HalfCube i₀ ⊕ Unit

def equation (i₀ : I) (f : Cube I) : Equation (Address i₀) where
  first := .inl (canonicalInput i₀ f)
  second := .inr ()
  third := .inr ()
  rhs := f i₀

@[simp] theorem equation_second_eq_third (i₀ : I) (f : Cube I) :
    (equation i₀ f).second = (equation i₀ f).third := rfl

end EmptyContext
end MinUncutGames.Foundations.Hastad

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_Serialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity

def encodeWord (n : Nat) : List Bool := List.replicate n true ++ [false]

def encodeWords : List Nat → List Bool
  | [] => []
  | n :: ns => encodeWord n ++ encodeWords ns

def decodeWordsAux : List Bool → Nat → Option (List Nat)
  | [], 0 => some []
  | [], _ + 1 => none
  | true :: bs, n => decodeWordsAux bs (n + 1)
  | false :: bs, n => (decodeWordsAux bs 0).map (n :: ·)

def decodeWords (bs : List Bool) : Option (List Nat) := decodeWordsAux bs 0

theorem decodeWordsAux_word (n k : Nat) (bs : List Bool) :
    decodeWordsAux (encodeWord n ++ bs) k =
      (decodeWordsAux bs 0).map ((k + n) :: ·) := by
  induction n generalizing k with
  | zero => simp [encodeWord, decodeWordsAux]
  | succ n ih =>
      simp only [encodeWord, List.replicate_succ, List.cons_append, List.append_assoc,
        decodeWordsAux]
      simpa [encodeWord, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

@[simp] theorem decodeWords_encodeWords (ns : List Nat) :
    decodeWords (encodeWords ns) = some ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      simp only [decodeWords, encodeWords, decodeWordsAux_word, Nat.zero_add]
      simpa [decodeWords] using congrArg (Option.map (n :: ·)) ih

@[simp] theorem encodeWord_length (n : Nat) : (encodeWord n).length = n + 1 := by
  simp [encodeWord]

@[simp] theorem encodeWords_append (xs ys : List Nat) :
    encodeWords (xs ++ ys) = encodeWords xs ++ encodeWords ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeWords, ih, List.append_assoc]

@[simp] theorem encodeWords_length (ns : List Nat) :
    (encodeWords ns).length = ns.sum + ns.length := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [encodeWords, ih]; omega

open Target

def literalWords {n : Nat} (literal : Literal n) : List Nat :=
  [literal.variableIndex.val, if literal.positive then 1 else 0]

def clauseWords {n : Nat} (clause : Clause n) : List Nat :=
  literalWords clause[0] ++ literalWords clause[1] ++ literalWords clause[2]

def formulaWords (formula : Formula) : List Nat :=
  [formula.«variables», formula.clauses.length] ++ formula.clauses.flatMap clauseWords

def formulaBits (formula : Formula) : List Bool := encodeWords (formulaWords formula)

@[simp] theorem literalWords_length {n : Nat} (literal : Literal n) :
    (literalWords literal).length = 2 := by simp [literalWords]

@[simp] theorem clauseWords_length {n : Nat} (clause : Clause n) :
    (clauseWords clause).length = 6 := by simp [clauseWords]

theorem clausesWords_length {n : Nat} (clauses : List (Clause n)) :
    (clauses.flatMap clauseWords).length = 6 * clauses.length := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp only [List.flatMap_cons, List.length_append, clauseWords_length,
        List.length_cons, ih, Nat.mul_add, Nat.mul_one]
      omega

@[simp] theorem formulaWords_length (formula : Formula) :
    (formulaWords formula).length = 2 + 6 * formula.clauses.length := by
  simp only [formulaWords, List.length_append, List.length_cons, List.length_nil,
    clausesWords_length]

end MinUncutGames.Foundations.Complexity

end
section
namespace MinUncutGames.Reduction.SourceEncoding

open MinUncutGames.Foundations.Complexity

structure Input where
  «variables» : Nat
  equations : List (CloneGap.Equation (Fin «variables»))
  nonempty : equations ≠ []

def equationWords {n : Nat} (e : CloneGap.Equation (Fin n)) : List Nat :=
  [e.first.val, e.second.val, e.third.val, if e.rhs then 1 else 0]

def inputWords (input : Input) : List Nat :=
  [input.«variables», input.equations.length] ++ input.equations.flatMap equationWords

@[simp] theorem equationWords_length {n : Nat} (e : CloneGap.Equation (Fin n)) :
    (equationWords e).length = 4 := by simp [equationWords]

theorem equationsWords_length {n : Nat} (equations : List (CloneGap.Equation (Fin n))) :
    (equations.flatMap equationWords).length = 4 * equations.length := by
  induction equations with
  | nil => rfl
  | cons e equations ih =>
      simp only [List.flatMap_cons, List.length_append, equationWords_length,
        List.length_cons, ih, Nat.mul_add, Nat.mul_one]
      omega

@[simp] theorem inputWords_length (input : Input) :
    (inputWords input).length = 2 + 4 * input.equations.length := by
  simp only [inputWords, List.length_append, List.length_cons, List.length_nil,
    equationsWords_length]

end MinUncutGames.Reduction.SourceEncoding

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ClauseVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP

open Target

structure ClauseAnswer where
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq

inductive Slot where
  | first
  | second
  | third
  deriving DecidableEq

def answerAt (answer : ClauseAnswer) : Slot → Bool
  | .first => answer.first
  | .second => answer.second
  | .third => answer.third

def nameAt {n : Nat} (clause : Clause n) : Slot → Fin n
  | .first => clause[0].variableIndex
  | .second => clause[1].variableIndex
  | .third => clause[2].variableIndex

def literalValue (positive value : Bool) : Bool :=
  if positive then value else !value

def localSatisfies {n : Nat} (clause : Clause n) (answer : ClauseAnswer) : Bool :=
  (literalValue clause[0].positive answer.first ||
   literalValue clause[1].positive answer.second) ||
   literalValue clause[2].positive answer.third

def honestAnswer {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : ClauseAnswer :=
  ⟨assignment clause[0].variableIndex, assignment clause[1].variableIndex,
   assignment clause[2].variableIndex⟩

def clauseAt (formula : Formula) (index : Fin formula.clauses.length) :
    Clause formula.«variables» := formula.clauses[index.val]

abbrev RandomEvent (formula : Formula) := Fin formula.clauses.length × Slot

end MinUncutGames.Foundations.PCP

end
section
namespace MinUncutGames.Foundations.Hastad.SourceContexts

open Target PCP

def clauseAnswerEquiv : ClauseAnswer ≃ Bool × Bool × Bool where
  toFun a := (a.first, a.second, a.third)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨a, b, c⟩; rfl

def clauseAnswerFinEquiv : ClauseAnswer ≃ Fin 8 :=
  clauseAnswerEquiv.trans
    ((Equiv.prodCongr finTwoEquiv.symm
      (Equiv.prodCongr finTwoEquiv.symm finTwoEquiv.symm)).trans
      ((Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv))

instance clauseAnswerFintype : Fintype ClauseAnswer :=
  Fintype.ofEquiv (Bool × Bool × Bool) clauseAnswerEquiv.symm

instance slotFintype : Fintype Slot where
  elems := {.first, .second, .third}
  complete s := by cases s <;> simp

@[simp] theorem card_clauseAnswer : Fintype.card ClauseAnswer = 8 := by
  rw [Fintype.card_congr clauseAnswerFinEquiv]
  rfl

@[simp] theorem card_slot : Fintype.card Slot = 3 := by decide

abbrev I (u : ℕ) := Fin u → Bool
abbrev J (u : ℕ) := Fin u → ClauseAnswer
abbrev ClauseContext (F : Formula) (u : ℕ) := Fin u → Fin F.clauses.length
abbrev VariableContext (F : Formula) (u : ℕ) := Fin u → Fin F.«variables»
abbrev SlotContext (u : ℕ) := Fin u → Slot

@[simp] theorem card_I (u : ℕ) : Fintype.card (I u) = 2 ^ u := by simp [I]
@[simp] theorem card_J (u : ℕ) : Fintype.card (J u) = 8 ^ u := by simp [J]
@[simp] theorem card_ClauseContext (F : Formula) (u : ℕ) :
    Fintype.card (ClauseContext F u) = F.clauses.length ^ u := by simp [ClauseContext]
@[simp] theorem card_VariableContext (F : Formula) (u : ℕ) :
    Fintype.card (VariableContext F u) = F.«variables» ^ u := by simp [VariableContext]
@[simp] theorem card_SlotContext (u : ℕ) :
    Fintype.card (SlotContext u) = 3 ^ u := by simp [SlotContext]

def localConsistent {n : ℕ} (clause : Clause n) (answer : ClauseAnswer) : Bool :=
  decide (∀ s s' : Slot, nameAt clause s = nameAt clause s' →
    answerAt answer s = answerAt answer s')

@[simp] theorem localConsistent_eq_true_iff {n : ℕ}
    (clause : Clause n) (answer : ClauseAnswer) :
    localConsistent clause answer = true ↔
      ∀ s s' : Slot, nameAt clause s = nameAt clause s' →
        answerAt answer s = answerAt answer s' := by
  simp [localConsistent]

def validJ (F : Formula) {u : ℕ} (c : ClauseContext F u) (j : J u) : Bool :=
  decide ((∀ t, localSatisfies (clauseAt F (c t)) (j t) = true) ∧
    ∀ t t' s s', nameAt (clauseAt F (c t)) s = nameAt (clauseAt F (c t')) s' →
      answerAt (j t) s = answerAt (j t') s')

@[simp] theorem validJ_eq_true_iff (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (j : J u) :
    validJ F c j = true ↔
      (∀ t, localSatisfies (clauseAt F (c t)) (j t) = true) ∧
      ∀ t t' s s', nameAt (clauseAt F (c t)) s = nameAt (clauseAt F (c t')) s' →
        answerAt (j t) s = answerAt (j t') s' := by
  simp [validJ]

def canonicalSlot {n : ℕ} (clause : Clause n) (v : Fin n) : Slot :=
  if nameAt clause .first = v then .first
  else if nameAt clause .second = v then .second else .third

def pi (F : Formula) {u : ℕ} (c : ClauseContext F u) (v : VariableContext F u)
    (j : J u) : I u :=
  fun t => answerAt (j t) (canonicalSlot (clauseAt F (c t)) (v t))

def sampledVariables (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) : VariableContext F u :=
  fun t => nameAt (clauseAt F (c t)) (s t)

def honestJ (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (assignment : Fin F.«variables» → Bool) : J u :=
  fun t => honestAnswer (clauseAt F (c t)) assignment

def honestI (F : Formula) {u : ℕ} (v : VariableContext F u)
    (assignment : Fin F.«variables» → Bool) : I u :=
  fun t => assignment (v t)

def baseAccepts (F : Formula) (v : Fin F.«variables») (c : Fin F.clauses.length)
    (i : Bool) (j : ClauseAnswer) : Bool :=
  decide (localSatisfies (clauseAt F c) j = true ∧
    localConsistent (clauseAt F c) j = true ∧
    answerAt j (canonicalSlot (clauseAt F c) v) = i)

@[simp] theorem baseAccepts_eq_true_iff (F : Formula) (v : Fin F.«variables»)
    (c : Fin F.clauses.length) (i : Bool) (j : ClauseAnswer) :
    baseAccepts F v c i j = true ↔
      localSatisfies (clauseAt F c) j = true ∧
      localConsistent (clauseAt F c) j = true ∧
      answerAt j (canonicalSlot (clauseAt F c) v) = i := by
  simp [baseAccepts]

end MinUncutGames.Foundations.Hastad.SourceContexts

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_FormulaEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity

open Target

def parseLiteral («variables» : Nat) : List Nat → Option (Literal «variables» × List Nat)
  | index :: sign :: rest =>
      if bounded : index < «variables» then
        if sign = 0 then some (⟨⟨index, bounded⟩, false⟩, rest)
        else if sign = 1 then some (⟨⟨index, bounded⟩, true⟩, rest)
        else none
      else none
  | _ => none

@[simp] theorem parseLiteral_encoded {n : Nat} (literal : Literal n) (rest : List Nat) :
    parseLiteral n (literalWords literal ++ rest) = some (literal, rest) := by
  cases literal with
  | mk index positive =>
      cases positive <;> simp [literalWords, parseLiteral, index.isLt]

def parseClause («variables» : Nat) (words : List Nat) : Option (Clause «variables» × List Nat) := do
  let (a, words) ← parseLiteral «variables» words
  let (b, words) ← parseLiteral «variables» words
  let (c, words) ← parseLiteral «variables» words
  return (⟨#[a, b, c], rfl⟩, words)

theorem clause_three_entries {n : Nat} (clause : Clause n) :
    (⟨#[clause[0], clause[1], clause[2]], rfl⟩ : Clause n) = clause := by
  apply Vector.ext
  intro i hi
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases_i with rfl | rfl | rfl <;> rfl

@[simp] theorem parseClause_encoded {n : Nat} (clause : Clause n) (rest : List Nat) :
    parseClause n (clauseWords clause ++ rest) = some (clause, rest) := by
  simp [clauseWords, List.append_assoc, parseClause, parseLiteral_encoded,
    clause_three_entries]

def parseClauses («variables» : Nat) : Nat → List Nat → Option (List (Clause «variables») × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (clause, words) ← parseClause «variables» words
      let (clauses, words) ← parseClauses «variables» count words
      return (clause :: clauses, words)

@[simp] theorem parseClauses_encoded {n : Nat} (clauses : List (Clause n)) (rest : List Nat) :
    parseClauses n clauses.length (clauses.flatMap clauseWords ++ rest) = some (clauses, rest) := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp [List.append_assoc, parseClauses, parseClause_encoded, ih]

def decodeFormulaWords : List Nat → Option Formula
  | «variables» :: count :: words => do
      let (clauses, trailing) ← parseClauses «variables» count words
      if trailing = [] then some ⟨«variables», clauses⟩ else none
  | _ => none

@[simp] theorem decodeFormulaWords_encoded (formula : Formula) :
    decodeFormulaWords (formulaWords formula) = some formula := by
  cases formula with
  | mk «variables» clauses =>
      have parsed := parseClauses_encoded clauses []
      simp only [List.append_nil] at parsed
      simp [decodeFormulaWords, formulaWords, parsed]

def decodeFormulaBits (bits : List Bool) : Option Formula :=
  decodeWords bits >>= decodeFormulaWords

@[simp] theorem decodeFormulaBits_encoded (formula : Formula) :
    decodeFormulaBits (formulaBits formula) = some formula := by
  simp [decodeFormulaBits, formulaBits]

end MinUncutGames.Foundations.Complexity

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_F2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace MinUncut.GaussianSmoothing

lemma weighted_exp_derivative {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X f : Ω → ℝ}
    (hX : Measurable X) (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1)
    (he : ∀ t : ℝ, Integrable (fun x => Real.exp (t * X x)) μ) :
    HasDerivAt (fun t : ℝ => ∫ x, Real.exp (t * X x) * f x ∂μ)
      (∫ x, X x * f x ∂μ) 0 := by
  have hdom : Integrable (fun x => |X x| * Real.exp |X x|) μ := by
    simpa using integrable_pow_abs_mul_exp_add_of_integrable_exp_mul
      (X := X) (v := 0) (t := 2) (x := 1) (by simpa using he 2)
      (by simpa using he (-2)) (by norm_num) (by norm_num) 1
  have hfint : Integrable f μ := (integrable_const (1 : ℝ)).mono'
    hf.aestronglyMeasurable (ae_of_all _ fun x => by simpa using hb x)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun t x => Real.exp (t * X x) * f x)
    (F' := fun t x => Real.exp (t * X x) * X x * f x)
    (bound := fun x => |X x| * Real.exp |X x|)
    (s := Set.Ioo (-1 : ℝ) 1) (x₀ := 0)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun t => (by fun_prop : Measurable
      (fun x => Real.exp (t * X x) * f x)).aestronglyMeasurable)
    (by simpa using hfint)
    (by fun_prop)
    (ae_of_all _ fun x t ht => ?_) hdom
    (ae_of_all _ fun x t _ => ?_)
  · simpa using h.2
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have ht' : |t| ≤ 1 := (abs_le.mpr ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    have hx : t * X x ≤ |X x| := by
      calc t * X x ≤ |t * X x| := le_abs_self _
           _ = |t| * |X x| := abs_mul _ _
           _ ≤ 1 * |X x| := mul_le_mul_of_nonneg_right ht' (abs_nonneg _)
           _ = |X x| := one_mul _
    calc Real.exp (t * X x) * |X x| * |f x|
        ≤ Real.exp (t * X x) * |X x| * 1 := by
          exact mul_le_mul_of_nonneg_left (hb x) (by positivity)
      _ ≤ |X x| * Real.exp |X x| := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hx)
          (abs_nonneg (X x))
  · simpa only [id_eq, one_mul] using
      (((hasDerivAt_id t).mul_const (X x)).exp).mul_const (f x)

lemma gaussianPDF_translate (t x : ℝ) :
    gaussianPDFReal t 1 x =
      gaussianPDFReal 0 1 x * (Real.exp (-(t^2)/2) * Real.exp (t*x)) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [← Real.exp_add, mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma gaussian_translate_integral {f : ℝ → ℝ} (hf : Measurable f) (t : ℝ) :
    (∫ x, f (x+t) ∂gaussianReal 0 1) =
      Real.exp (-(t^2)/2) * ∫ x, Real.exp (t*x) * f x ∂gaussianReal 0 1 := by
  have hm : (gaussianReal 0 1).map (fun x => x+t) = gaussianReal t 1 := by
    simpa using gaussianReal_map_add_const (μ := 0) (v := 1) t
  rw [← integral_map (by fun_prop : AEMeasurable (fun x : ℝ => x+t) (gaussianReal 0 1))
    hf.aestronglyMeasurable, hm]
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [gaussianPDF_translate]
  simp only [smul_eq_mul]
  ring

lemma gaussian_translate_derivative {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ 1) :
    HasDerivAt (fun t => ∫ x, f (x+t) ∂gaussianReal 0 1)
      (∫ x, x * f x ∂gaussianReal 0 1) 0 := by
  have hw := weighted_exp_derivative (μ := gaussianReal 0 1) measurable_id hf hb
    (fun t => integrable_exp_mul_gaussianReal t)
  have hd : HasDerivAt (fun t : ℝ => Real.exp (-(t^2)/2)) 0 0 := by
    convert ((((hasDerivAt_id 0).pow 2).neg).div_const 2).exp using 1 <;> norm_num
  convert! hd.mul hw using 1
  · funext t
    exact gaussian_translate_integral hf t
  · simp

lemma gaussian_convolution_derivative {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ 1) {σ : ℝ} (hσ : σ ≠ 0) (c : ℝ) :
    HasDerivAt (fun u => ∫ g, f (u + σ*g) ∂gaussianReal 0 1)
      (σ⁻¹ * ∫ g, g * f (c + σ*g) ∂gaussianReal 0 1) c := by
  have hQ : Measurable (fun g : ℝ => f (c + σ*g)) := hf.comp (by fun_prop)
  have h := gaussian_translate_derivative hQ (fun x => hb _)
  have ha : HasDerivAt (fun u : ℝ => (u-c)/σ) σ⁻¹ c := by
    simpa using ((hasDerivAt_id c).sub_const c).div_const σ
  have hcomp := HasDerivAt.comp c (by simpa only [sub_self, zero_div] using h) ha
  convert! hcomp using 1
  · ext u
    apply integral_congr_ae
    filter_upwards [] with g
    congr 1
    field_simp [hσ]
    ring
  · ring

section FiniteProduct
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev gamma (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

def split (i : ι) : (ι → ℝ) ≃ᵐ ℝ × ({j : ι // j ≠ i} → ℝ) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (· = i)).trans
    ((MeasurableEquiv.piUnique (fun _ : {j : ι // j = i} => ℝ)).prodCongr
      (MeasurableEquiv.refl _))

omit [Fintype ι] in
@[simp] lemma split_apply (i : ι) (g : ι → ℝ) :
    split i g = (g i, fun j => g j.1) := rfl

omit [Fintype ι] in
@[simp] lemma split_symm_apply (i : ι) (u : ℝ × ({j : ι // j ≠ i} → ℝ)) (j : ι) :
    (split i).symm u j = if h : j = i then u.1 else u.2 ⟨j,h⟩ := by
  rfl

lemma split_measurePreserving (i : ι) :
    MeasurePreserving (split i) (gamma ι)
      ((gaussianReal 0 1).prod (gamma {j : ι // j ≠ i})) := by
  let : Fintype {j : ι // j = i} := Subtype.fintype _
  exact ((measurePreserving_piUnique (fun _ : {j : ι // j = i} => gaussianReal 0 1)).prod
    (MeasurePreserving.id _)).comp
      (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => gaussianReal 0 1) (· = i))

lemma integral_split (i : ι) {f : (ι → ℝ) → ℝ} (hf : Integrable f (gamma ι)) :
    (∫ g, f g ∂gamma ι) =
    ∫ t, ∫ h, f ((split i).symm (t,h)) ∂gamma {j : ι // j ≠ i} ∂gaussianReal 0 1 := by
  let hm := (split_measurePreserving i).symm (split i)
  rw [← hm.integral_comp' f, integral_prod]
  exact (hm.integrable_comp hf.aestronglyMeasurable).mpr hf

omit [Fintype ι] in
lemma split_affine_update (i : ι) (c : ι → ℝ) (σ u t : ℝ)
    (h : {j : ι // j ≠ i} → ℝ) :
    Function.update c i u + σ • (split i).symm (t,h) =
      (split i).symm (u+σ*t, fun j => c j.1 + σ*h j) := by
  funext j
  by_cases hj : j = i
  · subst j; simp
  · simp [hj]

lemma product_convolution_derivative {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ 1) {σ : ℝ} (hσ : σ ≠ 0) (c : ι → ℝ) (i : ι) :
    HasDerivAt (fun u => ∫ g, f (Function.update c i u + σ • g) ∂gamma ι)
      (σ⁻¹ * ∫ g, g i * f (c + σ • g) ∂gamma ι) (c i) := by
  let Q : ℝ → ℝ := fun z => ∫ h : {j : ι // j ≠ i} → ℝ,
    f ((split i).symm (z, fun j => c j.1 + σ*h j)) ∂gamma {j : ι // j ≠ i}
  have hqm : Measurable Q := by
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.integral_prod_right
    exact (hf.comp ((split i).symm.measurable.comp (by fun_prop))).stronglyMeasurable
  have hqb (z : ℝ) : |Q z| ≤ 1 := by
    simpa [Q, ← Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le_const (μ := gamma {j : ι // j ≠ i})
        (ae_of_all _ fun h => (by simpa only [Real.norm_eq_abs] using (hb
          ((split i).symm (z, fun j => c j.1 + σ*h j))))))
  have hint (u : ℝ) : Integrable (fun g => f (Function.update c i u + σ • g)) (gamma ι) :=
    (integrable_const (1 : ℝ)).mono' (hf.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun g => by simpa only [Real.norm_eq_abs] using hb _)
  have heq (u : ℝ) : (∫ g, f (Function.update c i u + σ • g) ∂gamma ι) =
      ∫ t, Q (u+σ*t) ∂gaussianReal 0 1 := by
    rw [integral_split i (hint u)]
    simp only [split_affine_update, Q]
  have hint0 : Integrable (fun g => f (c + σ • g)) (gamma ι) := by
    simpa using hint (c i)
  have hsint : Integrable (fun g => g i * f (c + σ • g)) (gamma ι) := by
    have hi : Integrable (fun g : ι → ℝ => g i) (gamma ι) :=
      integrable_eval ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num))
    exact hi.mul_bdd (hf.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun g => by simpa only [Real.norm_eq_abs] using hb _)
  have hscore : (∫ g, g i * f (c + σ • g) ∂gamma ι) =
      ∫ t, t * Q (c i+σ*t) ∂gaussianReal 0 1 := by
    rw [integral_split i hsint]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with h
    simp only [split_symm_apply]
    congr 2
    simpa using split_affine_update i c σ (c i) t h
  simpa only [heq, hscore] using gaussian_convolution_derivative hqm hqb hσ (c i)

end FiniteProduct

end MinUncut.GaussianSmoothing

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_IntegralExpect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.GaussianHermite
open MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma integral_expect {T Ω : Type*} [Fintype T] [MeasurableSpace Ω] {μ : Measure Ω}
    (f : T → Ω → ℝ) (hf : ∀ t, Integrable (f t) μ) :
    (∫ x, (𝔼 t, f t x) ∂μ) = 𝔼 t, ∫ x, f t x ∂μ := by
  simp only [Finset.expect_eq_sum_div_card]
  rw [integral_div, integral_finsetSum _ (fun t _ => hf t)]

end MinUncut.GaussianHermite

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_OuterQuestions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Games

open scoped BigOperators

noncomputable section

structure FiniteDistribution (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonnegative : ∀ x, 0 ≤ weight x
  normalized : ∑ x, weight x = 1

namespace FiniteDistribution

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def probability (μ : FiniteDistribution Ω) (event : Ω → Bool) : ℝ :=
  ∑ x, if event x then μ.weight x else 0

@[simp] theorem probability_true (μ : FiniteDistribution Ω) :
    μ.probability (fun _ => true) = 1 := by
  simpa [probability] using μ.normalized

@[simp] theorem probability_false (μ : FiniteDistribution Ω) :
    μ.probability (fun _ => false) = 0 := by
  simp [probability]

def pushforward (μ : FiniteDistribution Ω) (f : Ω → Γ) : FiniteDistribution Γ := by
  classical
  exact
    { weight := fun y => ∑ x, if f x = y then μ.weight x else 0
      nonnegative := fun y => Finset.sum_nonneg fun x _ => by
        split
        · exact μ.nonnegative x
        · exact le_rfl
      normalized := by
        rw [Finset.sum_comm]
        simpa using μ.normalized }

def transport (μ : FiniteDistribution Ω) (equiv : Ω ≃ Γ) : FiniteDistribution Γ where
  weight y := μ.weight (equiv.symm y)
  nonnegative y := μ.nonnegative (equiv.symm y)
  normalized := by rw [equiv.symm.sum_comp, μ.normalized]

def iid (μ : FiniteDistribution Ω) (n : Nat) : FiniteDistribution (Fin n → Ω) where
  weight x := ∏ i, μ.weight (x i)
  nonnegative x := Finset.prod_nonneg fun i _ => μ.nonnegative (x i)
  normalized := by rw [← Fintype.sum_pow, μ.normalized, one_pow]

end FiniteDistribution

abbrev Strategy (Q₁ Q₂ A₁ A₂ : Type*) := (Q₁ → A₁) × (Q₂ → A₂)

structure Game (Q₁ Q₂ A₁ A₂ : Type*) [Fintype Q₁] [Fintype Q₂]
    [Fintype A₁] [Fintype A₂] where
  questions : FiniteDistribution (Q₁ × Q₂)
  accepts : Q₁ → Q₂ → A₁ → A₂ → Bool

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def tupleQuestionEquiv (n : Nat) :
    (Fin n → Q₁ × Q₂) ≃ (Fin n → Q₁) × (Fin n → Q₂) where
  toFun questions := (fun i => (questions i).1, fun i => (questions i).2)
  invFun questions := fun i => (questions.1 i, questions.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

def repetition (G : Game Q₁ Q₂ A₁ A₂) (n : Nat) :
    Game (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂) := by
  classical
  exact
    { questions := (G.questions.iid n).transport (tupleQuestionEquiv n)
      accepts := fun x y a b => decide (∀ i, G.accepts (x i) (y i) (a i) (b i) = true) }

@[simp] theorem repetition_question_weight (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (questions : (Fin n → Q₁) × (Fin n → Q₂)) :
    (G.repetition n).questions.weight questions =
      ∏ i, G.questions.weight (questions.1 i, questions.2 i) := rfl

@[simp] theorem repetition_accepts_iff (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (x : Fin n → Q₁) (y : Fin n → Q₂) (a : Fin n → A₁) (b : Fin n → A₂) :
    (G.repetition n).accepts x y a b = true ↔
      ∀ i, G.accepts (x i) (y i) (a i) (b i) = true := by
  classical
  simp [repetition]

def coordinateWin (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (coordinate : Fin n) (questions : (Fin n → Q₁) × (Fin n → Q₂)) : Bool :=
  G.accepts (questions.1 coordinate) (questions.2 coordinate)
    (strategy.1 questions.1 coordinate) (strategy.2 questions.2 coordinate)

def selectedWins (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : (Fin n → Q₁) × (Fin n → Q₂)) : Bool := by
  classical
  exact decide (∀ i ∈ selected, G.coordinateWin strategy i questions = true)

@[simp] theorem selectedWins_empty (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (questions : (Fin n → Q₁) × (Fin n → Q₂)) :
    G.selectedWins strategy ∅ questions = true := by
  simp [selectedWins]

end Game

end
end MinUncutGames.Foundations.Games

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_GameDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncutGames.Foundations.Hastad

open scoped BigOperators
open Finset
open MinUncutGames.Foundations.Games

variable {Q₁ Q₂ I J : Type*}
  [Fintype Q₁] [DecidableEq Q₁] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype J] [DecidableEq J] [Nonempty J]

inductive ConditionedOracle (valid : J → Bool) where
  | empty (noLegal : ∀ j, valid j = false)
  | stored (j₀ : {j : J // valid j = true}) (table : HalfCube j₀ → Bool)

def ConditionedOracle.answer {valid : J → Bool} : ConditionedOracle valid → Cube J → Bool
  | .empty _ => fun _ => false
  | .stored j₀ table => conditionedFoldedAnswer valid j₀ table

end MinUncutGames.Foundations.Hastad

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteDistribution Ω where
  weight _ := 1 / (Fintype.card Ω : ℝ)
  nonnegative _ := div_nonneg zero_le_one (Nat.cast_nonneg _)
  normalized := by
    have hn : (Fintype.card Ω : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div]
    exact mul_inv_cancel₀ hn

end
end MinUncutGames.Foundations.Games.FiniteDistribution

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_TotalVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

def condition (μ : FiniteDistribution Ω) (given : Ω → Bool)
    (positive : 0 < μ.probability given) : FiniteDistribution Ω where
  weight x := if given x then μ.weight x / μ.probability given else 0
  nonnegative x := by
    split
    · exact div_nonneg (μ.nonnegative x) positive.le
    · exact le_rfl
  normalized := by
    calc
      _ = (∑ x, if given x then μ.weight x else 0) / μ.probability given := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : given x = true <;> simp [hx]
      _ = 1 := div_self (ne_of_gt positive)

theorem probability_condition (μ : FiniteDistribution Ω) (given event : Ω → Bool)
    (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability event =
      μ.probability (fun x => given x && event x) / μ.probability given := by
  simp only [probability, condition, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hg : given x = true <;> by_cases he : event x = true <;> simp [hg, he]

@[simp] theorem probability_condition_given (μ : FiniteDistribution Ω)
    (given : Ω → Bool) (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability given = 1 := by
  rw [μ.probability_condition]
  simpa only [Bool.and_self] using div_self (ne_of_gt positive)

end FiniteDistribution

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  {n : Nat}

def selectedSuccess (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : ℝ :=
  (G.repetition n).questions.probability (G.selectedWins strategy selected)

@[simp] theorem selectedSuccess_empty (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    G.selectedSuccess strategy ∅ = 1 := by
  have h : G.selectedWins strategy ∅ = fun _ => true :=
    funext (G.selectedWins_empty strategy)
  rw [selectedSuccess, h, FiniteDistribution.probability_true]

end Game

end

end MinUncutGames.Foundations.Games

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_OuterRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

open scoped BigOperators
namespace MinUncut
open MeasureTheory GaussianHermite
lemma integrable_expect {T Ω : Type*} [Fintype T] [MeasurableSpace Ω] {μ : Measure Ω}
    (f : T → Ω → ℝ) (hf : ∀ t, Integrable (f t) μ) :
    Integrable (fun x => 𝔼 t, f t x) μ := by
  simp only [Finset.expect_eq_sum_div_card]
  exact (integrable_finsetSum _ (fun t _ => hf t)).div_const _
end MinUncut

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_FiniteNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Reduction.FiniteNoise

open scoped BigOperators

def realizedBit {D : Nat} (z : Fin D) : Bool := decide (z.val = 0)

def realizedNoise {A : Type*} {D : Nat} (z : A → Fin D) : A → Bool :=
  fun a => realizedBit (z a)

end MinUncutGames.Reduction.FiniteNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_HonestTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncutGames.Foundations.Hastad.SourceTape

open scoped BigOperators
open MinUncutGames.Reduction.FiniteNoise

abbrev TestTape (I J : Type*) (D : ℕ) :=
  Cube I × ((J → Fin D) × Cube J)

end MinUncutGames.Foundations.Hastad.SourceTape

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Occurrences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceOccurrences

open MinUncutGames.Reduction.CloneGap
open scoped BigOperators

structure Encoding (α : Type) where
  size : ℕ
  code : α ≃ Fin size

namespace Encoding

def fin (n : ℕ) : Encoding (Fin n) := ⟨n, Equiv.refl _⟩
def bool : Encoding Bool := ⟨2, finTwoEquiv.symm⟩
def unit : Encoding Unit := ⟨1, finOneEquiv.symm⟩

def prod {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α × β) :=
  ⟨a.size * b.size, (Equiv.prodCongr a.code b.code).trans finProdFinEquiv⟩

def sum {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α ⊕ β) :=
  ⟨a.size + b.size, (Equiv.sumCongr a.code b.code).trans finSumFinEquiv⟩

def function {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α → β) where
  size := b.size ^ a.size
  code := (show (α → β) ≃ (Fin a.size → Fin b.size) from
    { toFun := fun f i => b.code (f (a.code.symm i))
      invFun := fun f x => b.code.symm (f (a.code x))
      left_inv := by intro f; funext x; simp
      right_inv := by intro f; funext i; simp }).trans finFunctionFinEquiv

def enumerate {α : Type} (a : Encoding α) : List α := List.ofFn a.code.symm

@[simp] theorem length_enumerate {α : Type} (a : Encoding α) :
    a.enumerate.length = a.size := by simp [enumerate]

theorem mem_enumerate {α : Type} (a : Encoding α) (x : α) : x ∈ a.enumerate := by
  rw [enumerate, List.mem_ofFn']
  exact ⟨a.code x, a.code.symm_apply_apply x⟩

end Encoding

abbrev GlobalKey (V C I J : Type) := (V × Cube I) ⊕ ((C × Cube J) ⊕ Unit)

def globalEncoding {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J) :
    Encoding (GlobalKey V C I J) :=
  (v.prod (i.function Encoding.bool)).sum
    ((c.prod (j.function Encoding.bool)).sum Encoding.unit)

@[simp] theorem globalEncoding_size {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J) :
    (globalEncoding v c i j).size =
      v.size * 2 ^ i.size + (c.size * 2 ^ j.size + 1) := rfl

def extendRestricted {J : Type} (valid : J → Bool)
    (f : Cube {j : J // valid j = true}) : Cube J :=
  fun j => if h : valid j = true then f ⟨j, h⟩ else false

@[simp] theorem extendRestricted_valid {J : Type} (valid : J → Bool)
    (f : Cube {j : J // valid j = true}) (j : {j : J // valid j = true}) :
    extendRestricted valid f j.val = f j := by simp [extendRestricted, j.property]

@[simp] theorem restrictQuery_extendRestricted {J : Type} (valid : J → Bool)
    (f : Cube {j : J // valid j = true}) :
    restrictQuery valid (extendRestricted valid f) = f := by
  funext j
  exact extendRestricted_valid valid f j

@[simp] theorem canonicalInput_half {I : Type} [Fintype I] [DecidableEq I]
    (i₀ : I) (f : HalfCube i₀) :
    canonicalInput i₀ f.val = f := by
  apply Subtype.ext
  simp [canonicalInput, representative, f.property]

def assignmentOfKey {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J)
    (bits : GlobalKey V C I J → Bool) : Fin (globalEncoding v c i j).size → Bool :=
  fun q => bits ((globalEncoding v c i j).code.symm q)

@[simp] theorem assignmentOfKey_code {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J)
    (bits : GlobalKey V C I J → Bool) (key : GlobalKey V C I J) :
    assignmentOfKey v c i j bits ((globalEncoding v c i j).code key) = bits key := by
  exact congrArg bits ((globalEncoding v c i j).code.symm_apply_apply key)

section LocalEquations

variable {V C I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def localAddress (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (i₀ : I) (j₀ : {j : J // valid j = true}) :
    FoldedEquation.Address i₀ j₀ → Fin (globalEncoding vE cE iE jE).size
  | .inl f => (globalEncoding vE cE iE jE).code (.inl (v, f.val))
  | .inr g => (globalEncoding vE cE iE jE).code (.inr (.inl (c, extendRestricted valid g.val)))

def conditionedOccurrence
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true}) (f : Cube I) (g μ : Cube J) :
    Equation (Fin (globalEncoding vE cE iE jE).size) :=
  mapEquation (localAddress vE cE iE jE v c valid i₀ j₀)
    (FoldedEquation.conditionedEquation valid π i₀ j₀ f g μ)

end LocalEquations

def findValid {J : Type} (valid : J → Bool) : List J → Option {j : J // valid j = true}
  | [] => none
  | j :: rest => if h : valid j = true then some ⟨j, h⟩ else findValid valid rest

theorem findValid_none_iff {J : Type} (valid : J → Bool) (xs : List J) :
    findValid valid xs = none ↔ ∀ j ∈ xs, valid j = false := by
  induction xs with
  | nil => simp [findValid]
  | cons j xs ih =>
    by_cases hj : valid j = true
    · simp [findValid, hj]
    · simp [findValid, hj, ih]

def firstValid {J : Type} (e : Encoding J) (valid : J → Bool) :
    Option {j : J // valid j = true} := findValid valid e.enumerate

theorem firstValid_none_iff {J : Type} (e : Encoding J) (valid : J → Bool) :
    firstValid e valid = none ↔ ∀ j, valid j = false := by
  rw [firstValid, findValid_none_iff]
  exact ⟨fun h j => h j (e.mem_enumerate j), fun h j _ => h j⟩

def occurrenceList {Tape Name : Type} (tape : Encoding Tape)
    (emit : Tape → Equation Name) : List (Equation Name) := tape.enumerate.map emit

@[simp] theorem occurrenceList_length {Tape Name : Type} (tape : Encoding Tape)
    (emit : Tape → Equation Name) : (occurrenceList tape emit).length = tape.size := by
  simp [occurrenceList]

section ConcreteSource

open SourceContexts
open MinUncutGames.Reduction.FiniteNoise

def clauseAnswerEncoding : Encoding PCP.ClauseAnswer := ⟨8, clauseAnswerFinEquiv⟩

def slotEncoding : Encoding PCP.Slot where
  size := 3
  code :=
    { toFun := fun s => match s with | .first => 0 | .second => 1 | .third => 2
      invFun := fun i => if i.val = 0 then .first else if i.val = 1 then .second else .third
      left_inv := by intro s; cases s <;> rfl
      right_inv := by decide }

def iEncoding (u : ℕ) : Encoding (I u) := (Encoding.fin u).function Encoding.bool
def jEncoding (u : ℕ) : Encoding (J u) := (Encoding.fin u).function clauseAnswerEncoding
def variableEncoding (F : Target.Formula) (u : ℕ) : Encoding (VariableContext F u) :=
  (Encoding.fin u).function (Encoding.fin F.«variables»)
def clauseEncoding (F : Target.Formula) (u : ℕ) : Encoding (ClauseContext F u) :=
  (Encoding.fin u).function (Encoding.fin F.clauses.length)
def slotContextEncoding (u : ℕ) : Encoding (SlotContext u) :=
  (Encoding.fin u).function slotEncoding

def proofEncoding (F : Target.Formula) (u : ℕ) :
    Encoding (GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u)) :=
  globalEncoding (variableEncoding F u) (clauseEncoding F u) (iEncoding u) (jEncoding u)

def nBits (F : Target.Formula) (u : ℕ) : ℕ := (proofEncoding F u).size

@[simp] theorem nBits_eq (F : Target.Formula) (u : ℕ) :
    nBits F u = F.«variables» ^ u * 2 ^ (2 ^ u) +
      (F.clauses.length ^ u * 2 ^ (8 ^ u) + 1) := rfl

def dummyIndex (F : Target.Formula) (u : ℕ) : Fin (nBits F u) :=
  (proofEncoding F u).code (.inr (.inr ()))

def leftAnchor (u : ℕ) : I u := fun _ => false

def rightAnchor (F : Target.Formula) {u : ℕ} (c : ClauseContext F u) :
    Option {j : J u // validJ F c j = true} := firstValid (jEncoding u) (validJ F c)

theorem rightAnchor_none_iff (F : Target.Formula) {u : ℕ} (c : ClauseContext F u) :
    rightAnchor F c = none ↔ ∀ j : J u, validJ F c j = false :=
  firstValid_none_iff _ _

def halfTableKeyAssignment (F : Target.Formula) (u : ℕ)
    (a : VariableContext F u → HalfCube (leftAnchor u) → Bool)
    (b : ∀ c : ClauseContext F u, ∀ j₀ : {j : J u // validJ F c j = true},
      HalfCube j₀ → Bool) :
    GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u) → Bool
  | .inl (v, f) => a v (canonicalInput (leftAnchor u) f)
  | .inr (.inl (c, g)) =>
    match rightAnchor F c with
    | none => false
    | some j₀ => b c j₀ (canonicalInput j₀ (restrictQuery (validJ F c) g))
  | .inr (.inr _) => false

def emptyAddress (F : Target.Formula) (u : ℕ) (v : VariableContext F u) :
    EmptyContext.Address (leftAnchor u) → Fin (nBits F u)
  | .inl h => (proofEncoding F u).code (.inl (v, h.val))
  | .inr _ => dummyIndex F u

def contextEquation (F : Target.Formula) (u D : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u)
    (t : SourceTape.TestTape (I u) (J u) D) : Equation (Fin (nBits F u)) :=
  match rightAnchor F c with
  | none => mapEquation (emptyAddress F u v) (EmptyContext.equation (leftAnchor u) t.1)
  | some j₀ => conditionedOccurrence (variableEncoding F u) (clauseEncoding F u)
      (iEncoding u) (jEncoding u) v c (validJ F c) (pi F c v) (leftAnchor u) j₀
      t.1 t.2.2 (realizedNoise t.2.1)

def leftResponse (F : Target.Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (v : VariableContext F u) : Cube (I u) → Bool :=
  foldedAnswer (leftAnchor u) (fun h => bits ((proofEncoding F u).code (.inl (v, h.val))))

def rightResponse (F : Target.Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (c : ClauseContext F u) : Cube (J u) → Bool :=
  match rightAnchor F c with
  | none => fun _ => false
  | some j₀ => conditionedFoldedAnswer (validJ F c) j₀
      (fun h => bits ((proofEncoding F u).code (.inr (.inl (c, extendRestricted (validJ F c) h.val)))))

def testTapeEncoding (u D : ℕ) : Encoding (SourceTape.TestTape (I u) (J u) D) :=
  ((iEncoding u).function Encoding.bool).prod
    (((jEncoding u).function (Encoding.fin D)).prod ((jEncoding u).function Encoding.bool))

abbrev SourceIndex (F : Target.Formula) (u D : ℕ) :=
  (ClauseContext F u × SlotContext u) × SourceTape.TestTape (I u) (J u) D

def sourceIndexEncoding (F : Target.Formula) (u D : ℕ) : Encoding (SourceIndex F u D) :=
  ((clauseEncoding F u).prod (slotContextEncoding u)).prod (testTapeEncoding u D)

def sourceEquation (F : Target.Formula) (u D : ℕ) (p : SourceIndex F u D) :
    Equation (Fin (nBits F u)) :=
  contextEquation F u D p.1.1 (sampledVariables F p.1.1 p.1.2) p.2

def rawSourceList (F : Target.Formula) (u D : ℕ) : List (Equation (Fin (nBits F u))) :=
  occurrenceList (sourceIndexEncoding F u D) (sourceEquation F u D)

@[simp] theorem rawSourceList_length (F : Target.Formula) (u D : ℕ) :
    (rawSourceList F u D).length =
      (F.clauses.length ^ u * 3 ^ u) *
        (2 ^ (2 ^ u) * (D ^ (8 ^ u) * 2 ^ (8 ^ u))) := by
  rw [rawSourceList, occurrenceList_length]
  rfl

end ConcreteSource

end MinUncutGames.Foundations.Hastad.SourceOccurrences

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_CodeComputability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed
open Turing.ToPartrec

def bitsize (v : List ℕ) : ℕ := (Turing.PartrecToTM2.trList v).length

inductive CodeRun : Code → List ℕ → List ℕ → ℕ → Prop
  | zero (v) : CodeRun .zero' v (0::v) 1
  | succ (v) : CodeRun .succ v [v.headI+1] (32*(bitsize v+1))
  | tail (v) : CodeRun .tail v v.tail (32*(bitsize v+1))
  | cons {f fs v u w t t'} : CodeRun f v u t → CodeRun fs v w t' →
      CodeRun (.cons f fs) v (u.headI::w) (t+t'+32*(bitsize v+bitsize u+1))
  | comp {f g v u w t t'} : CodeRun g v u t → CodeRun f u w t' →
      CodeRun (.comp f g) v w (t+t'+1)
  | caseZero {f g v w t} : v.headI=0 → CodeRun f v.tail w t →
      CodeRun (.case f g) v w (t+32*(bitsize v+1))
  | caseSucc {f g v a w t} : CodeRun g (a::v) w t →
      CodeRun (.case f g) ((a+1)::v) w (t+32*(bitsize ((a+1)::v)+1))
  | fixDone {f v u t} : CodeRun f v u t → u.headI=0 →
      CodeRun (.fix f) v u.tail (t+1)
  | fixMore {f v u a w t t'} : CodeRun f v ((a+1)::u) t →
      CodeRun (.fix f) u w t' →
      CodeRun (.fix f) v w (t+t'+32*(bitsize ((a+1)::u)+1))

open _root_.Turing.PartrecToTM2 Turing.ToPartrec

lemma trPosNum_length_le (n : PosNum) : (trPosNum n).length≤(n:ℕ) := by
  induction n with
  | one => rfl
  | bit0 n ih =>
    have hp : 0<(n:ℕ) := PosNum.to_nat_pos n
    simp only [trPosNum,List.length_cons,PosNum.cast_bit0] at *
    omega
  | bit1 n ih =>
    simp only [trPosNum,List.length_cons,PosNum.cast_bit1] at *
    omega

lemma trNum_length_le (n : Num) : (trNum n).length≤(n:ℕ) := by
  cases n with
  | zero => rfl
  | pos n => exact trPosNum_length_le n

lemma trNat_length_le (n : ℕ) : (trNat n).length≤n := by
  have h := trNum_length_le (n:Num)
  simpa only [trNat,Num.to_of_nat] using h

def magnitude (v : List ℕ) : ℕ := (v.map (·+1)).sum

@[simp] lemma magnitude_nil : magnitude []=0 := rfl
@[simp] lemma magnitude_cons (a : ℕ) (v : List ℕ) : magnitude (a::v)=a+1+magnitude v := rfl
lemma magnitude_head (v : List ℕ) : v.headI≤ magnitude v := by
  cases v <;> simp only [List.headI_nil,List.headI_cons,magnitude_nil,magnitude_cons,Nat.default_eq_zero] <;> omega
lemma magnitude_tail (v : List ℕ) : magnitude v.tail≤ magnitude v := by
  cases v <;> simp [magnitude]
lemma magnitude_drop (n : ℕ) (v : List ℕ) : magnitude (v.drop n) ≤ magnitude v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← List.tail_drop]
    exact (magnitude_tail _).trans ih
lemma bitsize_le_magnitude (v : List ℕ) : bitsize v≤ magnitude v := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    have ha := trNat_length_le a
    simp only [bitsize,trList,List.length_append,List.length_cons] at *
    simp only [magnitude_cons]
    omega

def Runs (c : Code) (v w : List ℕ) (bound : ℕ) : Prop :=
  ∃t, t≤bound ∧ CodeRun c v w t

lemma Runs.mono {c v w b b'} (h : Runs c v w b) (hb : b≤b') : Runs c v w b' := by
  obtain ⟨t,ht,hc⟩ := h
  exact ⟨t,ht.trans hb,hc⟩
lemma run_zero (v : List ℕ) : Runs .zero' v (0::v) 1 := ⟨_,le_rfl,.zero v⟩
lemma run_succ (v : List ℕ) : Runs .succ v [v.headI+1] (32*(magnitude v+1)) :=
  ⟨_,by gcongr; exact bitsize_le_magnitude v,.succ v⟩
lemma run_tail (v : List ℕ) : Runs .tail v v.tail (32*(magnitude v+1)) :=
  ⟨_,by gcongr; exact bitsize_le_magnitude v,.tail v⟩
lemma run_comp {f g v u w b b'} (h : Runs g v u b) (h' : Runs f u w b') :
    Runs (.comp f g) v w (b+b'+1) := by
  obtain ⟨t,ht,hc⟩ := h
  obtain ⟨t',ht',hc'⟩ := h'
  exact ⟨_,by omega,.comp hc hc'⟩
lemma run_cons {f fs v u w b b'} (h : Runs f v u b) (h' : Runs fs v w b') :
    Runs (.cons f fs) v (u.headI::w) (b+b'+32*(magnitude v+magnitude u+1)) := by
  obtain ⟨t,ht,hc⟩ := h
  obtain ⟨t',ht',hc'⟩ := h'
  refine ⟨_,?_,.cons hc hc'⟩
  have := bitsize_le_magnitude v
  have := bitsize_le_magnitude u
  omega

lemma run_id (v : List ℕ) : Runs .id v v (70*(magnitude v+1)) := by
  have h : Runs .id v v (1+32*(magnitude (0::v)+1)+1) := run_comp (run_zero v) (run_tail (0::v))
  apply h.mono
  simp only [magnitude_cons]; omega
lemma run_nil (v : List ℕ) : Runs .nil v [] (140*(magnitude v+1)) := by
  have h : Runs .nil v [] (32*(magnitude v+1)+32*(magnitude [v.headI+1]+1)+1) :=
    run_comp (run_succ v) (run_tail [v.headI+1])
  apply h.mono
  have := magnitude_head v
  simp only [magnitude_cons,magnitude_nil]
  omega
lemma run_head (v : List ℕ) : Runs .head v [v.headI] (300*(magnitude v+1)) := by
  have h := run_cons (run_id v) (run_nil v)
  apply h.mono
  omega
lemma run_const_zero (v : List ℕ) : Runs .zero v [0] (210*(magnitude v+1)) := by
  have h := run_cons (run_zero v) (run_nil v)
  apply h.mono
  simp only [magnitude_cons]; omega

open Turing.ToPartrec

lemma run_caseZero {f g : Code} {v w : List ℕ} {b : ℕ} (hz : v.headI=0)
    (h : Runs f v.tail w b) : Runs (.case f g) v w (b+32*(magnitude v+1)) := by
  obtain ⟨t,ht,hc⟩ := h
  exact ⟨_,by have := bitsize_le_magnitude v; omega,.caseZero hz hc⟩
lemma run_caseSucc {f g : Code} {v w : List ℕ} {a b : ℕ}
    (h : Runs g (a::v) w b) :
    Runs (.case f g) ((a+1)::v) w (b+32*(magnitude ((a+1)::v)+1)) := by
  obtain ⟨t,ht,hc⟩ := h
  exact ⟨_,by have := bitsize_le_magnitude ((a+1)::v); omega,.caseSucc hc⟩
lemma run_pred (v : List ℕ) : Runs .pred v [v.headI-1] (332*(magnitude v+1)) := by
  cases v with
  | nil =>
    apply (run_caseZero (g:=.head) rfl (run_const_zero [])).mono
    simp only [magnitude_nil]; omega
  | cons a v =>
    cases a with
    | zero =>
      apply (run_caseZero (g:=.head) rfl (run_const_zero v)).mono
      simp only [magnitude_cons]; omega
    | succ a =>
      apply (run_caseSucc (f:=.zero) (run_head (a::v))).mono
      simp only [magnitude_cons]; omega

def dropCode : ℕ → Code
  | 0 => .id
  | n+1 => .comp .tail (dropCode n)

lemma run_drop (n : ℕ) (v : List ℕ) :
    Runs (dropCode n) v (v.drop n) ((71+33*n)*(magnitude v+1)) := by
  induction n with
  | zero => exact (run_id v).mono (by omega)
  | succ n ih =>
    have hb : magnitude (v.drop n)≤ magnitude v := magnitude_drop n v
    have h := run_comp ih (run_tail (v.drop n))
    rw [List.tail_drop] at h
    apply h.mono
    have hm : 32*(magnitude (v.drop n)+1)≤32*(magnitude v+1) := by omega
    nlinarith

def atCode (n : ℕ) : Code := .comp .head (dropCode n)
lemma run_at (n : ℕ) (v : List ℕ) :
    Runs (atCode n) v [(v.drop n).headI] ((372+33*n)*(magnitude v+1)) := by
  have hb : magnitude (v.drop n)≤ magnitude v := magnitude_drop n v
  apply (run_comp (run_drop n v) (run_head (v.drop n))).mono
  have : 300*(magnitude (v.drop n)+1)≤300*(magnitude v+1) := by omega
  nlinarith

def constCode : ℕ → Code
  | 0 => .zero
  | n+1 => .comp .succ (constCode n)

lemma run_const (n : ℕ) (v : List ℕ) :
    Runs (constCode n) v [n] ((250*(n+1)^2)*(magnitude v+1)) := by
  induction n with
  | zero => exact (run_const_zero v).mono (by nlinarith)
  | succ n ih =>
    have h := run_comp ih (run_succ [n])
    apply h.mono
    simp only [magnitude_cons,magnitude_nil]
    nlinarith

lemma run_fix_bounded {body : Code} {state : ℕ → List ℕ} {out : List ℕ}
    (n M B : ℕ)
    (hsize : ∀i≤n,magnitude (state i)≤M)
    (hstep : ∀i<n,Runs body (state i) (1::state (i+1)) B)
    (hdone : Runs body (state n) (0::out) B) :
    Runs (.fix body) (state 0) out ((n+1)*(B+32*(M+3))) := by
  have aux : ∀m i, i+m=n → Runs (.fix body) (state i) out ((m+1)*(B+32*(M+3))) := by
    intro m
    induction m with
    | zero =>
      intro i hi
      have he : i=n := by omega
      subst i
      obtain ⟨t,ht,hc⟩ := hdone
      exact ⟨_,by omega,.fixDone hc rfl⟩
    | succ m ih =>
      intro i hi
      obtain ⟨t,ht,hc⟩ := hstep i (by omega)
      obtain ⟨t',ht',hc'⟩ := ih (i+1) (by omega)
      refine ⟨_,?_,CodeRun.fixMore (a:=0) hc hc'⟩
      have hs := bitsize_le_magnitude (1::state (i+1))
      have hm := hsize (i+1) (by omega)
      simp only [magnitude_cons] at hs
      have hb : 32*(bitsize (1::state (i+1))+1)≤32*(M+3) := by omega
      nlinarith
  exact aux n 0 (by omega)

open Turing.ToPartrec

def dynamicDropBody : Code :=
  .case .zero' (.cons (.comp .succ .zero) (.cons .head (.comp .tail .tail)))
def dynamicDrop : Code := .fix dynamicDropBody

lemma run_dynamicDropBody_zero (v : List ℕ) :
    Runs dynamicDropBody (0::v) (0::v) (2000*(magnitude (0::v)+1)) := by
  exact (run_caseZero rfl (run_zero v)).mono (by omega)

lemma run_dynamicDropBody_succ (n : ℕ) (v : List ℕ) :
    Runs dynamicDropBody ((n+1)::v) (1::n::v.tail)
      (2000*(magnitude ((n+1)::v)+1)) := by
  have h1 := run_comp (run_const_zero (n::v)) (run_succ [0])
  have ht := run_comp (run_tail (n::v)) (run_tail v)
  have hh := run_caseSucc (f:=.zero') (run_cons h1 (run_cons (run_head (n::v)) ht))
  apply hh.mono
  have hv := magnitude_tail v
  simp only [magnitude_cons,magnitude_nil,List.headI_cons]
  omega

lemma run_dynamicDrop (n : ℕ) (v : List ℕ) :
    Runs dynamicDrop (n::v) (v.drop n)
      ((n+1)*2100*(magnitude (n::v)+1)) := by
  induction n generalizing v with
  | zero =>
    obtain ⟨t,ht,hc⟩ := run_dynamicDropBody_zero v
    exact ⟨_,by simp only [magnitude_cons] at *; omega,.fixDone hc rfl⟩
  | succ n ih =>
    obtain ⟨t,ht,hc⟩ := run_dynamicDropBody_succ n v
    obtain ⟨t',ht',hc'⟩ := ih v.tail
    have he : v.tail.drop n=v.drop (n+1) := List.drop_tail ..
    rw [he] at hc'
    refine ⟨_,?_,CodeRun.fixMore (a:=0) hc hc'⟩
    have hs := bitsize_le_magnitude (1::n::v.tail)
    have hv := magnitude_tail v
    simp only [magnitude_cons] at *
    have hm : (n+1)*2100*(n+1+magnitude v.tail+1)≤
      (n+1)*2100*((n+1)+1+magnitude v+1) := by gcongr; omega
    nlinarith

def dynamicAt : Code := .comp .head dynamicDrop
lemma run_dynamicAt (n : ℕ) (v : List ℕ) :
    Runs dynamicAt (n::v) [(v.drop n).headI]
      ((n+1)*2500*(magnitude (n::v)+1)) := by
  have h := run_comp (run_dynamicDrop n v) (run_head (v.drop n))
  apply h.mono
  have hv := magnitude_drop n v
  simp only [magnitude_cons]
  nlinarith

open Turing.ToPartrec

def precBody (g : Code) : Code :=
  .cons .tail <| .cons .succ <| .cons (.comp .pred .tail) <|
    .cons (.comp g (.cons .id (.comp .tail .tail))) (.comp .tail (.comp .tail .tail))

lemma run_precBody (g : Code) (a b r r' : ℕ) (v : List ℕ) (M B : ℕ)
    (ha : a≤M) (hb : b≤M) (hr : r≤M) (hr' : r'≤M) (hv : magnitude v≤M)
    (hg : Runs g (a::r::v) [r'] B) :
    Runs (precBody g) (a::b::r::v) (b::(a+1)::(b-1)::r'::v) (B+10000*(M+1)) := by
  have htail := run_tail (a::b::r::v)
  have htt := run_comp htail (run_tail (b::r::v))
  have httt := run_comp htt (run_tail (r::v))
  have hargs := run_cons (run_id (a::b::r::v)) htt
  have hg' := run_comp hargs hg
  have hp := run_comp htail (run_pred (b::r::v))
  have h := run_cons htail (run_cons (run_succ (a::b::r::v))
    (run_cons hp (run_cons hg' httt)))
  apply h.mono
  simp only [magnitude_cons,magnitude_nil,List.headI_cons,List.tail_cons]
  omega

lemma run_precLoop (g : Code) (n : ℕ) (r : ℕ → ℕ) (v : List ℕ) (M B : ℕ)
    (hn : n+1≤M) (hr : ∀i≤n+1,r i≤M) (hv : magnitude v≤M)
    (hg : ∀i≤n,Runs g (i::r i::v) [r (i+1)] B) (a b : ℕ) (hab : a+b=n) :
    Runs (.fix (precBody g)) (a::b::r a::v) ((n+1)::0::r (n+1)::v)
      ((b+1)*(B+11000*(M+1))) := by
  induction b generalizing a with
  | zero =>
    have han : a=n := by omega
    subst a
    obtain ⟨t,ht,hc⟩ := run_precBody g n 0 (r n) (r (n+1)) v M B
      (by omega) (by omega) (hr n (by omega)) (hr (n+1) le_rfl) hv (hg n le_rfl)
    exact ⟨_,by omega,.fixDone hc rfl⟩
  | succ b ih =>
    obtain ⟨t,ht,hc⟩ := run_precBody g a (b+1) (r a) (r (a+1)) v M B
      (by omega) (by omega) (hr a (by omega)) (hr (a+1) (by omega)) hv (hg a (by omega))
    simp only [Nat.add_sub_cancel] at hc
    obtain ⟨t',ht',hc'⟩ := ih (a+1) (by omega)
    refine ⟨_,?_,CodeRun.fixMore (a:=b) hc hc'⟩
    have hs := bitsize_le_magnitude ((b+1)::(a+1)::b::r (a+1)::v)
    have hm := hr (a+1) (by omega)
    simp only [magnitude_cons] at hs
    have hb : 32*(bitsize ((b+1)::(a+1)::b::r (a+1)::v)+1)≤1000*(M+1) := by omega
    nlinarith

lemma run_prec (f g : Code) (n : ℕ) (r : ℕ → ℕ) (v : List ℕ) (M A B : ℕ)
    (hn : n≤M) (hr : ∀i≤n,r i≤M) (hv : magnitude v≤M)
    (hf : Runs f v [r 0] A) (hg : ∀i<n,Runs g (i::r i::v) [r (i+1)] B) :
    Runs (.prec f g) (n::v) [r n] (A+(n+2)*(B+50000*(M+1))) := by
  let F := Code.case .id (.comp (.comp (.comp .tail .tail) (.fix (precBody g))) .zero')
  have hpre := run_cons (run_head (n::v)) (run_cons (run_comp (run_tail (n::v)) hf) (run_tail (n::v)))
  have hf' : Runs F (n::r 0::v) (r n::v) ((n+1)*(B+15000*(M+1))) := by
    cases n with
    | zero =>
      apply (run_caseZero (g:=.comp (.comp (.comp .tail .tail) (.fix (precBody g))) .zero')
        rfl (run_id (r 0::v))).mono
      have := hr 0 le_rfl
      simp only [magnitude_cons]
      nlinarith
    | succ n =>
      have hloop := run_precLoop g n r v M B hn hr hv (fun i hi => hg i (by omega)) 0 n (by omega)
      have htail := run_comp (run_tail ((n+1)::0::r (n+1)::v)) (run_tail (0::r (n+1)::v))
      have hh := run_caseSucc (f:=.id) (run_comp (run_zero (n::r 0::v)) (run_comp hloop htail))
      apply hh.mono
      have h0 := hr 0 (by omega)
      have hend := hr (n+1) le_rfl
      simp only [magnitude_cons]
      nlinarith
  have h := run_cons (run_comp hpre hf') (run_nil (n::v))
  change Runs (.prec f g) (n::v) [r n] _ at h
  apply h.mono
  have h0 := hr 0 (by omega)
  have hend := hr n le_rfl
  simp only [magnitude_cons,magnitude_nil,List.headI_cons]
  nlinarith

end MinUncut.Costed

noncomputable section
namespace MinUncut.Costed
open Turing.ToPartrec Polynomial

lemma evalNat_mono (p : Polynomial ℕ) {x y : ℕ} (h : x≤y) : p.eval x≤p.eval y := by
  simp only [Polynomial.eval_eq_sum,Polynomial.sum]
  apply Finset.sum_le_sum
  intro i hi
  gcongr

structure PolyProgram (f : List ℕ → List ℕ) where
  code : Code
  bound : Polynomial ℕ
  run : ∀v,Runs code v (f v) (bound.eval (magnitude v))
  size : ∀v,magnitude (f v)≤bound.eval (magnitude v)

namespace PolyProgram
variable {f g : List ℕ → List ℕ}

def id : PolyProgram (fun v=>v) where
  code := .id
  bound := C 70*(X+1)
  run v := by simpa using run_id v
  size v := by simp; omega

def tail : PolyProgram List.tail where
  code := .tail
  bound := C 32*(X+1)
  run v := by simpa using run_tail v
  size v := by have := magnitude_tail v; simp; omega

def head : PolyProgram (fun v=>[v.headI]) where
  code := .head
  bound := C 300*(X+1)
  run v := by simpa using run_head v
  size v := by have := magnitude_head v; simp; omega

def nil : PolyProgram (fun _=>[]) where
  code := .nil
  bound := C 140*(X+1)
  run v := by simpa using run_nil v
  size v := by simp

def succ : PolyProgram (fun v=>[v.headI+1]) where
  code := .succ
  bound := C 32*(X+1)
  run v := by simpa using run_succ v
  size v := by have := magnitude_head v; simp; omega

def const (n : ℕ) : PolyProgram (fun _=>[n]) where
  code := constCode n
  bound := C (250*(n+1)^2)*(X+1)
  run v := by simpa using run_const n v
  size v := by simp; nlinarith

def drop (n : ℕ) : PolyProgram (fun v=>v.drop n) where
  code := dropCode n
  bound := C (71+33*n)*(X+1)
  run v := by simpa using run_drop n v
  size v := by have := magnitude_drop n v; simp; nlinarith

def projection (n : ℕ) : PolyProgram (fun v=>[(v.drop n).headI]) where
  code := atCode n
  bound := C (372+33*n)*(X+1)
  run v := by simpa using run_at n v
  size v := by have := magnitude_drop n v; have := magnitude_head (v.drop n); simp; nlinarith

def comp (F : PolyProgram f) (G : PolyProgram g) : PolyProgram (f ∘ g) where
  code := .comp F.code G.code
  bound := G.bound+F.bound.comp G.bound+1
  run v := by
    have hh := run_comp (G.run v) (F.run (g v))
    apply hh.mono
    have hm := evalNat_mono F.bound (G.size v)
    simp only [eval_add,eval_comp,eval_one]
    omega
  size v := by
    have hm := (F.size (g v)).trans (evalNat_mono F.bound (G.size v))
    simpa using (hm.trans (Nat.le_add_left _ _)).trans (Nat.le_add_right _ 1)

def cons (F : PolyProgram f) (G : PolyProgram g) :
    PolyProgram (fun v=>(f v).headI::g v) where
  code := .cons F.code G.code
  bound := F.bound+G.bound+C 32*(X+F.bound+1)+1
  run v := by
    apply (run_cons (F.run v) (G.run v)).mono
    have hf := F.size v
    simp only [eval_add,eval_mul,eval_C,eval_X,eval_one]
    omega
  size v := by
    have hh := (magnitude_head (f v)).trans (F.size v)
    have hg := G.size v
    simp only [magnitude_cons,eval_add,eval_mul,eval_C,eval_X,eval_one]
    omega

def ofEq (F : PolyProgram f) (h : ∀v,f v=g v) : PolyProgram g where
  code := F.code
  bound := F.bound
  run v := h v ▸ F.run v
  size v := h v ▸ F.size v

open Turing.ToPartrec Polynomial

end PolyProgram
end MinUncut.Costed

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_CodeIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Costed
open Turing.ToPartrec

def iterBody (c : Code) : Code :=
  .case .zero' (.cons (.comp .succ .zero) (.cons .head (.comp c .tail)))
def iterCode (c : Code) : Code := .fix (iterBody c)

lemma run_iterBody_zero (c : Code) (v : List ℕ) :
    Runs (iterBody c) (0::v) (0::v) (2000*(magnitude (0::v)+1)) :=
  (run_caseZero rfl (run_zero v)).mono (by omega)

lemma run_iterBody_succ {c : Code} {v w : List ℕ} {B : ℕ}
    (h : Runs c v w B) (n : ℕ) :
    Runs (iterBody c) ((n+1)::v) (1::n::w)
      (B+2000*(magnitude ((n+1)::v)+magnitude w+1)) := by
  have h1 := run_comp (run_const_zero (n::v)) (run_succ [0])
  have hf := run_comp (run_tail (n::v)) h
  have hh := run_caseSucc (f:=.zero') (run_cons h1 (run_cons (run_head (n::v)) hf))
  apply hh.mono
  simp only [magnitude_nil,magnitude_cons,List.headI_cons]
  omega

lemma run_iter {c : Code} (f : List ℕ → List ℕ) (n : ℕ) (v : List ℕ) (M B : ℕ)
    (hs : ∀i≤n,magnitude (f^[i] v)≤M)
    (hf : ∀i<n,Runs c (f^[i] v) (f^[i+1] v) B) :
    Runs (iterCode c) (n::v) (f^[n] v) ((n+1)*(B+5000*(n+M+4))) := by
  let state := fun i => (n-i)::f^[i] v
  have hsize : ∀i≤n,magnitude (state i)≤n+M+1 := by
    intro i hi
    have := hs i hi
    simp only [state,magnitude_cons]
    omega
  have hstep : ∀i<n,Runs (iterBody c) (state i) (1::state (i+1))
      (B+4000*(n+M+2)) := by
    intro i hi
    have hn : n-i=(n-(i+1))+1 := by omega
    have hh := run_iterBody_succ (hf i hi) (n-(i+1))
    rw [← hn] at hh
    apply hh.mono
    have hsi := hs i (by omega)
    have hsj := hs (i+1) (by omega)
    simp only [magnitude_cons]
    omega
  have hdone : Runs (iterBody c) (state n) (0::f^[n] v)
      (B+4000*(n+M+2)) := by
    simp only [state,Nat.sub_self]

    apply (run_iterBody_zero c (f^[n] v)).mono
    have := hs n le_rfl
    simp only [magnitude_cons]; omega
  have hh := run_fix_bounded n (n+M+1) (B+4000*(n+M+2)) hsize hstep hdone
  change Runs (iterCode c) (n::v) (f^[n] v) _ at hh
  apply hh.mono
  apply Nat.mul_le_mul_left
  omega

end MinUncut.Costed

noncomputable section
namespace MinUncut.Costed.PolyProgram
open Turing.ToPartrec Polynomial

def iterate {f : List ℕ → List ℕ} (F : PolyProgram f) (p : Polynomial ℕ)
    (hs : ∀n v i, i≤n → magnitude (f^[i] v)≤p.eval (magnitude (n::v))) :
    PolyProgram (fun v=>f^[v.headI] v.tail) where
  code := iterCode F.code
  bound := p+(X+1)*(F.bound.comp p+C 5000*(X+p+4))+C 3000*(X+1)
  run v := by
    cases v with
    | nil =>
      obtain ⟨t,ht,hc⟩ := run_caseZero (f:=.zero') (g:=
        .cons (.comp .succ .zero) (.cons .head (.comp F.code .tail))) (v:=[]) rfl (run_zero [])
      refine ⟨_,?_,CodeRun.fixDone (u := [0]) hc rfl⟩
      simp only [magnitude_nil] at ht
      simp only [eval_add,eval_mul,eval_comp,eval_C,eval_X,eval_one,eval_ofNat,magnitude_nil]
      omega
    | cons n v =>
      have hh := run_iter (c := F.code) f n v (p.eval (magnitude (n::v)))
        (F.bound.eval (p.eval (magnitude (n::v)))) (hs n v) (by
          intro i hi
          have h := F.run (f^[i] v)
          have h' : Runs F.code (f^[i] v) (f^[i+1] v) (F.bound.eval (magnitude (f^[i] v))) := by
            simpa only [Function.iterate_succ_apply'] using h
          exact h'.mono (evalNat_mono F.bound (hs n v i (by omega))))
      apply hh.mono
      simp only [eval_add,eval_mul,eval_comp,eval_C,eval_X,eval_one,eval_ofNat]
      have hn : n≤ magnitude (n::v) := by simp only [magnitude_cons]; omega
      have h₁ : (n+1)*(F.bound.eval (p.eval (magnitude (n::v)))+
          5000*(n+p.eval (magnitude (n::v))+4)) ≤
          (magnitude (n::v)+1)*(F.bound.eval (p.eval (magnitude (n::v)))+
          5000*(magnitude (n::v)+p.eval (magnitude (n::v))+4)) := by gcongr
      omega
  size v := by
    cases v with
    | nil => simp
    | cons n v =>
      have hh := hs n v n le_rfl
      simp only [List.headI_cons,List.tail_cons,eval_add,eval_mul,eval_comp,
        eval_C,eval_X,eval_one,eval_ofNat]
      omega

def dynamic : PolyProgram (fun v=>[(v.tail.drop v.headI).headI]) where
  code := dynamicAt
  bound := C 3000*(X+1)^2
  run v := by
    cases v with
    | nil =>
      obtain ⟨t,ht,hc⟩ := run_caseZero (g:=.cons (.comp .succ .zero)
         (.cons .head (.comp .tail .tail))) (v:=[]) rfl (run_zero [])
      have hf : Runs dynamicDrop [] [] 100 := ⟨_,by simp only [magnitude_nil] at ht; omega,CodeRun.fixDone (u := [0]) hc rfl⟩
      exact (run_comp hf (run_head [])).mono (by norm_num [magnitude])
    | cons n v =>
      apply (run_dynamicAt n v).mono
      simp only [eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_one]
      have hn : n+1≤ magnitude (n::v)+1 := by simp only [magnitude_cons]; omega
      nlinarith
  size v := by
    have h := (magnitude_head (v.tail.drop v.headI)).trans
      ((magnitude_drop v.headI v.tail).trans (magnitude_tail v))
    simp only [magnitude_cons,magnitude_nil,eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_one]
    nlinarith

end MinUncut.Costed.PolyProgram

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_CodeArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Costed
open Turing.ToPartrec

def addCode : Code := .prec .head (.comp .succ .tail)
def subCode : Code := .prec .head (.comp .pred .tail)

lemma run_add (n a : ℕ) (v : List ℕ) :
    Runs addCode (n::a::v) [a+n] (100000*(magnitude (n::a::v)+2)^2) := by
  let M := magnitude (n::a::v)
  have hn : n≤M := by dsimp [M]; omega
  have ha : a≤M := by dsimp [M]; omega
  have hv : magnitude (a::v)≤M := by dsimp [M]; omega
  have hr : ∀i≤n,a+i≤M := by intro i hi; dsimp [M]; omega
  have hg : ∀i<n, Runs (.comp .succ .tail) (i::(a+i)::a::v) [a+(i+1)] (200*(M+1)) := by
    intro i hi
    have hh := run_comp (run_tail (i::(a+i)::a::v)) (run_succ ((a+i)::a::v))
    have hri := hr i (by omega)
    apply hh.mono
    simp only [magnitude_cons] at *
    omega
  have hh := run_prec .head (.comp .succ .tail) n (fun i=>a+i) (a::v) M
    (300*(M+1)) (200*(M+1)) hn hr hv ((run_head (a::v)).mono (by gcongr)) hg
  apply hh.mono
  dsimp [M] at *
  nlinarith

lemma run_sub (n a : ℕ) (v : List ℕ) :
    Runs subCode (n::a::v) [a-n] (100000*(magnitude (n::a::v)+2)^2) := by
  let M := magnitude (n::a::v)
  have hn : n≤M := by dsimp [M]; omega
  have ha : a≤M := by dsimp [M]; omega
  have hv : magnitude (a::v)≤M := by dsimp [M]; omega
  have hr : ∀i≤n,a-i≤M := by intro i _; omega
  have hg : ∀i<n, Runs (.comp .pred .tail) (i::(a-i)::a::v) [a-(i+1)] (1000*(M+1)) := by
    intro i hi
    have hh := run_comp (run_tail (i::(a-i)::a::v)) (run_pred ((a-i)::a::v))
    have he : a-i-1=a-(i+1) := by omega
    simp only [List.headI_cons,he] at hh
    apply hh.mono
    simp only [magnitude_cons] at *
    omega
  have hh := run_prec .head (.comp .pred .tail) n (fun i=>a-i) (a::v) M
    (300*(M+1)) (1000*(M+1)) hn hr hv ((run_head (a::v)).mono (by gcongr)) hg
  apply hh.mono
  dsimp [M] at *
  nlinarith

def mulCode : Code := .prec .zero (.comp addCode .tail)

lemma run_mul (n a : ℕ) (v : List ℕ) :
    Runs mulCode (n::a::v) [a*n] (10000000*(magnitude (n::a::v)+2)^6) := by
  let S := magnitude (n::a::v)
  let M := (S+2)^2
  have hnS : n≤S := by dsimp [S]; omega
  have haS : a≤S := by dsimp [S]; omega
  have hvS : magnitude (a::v)≤S := by dsimp [S]; omega
  have hSM : S≤M := by dsimp [M]; nlinarith
  have hr : ∀i≤n,a*i≤M := by
    intro i hi
    have hh : a*i≤S*S := Nat.mul_le_mul haS (hi.trans hnS)
    dsimp [M]; nlinarith
  have hg : ∀i<n,Runs (.comp addCode .tail) (i::(a*i)::a::v) [a*(i+1)]
      (1000000*(M+2)^2) := by
    intro i hi
    have hh := run_comp (run_tail (i::(a*i)::a::v)) (run_add (a*i) a v)
    have he : a+a*i=a*(i+1) := by ring
    rw [he] at hh
    apply hh.mono
    have hri := hr i (by omega)
    simp only [magnitude_cons] at *
    have hinput : a*i+1+(a+1+magnitude v)≤M+1+S := by omega
    have hiM : i≤M := (Nat.le_of_lt hi).trans (hnS.trans hSM)
    calc
      _ ≤ 32*(M+1+(2*M+1)+1)+100000*(2*M+3)^2+1 := by
        have ht : i+1+(a*i+1+(a+1+magnitude v))+1 ≤
            M+1+(2*M+1)+1 := by omega
        have hc : a*i+1+(a+1+magnitude v)+2 ≤ 2*M+3 := by omega
        exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 32 ht)
          (Nat.mul_le_mul_left 100000 (Nat.pow_le_pow_left hc 2))) 1
      _ ≤ _ := by ring_nf; omega
  have hh := run_prec .zero (.comp addCode .tail) n (fun i=>a*i) (a::v) M
    (210*(M+1)) (1000000*(M+2)^2) (hnS.trans hSM) hr (hvS.trans hSM)
    ((run_const_zero (a::v)).mono (by gcongr; exact hvS.trans hSM)) hg
  apply hh.mono
  change 210*(M+1)+(n+2)*(1000000*(M+2)^2+50000*(M+1))≤10000000*(S+2)^6
  calc
    _ ≤ 210*(M+1)+(S+2)*(1000000*(M+2)^2+50000*(M+1)) := by gcongr
    _ ≤ _ := by dsimp [M]; ring_nf; omega

end MinUncut.Costed

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_PolynomialArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Costed.PolyProgram
open Turing.ToPartrec Polynomial

def pairPack : PolyProgram (fun v=>[v.headI,v.tail.headI]) :=
  head.cons ((head.comp tail).cons nil)

def binary (c : Code) (f : ℕ → ℕ → ℕ) (p : Polynomial ℕ)
    (hr : ∀a b,Runs c [a,b] [f a b] (p.eval (magnitude [a,b])))
    (hs : ∀a b,magnitude [f a b]≤p.eval (magnitude [a,b])) :
    PolyProgram (fun v=>[f v.headI v.tail.headI]) where
  code := .comp c pairPack.code
  bound := pairPack.bound+p.comp pairPack.bound+1
  run v := by
    have h := run_comp (pairPack.run v) (hr v.headI v.tail.headI)
    apply h.mono
    simp only [eval_add,eval_comp,eval_one]
    have h' := evalNat_mono p (pairPack.size v)
    omega
  size v := by
    have h := (hs v.headI v.tail.headI).trans (evalNat_mono p (pairPack.size v))
    simp only [eval_add,eval_comp,eval_one]
    omega

def add : PolyProgram (fun v=>[v.headI+v.tail.headI]) :=
  binary addCode (fun a b=>a+b) (C 100000*(X+2)^2)
    (by intro a b; simpa [Nat.add_comm] using run_add a b [])
    (by intro a b; simp only [magnitude_cons,magnitude_nil,eval_mul,eval_C,eval_pow,
                               eval_add,eval_X,eval_ofNat]; nlinarith)

def sub : PolyProgram (fun v=>[v.headI-v.tail.headI]) :=
  (binary subCode (fun a b=>b-a) (C 100000*(X+2)^2)
    (by intro a b; simpa using run_sub a b [])
    (by intro a b; simp only [magnitude_cons,magnitude_nil,eval_mul,eval_C,eval_pow,
                               eval_add,eval_X,eval_ofNat];
        have h : b-a≤b := Nat.sub_le ..
        have hp : b+1≤(a+1+(b+1+0)+2)^2 :=
          (by omega : b+1≤a+1+(b+1+0)+2).trans (Nat.le_self_pow (by omega) _)
        omega)).comp
      ((head.comp tail).cons (head.cons nil))

def mul : PolyProgram (fun v=>[v.headI*v.tail.headI]) :=
  binary mulCode (fun a b=>a*b) (C 10000000*(X+2)^6)
    (by intro a b; simpa [Nat.mul_comm] using run_mul a b [])
    (by intro a b
        simp only [magnitude_cons,magnitude_nil,eval_mul,eval_C,eval_pow,
          eval_add,eval_X,eval_ofNat]
        have h₁ : a*b+1≤(a+1+(b+1+0)+2)^2 := by nlinarith
        have h₂ : (a+1+(b+1+0)+2)^2≤(a+1+(b+1+0)+2)^6 :=
          Nat.pow_le_pow_right (by omega) (by omega)
        omega)

def addOf {f g : List ℕ → List ℕ} (F : PolyProgram f) (G : PolyProgram g) :
    PolyProgram (fun v=>[(f v).headI+(g v).headI]) := add.comp (F.cons (G.cons nil))
def subOf {f g : List ℕ → List ℕ} (F : PolyProgram f) (G : PolyProgram g) :
    PolyProgram (fun v=>[(f v).headI-(g v).headI]) := sub.comp (F.cons (G.cons nil))
def mulOf {f g : List ℕ → List ℕ} (F : PolyProgram f) (G : PolyProgram g) :
    PolyProgram (fun v=>[(f v).headI*(g v).headI]) := mul.comp (F.cons (G.cons nil))

end MinUncut.Costed.PolyProgram

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_PolynomialRecursor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.Arena

open Turing.ToPartrec

def maximum (v : List ℕ) : ℕ := v.foldr max 0
@[simp] lemma maximum_nil : maximum []=0 := rfl
@[simp] lemma maximum_cons (a : ℕ) (v : List ℕ) : maximum (a::v)=max a (maximum v) := rfl

lemma maximum_append (v w : List ℕ) : maximum (v++w)=max (maximum v) (maximum w) := by
  induction v with
  | nil => simp
  | cons a v ih => simp only [List.cons_append,maximum_cons,ih,max_assoc]

lemma maximum_drop (v : List ℕ) (n : ℕ) : maximum (v.drop n)≤ maximum v := by
  induction n generalizing v with
  | zero => exact le_rfl
  | succ n ih =>
    cases v with
    | nil => simp
    | cons a v => exact (ih v).trans (le_max_right _ _)

lemma head_le_maximum (v : List ℕ) : v.headI≤ maximum v := by
  cases v with
  | nil => rfl
  | cons a v => exact le_max_left _ _

lemma maximum_le_magnitude (v : List ℕ) : maximum v≤ magnitude v := by
  induction v with
  | nil => rfl
  | cons a v ih => simp only [maximum_cons,magnitude_cons]; omega

lemma length_le_magnitude (v : List ℕ) : v.length≤ magnitude v := by
  induction v with
  | nil => rfl
  | cons a v ih => simp only [List.length_cons,magnitude_cons]; omega

lemma magnitude_le_length_maximum (v : List ℕ) : magnitude v≤v.length*(maximum v+1) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    simp only [magnitude_cons,List.length_cons,maximum_cons]
    have ha : a≤ max a (maximum v) := le_max_left _ _
    have hh : maximum v≤ max a (maximum v) := le_max_right _ _
    have hi := Nat.mul_le_mul_left v.length (Nat.add_le_add_right hh 1)
    nlinarith

end MinUncut.Costed.Arena

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Runtime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineComposition

def advance {σ : Type} (step : σ → Option σ) (state : Option σ) : Option σ :=
  state.bind step

@[simp] theorem advance_none {σ : Type} (step : σ → Option σ) :
    advance step none = none := rfl

@[simp] theorem advance_some {σ : Type} (step : σ → Option σ) (state : σ) :
    advance step (some state) = step state := rfl

@[simp] theorem advance_iterate_none {σ : Type} (step : σ → Option σ) (n : Nat) :
    (advance step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, advance_none]

end MinUncutGames.Foundations.Complexity.MachineComposition

namespace MinUncutGames.Reduction.MachineTransfer

open _root_.Turing

variable {α β : Type} [Fintype α] [Fintype β]

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

def tapesAt (src dst : K) (base : (k : K) → List (Γ k))
    (input : List (Γ src)) (output : List (Γ dst)) : (k : K) → List (Γ k) :=
  Function.update (Function.update base src input) dst output

@[simp] theorem tapesAt_src (src dst : K) (distinct : src ≠ dst)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst)) :
    tapesAt src dst base input output src = input := by
  simp [tapesAt, distinct]

@[simp] theorem tapesAt_dst (src dst : K)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst)) :
    tapesAt src dst base input output dst = output := by
  simp [tapesAt]

@[simp] theorem tapesAt_self (src dst : K) (base : (k : K) → List (Γ k)) :
    tapesAt src dst base (base src) (base dst) = base := by
  simp [tapesAt]

end MinUncutGames.Reduction.MachineTransfer

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Game
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncutGames.Foundations.Hastad.SourceGame

open scoped BigOperators
open Target PCP Games SourceContexts

theorem event_nonempty (F : Formula) (hne : F.clauses ≠ []) :
    Nonempty (RandomEvent F) :=
  ⟨(⟨0, List.length_pos_iff.mpr hne⟩, .first)⟩

def eventLaw (F : Formula) (hne : F.clauses ≠ []) :
    FiniteDistribution (RandomEvent F) := by
  let : Nonempty (RandomEvent F) := event_nonempty F hne
  exact FiniteDistribution.uniform _

def visibleQuestion (F : Formula) (e : RandomEvent F) :
    Fin F.«variables» × Fin F.clauses.length :=
  (nameAt (clauseAt F e.1) e.2, e.1)

def baseGame (F : Formula) (hne : F.clauses ≠ []) :
    Game (Fin F.«variables») (Fin F.clauses.length) Bool ClauseAnswer where
  questions := (eventLaw F hne).pushforward (visibleQuestion F)
  accepts := baseAccepts F

@[simp] theorem baseGame_accepts (F : Formula) (hne : F.clauses ≠ [])
    (v : Fin F.«variables») (c : Fin F.clauses.length) (i : Bool) (j : ClauseAnswer) :
    (baseGame F hne).accepts v c i j = baseAccepts F v c i j := rfl

end MinUncutGames.Foundations.Hastad.SourceGame

namespace MinUncutGames.Foundations.Hastad.SourceSoundness

open scoped BigOperators
open Target SourceContexts SourceOccurrences SourceGame

def leftTable (F : Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (v : VariableContext F u) : HalfCube (leftAnchor u) → Bool :=
  fun h => bits ((proofEncoding F u).code (.inl (v, h.val)))

def rightOracle (F : Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (c : ClauseContext F u) : ConditionedOracle (validJ F c) :=
  match h : rightAnchor F c with
  | none => .empty ((rightAnchor_none_iff F c).mp h)
  | some j₀ => .stored j₀
      (fun h => bits ((proofEncoding F u).code
        (.inr (.inl (c, extendRestricted (validJ F c) h.val)))))

@[simp] theorem rightOracle_answer (F : Formula) (u : ℕ)
    (bits : Fin (nBits F u) → Bool) (c : ClauseContext F u) :
    (rightOracle F u bits c).answer = rightResponse F u bits c := by
  unfold rightOracle
  split <;> simp_all [rightResponse, ConditionedOracle.answer]

@[simp] theorem leftTable_answer (F : Formula) (u : ℕ)
    (bits : Fin (nBits F u) → Bool) (v : VariableContext F u) :
    foldedAnswer (leftAnchor u) (leftTable F u bits v) = leftResponse F u bits v := rfl

end MinUncutGames.Foundations.Hastad.SourceSoundness

end
namespace MinUncutGames.Foundations.Hastad.SourceHonest

open MinUncutGames.Reduction.CloneGap
open MinUncutGames.Reduction.FiniteNoise
open scoped BigOperators

def taggedAssignment {V C I J : Type} (left : V → I) (right : C → J) :
    (V × Cube I) ⊕ ((C × Cube J) ⊕ Unit) → Bool
  | .inl (v, f) => f (left v)
  | .inr (.inl (c, g)) => g (right c)
  | .inr (.inr _) => false

@[simp] theorem taggedAssignment_left {V C I J : Type}
    (left : V → I) (right : C → J) (v : V) (f : Cube I) :
    taggedAssignment left right (.inl (v, f)) = f (left v) := rfl

@[simp] theorem taggedAssignment_right {V C I J : Type}
    (left : V → I) (right : C → J) (c : C) (g : Cube J) :
    taggedAssignment left right (.inr (.inl (c, g))) = g (right c) := rfl


open SourceContexts
open SourceOccurrences

def honestGlobal (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool) :
    (VariableContext F u × Cube (I u)) ⊕
      ((ClauseContext F u × Cube (J u)) ⊕ Unit) → Bool :=
  taggedAssignment (fun v => honestI F v assignment) (fun c => honestJ F c assignment)

def honestBits (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool) : Fin (nBits F u) → Bool :=
  assignmentOfKey (variableEncoding F u) (clauseEncoding F u) (iEncoding u)
    (jEncoding u) (honestGlobal F u assignment)

@[simp] theorem honestBits_code (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool)
    (key : GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u)) :
    honestBits F u assignment ((proofEncoding F u).code key) =
      honestGlobal F u assignment key :=
  assignmentOfKey_code (variableEncoding F u) (clauseEncoding F u)
    (iEncoding u) (jEncoding u) (honestGlobal F u assignment) key


end MinUncutGames.Foundations.Hastad.SourceHonest

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineUnaryCounter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineUnaryCounter

open _root_.Turing

variable {K Λ σ : Type} [DecidableEq K]

def counterTapes (counter : K) (base : K → List Bool) (n : Nat)
    (suffix : List Bool) : K → List Bool :=
  Function.update base counter (encodeWord n ++ suffix)

@[simp] theorem counterTapes_counter (counter : K) (base : K → List Bool)
    (n : Nat) (suffix : List Bool) :
    counterTapes counter base n suffix counter = encodeWord n ++ suffix := by
  simp [counterTapes]

end MinUncutGames.Foundations.Complexity.MachineUnaryCounter

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineCompare

open _root_.Turing
open MinUncutGames.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (K : Type) : K → Type := fun _ => Bool
abbrev State (σ : Type) := σ × Bool × Option Bool × Option Bool

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  .load (fun state => (state.1, false, none, none)) (exitAt exit)

def loop (left right : K) (loopLabel : Λ) (equalExit differentExit : Option Λ) :
    TM2.Stmt (Alphabet K) Λ (State σ) :=
  .pop left (fun state head => (state.1, state.2.1, head, state.2.2.2))
    (.pop right (fun state head => (state.1, state.2.1, state.2.2.1, head))
      (.branch (fun state => state.2.2.1.isNone && state.2.2.2.isNone)
        (.branch (fun state => state.2.1) (finish differentExit) (finish equalExit))
        (.load (fun state =>
          (state.1, state.2.1 || decide (state.2.2.1 ≠ state.2.2.2), none, none))
          (.goto fun _ => loopLabel))))

def mismatch (flag : Bool) (leftWord rightWord : List Bool) : Bool :=
  flag || decide (leftWord ≠ rightWord)

@[simp] theorem mismatch_nil_nil (flag : Bool) : mismatch flag [] [] = flag := by
  simp [mismatch]

@[simp] theorem mismatch_nil_cons (flag head : Bool) (tail : List Bool) :
    mismatch flag [] (head :: tail) = true := by simp [mismatch]

@[simp] theorem mismatch_cons_nil (flag head : Bool) (tail : List Bool) :
    mismatch flag (head :: tail) [] = true := by simp [mismatch]

@[simp] theorem mismatch_true (leftWord rightWord : List Bool) :
    mismatch true leftWord rightWord = true := by simp [mismatch]

theorem mismatch_cons (flag leftHead rightHead : Bool) (leftTail rightTail : List Bool) :
    mismatch (flag || decide (leftHead ≠ rightHead)) leftTail rightTail =
      mismatch flag (leftHead :: leftTail) (rightHead :: rightTail) := by
  cases flag <;> cases leftHead <;> cases rightHead <;> simp [mismatch]

@[simp] theorem stepAux_exitAt (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (exitAt exit) state tapes = ⟨exit, state, tapes⟩ := by
  cases exit <;> rfl

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (finish exit) state tapes =
      ⟨exit, (state.1, false, none, none), tapes⟩ := by
  simp [finish, TM2.stepAux]

theorem update_left (left right : K) (distinct : left ≠ right)
    (base : K → List Bool) (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) left replacement =
      tapesAt left right base replacement rightWord := by
  funext k
  by_cases hl : k = left
  · subst k
    simp [tapesAt, distinct]
  · by_cases hr : k = right
    · subst k
      simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hl, hr]

theorem update_right (left right : K) (base : K → List Bool)
    (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) right replacement =
      tapesAt left right base leftWord replacement := by
  simp [tapesAt]

theorem step_empty (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] []⟩ =
      some ⟨if flag then differentExit else equalExit, (ambient, false, none, none),
        tapesAt left right base [] []⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base [] [])) = _
  rw [atLoop]
  cases flag <;>
    simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_nil_cons (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] (head :: tail)⟩ =
      some ⟨some loopLabel, (ambient, true, none, none), tapesAt left right base [] tail⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base [] (head :: tail))) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_cons_nil (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base (head :: tail) []⟩ =
      some ⟨some loopLabel, (ambient, true, none, none), tapesAt left right base tail []⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base (head :: tail) [])) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_cons_cons (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftHead rightHead : Bool) (leftTail rightTail : List Bool)
    (ambient : σ) (flag : Bool) (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base (leftHead :: leftTail) (rightHead :: rightTail)⟩ =
      some ⟨some loopLabel,
        (ambient, flag || decide (leftHead ≠ rightHead), none, none),
        tapesAt left right base leftTail rightTail⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base (leftHead :: leftTail) (rightHead :: rightTail))) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem trace_left_empty (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (rightWord : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] rightWord⟩) =
      some ⟨if mismatch flag [] rightWord then differentExit else equalExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  induction rightWord generalizing flag leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, mismatch_nil_nil] using
      step_empty left right distinct loopLabel equalExit differentExit program atLoop base
        ambient flag leftRegister rightRegister
  | cons head tail ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
      (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] (head :: tail)⟩) = _
    rw [step_nil_cons left right distinct loopLabel equalExit differentExit program atLoop]
    simpa only [mismatch_true, mismatch_nil_cons] using ih true none none

theorem compareTrace_flag (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨if mismatch flag leftWord rightWord then differentExit else equalExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  induction leftWord generalizing rightWord flag leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_max] using
      trace_left_empty left right distinct loopLabel equalExit differentExit program atLoop
        base rightWord ambient flag leftRegister rightRegister
  | cons head tail ih =>
    cases rightWord with
    | nil =>
      rw [List.length_cons, List.length_nil, Nat.max_zero, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
        (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
          tapesAt left right base (head :: tail) []⟩) = _
      rw [step_cons_nil left right distinct loopLabel equalExit differentExit program atLoop]
      simpa only [List.length_nil, Nat.max_zero, mismatch_true, mismatch_cons_nil] using
        ih [] true none none
    | cons rightHead rightTail =>
      rw [List.length_cons, List.length_cons, Nat.succ_max_succ, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[max tail.length rightTail.length + 1]
        (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
          tapesAt left right base (head :: tail) (rightHead :: rightTail)⟩) = _
      rw [step_cons_cons left right distinct loopLabel equalExit differentExit program atLoop]
      simpa only [mismatch_cons] using
        ih rightTail (flag || decide (head ≠ rightHead)) none none

theorem compareTrace (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, false, leftRegister, rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨if leftWord = rightWord then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  have h := compareTrace_flag left right distinct loopLabel equalExit differentExit program
    atLoop base leftWord rightWord ambient false leftRegister rightRegister
  by_cases heq : leftWord = rightWord <;> simpa [mismatch, heq] using h

theorem compareTrace_fromTapes (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max (base left).length (base right).length + 1]
      (some ⟨some loopLabel, (ambient, false, leftRegister, rightRegister), base⟩) =
      some ⟨if base left = base right then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  simpa only [tapesAt_self] using
    compareTrace left right distinct loopLabel equalExit differentExit program atLoop base
      (base left) (base right) ambient leftRegister rightRegister

def compareInTime (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, false, leftRegister, rightRegister), base⟩
      (some ⟨if base left = base right then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩)
      (max (base left).length (base right).length + 1) where
  steps := max (base left).length (base right).length + 1
  evals_in_steps := compareTrace_fromTapes left right distinct loopLabel equalExit differentExit
    program atLoop base ambient leftRegister rightRegister
  steps_le_m := Nat.le_refl _

@[simp] theorem compareInTime_steps (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    (compareInTime left right distinct loopLabel equalExit differentExit program atLoop base
      ambient leftRegister rightRegister).steps =
        max (base left).length (base right).length + 1 := rfl

end MinUncutGames.Foundations.Complexity.MachineCompare

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ClauseLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceClauseLookup

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition

inductive Tape
  | formula | index | work | scratch | field (slot : Fin 6)
  deriving DecidableEq, Fintype

def scanTapes (base : Tape → List Bool) (index : Nat)
    (indexSuffix input : List Bool) : Tape → List Bool :=
  MachineUnaryCounter.counterTapes .index (Function.update base .work input) index indexSuffix

@[simp] theorem scanTapes_work (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) : scanTapes base i indexSuffix input .work = input := by
  simp [scanTapes, MachineUnaryCounter.counterTapes]

@[simp] theorem scanTapes_index (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) :
    scanTapes base i indexSuffix input .index = encodeWord i ++ indexSuffix := by
  simp [scanTapes, MachineUnaryCounter.counterTapes]

end MinUncutGames.Foundations.Hastad.SourceClauseLookup

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ContextLoad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceContextLoad

open _root_.Turing MinUncutGames.Foundations.Complexity
open MachineComposition

inductive Tape (u : Nat) (Extra : Type)
  | formula | index | work | scratch | copyScratch
  | current (coordinate : Fin u) | remaining (coordinate : Fin u)
  | field (coordinate : Fin u) (slot : Fin 6)
  | extra (value : Extra)
  deriving DecidableEq, Fintype

variable {u : Nat} {Extra : Type}

def place (j : Fin u) : SourceClauseLookup.Tape → Tape u Extra
  | .formula => .formula | .index => .index | .work => .work | .scratch => .scratch
  | .field s => .field j s

def fill (j : Fin u) (base : Tape u Extra → List Bool)
    (localTapes : SourceClauseLookup.Tape → List Bool) : Tape u Extra → List Bool
  | .formula => localTapes .formula | .index => localTapes .index
  | .work => localTapes .work | .scratch => localTapes .scratch
  | .field i s => if i = j then localTapes (.field s) else base (.field i s)
  | p => base p

@[simp] theorem fill_place (j : Fin u) (base : Tape u Extra → List Bool)
    (localTapes : SourceClauseLookup.Tape → List Bool) (p : SourceClauseLookup.Tape) :
    fill j base localTapes (place j p) = localTapes p := by
  cases p <;> simp [fill, place]

@[simp] theorem fill_self (j : Fin u) (base : Tape u Extra → List Bool) :
    fill j base (base ∘ place j) = base := by
  funext p
  cases p <;> simp [fill, place]
  intro h
  subst h
  rfl

variable [DecidableEq Extra]

def coordinateOutput {n : Nat} (j : Fin u) (clause : Target.Clause n)
    (base : Tape u Extra → List Bool) : Tape u Extra → List Bool
  | .index | .work => []
  | .field k s => if k = j then
      encodeWord ((clauseWords clause)[s.val]'(by simp)) ++ base (.field k s)
    else base (.field k s)
  | p => base p

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_current {n : Nat} (j k : Fin u) (clause : Target.Clause n)
    (base : Tape u Extra → List Bool) :
    coordinateOutput j clause base (.current k) = base (.current k) := rfl

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_remaining {n : Nat} (j k : Fin u) (clause : Target.Clause n)
    (base : Tape u Extra → List Bool) :
    coordinateOutput j clause base (.remaining k) = base (.remaining k) := rfl

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_field {n : Nat} (j : Fin u) (s : Fin 6)
    (clause : Target.Clause n) (base : Tape u Extra → List Bool) :
    coordinateOutput j clause base (.field j s) =
      encodeWord ((clauseWords clause)[s.val]'(by simp)) ++ base (.field j s) := by
  simp [coordinateOutput]

def variableSlot (s : Fin 3) : Fin 6 := ⟨2 * s.val, by omega⟩
def variableField (j : Fin u) (s : Fin 3) : Tape u Extra := .field j (variableSlot s)

end MinUncutGames.Foundations.Hastad.SourceContextLoad

namespace MinUncutGames.Foundations.Hastad.SourceLocalSignature

open Target PCP SourceContexts

abbrev Position (u : ℕ) := Fin u × Slot
abbrev NameProfile (u : ℕ) := Position u → Position u → Bool

structure Signature (u : ℕ) where
  signs : Position u → Bool
  sameName : NameProfile u
  selected : SlotContext u
  deriving DecidableEq

@[simp] theorem card_position (u : ℕ) : Fintype.card (Position u) = 3 * u := by
  simp [Position, Nat.mul_comm]

def positiveAt {n : ℕ} (clause : Clause n) : Slot → Bool
  | .first => clause[0].positive
  | .second => clause[1].positive
  | .third => clause[2].positive

def occurrenceName (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (p : Position u) : Fin F.«variables» :=
  nameAt (clauseAt F (c p.1)) p.2

def contextNameProfile (F : Formula) {u : ℕ} (c : ClauseContext F u) : NameProfile u :=
  fun p q => decide (occurrenceName F c p = occurrenceName F c q)

def ofContext (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (selected : SlotContext u) : Signature u where
  signs p := positiveAt (clauseAt F (c p.1)) p.2
  sameName := contextNameProfile F c
  selected := selected

@[simp] theorem ofContext_signs (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (p : Position u) :
    (ofContext F c s).signs p = positiveAt (clauseAt F (c p.1)) p.2 := rfl

@[simp] theorem ofContext_sameName (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (p q : Position u) :
    (ofContext F c s).sameName p q =
      decide (occurrenceName F c p = occurrenceName F c q) := rfl

@[simp] theorem ofContext_selected (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) : (ofContext F c s).selected = s := rfl

def signatureSatisfies {u : ℕ} (σ : Signature u) (j : J u) (t : Fin u) : Bool :=
  (literalValue (σ.signs (t, .first)) (j t).first ||
    literalValue (σ.signs (t, .second)) (j t).second) ||
    literalValue (σ.signs (t, .third)) (j t).third

@[simp] theorem signatureSatisfies_ofContext (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) (j : J u) (t : Fin u) :
    signatureSatisfies (ofContext F c s) j t =
      localSatisfies (clauseAt F (c t)) (j t) := rfl

end MinUncutGames.Foundations.Hastad.SourceLocalSignature

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ContextPrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MinUncutGames.Foundations.Hastad.SourceLoopInit

open _root_.Turing MinUncutGames.Foundations.Complexity
open MachineComposition

inductive HeaderTape
  | variableCount | clauseCount
  deriving DecidableEq

abbrev Tape (u : Nat) (Extra : Type) := SourceContextLoad.Tape u (HeaderTape ⊕ Extra)

variable {u : Nat} {Extra : Type}

def variableHeader : Tape u Extra := .extra (.inl .variableCount)
def clauseHeader : Tape u Extra := .extra (.inl .clauseCount)

variable [DecidableEq Extra]

def headerOutput (F : Target.Formula) (base : Tape u Extra → List Bool) : Tape u Extra → List Bool :=
  Function.update (Function.update (Function.update base .work []) variableHeader
    (encodeWord F.«variables» ++ base variableHeader)) clauseHeader
    (encodeWord F.clauses.length ++ base clauseHeader)

def digitOutput (j : Fin u) (m : Nat) (base : Tape u Extra → List Bool) : Tape u Extra → List Bool :=
  Function.update (Function.update base (.current j) (encodeWord 0)) (.remaining j) (encodeWord (m - 1))

theorem digitOutput_frame (j : Fin u) (m : Nat) (base : Tape u Extra → List Bool)
    (p : Tape u Extra) (hc : p ≠ .current j) (hr : p ≠ .remaining j) :
    digitOutput j m base p = base p := by simp [digitOutput, hc, hr]

def stageTapes (m : Nat) (base : Tape u Extra → List Bool) : Nat → Tape u Extra → List Bool
  | 0 => base
  | r + 1 => if h : r < u then digitOutput ⟨r, h⟩ m (stageTapes m base r)
    else stageTapes m base r

theorem stageTapes_frame (m : Nat) (base : Tape u Extra → List Bool) (r : Nat)
    (p : Tape u Extra) (hc : ∀ j, p ≠ .current j) (hr : ∀ j, p ≠ .remaining j) :
    stageTapes m base r p = base p := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [stageTapes]
    split
    · rw [digitOutput_frame _ _ _ _ (hc _) (hr _), ih]
    · exact ih

theorem stageTapes_current (m : Nat) (base : Tape u Extra → List Bool) (r : Nat) (j : Fin u) :
    stageTapes m base r (.current j) = if j.val < r then encodeWord 0 else base (.current j) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r, hr⟩ : Fin u)
      · subst j; simp [digitOutput]
      · rw [digitOutput_frame _ _ _ _ (by simpa using hj) (by simp), ih]
        have hval : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
        have he : j.val < r + 1 ↔ j.val < r := by omega
        simp only [he]
    next hr =>
      rw [ih]
      have hjr : j.val < r := by omega
      have hjr' : j.val < r + 1 := by omega
      simp only [hjr, hjr', ite_true]

theorem stageTapes_remaining (m : Nat) (base : Tape u Extra → List Bool) (r : Nat) (j : Fin u) :
    stageTapes m base r (.remaining j) =
      if j.val < r then encodeWord (m - 1) else base (.remaining j) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r, hr⟩ : Fin u)
      · subst j; simp [digitOutput]
      · rw [digitOutput_frame _ _ _ _ (by simp) (by simpa using hj), ih]
        have hval : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
        have he : j.val < r + 1 ↔ j.val < r := by omega
        simp only [he]
    next hr =>
      rw [ih]
      have hjr : j.val < r := by omega
      have hjr' : j.val < r + 1 := by omega
      simp only [hjr, hjr', ite_true]

def outputTapes (F : Target.Formula) (base : Tape u Extra → List Bool) : Tape u Extra → List Bool :=
  stageTapes F.clauses.length (headerOutput F base) u

@[simp] theorem output_current (F : Target.Formula) (base : Tape u Extra → List Bool) (j : Fin u) :
    outputTapes F base (.current j) = encodeWord 0 := by
  simp only [outputTapes, stageTapes_current, j.isLt, ite_true]

@[simp] theorem output_remaining (F : Target.Formula) (base : Tape u Extra → List Bool) (j : Fin u) :
    outputTapes F base (.remaining j) = encodeWord (F.clauses.length - 1) := by
  simp only [outputTapes, stageTapes_remaining, j.isLt, ite_true]

@[simp] theorem output_work (F : Target.Formula) (base : Tape u Extra → List Bool) :
    outputTapes F base .work = [] := by
  rw [outputTapes, stageTapes_frame _ _ _ _ (by simp) (by simp)]
  simp [headerOutput, variableHeader, clauseHeader]

@[simp] theorem output_variableHeader (F : Target.Formula) (base : Tape u Extra → List Bool) :
    outputTapes F base variableHeader = encodeWord F.«variables» ++ base variableHeader := by
  rw [outputTapes, stageTapes_frame _ _ _ _ (by simp [variableHeader]) (by simp [variableHeader])]
  simp [headerOutput, variableHeader, clauseHeader]

@[simp] theorem output_clauseHeader (F : Target.Formula) (base : Tape u Extra → List Bool) :
    outputTapes F base clauseHeader = encodeWord F.clauses.length ++ base clauseHeader := by
  rw [outputTapes, stageTapes_frame _ _ _ _ (by simp [clauseHeader]) (by simp [clauseHeader])]
  simp [headerOutput]

end MinUncutGames.Foundations.Hastad.SourceLoopInit

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_IterationMagnitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.Arena

lemma iterate_length_maximum {f : List ℕ → List ℕ} (L M : ℕ)
    (hf : ∀v,(f v).length≤v.length+L ∧ maximum (f v)≤ maximum v+M) (v : List ℕ) (i : ℕ) :
    (f^[i] v).length≤v.length+L*i ∧ maximum (f^[i] v)≤ maximum v+M*i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have hh := hf (f^[i] v)
    simp only [Nat.mul_add,Nat.mul_one] at *
    constructor <;> omega

lemma iterate_magnitude {f : List ℕ → List ℕ} (L M : ℕ)
    (hf : ∀v,(f v).length≤v.length+L ∧ maximum (f v)≤ maximum v+M)
    (n : ℕ) (v : List ℕ) (i : ℕ) (hi : i≤n) :
    magnitude (f^[i] v)≤(L+1)*(M+1)*(magnitude (n::v)+1)^2 := by
  have hb := iterate_length_maximum L M hf v i
  have hl := length_le_magnitude v
  have hm := maximum_le_magnitude v
  have hs := magnitude_le_length_maximum (f^[i] v)
  have hin : i ≤ magnitude (n::v)+1 := by simp only [magnitude_cons]; omega
  have h1 : (f^[i] v).length≤(L+1)*(magnitude (n::v)+1) := by
    have hh := Nat.mul_le_mul_left L hin
    simp only [magnitude_cons] at hh ⊢
    nlinarith
  have h2 : maximum (f^[i] v)+1≤(M+1)*(magnitude (n::v)+1) := by
    have hh := Nat.mul_le_mul_left M hin
    simp only [magnitude_cons] at hh ⊢
    nlinarith
  have h := Nat.mul_le_mul h1 h2
  nlinarith

noncomputable def PolyProgram.safeIterate {f : List ℕ → List ℕ} (F : PolyProgram f) (L M : ℕ)
    (hf : ∀v,(f v).length≤v.length+L ∧ maximum (f v)≤ maximum v+M) :
    PolyProgram (fun v=>f^[v.headI] v.tail) :=
  PolyProgram.iterate F (Polynomial.C ((L+1)*(M+1))*(Polynomial.X+1)^2) (by
    intro n v i hi
    simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using iterate_magnitude L M hf n v i hi)

end MinUncut.Costed.Arena

namespace MinUncut.Costed.Division
open Arena

def step (v : List ℕ) : List ℕ :=
  let q := (v.drop 0).headI
  let r := (v.drop 1).headI
  let d := (v.drop 2).headI
  if r+1=d then (q+1)::0::d::v.drop 3 else q::(r+1)::d::v.drop 3

lemma step_exact (n d : ℕ) (v : List ℕ) :
    step (n/d::n%d::d::v)=((n+1)/d)::((n+1)%d)::d::v := by
  by_cases hd : d=0
  · subst d
    simp [step]
  have hp : 0<d := by omega
  have hm := Nat.mod_lt n hp
  have hn : n=n/d*d+n%d := by simpa only [Nat.mul_comm] using (Nat.div_add_mod n d).symm
  by_cases hc : n%d+1=d
  · have he : n+1=(n/d+1)*d := by nlinarith
    simp only [step,List.drop_zero,List.headI_cons,List.drop_succ_cons,hc,ite_true,he,Nat.mul_div_cancel _ hp,Nat.mul_mod_left]
  · have he : n+1=n/d*d+(n%d+1) := by omega
    have hr : n%d+1<d := by omega
    simp only [step,List.drop_zero,List.headI_cons,List.drop_succ_cons,hc,ite_false,he]
    have hdv : (n/d*d+(n%d+1))/d=n/d := by
      rw [Nat.mul_comm (n/d) d,Nat.mul_add_div hp,Nat.div_eq_of_lt hr,Nat.add_zero]
    have hmd : (n/d*d+(n%d+1))%d=n%d+1 := by
      rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr]
    rw [hdv,hmd]

lemma iterate_exact (n d : ℕ) (v : List ℕ) :
    step^[n] (0::0::d::v)=n/d::n%d::d::v := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',ih,step_exact]

end MinUncut.Costed.Division

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_ArithmeticExpression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Costed
inductive AExpr where
  | const (n : ℕ)
  | reg (i : ℕ)
  | add (a b : AExpr)
  | sub (a b : AExpr)
  | mul (a b : AExpr)
  | div (a b : AExpr)
  | mod (a b : AExpr)
  | eq (a b : AExpr)
  | le (a b : AExpr)
  | at (a : AExpr)
  | cond (e a b : AExpr)

def AExpr.eval : AExpr → List ℕ → ℕ
  | .const n,_ => n
  | .reg i,v => (v.drop i).headI
  | .add a b,v => a.eval v+b.eval v
  | .sub a b,v => a.eval v-b.eval v
  | .mul a b,v => a.eval v*b.eval v
  | .div a b,v => a.eval v/b.eval v
  | .mod a b,v => a.eval v%b.eval v
  | .eq a b,v => if a.eval v=b.eval v then 1 else 0
  | .le a b,v => if a.eval v≤b.eval v then 1 else 0
  | .at a,v => (v.drop (a.eval v)).headI
  | .cond e a b,v => if e.eval v=0 then a.eval v else b.eval v

def AExpr.pow (a : AExpr) : ℕ → AExpr
  | 0 => .const 1
  | n+1 => .mul (a.pow n) a
lemma AExpr.eval_pow (a : AExpr) (n : ℕ) (v : List ℕ) : (a.pow n).eval v=a.eval v^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow,eval,ih,pow_succ]

def AExpr.sum : List AExpr → AExpr
  | [] => .const 0
  | a::as => .add a (sum as)
lemma AExpr.eval_sum (as : List AExpr) (v : List ℕ) : (sum as).eval v=(as.map (fun a=>a.eval v)).sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [sum,eval,List.map_cons,List.sum_cons,ih]

def AExpr.lookup (a : AExpr) : List (ℕ × ℕ) → AExpr
  | [] => .const 0
  | (i,x)::xs => .cond (.eq a (.const i)) (a.lookup xs) (.const x)
def AExpr.lookupValue (n : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (i,x)::xs => if n=i then x else lookupValue n xs
lemma AExpr.eval_lookup (a : AExpr) (xs : List (ℕ × ℕ)) (v : List ℕ) :
    (a.lookup xs).eval v=lookupValue (a.eval v) xs := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨i,x⟩
    by_cases h : a.eval v=i <;> simp only [lookup,eval,lookupValue,h,ite_true,ite_false,
      Nat.one_ne_zero,ih]

end MinUncut.Costed

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineTransducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineUnaryMultiply

open _root_.Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

def resultTapes (slots : Fin 5 ↪ K) (base : K → List Bool) (product : ℕ) : K → List Bool :=
  Function.update base (slots 2) (encodeWord product ++ base (slots 2))

@[simp] theorem resultTapes_output (slots : Fin 5 ↪ K) (base : K → List Bool) (p : ℕ) :
    resultTapes slots base p (slots 2) = encodeWord p ++ base (slots 2) := by
  simp [resultTapes]

end MinUncutGames.Foundations.Complexity.MachineUnaryMultiply

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineUnaryAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineUnaryAddAt

open _root_.Turing
open Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

def unaryTapes (source destination : K) (base : K → List Bool) (a b : Nat)
    (sourceSuffix destinationSuffix : List Bool) : K → List Bool :=
  tapesAt source destination base (encodeWord a ++ sourceSuffix)
    (encodeWord b ++ destinationSuffix)

@[simp] theorem unaryTapes_source (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool) :
    unaryTapes source destination base a b sourceSuffix destinationSuffix source =
      encodeWord a ++ sourceSuffix := by
  simp [unaryTapes, distinct]

@[simp] theorem unaryTapes_destination (source destination : K)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool) :
    unaryTapes source destination base a b sourceSuffix destinationSuffix destination =
      encodeWord b ++ destinationSuffix := by
  simp [unaryTapes]

end MinUncutGames.Foundations.Complexity.MachineUnaryAddAt

namespace MinUncutGames.Foundations.Complexity.MachineRadixStep

open _root_.Turing

variable {K Λ σ : Type}

variable [DecidableEq K]

def resultTapes (slots : Fin 6 ↪ K) (base : K → List Bool) (value : ℕ) : K → List Bool :=
  Function.update base (slots 3) (encodeWord value ++ base (slots 3))

@[simp] theorem resultTapes_output (slots : Fin 6 ↪ K) (base : K → List Bool) (value : ℕ) :
    resultTapes slots base value (slots 3) = encodeWord value ++ base (slots 3) := by
  simp [resultTapes]

end MinUncutGames.Foundations.Complexity.MachineRadixStep

namespace MinUncutGames.Foundations.Complexity.MachineHorner

open _root_.Turing

variable {K Λ σ : Type} {width : Nat}

abbrev Layout (width : Nat) := Fin 6 ⊕ Fin width

def parity : Nat → Bool
  | 0 => false
  | n + 1 => !(parity n)

def accumulator (flip : Bool) : Fin 6 := if flip then 2 else 1

@[simp] theorem accumulator_ne (flip : Bool) : accumulator flip ≠ accumulator (!flip) := by
  cases flip <;> decide

def radixLayout (flip : Bool) (i : Fin width) : Fin 6 ↪ Layout width where
  toFun
    | 0 => .inl 0
    | 1 => .inl (accumulator flip)
    | 2 => .inr i
    | 3 => .inl (accumulator (!flip))
    | 4 => .inl 4
    | 5 => .inl 5
  inj' := by
    intro a b h
    cases flip <;> fin_cases a <;> fin_cases b <;> simp [accumulator] at h ⊢

def radixSlots (slots : Layout width ↪ K) (i : Fin width) : Fin 6 ↪ K :=
  (radixLayout (parity i.val) i).trans slots

@[simp] theorem radixSlots_base (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 0 = slots (.inl 0) := rfl
@[simp] theorem radixSlots_acc (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 1 = slots (.inl (accumulator (parity i.val))) := rfl
@[simp] theorem radixSlots_digit (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 2 = slots (.inr i) := rfl
@[simp] theorem radixSlots_out (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 3 = slots (.inl (accumulator (parity (i.val + 1)))) := rfl
@[simp] theorem radixSlots_counter (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 4 = slots (.inl 4) := rfl
@[simp] theorem radixSlots_scratch (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 5 = slots (.inl 5) := rfl

variable [DecidableEq K]

def resultTapes (slots : Layout width ↪ K) (base : K → List Bool) (acc : Nat) : K → List Bool :=
  Function.update base (slots (.inl 3)) (encodeWord acc ++ base (slots (.inl 3)))

open scoped BigOperators

@[simp] theorem resultTapes_output (slots : Layout width ↪ K) (base : K → List Bool) (acc : Nat) :
    resultTapes slots base acc (slots (.inl 3)) = encodeWord acc ++ base (slots (.inl 3)) := by
  simp [resultTapes]

end MinUncutGames.Foundations.Complexity.MachineHorner

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_AddressArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceRankPhase

open _root_.Turing Complexity
open scoped BigOperators
open Target SourceContexts SourceOccurrences

variable {K Λ σ : Type} {width : Nat}

def reverseSlots (slots : MachineHorner.Layout width ↪ K) : MachineHorner.Layout width ↪ K :=
  (Equiv.sumCongr (Equiv.refl (Fin 6)) (Fin.revPerm (n := width))).toEmbedding.trans slots

@[simp] theorem reverseSlots_control (slots : MachineHorner.Layout width ↪ K) (i : Fin 6) :
    reverseSlots slots (.inl i) = slots (.inl i) := rfl

@[simp] theorem reverseSlots_digit (slots : MachineHorner.Layout width ↪ K) (i : Fin width) :
    reverseSlots slots (.inr i) = slots (.inr i.rev) := rfl

variable [DecidableEq K]

variable {u : Nat} {Extra : Type}

def clauseSlots (controls : Fin 6 ↪ Extra) :
    MachineHorner.Layout u ↪ SourceContextLoad.Tape u Extra where
  toFun
    | .inl i => .extra (controls i)
    | .inr i => .current i
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (controls.injective (SourceContextLoad.Tape.extra.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (SourceContextLoad.Tape.current.inj h)

def variableSlots (controls : Fin 6 ↪ Extra) (selected : SlotContext u) :
    MachineHorner.Layout u ↪ SourceContextLoad.Tape u Extra where
  toFun
    | .inl i => .extra (controls i)
    | .inr i => SourceContextLoad.variableField i (slotEncoding.code (selected i))
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (controls.injective (SourceContextLoad.Tape.extra.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (SourceContextLoad.Tape.field.inj h).1

@[simp] theorem clauseSlots_control (controls : Fin 6 ↪ Extra) (i : Fin 6) :
    clauseSlots (u := u) controls (.inl i) = .extra (controls i) := rfl

@[simp] theorem clauseSlots_digit (controls : Fin 6 ↪ Extra) (i : Fin u) :
    clauseSlots controls (.inr i) = .current i := rfl

@[simp] theorem variableSlots_control (controls : Fin 6 ↪ Extra) (selected : SlotContext u) (i : Fin 6) :
    variableSlots controls selected (.inl i) = .extra (controls i) := rfl

@[simp] theorem variableSlots_digit (controls : Fin 6 ↪ Extra) (selected : SlotContext u) (i : Fin u) :
    variableSlots controls selected (.inr i) =
      SourceContextLoad.variableField i (slotEncoding.code (selected i)) := rfl

end MinUncutGames.Foundations.Hastad.SourceRankPhase

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RuntimeModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.CookLevin.PolynomialMachine

noncomputable def coefficientPolynomial : List Nat → Polynomial Nat
  | [] => 0
  | a :: rest => coefficientPolynomial rest * Polynomial.X + Polynomial.C a

noncomputable def coefficients (p : Polynomial Nat) :
    {cs : List Nat // coefficientPolynomial cs = p} := by
  refine Polynomial.recOnHorner p ?_ ?_ ?_
  · exact ⟨[], rfl⟩
  · intro q a hq ha ih
    rcases ih with ⟨cs, hcs⟩
    cases cs with
    | nil =>
      refine ⟨[a], ?_⟩
      rw [← hcs]
      simp [coefficientPolynomial]
    | cons b rest =>
      refine ⟨(b + a) :: rest, ?_⟩
      rw [← hcs]
      simp only [coefficientPolynomial, Polynomial.C_add, add_assoc]
  · intro q hq ih
    rcases ih with ⟨cs, hcs⟩
    refine ⟨0 :: cs, ?_⟩
    simp only [coefficientPolynomial, Polynomial.C_0, add_zero, hcs]

noncomputable def highCoefficients (p : Polynomial Nat) : List Nat :=
  (coefficients p).val.reverse

noncomputable def width (p : Polynomial Nat) : Nat := (highCoefficients p).length

noncomputable def digit (p : Polynomial Nat) (i : Nat) : Nat :=
  if hi : i < width p then (highCoefficients p)[i] else 0

section LiteralFields

open _root_.Turing

variable {K Λ σ : Type} [DecidableEq K]

def prependFieldsTapes (word : K → List Bool) : List K →
    (K → List Bool) → K → List Bool
  | [], tapes => tapes
  | k :: rest, tapes =>
      prependFieldsTapes word rest (Function.update tapes k (word k ++ tapes k))

theorem prependFieldsTapes_apply (word : K → List Bool) (indices : List K)
    (hn : indices.Nodup) (tapes : K → List Bool) (k : K) :
    prependFieldsTapes word indices tapes k =
      if k ∈ indices then word k ++ tapes k else tapes k := by
  induction indices generalizing tapes with
  | nil => simp [prependFieldsTapes]
  | cons j rest ih =>
    have hnodup := List.nodup_cons.mp hn
    rw [prependFieldsTapes, ih hnodup.2]
    by_cases hkj : k = j
    · subst k
      simp [hnodup.1]
    · simp [hkj]

end LiteralFields

noncomputable section

abbrev Layout (p : Polynomial Nat) := MachineHorner.Layout (width p)

def fieldWord (p : Polynomial Nat) : Layout p → List Bool
  | .inl _ => []
  | .inr i => encodeWord (digit p i.val)

def fieldIndices (p : Polynomial Nat) : List (Layout p) :=
  (List.finRange (width p)).map Sum.inr

theorem fieldIndices_nodup (p : Polynomial Nat) : (fieldIndices p).Nodup :=
  (List.nodup_finRange _).map Sum.inr_injective

@[simp] theorem inl_not_mem_fields (p : Polynomial Nat) (i : Fin 6) :
    Sum.inl i ∉ fieldIndices p := by simp [fieldIndices]

@[simp] theorem inr_mem_fields (p : Polynomial Nat) (i : Fin (width p)) :
    Sum.inr i ∈ fieldIndices p := by simp [fieldIndices]

end

end MinUncutGames.Foundations.Complexity.CookLevin.PolynomialMachine

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_HeaderCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MinUncutGames.Foundations.Hastad.SourceHeaderCounts

open _root_.Turing Complexity
open MachineComposition

noncomputable section

namespace Eval

open CookLevin.PolynomialMachine

variable {K Λ σ : Type} [DecidableEq K]

def word (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K) : K → List Bool :=
  Function.extend slots (fieldWord p) (fun _ => [])

def indices (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K) : List K :=
  (fieldIndices p).map slots

omit [DecidableEq K] in
theorem indices_nodup (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K) :
    (indices p slots).Nodup := (fieldIndices_nodup p).map slots.injective

omit [DecidableEq K] in
@[simp] theorem word_slot (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (i : MachineHorner.Layout (width p)) : word p slots (slots i) = fieldWord p i :=
  slots.injective.extend_apply _ _ i

omit [DecidableEq K] in
@[simp] theorem control_not_mem (p : Polynomial Nat)
    (slots : MachineHorner.Layout (width p) ↪ K) (i : Fin 6) :
    slots (.inl i) ∉ indices p slots := by
  simp [indices, slots.injective.eq_iff]

omit [DecidableEq K] in
@[simp] theorem digit_mem (p : Polynomial Nat)
    (slots : MachineHorner.Layout (width p) ↪ K) (i : Fin (width p)) :
    slots (.inr i) ∈ indices p slots := by
  simp [indices, slots.injective.eq_iff]

def prepared (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (base : K → List Bool) : K → List Bool :=
  prependFieldsTapes (word p slots) (indices p slots) base

@[simp] theorem prepared_control (p : Polynomial Nat)
    (slots : MachineHorner.Layout (width p) ↪ K) (base : K → List Bool) (i : Fin 6) :
    prepared p slots base (slots (.inl i)) = base (slots (.inl i)) := by
  rw [prepared, prependFieldsTapes_apply _ _ (indices_nodup p slots)]
  simp

@[simp] theorem prepared_digit (p : Polynomial Nat)
    (slots : MachineHorner.Layout (width p) ↪ K) (base : K → List Bool)
    (i : Fin (width p)) (hi : base (slots (.inr i)) = []) :
    prepared p slots base (slots (.inr i)) = encodeWord (digit p i.val) := by
  rw [prepared, prependFieldsTapes_apply _ _ (indices_nodup p slots)]
  simp [fieldWord, hi]

end Eval

def leftValue (u n : Nat) : Nat := 2 ^ (2 ^ u) * n ^ u
def rightValue (u m : Nat) : Nat := 2 ^ (8 ^ u) * m ^ u
def occurrenceValue (u D m : Nat) : Nat :=
  3 ^ u * (SourceOccurrences.testTapeEncoding u D).size * m ^ u

inductive Kind
  | left | right | occurrences
  deriving DecidableEq

def polynomial (u D : Nat) : Kind → Polynomial Nat
  | .left => Polynomial.C (2 ^ (2 ^ u)) * Polynomial.X ^ u
  | .right => Polynomial.C (2 ^ (8 ^ u)) * Polynomial.X ^ u
  | .occurrences => Polynomial.C (3 ^ u * (SourceOccurrences.testTapeEncoding u D).size) *
      Polynomial.X ^ u

@[simp] theorem polynomial_left_eval (u D n : Nat) :
    (polynomial u D .left).eval n = leftValue u n := by simp [polynomial, leftValue]
@[simp] theorem polynomial_right_eval (u D m : Nat) :
    (polynomial u D .right).eval m = rightValue u m := by simp [polynomial, rightValue]
@[simp] theorem polynomial_occurrences_eval (u D m : Nat) :
    (polynomial u D .occurrences).eval m = occurrenceValue u D m := by
  simp [polynomial, occurrenceValue]

inductive Control
  | variableCount | clauseCount | leftBlockSize | rightTemporary | dummyIndex
  | bitCount | occurrenceCount | accA | accB | counter | scratch
  deriving DecidableEq

abbrev Coefficients (u D : Nat) :=
  Fin (CookLevin.PolynomialMachine.width (polynomial u D .left)) ⊕
    (Fin (CookLevin.PolynomialMachine.width (polynomial u D .right)) ⊕
      Fin (CookLevin.PolynomialMachine.width (polynomial u D .occurrences)))

abbrev Layout (u D : Nat) := Control ⊕ Coefficients u D

def coefficientBlock (u D : Nat) (kind : Kind) :
    Fin (CookLevin.PolynomialMachine.width (polynomial u D kind)) ↪ Coefficients u D :=
  match kind with
  | .left => ⟨Sum.inl, Sum.inl_injective⟩
  | .right => ⟨fun i => .inr (.inl i), Sum.inr_injective.comp Sum.inl_injective⟩
  | .occurrences => ⟨fun i => .inr (.inr i), Sum.inr_injective.comp Sum.inr_injective⟩

def inputControl : Kind → Control
  | .left => .variableCount | _ => .clauseCount

def outputControl : Kind → Control
  | .left => .leftBlockSize | .right => .rightTemporary | .occurrences => .occurrenceCount

def controlSlots (kind : Kind) : Fin 6 ↪ Control where
  toFun i := match i.val with
    | 0 => inputControl kind | 1 => .accA | 2 => .accB
    | 3 => outputControl kind | 4 => .counter | _ => .scratch
  inj' := by
    intro i j h
    cases kind <;> fin_cases i <;> fin_cases j <;> cases h <;> rfl

def localSlots (u D : Nat) (kind : Kind) :
    MachineHorner.Layout (CookLevin.PolynomialMachine.width (polynomial u D kind)) ↪ Layout u D where
  toFun
    | .inl i => .inl (controlSlots kind i)
    | .inr i => .inr (coefficientBlock u D kind i)
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl ((controlSlots kind).injective (Sum.inl.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr ((coefficientBlock u D kind).injective (Sum.inr.inj h))

variable {u D : Nat} {K Λ σ : Type}

def control (slots : Layout u D ↪ K) (c : Control) : K := slots (.inl c)

def evalSlots (slots : Layout u D ↪ K) (kind : Kind) :
    MachineHorner.Layout (CookLevin.PolynomialMachine.width (polynomial u D kind)) ↪ K :=
  (localSlots u D kind).trans slots

@[simp] theorem evalSlots_radix (slots : Layout u D ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 0) = control slots (inputControl kind) := rfl
@[simp] theorem evalSlots_accA (slots : Layout u D ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 1) = control slots .accA := rfl
@[simp] theorem evalSlots_accB (slots : Layout u D ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 2) = control slots .accB := rfl
@[simp] theorem evalSlots_destination (slots : Layout u D ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 3) = control slots (outputControl kind) := rfl
@[simp] theorem evalSlots_counter (slots : Layout u D ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 4) = control slots .counter := rfl
@[simp] theorem evalSlots_scratch (slots : Layout u D ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 5) = control slots .scratch := rfl

end

end MinUncutGames.Foundations.Hastad.SourceHeaderCounts

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_HeaderAccumulate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceHeaderAccumulate

open _root_.Turing MinUncutGames.Foundations.Complexity
open MachineComposition
open MinUncutGames.Reduction.MachineTransfer

structure Layout (K : Type) where
  bits : K
  count : K
  accumulator : K
  bits_count : bits ≠ count
  bits_accumulator : bits ≠ accumulator
  count_accumulator : count ≠ accumulator

end MinUncutGames.Foundations.Hastad.SourceHeaderAccumulate

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_SignatureEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer.LocalTemplate
open MinUncut.Costed
open MinUncutGames.Foundations.Hastad.SourceOccurrences

def constantTable {α : Type} (e : Encoding α) (f : α → ℕ) : List (ℕ × ℕ) :=
  e.enumerate.map (fun a=>((e.code a).val,f a))

end MinUncut.Outer.LocalTemplate

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ExpressionOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap

structure Signature (u : ℕ) where
  positive : Fin u → Slot → Bool
  same : (Fin u × Slot) → (Fin u × Slot) → Bool

def positiveAt {n : ℕ} (c : Clause n) : Slot → Bool
  | .first => (c)[0].positive
  | .second => (c)[1].positive
  | .third => (c)[2].positive

def signature (F : Formula) {u : ℕ} (c : ClauseContext F u) : Signature u where
  positive t := positiveAt (clauseAt F (c t))
  same a b := decide (nameAt (clauseAt F (c a.1)) a.2 = nameAt (clauseAt F (c b.1)) b.2)

def Signature.satisfies {u : ℕ} (S : Signature u) (j : J u) (t : Fin u) : Bool :=
  (literalValue (S.positive t .first) (j t).first ||
    literalValue (S.positive t .second) (j t).second) ||
    literalValue (S.positive t .third) (j t).third

def Signature.valid {u : ℕ} (S : Signature u) (j : J u) : Bool :=
  decide ((∀ t, S.satisfies j t = true) ∧ ∀ t t' s s',
    S.same (t,s) (t',s') = true → answerAt (j t) s = answerAt (j t') s')

def Signature.slot {u : ℕ} (S : Signature u) (s : SlotContext u) (t : Fin u) : Slot :=
  if S.same (t,.first) (t,s t) then .first
  else if S.same (t,.second) (t,s t) then .second else .third

def Signature.project {u : ℕ} (S : Signature u) (s : SlotContext u) (j : J u) : I u :=
  fun t => answerAt (j t) (S.slot s t)

@[simp] lemma signature_valid (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    (signature F c).valid = validJ F c := by
  funext j
  simp only [Signature.valid, signature, Signature.satisfies, positiveAt,
    validJ, localSatisfies, decide_eq_true_eq]
  rfl

@[simp] lemma signature_project (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) :
    (signature F c).project s = pi F c (sampledVariables F c s) := by
  funext j t
  simp only [Signature.project, Signature.slot, signature, decide_eq_true_eq,
    pi, canonicalSlot, sampledVariables]
  rfl

abbrev LocalKey (u : ℕ) := Cube (I u) ⊕ (Cube (J u) ⊕ Unit)

def emptyLocal {u : ℕ} : EmptyContext.Address (leftAnchor u) → LocalKey u
  | .inl f => .inl f.val
  | .inr _ => .inr (.inr ())

def foldedLocal {u : ℕ} (valid : J u → Bool)
    (j₀ : {j : J u // valid j = true}) :
    FoldedEquation.Address (leftAnchor u) j₀ → LocalKey u
  | .inl f => .inl f.val
  | .inr g => .inr (.inl (extendRestricted valid g.val))

def localEquation {u D : ℕ} (valid : J u → Bool) (π : J u → I u)
    (t : SourceTape.TestTape (I u) (J u) D) : Equation (LocalKey u) :=
  match firstValid (jEncoding u) valid with
  | none => mapEquation emptyLocal (EmptyContext.equation (leftAnchor u) t.1)
  | some j₀ => mapEquation (foldedLocal valid j₀)
      (FoldedEquation.conditionedEquation valid π (leftAnchor u) j₀ t.1 t.2.2
        (MinUncutGames.Reduction.FiniteNoise.realizedNoise t.2.1))

def Signature.equation {u D : ℕ} (S : Signature u) (s : SlotContext u)
    (t : SourceTape.TestTape (I u) (J u) D) : Equation (LocalKey u) :=
  localEquation S.valid (S.project s) t

end MinUncut.SourceTemplate

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_BlockEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Costed
open Turing.ToPartrec Polynomial

namespace PolyProgram

def variableDrop : PolyProgram (fun v=>v.tail.drop v.headI) where
  code := dynamicDrop
  bound := C 3000*(X+1)^2
  run v := by
    cases v with
    | nil =>
      obtain ⟨t,ht,hc⟩ := run_caseZero (g:=.cons (.comp .succ .zero)
         (.cons .head (.comp .tail .tail))) (v:=[]) rfl (run_zero [])
      exact ⟨_,by norm_num [magnitude] at ht ⊢; omega,CodeRun.fixDone (u := [0]) hc rfl⟩
    | cons n v =>
      apply (run_dynamicDrop n v).mono
      simp only [eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_one]
      have hn : n+1≤ magnitude (n::v)+1 := by simp only [magnitude_cons]; omega
      nlinarith
  size v := by
    have h := (magnitude_drop v.headI v.tail).trans (magnitude_tail v)
    simp only [eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_one]
    nlinarith

end PolyProgram

namespace Blocks

def block (es : List AExpr) (i : ℕ) (v : List ℕ) : List ℕ := es.map (fun e=>e.eval (i::v))
def source (v : List ℕ) : List ℕ := v.drop (v.tail.headI+2)
def step (es : List AExpr) (v : List ℕ) : List ℕ :=
  (v.headI+1)::(v.tail.headI+es.length)::(block es v.headI (source v)++v.drop 2)

def extractor : PolyProgram (fun v=>v.headI::source v) :=
  PolyProgram.head.cons ((PolyProgram.variableDrop.comp
    ((PolyProgram.addOf (PolyProgram.projection 1) (PolyProgram.const 2)).cons PolyProgram.id)).ofEq
      (by intro v; simp only [Function.comp_def,List.headI_cons,List.tail_cons,List.drop_one,source]))

@[simp] lemma length_block (es : List AExpr) (i : ℕ) (v : List ℕ) :
    (block es i v).length=es.length := by simp [block]

lemma source_step (es : List AExpr) (v : List ℕ) : source (step es v)=source v := by
  simp only [source,step,List.drop_succ_cons,List.headI_cons,List.tail_cons]
  rw [show v.tail.headI+es.length=es.length+v.tail.headI by omega,← List.drop_drop]
  rw [← length_block es v.headI (v.drop (v.tail.headI+2)),List.drop_left]
  rw [List.drop_drop]
  congr 1
  omega

@[simp] lemma head_step (es : List AExpr) (v : List ℕ) : (step es v).headI=v.headI+1 := rfl
@[simp] lemma second_step (es : List AExpr) (v : List ℕ) : (step es v).tail.headI=v.tail.headI+es.length := rfl

lemma iterate_head (es : List AExpr) (v : List ℕ) (i : ℕ) :
    ((step es)^[i] v).headI=v.headI+i := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply',head_step,ih]; omega
lemma iterate_source (es : List AExpr) (v : List ℕ) (i : ℕ) :
    source ((step es)^[i] v)=source v := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply',source_step,ih]

lemma magnitude_append (v w : List ℕ) : magnitude (v++w)=magnitude v+magnitude w := by
  induction v with
  | nil => simp only [List.nil_append,magnitude_nil,Nat.zero_add]
  | cons a v ih => simp only [List.cons_append,magnitude_cons,ih]; omega

lemma magnitude_step (es : List AExpr) (v : List ℕ) :
    magnitude (step es v)≤ magnitude v+es.length+3+magnitude (block es v.headI (source v)) := by
  simp only [step,magnitude_cons,magnitude_append]
  cases v with
  | nil => simp [magnitude]; omega
  | cons a v =>
    cases v with
    | nil => simp [magnitude]; omega
    | cons b v => simp only [List.headI_cons,List.tail_cons,List.drop_succ_cons,List.drop_zero,magnitude_cons]; omega

lemma iterate_accumulator (es : List AExpr) (v : List ℕ) (n : ℕ) :
    (step es)^[n] (0::0::v)=n::(n*es.length)::
      ((List.range n).reverse.flatMap (fun i=>block es i v)++v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    have hs : source (n::(n*es.length)::((List.range n).reverse.flatMap (fun i=>block es i v)++v))=v := by
      rw [← ih,iterate_source]
      rfl
    simp only [step,List.headI_cons,List.tail_cons,hs,List.drop_succ_cons,List.drop_zero,
      List.range_succ,List.reverse_append,List.reverse_singleton,List.flatMap_append,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
    simp only [Nat.add_mul,Nat.one_mul]

end Blocks
end MinUncut.Costed

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ReversePrefixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed
open Turing.ToPartrec Polynomial Arena

def prefixStep (v : List ℕ) : List ℕ :=
  (v.headI+1)::((v.drop (2*v.headI+1)).headI)::v.tail

lemma prefixStep_safe (v : List ℕ) :
    (prefixStep v).length≤v.length+2 ∧ maximum (prefixStep v)≤ maximum v+1 := by
  have h0 := head_le_maximum v
  have ha := (head_le_maximum (v.drop (2*v.headI+1))).trans (maximum_drop v _)
  have ht := maximum_drop v 1
  have hl : v.tail.length≤v.length := by cases v <;> simp
  rw [List.drop_one] at ht
  simp only [prefixStep,List.length_cons,maximum_cons]
  exact ⟨by omega,max_le (by omega) (max_le (by omega) (by omega))⟩

lemma prefixStep_iter (xs rest : List ℕ) (i : ℕ) (hi : i≤xs.length) :
    prefixStep^[i] (0::(xs++rest))=i::((xs.take i).reverse++xs++rest) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hil : i<xs.length := by omega
    rw [Function.iterate_succ_apply',ih (by omega)]
    have hd : (((i::((xs.take i).reverse++xs++rest)).drop (2*i+1)).headI)=xs[i] := by
      have hlen : (xs.take i).reverse.length=i := by simp [Nat.min_eq_left (by omega : i≤xs.length)]
      have h1 : (i::((xs.take i).reverse++xs++rest)).drop (i+1)=xs++rest := by
        rw [List.drop_succ_cons]
        calc
          _ = (((xs.take i).reverse++xs++rest).drop (xs.take i).reverse.length) := by rw [hlen]
          _ = xs++rest := by rw [List.append_assoc,List.drop_left]
      rw [show 2*i+1=(i+1)+i by omega,←List.drop_drop,h1]
      have hk : ((xs++rest).drop i).headI=xs[i] := by
        rw [List.drop_append_of_le_length (by omega)]
        rw [List.drop_eq_getElem_cons hil]
        rfl
      exact hk
    simp only [prefixStep,List.headI_cons,List.tail_cons,hd]
    congr 1
    rw [List.take_succ_eq_append_getElem hil,List.reverse_append]
    rfl

lemma reversePrefix_spec (xs rest : List ℕ) :
    (prefixStep^[xs.length] (0::(xs++rest))).tail=xs.reverse++xs++rest := by
  rw [prefixStep_iter xs rest xs.length (le_refl _),List.tail_cons,List.take_length]

end MinUncut.Costed

namespace MinUncut.Costed.Blocks
noncomputable section

def emitted (es : List AExpr) (n : ℕ) (v : List ℕ) : List ℕ :=
  (List.range n).flatMap (fun i=>block es i v)
def retained (es : List AExpr) (n : ℕ) (v : List ℕ) : List ℕ :=
  (emitted es n v).reverse++v

lemma block_reverse (es : List AExpr) (i : ℕ) (v : List ℕ) :
    block es.reverse i v=(block es i v).reverse := by
  simp only [block,List.map_reverse]
lemma enumerate_reverse (es : List AExpr) (n : ℕ) (v : List ℕ) :
    (List.range n).reverse.flatMap (fun i=>block es.reverse i v)=(emitted es n v).reverse := by
  simp only [emitted,List.reverse_flatMap,Function.comp_def,block_reverse]
lemma length_emitted (es : List AExpr) (n : ℕ) (v : List ℕ) :
    (emitted es n v).length=n*es.length := by
  simp only [emitted,List.length_flatMap,length_block,List.map_const',List.length_range,
    List.sum_replicate,nsmul_eq_mul,Nat.cast_id]

end
end MinUncut.Costed.Blocks

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_TemplateArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap
open MinUncut.Costed
open scoped BigOperators

def keyTag {u : ℕ} : LocalKey u → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

def keyTable {u : ℕ} : LocalKey u → ℕ
  | .inl f => (((iEncoding u).function Encoding.bool).code f).val
  | .inr (.inl g) => (((jEncoding u).function Encoding.bool).code g).val
  | .inr (.inr _) => 0

def signatureEquiv (u : ℕ) : Signature u ≃
    (Fin u → Slot → Bool) × ((Fin u × Slot) → (Fin u × Slot) → Bool) where
  toFun s := (s.positive,s.same)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def coordinateEncoding (u : ℕ) : Encoding (Fin u × Slot) := (Encoding.fin u).prod slotEncoding

def signatureEncoding (u : ℕ) : Encoding (Signature u) :=
  let p := (Encoding.fin u).function (slotEncoding.function Encoding.bool)
  let s := (coordinateEncoding u).function ((coordinateEncoding u).function Encoding.bool)
  ⟨(p.prod s).size,(signatureEquiv u).trans (p.prod s).code⟩

def tupleDigit (i : ℕ) : AExpr := .mod (.div (.reg 0) ((AExpr.reg 2).pow i)) (.reg 2)
def slotWord (i : ℕ) (s : Slot) (p : ℕ) : AExpr :=
  .at (.add (.add (.const 3) (.mul (.const 6) (tupleDigit i)))
    (.const (2*(slotEncoding.code s).val+p)))

end MinUncut.SourceTemplate

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_TemplateExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap
open MinUncut.Costed
open scoped BigOperators

def functionExpr {A : Type} (e : Encoding A) (b : ℕ) (f : A → AExpr) : AExpr :=
  AExpr.sum (List.ofFn (fun i : Fin e.size => .mul (f (e.code.symm i)) (.const (b^i.val))))

def sampledExpr {u : ℕ} (s : SlotContext u) : AExpr :=
  AExpr.sum (List.ofFn (fun i : Fin u=>.mul (slotWord i.val (s i) 0) ((AExpr.reg 1).pow i.val)))

end MinUncut.SourceTemplate

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_FiberPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed
open Polynomial

def quadruple (v : List ℕ) : List ℕ := v.reverse++v++v.reverse++v
lemma quadruple_length (v : List ℕ) : (quadruple v).length=4*v.length := by
  simp only [quadruple,List.length_append,List.length_reverse]; omega

def quadrupleWords (v : List ℕ) : List ℕ :=
  (prefixStep^[2*v.headI] (0::(prefixStep^[v.headI] (0::v.tail)).tail)).tail
end MinUncut.Costed

namespace MinUncut.Costed.Arena.Init
open Turing.ToPartrec

def countExpr : AExpr := .reg 0
def sizeExpr : AExpr := .at (.add (.mul (.const 4) countExpr) (.const 3))
def restExpr : AExpr := .at (.add (.mul (.const 4) countExpr) (.const 2))
def lengthExpr : AExpr := .add (.add (.add (.mul (.const 4) countExpr) (.const 4)) sizeExpr) restExpr

def canvasWords (v : List ℕ) : List ℕ :=
  [countExpr.eval v,sizeExpr.eval v,lengthExpr.eval v,0]++quadrupleWords (lengthExpr.eval v::v)

open Turing.ToPartrec

def cExpr : AExpr := .reg 1
def mExpr : AExpr := .reg 2
def lExpr : AExpr := .reg 3
def iExpr : AExpr := .reg 0
def bExpr : AExpr := .add (.add (.add cExpr mExpr) lExpr) (.const 1)
def rawCell (j : ℕ) : AExpr :=
  .at (.add (.add (.add lExpr (.const 6)) (.mul (.const 4) (.sub iExpr mExpr))) (.const j))
def rawData : AExpr :=
  .at (.add (.add (.add lExpr (.mul (.const 4) cExpr)) (.const 9)) (.sub (.sub mExpr (.const 1)) iExpr))
def pointerExpr (a : AExpr) : AExpr := .cond (.eq a (.const 0)) (.add bExpr a) (.const 0)
def isData : AExpr := .le (.add iExpr (.const 1)) mExpr
def dataPointer : AExpr := .cond (.eq (.add iExpr (.const 1)) mExpr)
  (.sub (.sub (.add (.add bExpr cExpr) mExpr) iExpr) (.const 1)) (.const 0)
def rowExpressions : List AExpr :=
  [.cond isData (rawCell 0) rawData,.cond isData (pointerExpr (rawCell 1)) dataPointer,
   .cond isData (pointerExpr (rawCell 2)) (.const 0),.cond isData (rawCell 3) (.const 0)]

lemma at_append (v w : List ℕ) (i : ℕ) (hi : i<v.length) :
    ((v++w).drop i).headI=(v.drop i).headI := by
  rw [List.drop_append_of_le_length hi.le,List.drop_eq_getElem_cons hi]
  rfl

open Turing.ToPartrec

def countRows : AExpr := .add (.reg 0) (.reg 1)

open Turing.ToPartrec

def canvasBase : AExpr := .add (.add countRows (.reg 2)) (.const 1)
def canvasPc : AExpr := .add canvasBase (.reg 0)
def canvasTotal : AExpr := .add canvasBase countRows
def canvasEnv : AExpr := .cond (.eq (.reg 1) (.const 0)) canvasTotal (.const 0)

end MinUncut.Costed.Arena.Init

end OAI
end


