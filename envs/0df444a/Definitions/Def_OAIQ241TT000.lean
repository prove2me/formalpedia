-- Prove2me | Definitions.Def_OAIQ241TT000
-- name    : OAIQ241TT000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:47:15.702199+00:00
-- url     : https://prove2.me/theorems/a0219418-511a-49de-8eaf-ccae8c7b3fa0
-- title:
--   Definitions bundle OAIQ241TT000 of the split of OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 701 declarations of OpenAI's Lean: 408 definitions, 22 inductive types or structures and 271 theorems. The definitions and types are `OAI.AlgorithmicThinTrees.BinaryInput.copies`, `OAI.AlgorithmicThinTrees.BinaryInput.copiesEquiv`, `OAI.AlgorithmicThinTrees.BinaryInput.crossing`, `OAI.AlgorithmicThinTrees.BinaryInput.expanded`, `OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv`, `OAI.AlgorithmicThinTrees.BinaryInput.liftCopy`, `OAI.AlgorithmicThinTrees.BinaryInput.liftLabel`, `OAI.AlgorithmicThinTrees.BinaryInput.originalCopy`, `OAI.AlgorithmicThinTrees.BinaryInput.originalLabel`, `OAI.AlgorithmicThinTrees.BinaryInput.reduced`, `OAI.AlgorithmicThinTrees.FormSigning.selected`, `OAI.AlgorithmicThinTrees.FormSigning.whiten`, `OAI.AlgorithmicThinTrees.GramWhitening.rationalFactor`, `OAI.AlgorithmicThinTrees.GraphStack.Edge`, `OAI.AlgorithmicThinTrees.GraphStack.Graph`, `OAI.AlgorithmicThinTrees.GraphStack.Graph.data`, `OAI.AlgorithmicThinTrees.GraphStack.constantMatrix`, `OAI.AlgorithmicThinTrees.GraphStack.edgeCode`, `OAI.AlgorithmicThinTrees.GraphStack.edgeGraph`, `OAI.AlgorithmicThinTrees.GraphStack.edgeIndex`, `OAI.AlgorithmicThinTrees.GraphStack.endpoints`, `OAI.AlgorithmicThinTrees.GraphStack.graphCode`, `OAI.AlgorithmicThinTrees.GraphStack.graphDataCode`, `OAI.AlgorithmicThinTrees.GraphStack.lefts`, `OAI.AlgorithmicThinTrees.GraphStack.view`, `OAI.AlgorithmicThinTrees.Partitions.crossing`, `OAI.AlgorithmicThinTrees.RationalGram.base4Squares`, `OAI.AlgorithmicThinTrees.RationalGram.factorColumns`, `OAI.AlgorithmicThinTrees.RationalGram.factorMatrix`, `OAI.AlgorithmicThinTrees.RationalGram.scalarFactors`, `OAI.AlgorithmicThinTrees.RationalInverse.inverse`, `OAI.AlgorithmicThinTrees.RationalInverse.liftSolve`, `OAI.AlgorithmicThinTrees.RationalSigning.entry`, `OAI.AlgorithmicThinTrees.RationalSigning.input`, `OAI.AlgorithmicThinTrees.RationalSigning.selected`, `OAI.AlgorithmicThinTrees.StackedSigning.selected`, `OAI.AlgorithmicThinTrees.StackedSigning.stack`, `OAI.CurrentKS.CleanRoutine.Routine`, `OAI.CurrentKS.CleanRoutine.Routine.compose`, `OAI.CurrentKS.CleanRoutine.Routine.pad` and 390 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `MatrixSigning_Arithmetic_CubeInterval`, `MatrixSigning_Arithmetic_MultiplicationNormalize`, `MatrixSigning_Arithmetic_RationalArithmeticMeter`, `MatrixSigning_Encoding_BinaryEncoding`, `MatrixSigning_Encoding_FixedPositiveSerializer`, `MatrixSigning_Encoding_FrameDecoder`, `MatrixSigning_Encoding_FrameWireCodec`, `MatrixSigning_Encoding_PositiveWireSerializer`, `MatrixSigning_Encoding_WirePrimitives`, `MatrixSigning_Encoding_WordOperations`, `MatrixSigning_Machines_BinaryMachine`, `MatrixSigning_Machines_BinaryStackMoves`, `MatrixSigning_Machines_BinaryTrimMachine`, `MatrixSigning_Machines_CopyInput`, `MatrixSigning_Machines_EntryPoint`, `MatrixSigning_Machines_ExpressionSyntax`, `MatrixSigning_Machines_FiniteControl`, `MatrixSigning_Machines_FiniteDispatch`, `MatrixSigning_Machines_FixedBranch`, `MatrixSigning_Machines_FixedCopyRestore`, `MatrixSigning_Machines_FixedLoop`, `MatrixSigning_Machines_FixedPortRunSpec`, `MatrixSigning_Machines_FixedRun`, `MatrixSigning_Machines_FixedSequential`, `MatrixSigning_Machines_FixedStackMachine`, `MatrixSigning_Machines_FixedStackPortLift`, `MatrixSigning_Machines_InputHeaderPrimitives`, `MatrixSigning_Machines_LiteralProgram`, `MatrixSigning_Machines_MachineCombinators`, `MatrixSigning_Machines_NormalizeOutput`, `MatrixSigning_Machines_StackTransfer`, `MatrixSigning_Machines_StackTransferSpecs`, `MatrixSigning_Matrices_PSDSeparation`, `MatrixSigning_Matrices_RationalElimination`, `MatrixSigning_Matrices_RealDecode`, `MatrixSigning_Matrices_UniformElimination`, `MatrixSigning_Model`, `MatrixSigning_Optimization_Affine`, `MatrixSigning_Optimization_BlockScalar`, `MatrixSigning_Optimization_Coordinates`, `MatrixSigning_Optimization_FaceStencil`, `MatrixSigning_Optimization_FixedPart`, `MatrixSigning_Optimization_Level`, `MatrixSigning_Optimization_Lookup`, `MatrixSigning_Optimization_MinList`, `MatrixSigning_Optimization_NearestEndpoint`, `MatrixSigning_Optimization_NegativeDirection`, `MatrixSigning_Optimization_NegativeWitness`, `MatrixSigning_Optimization_NormalizedRun`, `MatrixSigning_Optimization_ObjectiveCLM`, `MatrixSigning_Optimization_Pencil`, `MatrixSigning_Optimization_RationalAtoms`, `MatrixSigning_Optimization_RealVector`, `MatrixSigning_Optimization_RootTolerance`, `MatrixSigning_Optimization_SearchStep`, `MatrixSigning_Optimization_Select`, `MatrixSigning_Optimization_ShiftedHessian`, `MatrixSigning_Optimization_Signing`, `MatrixSigning_Optimization_SqSum`, `MatrixSigning_Optimization_SquareInterval`, `MatrixSigning_Optimization_Transition`, `MatrixSigning_Optimization_UpperIndex`, `MatrixSigning_Optimization_ValueDimension`, `MatrixSigning_Optimization_ValueObjectiveCoeffs`, `MatrixSigning_Optimization_ValueOuterRadius`, `MatrixSigning_Potential_ChooseCoordinate`, `MatrixSigning_Potential_EndpointCandidates`, `MatrixSigning_Potential_EuclideanForget`, `MatrixSigning_Potential_FaceState`, `MatrixSigning_Potential_MovementBudget`, `MatrixSigning_Potential_Parameters2`, `MatrixSigning_Potential_PenaltyParameter`, `MatrixSigning_Potential_RationalBasis`, `MatrixSigning_Realization_ArrayRealization`, `MatrixSigning_Realization_CleanRoutine`, `MatrixSigning_Realization_CompareRoutine`, `MatrixSigning_Realization_ConditionalRoutine`, `MatrixSigning_Realization_DependentRealization`, `MatrixSigning_Realization_FaceArrayRealization`, `MatrixSigning_Realization_FoldRoutine`, `MatrixSigning_Realization_FramedMapRoutine`, `MatrixSigning_Realization_IterateRoutine`, `MatrixSigning_Realization_LevelPencilRealization`, `MatrixSigning_Realization_ListRealization`, `MatrixSigning_Realization_NaturalRealization`, `MatrixSigning_Realization_PairRoutine`, `MatrixSigning_Realization_Realization`, `MatrixSigning_Realization_ScalarRealization`, `MatrixSigning_Realization_VectorRealization`, `ThinTrees_Continuation_PartitionGeometry`, `ThinTrees_Encoding_BinaryReduction`, `ThinTrees_Encoding_CanonicalExpansion`, `ThinTrees_Encoding_GraphRealization`, `ThinTrees_RationalMatrix_Gram`, `ThinTrees_RationalMatrix_Inverse`, `ThinTrees_RationalMatrix_Squares`, `ThinTrees_Signing_FormSigning`, `ThinTrees_Signing_GramWhitening`, `ThinTrees_Signing_RationalSigning`, `ThinTrees_Signing_StackedSigning`.
--
--   **Imports.** It imports the published bundle `Def_AlgorithmicThinTrees`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ241TT004`, `OAIQ241TT005` and `OAIQ241TT006`; the statements `OAI.CurrentKS.RationalFace.normalizedRun_spec`, `OAI.CurrentKS.RationalFace.transition_spec` and `OAI.CurrentKS.State.LightPoint.computed_candidates_progress`.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_AlgorithmicThinTrees

section
-- module Solutions.OAIQ241_TT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
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
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_CubeInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar

def cubeInterval (q : ℚ) : ℕ → ℚ × ℚ
  | 0 => (0,1)
  | k+1 =>
    let s := cubeInterval q k
    let m := (s.1+s.2)/2
    if m^3 ≤ q then (m,s.2) else (s.1,m)

def approxPsi (x δ : ℚ) : ℚ := (cubeInterval (1-x^2) δ.den.size).1

end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_BinaryEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01

def frame : List Bool → List Bool
  | [] => [true]
  | b :: bs => false :: b :: frame bs

@[simp] theorem length_frame (bs : List Bool) :
    (frame bs).length = 2 * bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [frame, List.length_cons, ih]; omega

def encodeNat (n : ℕ) : List Bool := frame (Computability.encodeNat n)

def encodeInt : ℤ → List Bool
  | .ofNat n => false :: encodeNat n
  | .negSucc n => true :: encodeNat n

def encodeRat (q : ℚ) : List Bool := encodeInt q.num ++ encodeNat q.den

def natPayloadLength (n : ℕ) : ℕ := (Computability.encodeNat n).length

def intPayload (n : ℤ) : ℕ := match n with
  | .ofNat k => k
  | .negSucc k => k

@[simp] theorem length_encodeNat (n : ℕ) :
    (encodeNat n).length = 2 * natPayloadLength n + 1 := by
  simp [encodeNat, natPayloadLength]

@[simp] theorem length_encodeInt (n : ℤ) :
    (encodeInt n).length = 2 * natPayloadLength (intPayload n) + 2 := by
  cases n <;> simp [encodeInt, intPayload]

@[simp] theorem length_encodeRat (q : ℚ) :
    (encodeRat q).length =
      2 * (natPayloadLength (intPayload q.num) + natPayloadLength q.den) + 3 := by
  simp only [encodeRat, List.length_append, length_encodeInt, length_encodeNat]
  omega

end KS.W01

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_BinaryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W29

inductive StackAction where
  | stay
  | pop
  | push (bit : Bool)
  deriving DecidableEq, Repr

def StackAction.apply : StackAction → List Bool → List Bool
  | .stay, xs => xs
  | .pop, xs => xs.tail
  | .push b, xs => b :: xs

structure Instruction (q : Nat) where
  next : Option (Fin q)
  first : StackAction
  second : StackAction
  third : StackAction
  deriving DecidableEq, Repr

def Instruction.action {q : Nat} (i : Instruction q) (stack : Fin 3) : StackAction :=
  if stack = 0 then i.first else if stack = 1 then i.second else i.third

def Instruction.halt (q : Nat) : Instruction q :=
  ⟨none, .stay, .stay, .stay⟩

structure BinaryMachine where
  states : Nat
  initial : Fin states
  table : List (Instruction states)

structure Config (q : Nat) where
  state : Option (Fin q)
  «stacks» : Fin 3 → List Bool

def topCode : List Bool → Nat
  | [] => 0
  | false :: _ => 1
  | true :: _ => 2

theorem topCode_lt_three (xs : List Bool) : topCode xs < 3 := by
  cases xs with
  | nil => decide
  | cons b xs => cases b <;> simp [topCode]

def headCode {q : Nat} (c : Config q) : Nat :=
  topCode (c.«stacks» 0) + 3 * topCode (c.«stacks» 1) + 9 * topCode (c.«stacks» 2)

theorem headCode_lt (q : Nat) (c : Config q) : headCode c < 27 := by
  have h₀ := topCode_lt_three (c.«stacks» 0)
  have h₁ := topCode_lt_three (c.«stacks» 1)
  have h₂ := topCode_lt_three (c.«stacks» 2)
  unfold headCode
  omega

def bitCode (b : Bool) : Nat := if b then 1 else 0

def transitionIndex {q : Nat} (s : Fin q) (c : Config q) (b : Bool) : Nat :=
  54 * s.val + 2 * headCode c + bitCode b

theorem transitionIndex_lt {q : Nat} (s : Fin q) (c : Config q) (b : Bool) :
    transitionIndex s c b < 54 * q := by
  have hs := s.isLt
  have hc := headCode_lt q c
  have hb : bitCode b < 2 := by cases b <;> decide
  unfold transitionIndex
  omega

def BinaryMachine.step (M : BinaryMachine) (c : Config M.states) (b : Bool) :
    Config M.states :=
  match c.state with
  | none => c
  | some s =>
      let i := M.table.getD (transitionIndex s c b) (Instruction.halt M.states)
      ⟨i.next, fun j => (i.action j).apply (c.«stacks» j)⟩

def BinaryMachine.init (M : BinaryMachine) (input : List Bool) : Config M.states :=
  ⟨some M.initial, fun j => if j = 0 then input else []⟩

def BinaryMachine.run (M : BinaryMachine) : Config M.states → List Bool → Config M.states
  | c, [] => c
  | c, b :: bs => M.run (M.step c b) bs

@[simp] theorem BinaryMachine.step_halted (M : BinaryMachine) (c : Config M.states)
    (h : c.state = none) (b : Bool) : M.step c b = c := by
  simp [BinaryMachine.step, h]

theorem BinaryMachine.run_append (M : BinaryMachine) (c : Config M.states)
    (xs ys : List Bool) : M.run c (xs ++ ys) = M.run (M.run c xs) ys := by
  induction xs generalizing c with
  | nil => rfl
  | cons b bs ih => simpa [BinaryMachine.run] using ih (M.step c b)

end KS.W29

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FiniteDispatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W29
namespace FiniteDispatch

def decodeState {q : Nat} (index : Fin (54 * q)) : Fin q :=
  ⟨index.val / 54, by have h := index.isLt; omega⟩

def decodeHeads {q : Nat} (index : Fin (54 * q)) : Fin 27 :=
  ⟨index.val / 2 % 27, Nat.mod_lt _ (by decide)⟩

def decodeBit {q : Nat} (index : Fin (54 * q)) : Bool := index.val % 2 == 1

def compile {q : Nat} (initial : Fin q)
    (dispatch : Fin q → Fin 27 → Bool → Instruction q) : BinaryMachine :=
  ⟨q, initial, List.ofFn (fun index : Fin (54 * q) =>
    dispatch (decodeState index) (decodeHeads index) (decodeBit index))⟩

theorem decodeState_index {q : Nat} (s : Fin q) (c : Config q) (b : Bool) :
    decodeState ⟨transitionIndex s c b, transitionIndex_lt s c b⟩ = s := by
  apply Fin.ext
  have hh := headCode_lt q c
  have hb : bitCode b < 2 := by cases b <;> decide
  change (54 * s.val + 2 * headCode c + bitCode b) / 54 = s.val
  omega

theorem decodeHeads_index {q : Nat} (s : Fin q) (c : Config q) (b : Bool) :
    decodeHeads ⟨transitionIndex s c b, transitionIndex_lt s c b⟩ =
      ⟨headCode c, headCode_lt q c⟩ := by
  apply Fin.ext
  have hh := headCode_lt q c
  have hb : bitCode b < 2 := by cases b <;> decide
  change (54 * s.val + 2 * headCode c + bitCode b) / 2 % 27 = headCode c
  omega

theorem decodeBit_index {q : Nat} (s : Fin q) (c : Config q) (b : Bool) :
    decodeBit ⟨transitionIndex s c b, transitionIndex_lt s c b⟩ = b := by
  cases b with
  | false =>
      have h : transitionIndex s c false % 2 = 0 := by
        change (54 * s.val + 2 * headCode c + 0) % 2 = 0
        omega
      simp [decodeBit, h]
  | true =>
      have h : transitionIndex s c true % 2 = 1 := by
        change (54 * s.val + 2 * headCode c + 1) % 2 = 1
        omega
      simp [decodeBit, h]

theorem lookup_compile {q : Nat} (initial : Fin q)
    (dispatch : Fin q → Fin 27 → Bool → Instruction q)
    (s : Fin q) (c : Config q) (b : Bool) :
    (compile initial dispatch).table.getD (transitionIndex s c b) (Instruction.halt q) =
      dispatch s ⟨headCode c, headCode_lt q c⟩ b := by
  have hi := transitionIndex_lt s c b
  unfold compile
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_ofFn, decodeState_index, decodeHeads_index, decodeBit_index]

theorem step_compile {q : Nat} (initial : Fin q)
    (dispatch : Fin q → Fin 27 → Bool → Instruction q)
    (s : Fin q) («stacks» : Fin 3 → List Bool) (b : Bool) :
    (compile initial dispatch).step ⟨some s, «stacks»⟩ b =
      let c : Config q := ⟨some s, «stacks»⟩
      let i := dispatch s ⟨headCode c, headCode_lt q c⟩ b
      Config.mk i.next (fun j => (i.action j).apply («stacks» j)) := by
  simp only [BinaryMachine.step]
  erw [lookup_compile]
  rfl

end FiniteDispatch
end KS.W29

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_CopyInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W29
namespace CopyInput

def reverseEntry (top : Nat) : Instruction 2 :=
  if top = 0 then ⟨some 1, .stay, .stay, .stay⟩
  else ⟨some 0, .pop, .stay, .push (top == 2)⟩

def copyEntry (top : Nat) : Instruction 2 :=
  if top = 0 then Instruction.halt 2
  else ⟨some 1, .push (top == 2), .push (top == 2), .pop⟩

def tableEntry (index : Nat) : Instruction 2 :=
  if index < 54 then reverseEntry (index / 2 % 3)
  else copyEntry (index / 18 % 3)

def machine : BinaryMachine :=
  ⟨2, 0, List.ofFn (fun i : Fin 108 => tableEntry i.val)⟩

def cfg (state : Option (Fin 2)) (input output scratch : List Bool) : Config 2 :=
  ⟨state, fun j => if j = 0 then input else if j = 1 then output else scratch⟩

theorem table_lookup (s : Fin 2) (c : Config 2) (b : Bool) :
    machine.table.getD (transitionIndex s c b) (Instruction.halt 2) =
      if s.val = 0 then reverseEntry (topCode (c.«stacks» 0))
      else copyEntry (topCode (c.«stacks» 2)) := by
  have hs := s.isLt
  have h₀ := topCode_lt_three (c.«stacks» 0)
  have h₁ := topCode_lt_three (c.«stacks» 1)
  have h₂ := topCode_lt_three (c.«stacks» 2)
  have hb : bitCode b < 2 := by cases b <;> decide
  have hi : transitionIndex s c b < 108 := transitionIndex_lt s c b
  have hc₀ : transitionIndex s c b / 2 % 3 = topCode (c.«stacks» 0) := by
    unfold transitionIndex headCode
    omega
  have hc₂ : transitionIndex s c b / 18 % 3 = topCode (c.«stacks» 2) := by
    unfold transitionIndex headCode
    omega
  have hphase : transitionIndex s c b < 54 ↔ s.val = 0 := by
    unfold transitionIndex headCode
    omega
  change (List.ofFn (fun i : Fin 108 => tableEntry i.val)).getD _ _ = _
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
  simp only [List.getElem_ofFn, tableEntry, hc₀, hc₂, hphase]

theorem reverse_step (x : Bool) (xs ys zs : List Bool) (b : Bool) :
    machine.step (cfg (some 0) (x :: xs) ys zs) b = cfg (some 0) xs ys (x :: zs) := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases x <;> change Config.mk (some (0 : Fin 2)) _ = Config.mk (some (0 : Fin 2)) _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem reverse_done (ys zs : List Bool) (b : Bool) :
    machine.step (cfg (some 0) [] ys zs) b = cfg (some 1) [] ys zs := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  change Config.mk (some (1 : Fin 2)) _ = Config.mk (some (1 : Fin 2)) _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem copy_step (x : Bool) (xs ys zs : List Bool) (b : Bool) :
    machine.step (cfg (some 1) xs ys (x :: zs)) b = cfg (some 1) (x :: xs) (x :: ys) zs := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases x <;> change Config.mk (some (1 : Fin 2)) _ = Config.mk (some (1 : Fin 2)) _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem copy_done (xs ys : List Bool) (b : Bool) :
    machine.step (cfg (some 1) xs ys []) b = cfg none xs ys [] := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  change Config.mk none _ = Config.mk none _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem run_reverse (xs ys zs bits : List Bool) (hlen : bits.length = xs.length) :
    machine.run (cfg (some 0) xs ys zs) bits =
      cfg (some 0) [] ys (xs.reverse ++ zs) := by
  induction xs generalizing zs bits with
  | nil =>
      have hb : bits = [] := List.length_eq_zero_iff.mp hlen
      subst bits
      simp only [BinaryMachine.run, List.reverse_nil, List.nil_append]
      rfl
  | cons x xs ih =>
      cases bits with
      | nil => simp at hlen
      | cons b bs =>
          have hbs : bs.length = xs.length := by simpa using hlen
          erw [BinaryMachine.run.eq_2, reverse_step, ih _ _ hbs]
          simp [List.reverse_cons, List.append_assoc]
          rfl

theorem run_copy (xs ys zs bits : List Bool) (hlen : bits.length = zs.length) :
    machine.run (cfg (some 1) xs ys zs) bits =
      cfg (some 1) (zs.reverse ++ xs) (zs.reverse ++ ys) [] := by
  induction zs generalizing xs ys bits with
  | nil =>
      have hb : bits = [] := List.length_eq_zero_iff.mp hlen
      subst bits
      simp only [BinaryMachine.run, List.reverse_nil, List.nil_append]
      rfl
  | cons z zs ih =>
      cases bits with
      | nil => simp at hlen
      | cons b bs =>
          have hbs : bs.length = zs.length := by simpa using hlen
          erw [BinaryMachine.run.eq_2, copy_step, ih _ _ _ hbs]
          simp [List.reverse_cons, List.append_assoc]
          rfl

theorem run_copy_input (xs left right : List Bool) (a b : Bool)
    (hl : left.length = xs.length) (hr : right.length = xs.length) :
    machine.run (cfg (some 0) xs [] []) (left ++ a :: (right ++ [b])) =
      cfg none xs xs [] := by
  erw [machine.run_append, run_reverse _ _ _ _ hl]
  simp only [List.append_nil, BinaryMachine.run]
  erw [reverse_done, machine.run_append, run_copy]
  · simp [BinaryMachine.run, copy_done]
    rfl
  · simpa using hr

theorem split_copy_fuel (bits : List Bool) (n : Nat) (h : bits.length = 2 * n + 2) :
    ∃ left a right b, bits = left ++ a :: (right ++ [b]) ∧
      left.length = n ∧ right.length = n := by
  have hn : n ≤ bits.length := by omega
  cases hd : bits.drop n with
  | nil =>
      have he := congrArg List.length hd
      simp only [List.length_drop, List.length_nil] at he
      omega
  | cons a tail =>
      have ht : tail.length = n + 1 := by
        have he := congrArg List.length hd
        simp only [List.length_drop, List.length_cons] at he
        omega
      cases he : tail.drop n with
      | nil =>
          have hz := congrArg List.length he
          simp only [List.length_drop, List.length_nil] at hz
          omega
      | cons b rest =>
          have hr : rest = [] := by
            apply List.length_eq_zero_iff.mp
            have hz := congrArg List.length he
            simp only [List.length_drop, List.length_cons] at hz
            omega
          subst rest
          refine ⟨bits.take n, a, tail.take n, b, ?_, ?_, ?_⟩
          · have hb : bits = bits.take n ++ a :: tail := by
              simpa [hd] using (List.take_append_drop n bits).symm
            have htail : tail = tail.take n ++ [b] := by
              simpa [he] using (List.take_append_drop n tail).symm
            calc
              bits = bits.take n ++ a :: tail := hb
              _ = bits.take n ++ a :: (tail.take n ++ [b]) :=
                congrArg (fun t => bits.take n ++ a :: t) htail
          · simp [List.length_take, Nat.min_eq_left hn]
          · simp [List.length_take, ht]

theorem run_eq_copy (xs bits : List Bool) (h : bits.length = 2 * xs.length + 2) :
    machine.run (machine.init xs) bits = cfg none xs xs [] := by
  obtain ⟨left, a, right, b, rfl, hl, hr⟩ := split_copy_fuel bits xs.length h
  have hi : machine.init xs = cfg (some 0) xs [] [] := by
    simp [BinaryMachine.init, cfg, machine]
  rw [hi]
  exact run_copy_input xs left right a b hl hr

end CopyInput
end KS.W29

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedStackMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01.FixedStack
open KS.W29 (StackAction )

structure Instruction (stackCount states : ℕ) where
  next : Option (Fin states)
  actions : Vector StackAction stackCount

def Instruction.action {k q : ℕ} (i : Instruction k q) (j : Fin k) : StackAction :=
  i.actions[j.val]

def Instruction.halt (k q : ℕ) : Instruction k q :=
  ⟨none, Vector.ofFn (fun _ => .stay)⟩

structure Machine where
  stackCount : ℕ
  states : ℕ
  initial : Fin states
  inputStack : Fin stackCount
  outputStack : Fin stackCount
  table : List (Instruction stackCount states)

structure Config (k q : ℕ) where
  state : Option (Fin q)
  «stacks» : Fin k → List Bool

def headsCode : (k : ℕ) → (Fin k → Fin 3) → ℕ
  | 0, _ => 0
  | k + 1, h => (h 0).val + 3 * headsCode k (fun i => h i.succ)

def decodeHeads : (k : ℕ) → ℕ → Fin k → Fin 3
  | 0, _, i => Fin.elim0 i
  | k + 1, n, i => Fin.cases ⟨n % 3, Nat.mod_lt _ (by decide)⟩ (decodeHeads k (n / 3)) i

theorem headsCode_lt (k : ℕ) (h : Fin k → Fin 3) : headsCode k h < 3 ^ k := by
  induction k with
  | zero => simp [headsCode]
  | succ k ih =>
      have h0 := (h 0).isLt
      have ht := ih (fun i => h i.succ)
      simp only [headsCode, pow_succ]
      omega

@[simp] theorem decodeHeads_headsCode (k : ℕ) (h : Fin k → Fin 3) :
    decodeHeads k (headsCode k h) = h := by
  induction k with
  | zero => funext i; exact Fin.elim0 i
  | succ k ih =>
      have h0 := (h 0).isLt
      have hm : ((h 0).val + 3 * headsCode k (fun i => h i.succ)) % 3 = (h 0).val := by
        omega
      have hd : ((h 0).val + 3 * headsCode k (fun i => h i.succ)) / 3 =
          headsCode k (fun i => h i.succ) := by omega
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · apply Fin.ext
        exact hm
      · change decodeHeads k (((h 0).val + 3 * headsCode k (fun i => h i.succ)) / 3) j = _
        rw [hd, ih]

def observedHeads {k q : ℕ} (c : Config k q) : Fin k → Fin 3 :=
  fun j => ⟨KS.W29.topCode (c.«stacks» j), KS.W29.topCode_lt_three _⟩

def headFin {k : ℕ} (h : Fin k → Fin 3) : Fin (3 ^ k) :=
  ⟨headsCode k h, headsCode_lt k h⟩

def coinFin (b : Bool) : Fin 2 := if b then 1 else 0

def tableIndex {k q : ℕ} (s : Fin q) (h : Fin k → Fin 3) (b : Bool) :
    Fin (q * (3 ^ k * 2)) :=
  finProdFinEquiv (s, finProdFinEquiv (headFin h, coinFin b))

def Machine.step (M : Machine) (c : Config M.stackCount M.states) (b : Bool) :
    Config M.stackCount M.states :=
  match c.state with
  | none => c
  | some s =>
      let i := M.table.getD (tableIndex s (observedHeads c) b).val
        (Instruction.halt M.stackCount M.states)
      ⟨i.next, fun j => (i.action j).apply (c.«stacks» j)⟩

def Machine.init (M : Machine) (input : List Bool) : Config M.stackCount M.states :=
  ⟨some M.initial, fun j => if j = M.inputStack then input else []⟩

def Machine.run (M : Machine) : Config M.stackCount M.states → List Bool →
    Config M.stackCount M.states
  | c, [] => c
  | c, b :: bs => M.run (M.step c b) bs

@[simp] theorem Machine.step_halted (M : Machine) (c : Config M.stackCount M.states)
    (h : c.state = none) (b : Bool) : M.step c b = c := by simp [Machine.step, h]

theorem Machine.run_halted (M : Machine) (c : Config M.stackCount M.states)
    (h : c.state = none) (bits : List Bool) : M.run c bits = c := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simpa [Machine.run, M.step_halted c h b] using ih

theorem Machine.run_append (M : Machine) (c : Config M.stackCount M.states)
    (xs ys : List Bool) : M.run c (xs ++ ys) = M.run (M.run c xs) ys := by
  induction xs generalizing c with
  | nil => rfl
  | cons b bs ih => simpa [Machine.run] using ih (M.step c b)

def decodeDispatch {k q : ℕ}
    (dispatch : Fin q → (Fin k → Fin 3) → Bool → Instruction k q)
    (index : Fin (q * (3 ^ k * 2))) : Instruction k q :=
  let stateHeads : Fin q × Fin (3 ^ k * 2) := finProdFinEquiv.symm index
  let headsBit : Fin (3 ^ k) × Fin 2 := finProdFinEquiv.symm stateHeads.2
  dispatch stateHeads.1 (decodeHeads k headsBit.1.val) (headsBit.2.val == 1)

def compile {k q : ℕ} (initial : Fin q) (input output : Fin k)
    (dispatch : Fin q → (Fin k → Fin 3) → Bool → Instruction k q) : Machine :=
  ⟨k, q, initial, input, output, List.ofFn (decodeDispatch dispatch)⟩

theorem decodeDispatch_tableIndex {k q : ℕ}
    (dispatch : Fin q → (Fin k → Fin 3) → Bool → Instruction k q)
    (s : Fin q) (h : Fin k → Fin 3) (b : Bool) :
    decodeDispatch dispatch (tableIndex s h b) = dispatch s h b := by
  simp only [decodeDispatch, tableIndex, Equiv.symm_apply_apply, headFin,
    decodeHeads_headsCode]
  cases b <;> rfl

theorem lookup_compile {k q : ℕ} (initial : Fin q) (input output : Fin k)
    (dispatch : Fin q → (Fin k → Fin 3) → Bool → Instruction k q)
    (s : Fin q) (h : Fin k → Fin 3) (b : Bool) :
    (compile initial input output dispatch).table.getD (tableIndex s h b).val
      (Instruction.halt k q) = dispatch s h b := by
  change (List.ofFn (decodeDispatch dispatch)).getD _ _ = _
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_ofFn]
  exact decodeDispatch_tableIndex dispatch s h b

theorem step_compile {k q : ℕ} (initial : Fin q) (input output : Fin k)
    (dispatch : Fin q → (Fin k → Fin 3) → Bool → Instruction k q)
    (s : Fin q) («stacks» : Fin k → List Bool) (b : Bool) :
    (compile initial input output dispatch).step ⟨some s, «stacks»⟩ b =
      let c : Config k q := ⟨some s, «stacks»⟩
      let i := dispatch s (observedHeads c) b
      Config.mk i.next (fun j => (i.action j).apply («stacks» j)) := by
  simp only [Machine.step]
  erw [lookup_compile]
  rfl

def liftInstruction {k q : ℕ} (ports : Fin 3 ↪ Fin k)
    (i : KS.W29.Instruction q) : Instruction k q :=
  ⟨i.next, Vector.ofFn (fun j =>
    if j = ports 0 then i.first else if j = ports 1 then i.second
    else if j = ports 2 then i.third else .stay)⟩

@[simp] theorem liftInstruction_on_port {k q : ℕ} (ports : Fin 3 ↪ Fin k)
    (i : KS.W29.Instruction q) (j : Fin 3) :
    (liftInstruction ports i).action (ports j) = i.action j := by
  fin_cases j <;> simp [Instruction.action, liftInstruction, KS.W29.Instruction.action,
    ports.injective.eq_iff]

@[simp] theorem liftInstruction_off_port {k q : ℕ} (ports : Fin 3 ↪ Fin k)
    (i : KS.W29.Instruction q) (j : Fin k) (hj : ∀ r : Fin 3, j ≠ ports r) :
    (liftInstruction ports i).action j = .stay := by
  simp [Instruction.action, liftInstruction, hj]

def project {k q : ℕ} (ports : Fin 3 ↪ Fin k) (c : Config k q) : KS.W29.Config q :=
  ⟨c.state, fun j => c.«stacks» (ports j)⟩

def selectedCode {k : ℕ} (ports : Fin 3 ↪ Fin k) (h : Fin k → Fin 3) : ℕ :=
  (h (ports 0)).val + 3 * (h (ports 1)).val + 9 * (h (ports 2)).val

def liftDispatch {k : ℕ} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (s : Fin M.states) (h : Fin k → Fin 3) (b : Bool) : Instruction k M.states :=
  liftInstruction ports (M.table.getD
    (54 * s.val + 2 * selectedCode ports h + KS.W29.bitCode b)
    (KS.W29.Instruction.halt M.states))

def lift3 {k : ℕ} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k) : Machine :=
  compile M.initial (ports 0) (ports 1) (liftDispatch M ports)

theorem lift3_step {k : ℕ} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (s : Fin M.states) («stacks» : Fin k → List Bool) (b : Bool) :
    (lift3 M ports).step ⟨some s, «stacks»⟩ b =
      let c : Config k M.states := ⟨some s, «stacks»⟩
      let i := M.table.getD (KS.W29.transitionIndex s (project ports c) b)
        (KS.W29.Instruction.halt M.states)
      Config.mk i.next (fun j => ((liftInstruction ports i).action j).apply («stacks» j)) := by
  unfold lift3
  rw [step_compile]
  rfl

theorem lift3_project_step {k : ℕ} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (c : Config k M.states) (b : Bool) :
    project ports ((lift3 M ports).step c b) = M.step (project ports c) b := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s =>
      erw [lift3_step M ports s «stacks» b]
      change KS.W29.Config.mk _ _ = KS.W29.Config.mk _ _
      congr 1
      funext j
      dsimp only [project]
      rw [liftInstruction_on_port ports _ j]

theorem lift3_step_preserves_other {k : ℕ} (M : KS.W29.BinaryMachine)
    (ports : Fin 3 ↪ Fin k) (c : Config k M.states) (b : Bool)
    (j : Fin k) (hj : ∀ r : Fin 3, j ≠ ports r) :
    ((lift3 M ports).step c b).«stacks» j = c.«stacks» j := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s =>
      erw [lift3_step M ports s «stacks» b]
      change ((liftInstruction ports _).action j).apply («stacks» j) = «stacks» j
      rw [liftInstruction_off_port ports _ j hj]
      rfl

theorem lift3_project_run {k : ℕ} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (c : Config k M.states) (bits : List Bool) :
    project ports ((lift3 M ports).run c bits) = M.run (project ports c) bits := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      erw [Machine.run.eq_def, ih]
      erw [lift3_project_step M ports c b]
      rfl

theorem lift3_run_preserves_other {k : ℕ} (M : KS.W29.BinaryMachine)
    (ports : Fin 3 ↪ Fin k) (c : Config k M.states) (bits : List Bool)
    (j : Fin k) (hj : ∀ r : Fin 3, j ≠ ports r) :
    ((lift3 M ports).run c bits).«stacks» j = c.«stacks» j := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      erw [Machine.run.eq_def, ih]
      exact lift3_step_preserves_other M ports c b j hj

@[simp] theorem lift3_project_init {k : ℕ} (M : KS.W29.BinaryMachine)
    (ports : Fin 3 ↪ Fin k) (input : List Bool) :
    project ports ((lift3 M ports).init input) = M.init input := by
  change KS.W29.Config.mk (some M.initial)
      (fun j => if ports j = ports 0 then input else []) =
    KS.W29.Config.mk (some M.initial) (fun j => if j = 0 then input else [])
  congr 1
  funext j
  simp [ports.injective.eq_iff]

end KS.W01.FixedStack

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedSequential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W29.FixedSequential

structure Program (k : Nat) where
  states : Nat
  initial : Fin states
  input : Fin k
  output : Fin k
  table : List (KS.W01.FixedStack.Instruction k states)

def Program.toMachine {k : Nat} (P : Program k) : KS.W01.FixedStack.Machine :=
  ⟨k, P.states, P.initial, P.input, P.output, P.table⟩

def ofMachine (M : KS.W01.FixedStack.Machine) : Program M.stackCount :=
  ⟨M.states, M.initial, M.inputStack, M.outputStack, M.table⟩

@[simp] theorem toMachine_ofMachine (M : KS.W01.FixedStack.Machine) : (ofMachine M).toMachine = M := by
  cases M
  rfl

@[simp] theorem ofMachine_toMachine {k : Nat} (P : Program k) : ofMachine P.toMachine = P := by
  cases P
  rfl

def leftState {k : Nat} (P Q : Program k) (s : Fin P.states) : Fin (P.states + Q.states) :=
  ⟨s.val, by have h := s.isLt; omega⟩

def rightState {k : Nat} (P Q : Program k) (s : Fin Q.states) : Fin (P.states + Q.states) :=
  ⟨P.states + s.val, by have h := s.isLt; omega⟩

def liftLeft {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k P.states) :
    KS.W01.FixedStack.Config k (P.states + Q.states) :=
  ⟨some (match c.state with
      | none => rightState P Q Q.initial
      | some s => leftState P Q s), c.«stacks»⟩

def liftRight {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k Q.states) :
    KS.W01.FixedStack.Config k (P.states + Q.states) :=
  ⟨c.state.map (rightState P Q), c.«stacks»⟩

def leftInstruction {k : Nat} (P Q : Program k) (i : KS.W01.FixedStack.Instruction k P.states) :
    KS.W01.FixedStack.Instruction k (P.states + Q.states) :=
  ⟨some (match i.next with
      | none => rightState P Q Q.initial
      | some s => leftState P Q s), i.actions⟩

def rightInstruction {k : Nat} (P Q : Program k) (i : KS.W01.FixedStack.Instruction k Q.states) :
    KS.W01.FixedStack.Instruction k (P.states + Q.states) :=
  ⟨i.next.map (rightState P Q), i.actions⟩

def fetch {k : Nat} (P : Program k) (s : Fin P.states) (heads : Fin k → Fin 3) (b : Bool) :
    KS.W01.FixedStack.Instruction k P.states :=
  P.table.getD (KS.W01.FixedStack.tableIndex s heads b).val (KS.W01.FixedStack.Instruction.halt k P.states)

def dispatch {k : Nat} (P Q : Program k) (s : Fin (P.states + Q.states))
    (heads : Fin k → Fin 3) (b : Bool) : KS.W01.FixedStack.Instruction k (P.states + Q.states) :=
  if h : s.val < P.states then
    leftInstruction P Q (fetch P ⟨s.val, h⟩ heads b)
  else
    rightInstruction P Q
      (fetch Q ⟨s.val - P.states, by have hs := s.isLt; omega⟩ heads b)

def compose {k : Nat} (P Q : Program k) : Program k :=
  ofMachine (KS.W01.FixedStack.compile (leftState P Q P.initial) P.input Q.output (dispatch P Q))

@[simp] theorem compose_toMachine {k : Nat} (P Q : Program k) :
    (compose P Q).toMachine =
      KS.W01.FixedStack.compile (leftState P Q P.initial) P.input Q.output (dispatch P Q) :=
  toMachine_ofMachine _

@[simp] theorem compose_input {k : Nat} (P Q : Program k) : (compose P Q).input = P.input := rfl
@[simp] theorem compose_output {k : Nat} (P Q : Program k) : (compose P Q).output = Q.output := rfl

theorem dispatch_left {k : Nat} (P Q : Program k) (s : Fin P.states)
    (heads : Fin k → Fin 3) (b : Bool) :
    dispatch P Q (leftState P Q s) heads b = leftInstruction P Q (fetch P s heads b) := by
  simp [dispatch, leftState, s.isLt]

theorem dispatch_right {k : Nat} (P Q : Program k) (s : Fin Q.states)
    (heads : Fin k → Fin 3) (b : Bool) :
    dispatch P Q (rightState P Q s) heads b = rightInstruction P Q (fetch Q s heads b) := by
  simp [dispatch, rightState]

theorem step_left {k : Nat} (P Q : Program k) (s : Fin P.states)
    («stacks» : Fin k → List Bool) (b : Bool) :
    (compose P Q).toMachine.step ⟨some (leftState P Q s), «stacks»⟩ b =
      liftLeft P Q (P.toMachine.step ⟨some s, «stacks»⟩ b) := by
  change (KS.W01.FixedStack.compile (leftState P Q P.initial) P.input Q.output
    (dispatch P Q)).step _ _ = _
  erw [KS.W01.FixedStack.step_compile]
  dsimp only
  rw [dispatch_left]
  rfl

theorem step_right {k : Nat} (P Q : Program k) (s : Fin Q.states)
    («stacks» : Fin k → List Bool) (b : Bool) :
    (compose P Q).toMachine.step ⟨some (rightState P Q s), «stacks»⟩ b =
      liftRight P Q (Q.toMachine.step ⟨some s, «stacks»⟩ b) := by
  change (KS.W01.FixedStack.compile (leftState P Q P.initial) P.input Q.output
    (dispatch P Q)).step _ _ = _
  erw [KS.W01.FixedStack.step_compile]
  dsimp only
  rw [dispatch_right]
  rfl

theorem step_liftRight {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k Q.states) (b : Bool) :
    (compose P Q).toMachine.step (liftRight P Q c) b =
      liftRight P Q (Q.toMachine.step c b) := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s => exact step_right P Q s «stacks» b

theorem run_liftRight {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k Q.states) (bits : List Bool) :
    (compose P Q).toMachine.run (liftRight P Q c) bits =
      liftRight P Q (Q.toMachine.run c bits) := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      change (compose P Q).toMachine.run
        ((compose P Q).toMachine.step (liftRight P Q c) b) bs =
        liftRight P Q (Q.toMachine.run (Q.toMachine.step c b) bs)
      erw [step_liftRight P Q c b]
      exact ih (Q.toMachine.step c b)

def ActiveFor {k : Nat} (P : Program k) : KS.W01.FixedStack.Config k P.states → List Bool → Prop
  | _, [] => True
  | c, b :: bs => c.state ≠ none ∧ ActiveFor P (P.toMachine.step c b) bs

def HaltsAfter {k : Nat} (P : Program k) (c : KS.W01.FixedStack.Config k P.states) (bits : List Bool) : Prop :=
  ActiveFor P c bits ∧ (P.toMachine.run c bits).state = none

theorem step_liftLeft {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k P.states) (b : Bool)
    (h : c.state ≠ none) :
    (compose P Q).toMachine.step (liftLeft P Q c) b =
      liftLeft P Q (P.toMachine.step c b) := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => exact (h rfl).elim
  | some s => exact step_left P Q s «stacks» b

theorem run_liftLeft {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k P.states) (bits : List Bool)
    (h : ActiveFor P c bits) :
    (compose P Q).toMachine.run (liftLeft P Q c) bits = liftLeft P Q (P.toMachine.run c bits) := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      change (compose P Q).toMachine.run
        ((compose P Q).toMachine.step (liftLeft P Q c) b) bs =
        liftLeft P Q (P.toMachine.run (P.toMachine.step c b) bs)
      erw [step_liftLeft P Q c b h.1]
      exact ih _ h.2

theorem run_compose {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k P.states)
    (first second : List Bool) (h : HaltsAfter P c first) :
    (compose P Q).toMachine.run (liftLeft P Q c) (first ++ second) =
      liftRight P Q (Q.toMachine.run ⟨some Q.initial, (P.toMachine.run c first).«stacks»⟩ second) := by
  erw [KS.W01.FixedStack.Machine.run_append, run_liftLeft P Q c first h.1]
  have he : liftLeft P Q (P.toMachine.run c first) =
      liftRight P Q ⟨some Q.initial, (P.toMachine.run c first).«stacks»⟩ := by
    simp [liftLeft, liftRight, h.2]
  rw [he, run_liftRight]
  rfl

theorem exists_halting_prefix {k : Nat} (P : Program k) (c : KS.W01.FixedStack.Config k P.states)
    (bits : List Bool) (h : (P.toMachine.run c bits).state = none) :
    ∃ first rest, bits = first ++ rest ∧ HaltsAfter P c first := by
  induction bits generalizing c with
  | nil => exact ⟨[], [], rfl, ⟨trivial, h⟩⟩
  | cons b bs ih =>
      by_cases hc : c.state = none
      · exact ⟨[], b :: bs, rfl, ⟨trivial, hc⟩⟩
      · obtain ⟨first, rest, heq, ha⟩ := ih (P.toMachine.step c b) h
        refine ⟨b :: first, rest, ?_, ?_⟩
        · simp [heq]
        · exact ⟨⟨hc, ha.1⟩, ha.2⟩

end KS.W29.FixedSequential

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedCopyRestore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W01.FixedCopy
open KS.W29

def machine {k : ℕ} (ports : Fin 3 ↪ Fin k) : FixedStack.Machine :=
  FixedStack.lift3 CopyInput.machine ports

def program {k : ℕ} (ports : Fin 3 ↪ Fin k) : FixedSequential.Program k :=
  FixedSequential.ofMachine (machine ports)

theorem config_ext {k q : ℕ} {c d : FixedStack.Config k q}
    (hs : c.state = d.state) (ht : c.«stacks» = d.«stacks») : c = d := by
  cases c
  cases d
  cases hs
  cases ht
  rfl

theorem project_start {k : ℕ} (ports : Fin 3 ↪ Fin k) («stacks» : Fin k → List Bool)
    (xs : List Bool) (hsrc : «stacks» (ports 0) = xs)
    (hdst : «stacks» (ports 1) = []) (hscratch : «stacks» (ports 2) = []) :
    FixedStack.project ports (⟨some 0, «stacks»⟩ : FixedStack.Config k 2) =
      CopyInput.machine.init xs := by
  change Config.mk (some 0) (fun j => «stacks» (ports j)) =
    Config.mk (some 0) (fun j => if j = 0 then xs else [])
  congr 1
  funext j
  fin_cases j <;> simp [hsrc, hdst, hscratch]

theorem run_copy_restore {k : ℕ} (ports : Fin 3 ↪ Fin k)
    («stacks» : Fin k → List Bool) (xs bits : List Bool)
    (hsrc : «stacks» (ports 0) = xs) (hdst : «stacks» (ports 1) = [])
    (hscratch : «stacks» (ports 2) = []) (hlen : bits.length = 2 * xs.length + 2) :
    (machine ports).run (⟨some 0, «stacks»⟩ : FixedStack.Config k 2) bits =
      ⟨none, Function.update «stacks» (ports 1) xs⟩ := by
  have hp := FixedStack.lift3_project_run CopyInput.machine ports
    (⟨some 0, «stacks»⟩ : FixedStack.Config k 2) bits
  erw [project_start ports «stacks» xs hsrc hdst hscratch,
    CopyInput.run_eq_copy xs bits hlen] at hp
  have hstate := congrArg (fun c : Config 2 => c.state) hp
  have h0 := congrArg (fun c : Config 2 => c.«stacks» 0) hp
  have h1 := congrArg (fun c : Config 2 => c.«stacks» 1) hp
  have h2 := congrArg (fun c : Config 2 => c.«stacks» 2) hp
  dsimp only [FixedStack.project, CopyInput.cfg] at hstate h0 h1 h2
  apply config_ext hstate
  funext j
  change ((FixedStack.lift3 CopyInput.machine ports).run
    (⟨some 0, «stacks»⟩ : FixedStack.Config k 2) bits).«stacks» j =
      Function.update «stacks» (ports 1) xs j
  by_cases hj1 : j = ports 1
  · subst j
    simpa [Function.update] using h1
  · erw [Function.update_of_ne hj1]
    by_cases hj0 : j = ports 0
    · subst j
      simpa [hsrc] using h0
    · by_cases hj2 : j = ports 2
      · subst j
        simpa [hscratch] using h2
      · exact FixedStack.lift3_run_preserves_other CopyInput.machine ports
          (⟨some 0, «stacks»⟩ : FixedStack.Config k 2) bits j (by
            intro r
            fin_cases r <;> assumption)

end KS.W01.FixedCopy

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W29.FixedLoop
open KS.W29.FixedSequential (Program ofMachine ActiveFor HaltsAfter fetch)
open KS.W01.FixedStack (Config Instruction observedHeads)

inductive Choice where
  | halt
  | restart
  | call
  deriving DecidableEq

structure GuardInstruction (k : Nat) where
  choice : Choice
  actions : Vector KS.W29.StackAction k

def guardState {k : Nat} (P : Program k) : Fin (P.states + 1) := ⟨0, by omega⟩

def bodyState {k : Nat} (P : Program k) (s : Fin P.states) : Fin (P.states + 1) :=
  ⟨s.val + 1, by have h := s.isLt; omega⟩

def guardInstruction {k : Nat} (P : Program k) (i : GuardInstruction k) :
    KS.W01.FixedStack.Instruction k (P.states + 1) :=
  ⟨match i.choice with
    | .halt => none
    | .restart => some (guardState P)
    | .call => some (bodyState P P.initial), i.actions⟩

def bodyInstruction {k : Nat} (P : Program k) (i : KS.W01.FixedStack.Instruction k P.states) :
    KS.W01.FixedStack.Instruction k (P.states + 1) :=
  ⟨some (match i.next with
    | none => guardState P
    | some s => bodyState P s), i.actions⟩

def dispatch {k : Nat} (P : Program k)
    (guard : (Fin k → Fin 3) → Bool → GuardInstruction k)
    (s : Fin (P.states + 1)) (heads : Fin k → Fin 3) (b : Bool) :
    KS.W01.FixedStack.Instruction k (P.states + 1) :=
  if h : s.val = 0 then guardInstruction P (guard heads b)
  else bodyInstruction P (fetch P ⟨s.val - 1, by have hs := s.isLt; omega⟩ heads b)

def loop {k : Nat} (P : Program k)
    (guard : (Fin k → Fin 3) → Bool → GuardInstruction k) : Program k :=
  ofMachine (KS.W01.FixedStack.compile (guardState P) P.input P.output (dispatch P guard))

@[simp] theorem loop_states {k : Nat} (P : Program k) (guard) :
    (loop P guard).states = P.states + 1 := rfl

@[simp] theorem loop_input {k : Nat} (P : Program k) (guard) :
    (loop P guard).input = P.input := rfl

@[simp] theorem loop_output {k : Nat} (P : Program k) (guard) :
    (loop P guard).output = P.output := rfl

@[simp] theorem loop_initial {k : Nat} (P : Program k) (guard) :
    (loop P guard).initial = guardState P := rfl

@[simp] theorem loop_toMachine {k : Nat} (P : Program k) (guard) :
    (loop P guard).toMachine =
      KS.W01.FixedStack.compile (guardState P) P.input P.output (dispatch P guard) :=
  KS.W29.FixedSequential.toMachine_ofMachine _

@[simp] theorem dispatch_guard {k : Nat} (P : Program k) (guard) (heads) (b) :
    dispatch P guard (guardState P) heads b = guardInstruction P (guard heads b) := by
  simp [dispatch, guardState]

@[simp] theorem dispatch_body {k : Nat} (P : Program k) (guard) (s : Fin P.states) (heads) (b) :
    dispatch P guard (bodyState P s) heads b = bodyInstruction P (fetch P s heads b) := by
  simp [dispatch, bodyState]

def liftBody {k : Nat} (P : Program k) (c : KS.W01.FixedStack.Config k P.states) : KS.W01.FixedStack.Config k (P.states + 1) :=
  ⟨some (match c.state with
    | none => guardState P
    | some s => bodyState P s), c.«stacks»⟩

theorem step_guard {k : Nat} (P : Program k) (guard)
    («stacks» : Fin k → List Bool) (b : Bool) :
    (loop P guard).toMachine.step ⟨some (guardState P), «stacks»⟩ b =
      let heads := observedHeads (KS.W01.FixedStack.Config.mk (some (guardState P)) «stacks»)
      let i := guardInstruction P (guard heads b)
      KS.W01.FixedStack.Config.mk i.next (fun j => (i.action j).apply («stacks» j)) := by
  change (KS.W01.FixedStack.compile (guardState P) P.input P.output
    (dispatch P guard)).step _ _ = _
  erw [KS.W01.FixedStack.step_compile]
  dsimp only
  rw [dispatch_guard]

theorem step_body {k : Nat} (P : Program k) (guard) (s : Fin P.states)
    («stacks» : Fin k → List Bool) (b : Bool) :
    (loop P guard).toMachine.step ⟨some (bodyState P s), «stacks»⟩ b =
      liftBody P (P.toMachine.step ⟨some s, «stacks»⟩ b) := by
  change (KS.W01.FixedStack.compile (guardState P) P.input P.output
    (dispatch P guard)).step _ _ = _
  erw [KS.W01.FixedStack.step_compile]
  dsimp only
  rw [dispatch_body]
  rfl

theorem step_liftBody {k : Nat} (P : Program k) (guard) (c : KS.W01.FixedStack.Config k P.states)
    (b : Bool) (h : c.state ≠ none) :
    (loop P guard).toMachine.step (liftBody P c) b =
      liftBody P (P.toMachine.step c b) := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => exact (h rfl).elim
  | some s => exact step_body P guard s «stacks» b

theorem run_body {k : Nat} (P : Program k) (guard) (c : KS.W01.FixedStack.Config k P.states)
    (bits : List Bool) (h : ActiveFor P c bits) :
    (loop P guard).toMachine.run (liftBody P c) bits =
      liftBody P (P.toMachine.run c bits) := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      change (loop P guard).toMachine.run
        ((loop P guard).toMachine.step (liftBody P c) b) bs =
        liftBody P (P.toMachine.run (P.toMachine.step c b) bs)
      erw [step_liftBody P guard c b h.1]
      exact ih _ h.2

theorem run_body_then {k : Nat} (P : Program k) (guard) (c : KS.W01.FixedStack.Config k P.states)
    (first rest : List Bool) (h : HaltsAfter P c first) :
    (loop P guard).toMachine.run (liftBody P c) (first ++ rest) =
      (loop P guard).toMachine.run
        ⟨some (guardState P), (P.toMachine.run c first).«stacks»⟩ rest := by
  erw [KS.W01.FixedStack.Machine.run_append, run_body P guard c first h.1]
  have he : liftBody P (P.toMachine.run c first) =
      ⟨some (guardState P), (P.toMachine.run c first).«stacks»⟩ := by
    simp [liftBody, h.2]
  rw [he]
  rfl

end KS.W29.FixedLoop

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_MachineCombinators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W03.MachineCombinators

open KS.W01.FixedStack
open KS.W29.FixedSequential

def RunSpec {k : ℕ} (P : Program k) (before after : Fin k → List Bool) (ticks : ℕ) : Prop :=
  ∀ bits : List Bool, bits.length = ticks →
    P.toMachine.run ⟨some P.initial, before⟩ bits = ⟨none, after⟩

theorem RunSpec.run_of_le {k : ℕ} {P : Program k} {before after : Fin k → List Bool}
    {ticks : ℕ} (h : RunSpec P before after ticks) (bits : List Bool)
    (hlen : ticks ≤ bits.length) :
    P.toMachine.run ⟨some P.initial, before⟩ bits = ⟨none, after⟩ := by
  have ht : (bits.take ticks).length = ticks := by
    simp only [List.length_take, Nat.min_eq_left hlen]
  have hs := h (bits.take ticks) ht
  conv_lhs => rw [← List.take_append_drop ticks bits]
  rw [Machine.run_append, hs, Machine.run_halted _ _ rfl]

theorem RunSpec.compose {k : ℕ} {P Q : Program k}
    {before middle after : Fin k → List Bool} {t₁ t₂ : ℕ}
    (hP : RunSpec P before middle t₁) (hQ : RunSpec Q middle after t₂) :
    RunSpec (KS.W29.FixedSequential.compose P Q) before after (t₁ + t₂) := by
  intro bits hbits
  let c : Config k P.states := ⟨some P.initial, before⟩
  have htake : (bits.take t₁).length = t₁ := by
    simp only [List.length_take, hbits]
    omega
  have hfirst : P.toMachine.run c (bits.take t₁) = ⟨none, middle⟩ := hP _ htake
  obtain ⟨first, leftover, heq, halt⟩ :=
    exists_halting_prefix P c (bits.take t₁) (congrArg Config.state hfirst)
  have hfl : first.length ≤ t₁ := by
    have hh := congrArg List.length heq
    simp only [List.length_append, htake] at hh
    omega
  have hfout : P.toMachine.run c first = ⟨none, middle⟩ := by
    erw [heq, Machine.run_append, Machine.run_halted _ _ halt.2] at hfirst
    exact hfirst
  have hwhole : bits = first ++ (leftover ++ bits.drop t₁) := by
    calc
      bits = bits.take t₁ ++ bits.drop t₁ := (List.take_append_drop t₁ bits).symm
      _ = first ++ (leftover ++ bits.drop t₁) := by rw [heq, List.append_assoc]
  have hremain : t₂ ≤ (leftover ++ bits.drop t₁).length := by
    have hh := congrArg List.length hwhole
    simp only [List.length_append, hbits] at hh
    simp only [List.length_append]
    omega
  change (KS.W29.FixedSequential.compose P Q).toMachine.run (liftLeft P Q c) bits = ⟨none, after⟩
  rw [hwhole, run_compose P Q c first _ halt, hfout,
    hQ.run_of_le _ hremain]
  rfl

theorem lift3_run_eq {k : ℕ} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (c : Config k M.states) (bits : List Bool) (out : Fin k → List Bool)
    (h : M.run (project ports c) bits = ⟨none, fun i => out (ports i)⟩)
    (hother : ∀ j, (∀ i, j ≠ ports i) → out j = c.«stacks» j) :
    (lift3 M ports).run c bits = ⟨none, out⟩ := by
  have hp := lift3_project_run M ports c bits
  rw [h] at hp
  have hs : ((lift3 M ports).run c bits).state = none :=
    congrArg (fun d : KS.W29.Config M.states => d.state) hp
  have hst : ((lift3 M ports).run c bits).«stacks» = out := by
    funext j
    by_cases hj : ∃ i, j = ports i
    · obtain ⟨i, rfl⟩ := hj
      exact congrArg (fun d : KS.W29.Config M.states => d.«stacks» i) hp
    · have hnone : ∀ i, j ≠ ports i := by simpa only [not_exists] using hj
      rw [lift3_run_preserves_other M ports c bits j hnone, hother j hnone]
  exact congrArg₂ Config.mk hs hst

theorem RunSpec.loop_body_then {k : ℕ} {P : Program k}
    {before after : Fin k → List Bool} {ticks : ℕ}
    (hP : RunSpec P before after ticks)
    (guard : (Fin k → Fin 3) → Bool → KS.W29.FixedLoop.GuardInstruction k)
    (bits : List Bool) (hlen : ticks ≤ bits.length) :
    ∃ rest : List Bool, bits.length - ticks ≤ rest.length ∧
      (KS.W29.FixedLoop.loop P guard).toMachine.run
        (KS.W29.FixedLoop.liftBody P ⟨some P.initial, before⟩) bits =
      (KS.W29.FixedLoop.loop P guard).toMachine.run
        ⟨some (KS.W29.FixedLoop.guardState P), after⟩ rest := by
  let c : Config k P.states := ⟨some P.initial, before⟩
  have htake : (bits.take ticks).length = ticks := by
    simp only [List.length_take, Nat.min_eq_left hlen]
  have hfull : P.toMachine.run c (bits.take ticks) = ⟨none, after⟩ := hP _ htake
  obtain ⟨first, leftover, heq, halt⟩ :=
    exists_halting_prefix P c (bits.take ticks) (congrArg Config.state hfull)
  have hout : P.toMachine.run c first = ⟨none, after⟩ := by
    erw [heq, Machine.run_append, Machine.run_halted _ _ halt.2] at hfull
    exact hfull
  have hwhole : bits = first ++ (leftover ++ bits.drop ticks) := by
    calc
      bits = bits.take ticks ++ bits.drop ticks := (List.take_append_drop ticks bits).symm
      _ = first ++ (leftover ++ bits.drop ticks) := by rw [heq, List.append_assoc]
  refine ⟨leftover ++ bits.drop ticks, ?_, ?_⟩
  · simp only [List.length_append, List.length_drop]
    omega
  · conv_lhs => rw [hwhole]
    rw [KS.W29.FixedLoop.run_body_then P guard c first _ halt, hout]

end KS.W03.MachineCombinators

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FrameDecoder
attribute [-simp] _root_.OAI.KS.W01.FixedStack.lift3_project_init
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W29
namespace FrameDecoder

def config (s : Option (Fin 3)) (input output scratch : List Bool) : Config 3 :=
  ⟨s, fun j => if j = 0 then input else if j = 1 then output else scratch⟩

def tagEntry (top : Nat) : Instruction 3 :=
  if top = 0 then Instruction.halt 3
  else if top = 1 then ⟨some 1, .pop, .stay, .stay⟩
  else ⟨some 2, .pop, .stay, .stay⟩

def dataEntry (top : Nat) : Instruction 3 :=
  if top = 0 then Instruction.halt 3
  else ⟨some 0, .pop, .stay, .push (top == 2)⟩

def reverseEntry (top : Nat) : Instruction 3 :=
  if top = 0 then Instruction.halt 3
  else ⟨some 2, .stay, .push (top == 2), .pop⟩

def dispatch (s : Fin 3) (heads : Fin 27) (_coin : Bool) : Instruction 3 :=
  if s.val = 0 then tagEntry (heads.val % 3)
  else if s.val = 1 then dataEntry (heads.val % 3)
  else reverseEntry (heads.val / 9)

def machine : BinaryMachine := FiniteDispatch.compile 0 dispatch

theorem first_head (c : Config 3) : headCode c % 3 = topCode (c.«stacks» 0) := by
  have h₀ := topCode_lt_three (c.«stacks» 0)
  unfold headCode
  omega

theorem third_head (c : Config 3) : headCode c / 9 = topCode (c.«stacks» 2) := by
  have h₀ := topCode_lt_three (c.«stacks» 0)
  have h₁ := topCode_lt_three (c.«stacks» 1)
  unfold headCode
  omega

theorem tag_false_step (xs ys zs : List Bool) (b : Bool) :
    machine.step (config (some 0) (false :: xs) ys zs) b =
      config (some 1) xs ys zs := by
  unfold machine config
  erw [FiniteDispatch.step_compile]
  dsimp only
  simp only [dispatch, first_head]
  change Config.mk (some (1 : Fin 3)) _ = Config.mk (some (1 : Fin 3)) _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem tag_true_step (xs ys zs : List Bool) (b : Bool) :
    machine.step (config (some 0) (true :: xs) ys zs) b =
      config (some 2) xs ys zs := by
  unfold machine config
  erw [FiniteDispatch.step_compile]
  dsimp only
  simp only [dispatch, first_head]
  change Config.mk (some (2 : Fin 3)) _ = Config.mk (some (2 : Fin 3)) _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem data_step (x : Bool) (xs ys zs : List Bool) (b : Bool) :
    machine.step (config (some 1) (x :: xs) ys zs) b =
      config (some 0) xs ys (x :: zs) := by
  unfold machine config
  erw [FiniteDispatch.step_compile]
  dsimp only
  simp only [dispatch, first_head]
  cases x <;> change Config.mk (some (0 : Fin 3)) _ = Config.mk (some (0 : Fin 3)) _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem reverse_step (x : Bool) (xs ys zs : List Bool) (b : Bool) :
    machine.step (config (some 2) xs ys (x :: zs)) b =
      config (some 2) xs (x :: ys) zs := by
  unfold machine config
  erw [FiniteDispatch.step_compile]
  dsimp only
  simp only [dispatch, third_head]
  cases x <;> change Config.mk (some (2 : Fin 3)) _ = Config.mk (some (2 : Fin 3)) _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem reverse_done (xs ys : List Bool) (b : Bool) :
    machine.step (config (some 2) xs ys []) b = config none xs ys [] := by
  unfold machine config
  erw [FiniteDispatch.step_compile]
  dsimp only
  simp only [dispatch, third_head]
  change Config.mk none _ = Config.mk none _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem run_read (payload tail out scratch bits : List Bool)
    (h : bits.length = 2 * payload.length + 1) :
    machine.run (config (some 0) (W01.frame payload ++ tail) out scratch) bits =
      config (some 2) tail out (payload.reverse ++ scratch) := by
  induction payload generalizing scratch bits with
  | nil =>
      cases bits with
      | nil => simp at h
      | cons b bs =>
          have hb : bs = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [List.length_cons, List.length_nil] at h
            omega
          subst bs
          simpa [W01.frame, BinaryMachine.run] using tag_true_step tail out scratch b
  | cons x xs ih =>
      cases bits with
      | nil => simp at h
      | cons b₀ bs =>
          cases bs with
          | nil => simp at h
          | cons b₁ rest =>
              have hr : rest.length = 2 * xs.length + 1 := by
                simp only [List.length_cons] at h
                omega
              simp only [W01.frame, List.cons_append, BinaryMachine.run]
              rw [tag_false_step, data_step, ih _ _ hr]
              simp [List.reverse_cons, List.append_assoc]
              rfl

theorem run_reverse (input output scratch bits : List Bool)
    (h : bits.length = scratch.length + 1) :
    machine.run (config (some 2) input output scratch) bits =
      config none input (scratch.reverse ++ output) [] := by
  induction scratch generalizing output bits with
  | nil =>
      cases bits with
      | nil => simp at h
      | cons b bs =>
          have hb : bs = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [List.length_cons, List.length_nil] at h
            omega
          subst bs
          simpa [BinaryMachine.run] using reverse_done input output b
  | cons x xs ih =>
      cases bits with
      | nil => simp at h
      | cons b bs =>
          have hb : bs.length = xs.length + 1 := by simpa using h
          erw [BinaryMachine.run, reverse_step, ih _ _ hb]
          simp [List.reverse_cons, List.append_assoc]
          rfl

theorem run_frame (payload tail bits : List Bool)
    (h : bits.length = 3 * payload.length + 2) :
    machine.run (machine.init (W01.frame payload ++ tail)) bits =
      config none tail payload [] := by
  have hi : machine.init (W01.frame payload ++ tail) =
      config (some 0) (W01.frame payload ++ tail) [] [] := by
    simp [BinaryMachine.init, machine, FiniteDispatch.compile, config]
  rw [hi]
  have hl : (bits.take (2 * payload.length + 1)).length = 2 * payload.length + 1 := by
    simp only [List.length_take, h]
    omega
  have hr : (bits.drop (2 * payload.length + 1)).length = payload.length + 1 := by
    simp only [List.length_drop, h]
    omega
  conv_lhs => rw [← List.take_append_drop (2 * payload.length + 1) bits]
  erw [machine.run_append, run_read _ _ _ _ _ hl]
  simp only [List.append_nil]
  rw [run_reverse]
  · simp
    rfl
  · simpa using hr

end FrameDecoder
end KS.W29

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_EntryPoint
attribute [-simp] _root_.OAI.KS.W01.FixedStack.lift3_project_init
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W29

def BinaryMachine.withEntry (M : BinaryMachine) (entry : Fin M.states) : BinaryMachine :=
  ⟨M.states, entry, M.table⟩

@[simp] theorem BinaryMachine.withEntry_step (M : BinaryMachine) (entry : Fin M.states)
    (c : Config M.states) (b : Bool) : (M.withEntry entry).step c b = M.step c b := by
  rcases c with ⟨state, «stacks»⟩
  cases state <;> rfl

theorem BinaryMachine.withEntry_run (M : BinaryMachine) (entry : Fin M.states)
    (c : Config M.states) (bits : List Bool) :
    (M.withEntry entry).run c bits = M.run c bits := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      erw [BinaryMachine.run, BinaryMachine.withEntry_step, ih, BinaryMachine.run]

@[simp] theorem BinaryMachine.withEntry_initial (M : BinaryMachine) (entry : Fin M.states) :
    (M.withEntry entry).initial = entry := rfl

@[simp] theorem BinaryMachine.withEntry_init_state (M : BinaryMachine) (entry : Fin M.states)
    (input : List Bool) : ((M.withEntry entry).init input).state = some entry := rfl

@[simp] theorem BinaryMachine.withEntry_init_stacks (M : BinaryMachine) (entry : Fin M.states)
    (input : List Bool) : ((M.withEntry entry).init input).«stacks» = (M.init input).«stacks» := rfl

end KS.W29

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_NormalizeOutput
attribute [-simp] _root_.OAI.KS.W01.FixedStack.lift3_project_init
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W29
namespace NormalizeOutput

def machine : BinaryMachine := FrameDecoder.machine.withEntry (2 : Fin 3)

theorem run_normalize (input output scratch bits : List Bool)
    (h : bits.length = scratch.length + 1) :
    machine.run (FrameDecoder.config (some 2) input output scratch) bits =
      FrameDecoder.config none input (scratch.reverse ++ output) [] := by
  unfold machine
  erw [BinaryMachine.withEntry_run]
  exact FrameDecoder.run_reverse input output scratch bits h

theorem initial_eq : machine.initial = (2 : Fin 3) := rfl

theorem run_reversed (input result bits : List Bool) (h : bits.length = result.length + 1) :
    machine.run (FrameDecoder.config (some machine.initial) input [] result.reverse) bits =
      FrameDecoder.config none input result [] := by
  rw [initial_eq, run_normalize]
  · simp
    rfl
  · simpa using h

end NormalizeOutput
end KS.W29

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_BinaryTrimMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.BinaryTrimMachine
open KS.W29

def dispatch (s : Fin 2) (heads : Fin 27) (_coin : Bool) : Instruction 2 :=
  let top := heads.val / 9
  if top = 0 then Instruction.halt 2
  else if s = 0 ∧ top = 1 then ⟨some 0, .stay, .stay, .pop⟩
  else ⟨some 1, .stay, .push (top == 2), .pop⟩

def machine : BinaryMachine := FiniteDispatch.compile 0 dispatch

end KS.W19.BinaryTrimMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_MultiplicationNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W03.MultiplicationNormalize

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def reversePorts : Fin 3 ↪ Fin 7 := ⟨![0, 6, 3], by decide⟩
def trimPorts : Fin 3 ↪ Fin 7 := ⟨![0, 3, 6], by decide⟩

def reverseProgram : Program 7 := ofMachine (lift3 KS.W29.NormalizeOutput.machine reversePorts)
def trimProgram : Program 7 := ofMachine (lift3 KS.W19.BinaryTrimMachine.machine trimPorts)
def program : Program 7 := compose reverseProgram trimProgram

@[simp] theorem output_port : program.output = 3 := rfl

end KS.W03.MultiplicationNormalize

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_NegativeWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open Matrix

def zeroPivotWitness {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) : Fin n → ℚ :=
  Pi.single i (-(M j j + 1) / (2 * M i j)) + Pi.single j 1

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RationalElimination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

def trailingMatrix {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) :
    Matrix (Fin n) (Fin n) ℚ := fun i j => M i.succ j.succ

def schurTail {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j => M i.succ j.succ - M i.succ 0 * M 0 j.succ / M 0 0

def schurWitnessLift {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (y : Fin n → ℚ) : Fin (n + 1) → ℚ :=
  Fin.cons (-(∑ j, M 0 j.succ * y j) / M 0 0) y

def firstNonzeroOffDiagonal {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) : Option (Fin n) :=
  (List.finRange n).find? (fun j => decide (M 0 j.succ ≠ 0))

def rationalNegativeWitness : (n : ℕ) →
    Matrix (Fin n) (Fin n) ℚ → Option (Fin n → ℚ)
  | 0, _ => none
  | n + 1, M =>
      if M 0 0 < 0 then some (Pi.single 0 1)
      else if M 0 0 = 0 then
        match firstNonzeroOffDiagonal M with
        | some j => some (zeroPivotWitness M 0 j.succ)
        | none => (rationalNegativeWitness n (trailingMatrix M)).map (Fin.cons 0)
      else (rationalNegativeWitness n (schurTail M)).map (schurWitnessLift M)

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalArithmeticMeter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

inductive RationalExpr where
  | value : ℚ → RationalExpr
  | add : RationalExpr → RationalExpr → RationalExpr
  | sub : RationalExpr → RationalExpr → RationalExpr
  | mul : RationalExpr → RationalExpr → RationalExpr
  | div : RationalExpr → RationalExpr → RationalExpr
  | neg : RationalExpr → RationalExpr

def RationalExpr.eval : RationalExpr → ℚ
  | .value q => q
  | .add x y => x.eval + y.eval
  | .sub x y => x.eval - y.eval
  | .mul x y => x.eval * y.eval
  | .div x y => x.eval / y.eval
  | .neg x => -x.eval

def schurEntryExpr {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (i j : Fin n) : RationalExpr :=
  .sub (.value (M i.succ j.succ))
    (.div (.mul (.value (M i.succ 0)) (.value (M 0 j.succ))) (.value (M 0 0)))

@[simp] theorem schurEntryExpr_eval {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (i j : Fin n) :
    (schurEntryExpr M i j).eval = schurTail M i j := rfl

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_PositiveWireSerializer
attribute [-simp] _root_.OAI.KS.W01.FixedStack.lift3_project_init _root_.OAI.KS.W29.BinaryMachine.withEntry_init_stacks _root_.OAI.KS.W29.BinaryMachine.withEntry_init_state _root_.OAI.KS.W29.BinaryMachine.withEntry_initial _root_.OAI.KS.W29.BinaryMachine.withEntry_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W28.PositiveWireSerializer
open KS.W29

def dispatch (s : Fin 5) (heads : Fin 27) (_coin : Bool) : Instruction 5 :=
  if s = 4 then ⟨some 0, .stay, .stay, .push false⟩
  else if s = 0 then
    if heads.val % 3 = 0 then ⟨some 2, .stay, .stay, .push true⟩
    else ⟨some 1, .stay, .stay, .push false⟩
  else if s = 1 then ⟨some 0, .pop, .stay, .push (heads.val % 3 == 2)⟩
  else if s = 2 then
    if heads.val / 3 % 3 = 0 then ⟨none, .stay, .stay, .push true⟩
    else ⟨some 3, .stay, .stay, .push false⟩
  else ⟨some 2, .stay, .pop, .push (heads.val / 3 % 3 == 2)⟩

def machine : BinaryMachine := FiniteDispatch.compile 4 dispatch

def cfg (state : Option (Fin 5)) (xs ys zs : List Bool) : Config 5 :=
  ⟨state, fun j => if j = 0 then xs else if j = 1 then ys else zs⟩

theorem head_left (c : Config 5) : headCode c % 3 = topCode (c.«stacks» 0) := by
  have h0 := topCode_lt_three (c.«stacks» 0)
  unfold headCode
  omega

theorem head_right (c : Config 5) : headCode c / 3 % 3 = topCode (c.«stacks» 1) := by
  have h0 := topCode_lt_three (c.«stacks» 0)
  have h1 := topCode_lt_three (c.«stacks» 1)
  unfold headCode
  omega

theorem step_den_prefix (b : Bool) (ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some 2) [] (b :: ys) zs) coin =
      cfg (some 3) [] (b :: ys) (false :: zs) := by
  unfold machine
  erw [FiniteDispatch.step_compile]
  simp only [dispatch, head_left, head_right]
  cases b <;> change Config.mk _ _ = Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem step_den_digit (b : Bool) (ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some 3) [] (b :: ys) zs) coin = cfg (some 2) [] ys (b :: zs) := by
  unfold machine
  erw [FiniteDispatch.step_compile]
  simp only [dispatch, head_left, head_right]
  cases b <;> change Config.mk _ _ = Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem step_den_done (zs : List Bool) (coin : Bool) :
    machine.step (cfg (some 2) [] [] zs) coin = cfg none [] [] (true :: zs) := by
  unfold machine
  erw [FiniteDispatch.step_compile]
  simp only [dispatch, head_left, head_right]
  change Config.mk _ _ = Config.mk _ _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem run_den (ys zs coins : List Bool) (hlen : coins.length = 2 * ys.length + 1) :
    machine.run (cfg (some 2) [] ys zs) coins =
      cfg none [] [] ((KS.W01.frame ys).reverse ++ zs) := by
  induction ys generalizing zs coins with
  | nil =>
      cases coins with
      | nil => simp at hlen
      | cons c cs =>
          have hc : cs = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [List.length_cons, List.length_nil] at hlen
            omega
          subst cs
          erw [BinaryMachine.run, step_den_done]
          rfl
  | cons b ys ih =>
      cases coins with
      | nil => simp at hlen
      | cons c cs =>
          cases cs with
          | nil => simp at hlen
          | cons d ds =>
              have hd : ds.length = 2 * ys.length + 1 := by
                simp only [List.length_cons] at hlen
                omega
              erw [BinaryMachine.run, step_den_prefix, BinaryMachine.run, step_den_digit, ih _ _ hd]
              simp [KS.W01.frame, List.reverse_cons, List.append_assoc]
              rfl

end KS.W28.PositiveWireSerializer

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FixedPositiveSerializer
attribute [-simp] _root_.OAI.KS.W03.MultiplicationNormalize.output_port
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W28.FixedPositiveSerializer
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def registers {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs ys zs : List Bool) : Fin k → List Bool := fun j =>
  if j = ports 0 then xs else if j = ports 1 then ys else if j = ports 2 then zs else spare j

@[simp] theorem registers_port {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (spare : Fin k → List Bool) (xs ys zs : List Bool) (i : Fin 3) :
    registers ports spare xs ys zs (ports i) =
      if i = 0 then xs else if i = 1 then ys else zs := by
  fin_cases i <;> simp [registers, ports.injective.eq_iff]

theorem registers_other {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (spare : Fin k → List Bool) (xs ys zs : List Bool) (j : Fin k)
    (hj : ∀ i, j ≠ ports i) : registers ports spare xs ys zs j = spare j := by
  simp [registers, hj 0, hj 1, hj 2]

def reverseProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 KS.W29.NormalizeOutput.machine ports)

theorem reverse_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (wire : List Bool) :
    RunSpec (reverseProgram ports) (registers ports spare [] [] wire.reverse)
      (registers ports spare [] wire []) (wire.length + 1) := by
  intro bits hbits
  change (lift3 KS.W29.NormalizeOutput.machine ports).run
    ⟨some (2 : Fin 3), registers ports spare [] [] wire.reverse⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports
        (⟨some 2, registers ports spare [] [] wire.reverse⟩ : Config k 3) =
        KS.W29.FrameDecoder.config (some 2) [] [] wire.reverse := by
      change KS.W29.Config.mk (some (2 : Fin 3)) _ = KS.W29.Config.mk (some (2 : Fin 3)) _
      apply congrArg (KS.W29.Config.mk (some (2 : Fin 3)))
      funext j
      simp
    erw [hp, KS.W29.NormalizeOutput.run_reversed [] wire bits hbits]
    apply congrArg (KS.W29.Config.mk none)
    funext j
    simp
  · intro j hj
    change registers ports spare [] wire [] j = registers ports spare [] [] wire.reverse j
    rw [registers_other _ _ _ _ _ _ hj, registers_other _ _ _ _ _ _ hj]

end KS.W28.FixedPositiveSerializer

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FrameWireCodec
attribute [-simp] _root_.OAI.KS.W03.MultiplicationNormalize.output_port
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.FrameWireCodec
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W28.FixedPositiveSerializer (registers registers_port registers_other)

def inputAt {k : ℕ} (P : Program k) (port : Fin k) : Program k := { P with input := port }

theorem inputAt_step {k : ℕ} (P : Program k) (port : Fin k)
    (c : Config k P.states) (coin : Bool) :
    (inputAt P port).toMachine.step c coin = P.toMachine.step c coin := by
  cases c with
  | mk state «stacks» => cases state <;> rfl

theorem inputAt_run {k : ℕ} (P : Program k) (port : Fin k)
    (c : Config k P.states) (bits : List Bool) :
    (inputAt P port).toMachine.run c bits = P.toMachine.run c bits := by
  induction bits generalizing c with
  | nil => rfl
  | cons coin bits ih => erw [Machine.run.eq_2, inputAt_step, ih, Machine.run.eq_2]

def frameEmitter : KS.W29.BinaryMachine :=
  KS.W28.PositiveWireSerializer.machine.withEntry (2 : Fin 5)

def emitProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  inputAt (ofMachine (lift3 frameEmitter ports)) (ports 1)

def frameProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  compose (emitProgram ports) (KS.W28.FixedPositiveSerializer.reverseProgram ports)

theorem emit_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (payload : List Bool) :
    RunSpec (emitProgram ports) (registers ports spare [] payload [])
      (registers ports spare [] [] (KS.W01.frame payload).reverse)
      (2 * payload.length + 1) := by
  intro bits hbits
  unfold emitProgram
  erw [inputAt_run]
  change (lift3 frameEmitter ports).run
    ⟨some (2 : Fin 5), registers ports spare [] payload []⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some (2 : Fin 5), registers ports spare [] payload []⟩ : Config k 5) =
        KS.W28.PositiveWireSerializer.cfg (some 2) [] payload [] := by
      change KS.W29.Config.mk (some (2 : Fin 5)) _ = KS.W29.Config.mk (some (2 : Fin 5)) _
      congr 1
      funext j
      simp
    erw [hp]
    unfold frameEmitter
    erw [KS.W29.BinaryMachine.withEntry_run,
      KS.W28.PositiveWireSerializer.run_den payload [] bits hbits]
    apply congrArg (KS.W29.Config.mk none)
    funext j
    simp
  · intro j hj
    change registers ports spare _ _ _ j = registers ports spare _ _ _ j
    rw [registers_other _ _ _ _ _ _ hj, registers_other _ _ _ _ _ _ hj]

theorem frame_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (payload : List Bool) :
    RunSpec (frameProgram ports) (registers ports spare [] payload [])
      (registers ports spare [] (KS.W01.frame payload) []) (4 * payload.length + 3) := by
  have h := (emit_spec ports spare payload).compose
    (KS.W28.FixedPositiveSerializer.reverse_spec ports spare (KS.W01.frame payload))
  have ht : (2 * payload.length + 1) + ((KS.W01.frame payload).length + 1) =
      4 * payload.length + 3 := by rw [KS.W01.length_frame]; omega
  rw [ht] at h
  exact h

def unframeProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 KS.W29.FrameDecoder.machine ports)

theorem unframe_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (payload tail : List Bool) :
    RunSpec (unframeProgram ports) (registers ports spare (KS.W01.frame payload ++ tail) [] [])
      (registers ports spare tail payload []) (3 * payload.length + 2) := by
  intro bits hbits
  change (lift3 KS.W29.FrameDecoder.machine ports).run
    ⟨some (0 : Fin 3), registers ports spare (KS.W01.frame payload ++ tail) [] []⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports
        (⟨some (0 : Fin 3), registers ports spare (KS.W01.frame payload ++ tail) [] []⟩ : Config k 3) =
        KS.W29.FrameDecoder.machine.init (KS.W01.frame payload ++ tail) := by
      change KS.W29.Config.mk (some (0 : Fin 3)) _ = KS.W29.Config.mk (some (0 : Fin 3)) _
      congr 1
      funext j
      fin_cases j <;> simp [registers]
    erw [hp, KS.W29.FrameDecoder.run_frame payload tail bits hbits]
    apply congrArg (KS.W29.Config.mk none)
    funext j
    simp
  · intro j hj
    change registers ports spare _ _ _ j = registers ports spare _ _ _ j
    rw [registers_other _ _ _ _ _ _ hj, registers_other _ _ _ _ _ _ hj]

end KS.W11.FrameWireCodec

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedRun
attribute [-simp] _root_.OAI.KS.W29.BinaryMachine.withEntry_init_stacks _root_.OAI.KS.W29.BinaryMachine.withEntry_init_state _root_.OAI.KS.W29.BinaryMachine.withEntry_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.FixedRun
open KS.W01.FixedStack

def pack {k q : Nat} (ports : Fin 3 ↪ Fin k) (c : KS.W29.Config q)
    (rest : Fin k → List Bool) : Config k q :=
  ⟨c.state, fun j => if j = ports 0 then c.«stacks» 0 else if j = ports 1 then c.«stacks» 1
    else if j = ports 2 then c.«stacks» 2 else rest j⟩

@[simp] theorem pack_on_port {k q : Nat} (ports : Fin 3 ↪ Fin k) (c : KS.W29.Config q)
    (rest : Fin k → List Bool) (j : Fin 3) :
    (pack ports c rest).«stacks» (ports j) = c.«stacks» j := by
  fin_cases j <;> simp [pack, ports.injective.eq_iff]

theorem config_ext {k q : Nat} {c d : Config k q} (hs : c.state = d.state)
    (ht : ∀ j, c.«stacks» j = d.«stacks» j) : c = d := by
  cases c
  cases d
  exact congrArg₂ Config.mk hs (funext ht)

end KS.W19.FixedRun

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_BinaryStackMoves
attribute [-simp] _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedLoop.dispatch_body _root_.OAI.KS.W29.FixedLoop.dispatch_guard _root_.OAI.KS.W29.FixedLoop.loop_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W04.BinaryStackMoves
open KS.W01.FixedStack
open KS.W29 (StackAction)
open KS.W29.FixedSequential (Program ActiveFor HaltsAfter )

variable {k : Nat}

def clearDispatch (port : Fin k) (_state : Fin 1) (heads : Fin k → Fin 3)
    (_coin : Bool) : Instruction k 1 :=
  if (heads port).val = 0 then Instruction.halt k 1
  else ⟨some (0 : Fin 1), Vector.ofFn (fun j => if j = port then .pop else .stay)⟩

def clearMachine (port : Fin k) : Machine := compile 0 port port (clearDispatch port)
def clearProgram (port : Fin k) : Program k :=
  KS.W29.FixedSequential.ofMachine (clearMachine port)

def oneConfig (port : Fin k) (state : Option (Fin 1)) (payload : List Bool)
    (rest : Fin k → List Bool) : Config k 1 :=
  ⟨state, fun j => if j = port then payload else rest j⟩

theorem config_ext {q : Nat} {c d : Config k q} (hs : c.state = d.state)
    (ht : ∀ j, c.«stacks» j = d.«stacks» j) : c = d := by
  cases c
  cases d
  exact congrArg₂ Config.mk hs (funext ht)

theorem clear_step_cons (port : Fin k) (b : Bool) (xs : List Bool)
    (rest : Fin k → List Bool) (coin : Bool) :
    (clearMachine port).step (oneConfig port (some (0 : Fin 1)) (b :: xs) rest) coin =
      oneConfig port (some (0 : Fin 1)) xs rest := by
  unfold clearMachine oneConfig
  erw [step_compile]
  dsimp only [compile]
  cases b <;> apply config_ext
  all_goals
    first | (solve | simp [clearDispatch, observedHeads, KS.W29.topCode]) |
      (intro j; by_cases hj : j = port <;>
      simp [clearDispatch, observedHeads, Instruction.action,
        KS.W29.topCode, StackAction.apply, hj])

theorem clear_step_nil (port : Fin k) (rest : Fin k → List Bool) (coin : Bool) :
    (clearMachine port).step (oneConfig port (some (0 : Fin 1)) [] rest) coin =
      oneConfig port none [] rest := by
  unfold clearMachine oneConfig
  erw [step_compile]
  dsimp only [compile]
  apply config_ext
  · simp [clearDispatch, observedHeads, KS.W29.topCode, Instruction.halt]
  · intro j
    simp [clearDispatch, observedHeads, KS.W29.topCode, Instruction.halt,
      Instruction.action, StackAction.apply]
    all_goals rfl

theorem run_clear (port : Fin k) (xs : List Bool) (rest : Fin k → List Bool)
    (bits : List Bool) (hlen : bits.length = xs.length + 1) :
    (clearMachine port).run (oneConfig port (some (0 : Fin 1)) xs rest) bits =
      oneConfig port none [] rest := by
  induction xs generalizing bits with
  | nil =>
      cases bits with
      | nil => simp at hlen
      | cons coin tail =>
          have ht : tail = [] := by apply List.length_eq_zero_iff.mp; simpa using hlen
          subst tail
          simpa [Machine.run] using clear_step_nil port rest coin
  | cons b xs ih =>
      cases bits with
      | nil => simp at hlen
      | cons coin tail =>
          change (clearMachine port).run ((clearMachine port).step
            (oneConfig port (some 0) (b :: xs) rest) coin) tail = _
          erw [clear_step_cons]
          exact ih tail (by simpa using hlen)

def moveDispatch (source target : Fin k) (_state : Fin 1) (heads : Fin k → Fin 3)
    (_coin : Bool) : Instruction k 1 :=
  if (heads source).val = 0 then Instruction.halt k 1
  else ⟨some (0 : Fin 1), Vector.ofFn (fun j => if j = source then .pop
    else if j = target then .push ((heads source).val == 2) else .stay)⟩

def moveMachine (source target : Fin k) : Machine :=
  compile 0 source target (moveDispatch source target)
def moveProgram (source target : Fin k) : Program k :=
  KS.W29.FixedSequential.ofMachine (moveMachine source target)

def twoConfig (source target : Fin k) (state : Option (Fin 1))
    (payload destination : List Bool) (rest : Fin k → List Bool) : Config k 1 :=
  ⟨state, fun j => if j = source then payload else if j = target then destination else rest j⟩

theorem move_step_cons (source target : Fin k) (_ : source ≠ target)
    (b : Bool) (xs ys : List Bool) (rest : Fin k → List Bool) (coin : Bool) :
    (moveMachine source target).step (twoConfig source target (some (0 : Fin 1)) (b :: xs) ys rest) coin =
      twoConfig source target (some (0 : Fin 1)) xs (b :: ys) rest := by
  unfold moveMachine twoConfig
  erw [step_compile]
  dsimp only [compile]
  cases b <;> apply config_ext
  all_goals
    first | (solve | simp [moveDispatch, observedHeads, KS.W29.topCode]) |
      (intro j; by_cases hjs : j = source <;> by_cases hjt : j = target <;>
      simp_all [moveDispatch, observedHeads, Instruction.action,
        KS.W29.topCode, StackAction.apply])

theorem move_step_nil (source target : Fin k) (ys : List Bool)
    (rest : Fin k → List Bool) (coin : Bool) :
    (moveMachine source target).step (twoConfig source target (some (0 : Fin 1)) [] ys rest) coin =
      twoConfig source target none [] ys rest := by
  unfold moveMachine twoConfig
  erw [step_compile]
  dsimp only [compile]
  apply config_ext
  · simp [moveDispatch, observedHeads, KS.W29.topCode, Instruction.halt]
  · intro j
    simp [moveDispatch, observedHeads, KS.W29.topCode, Instruction.halt,
      Instruction.action, StackAction.apply]
    all_goals rfl

theorem run_move (source target : Fin k) (hst : source ≠ target)
    (xs ys : List Bool) (rest : Fin k → List Bool) (bits : List Bool)
    (hlen : bits.length = xs.length + 1) :
    (moveMachine source target).run (twoConfig source target (some (0 : Fin 1)) xs ys rest) bits =
      twoConfig source target none [] (xs.reverse ++ ys) rest := by
  induction xs generalizing ys bits with
  | nil =>
      cases bits with
      | nil => simp at hlen
      | cons coin tail =>
          have ht : tail = [] := by apply List.length_eq_zero_iff.mp; simpa using hlen
          subst tail
          simpa [Machine.run] using move_step_nil source target ys rest coin
  | cons b xs ih =>
      cases bits with
      | nil => simp at hlen
      | cons coin tail =>
          change (moveMachine source target).run ((moveMachine source target).step
            (twoConfig source target (some 0) (b :: xs) ys rest) coin) tail = _
          erw [move_step_cons source target hst]
          simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
          exact ih (b :: ys) tail (by simpa using hlen)

@[simp] theorem oneConfig_original (port : Fin k) (state : Option (Fin 1))
    («stacks» : Fin k → List Bool) : oneConfig port state («stacks» port) «stacks» = ⟨state, «stacks»⟩ := by
  refine config_ext ?_ ?_
  · rfl
  intro j
  by_cases hj : j = port <;> simp [oneConfig, hj]

@[simp] theorem twoConfig_original (source target : Fin k) (state : Option (Fin 1))
    («stacks» : Fin k → List Bool) :
    twoConfig source target state («stacks» source) («stacks» target) «stacks» = ⟨state, «stacks»⟩ := by
  refine config_ext ?_ ?_
  · rfl
  intro j
  by_cases hjs : j = source <;> by_cases hjt : j = target <;>
    simp_all [twoConfig]

theorem run_clear_stacks (port : Fin k) («stacks» : Fin k → List Bool) (bits : List Bool)
    (hlen : bits.length = («stacks» port).length + 1) :
    (clearMachine port).run ⟨some (0 : Fin 1), «stacks»⟩ bits = oneConfig port none [] «stacks» := by
  have h := run_clear port («stacks» port) «stacks» bits hlen
  erw [oneConfig_original] at h
  exact h

theorem run_move_stacks (source target : Fin k) (hst : source ≠ target)
    («stacks» : Fin k → List Bool) (bits : List Bool)
    (hlen : bits.length = («stacks» source).length + 1) :
    (moveMachine source target).run ⟨some (0 : Fin 1), «stacks»⟩ bits =
      twoConfig source target none [] ((«stacks» source).reverse ++ «stacks» target) «stacks» := by
  have h := run_move source target hst («stacks» source) («stacks» target) «stacks» bits hlen
  erw [twoConfig_original] at h
  exact h

end KS.W04.BinaryStackMoves

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_StackTransferSpecs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W15.RationalMultiply
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def clearAfter {k : Nat} (port : Fin k) (before : Fin k → List Bool) : Fin k → List Bool :=
  fun j => if j = port then [] else before j

theorem clear_spec {k : Nat} (port : Fin k) (before : Fin k → List Bool) :
    RunSpec (KS.W04.BinaryStackMoves.clearProgram port) before
      (clearAfter port before) ((before port).length + 1) := by
  intro bits hlen
  exact KS.W04.BinaryStackMoves.run_clear_stacks port before bits hlen

def moveAfter {k : Nat} (source target : Fin k) (before : Fin k → List Bool) :
    Fin k → List Bool :=
  fun j => if j = source then [] else if j = target then (before source).reverse ++ before target
    else before j

theorem move_spec {k : Nat} (source target : Fin k) (hst : source ≠ target)
    (before : Fin k → List Bool) :
    RunSpec (KS.W04.BinaryStackMoves.moveProgram source target) before
      (moveAfter source target before) ((before source).length + 1) := by
  intro bits hlen
  exact KS.W04.BinaryStackMoves.run_move_stacks source target hst before bits hlen

end KS.W15.RationalMultiply

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_WirePrimitives
attribute [-simp] _root_.OAI.KS.W03.MultiplicationNormalize.output_port
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W20.Wire
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

variable {k : ℕ}

def pushDispatch (port : Fin k) (value : Bool) (_ : Fin 1)
    (_ : Fin k → Fin 3) (_ : Bool) : Instruction k 1 :=
  ⟨none, Vector.ofFn (fun j => if j = port then .push value else .stay)⟩

def push (port : Fin k) (value : Bool) : Program k :=
  ofMachine (compile 0 port port (pushDispatch port value))

theorem push_spec (port : Fin k) (value : Bool) (before : Fin k → List Bool) :
    RunSpec (push port value) before (Function.update before port (value :: before port)) 1 := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin tail =>
    have ht : tail = [] := by apply List.length_eq_zero_iff.mp; simpa using hbits
    subst tail
    rw [Machine.run]
    change (compile (0 : Fin 1) port port (pushDispatch port value)).step
      ⟨some (0 : Fin 1), before⟩ coin = _
    rw [step_compile]
    apply KS.W19.FixedRun.config_ext
    · rfl
    · intro j
      by_cases hj : j = port <;>
        simp [pushDispatch, Instruction.action, KS.W29.StackAction.apply, Function.update, hj]

def halt (port : Fin k) : Program k :=
  ofMachine (compile (0 : Fin 1) port port (fun _ _ _ => Instruction.halt k 1))

theorem halt_spec (port : Fin k) (before : Fin k → List Bool) :
    RunSpec (halt port) before before 1 := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin tail =>
    have ht : tail = [] := by apply List.length_eq_zero_iff.mp; simpa using hbits
    subst tail
    rw [Machine.run]
    change (compile (0 : Fin 1) port port (fun _ _ _ => Instruction.halt k 1)).step
      ⟨some (0 : Fin 1), before⟩ coin = _
    rw [step_compile]
    apply KS.W19.FixedRun.config_ext
    · rfl
    · intro j
      simp [Instruction.halt, Instruction.action, KS.W29.StackAction.apply]

def writeBits (port : Fin k) : List Bool → Program k
  | [] => halt port
  | b :: bs => compose (writeBits port bs) (push port b)

theorem writeBits_spec (port : Fin k) (xs : List Bool) (before : Fin k → List Bool) :
    RunSpec (writeBits port xs) before
      (Function.update before port (xs ++ before port)) (xs.length + 1) := by
  induction xs with
  | nil =>
      simpa only [writeBits, List.nil_append, List.length_nil, Nat.zero_add,
        Function.update_eq_self] using halt_spec port before
  | cons b bs ih =>
      have h := ih.compose (push_spec port b (Function.update before port (bs ++ before port)))
      convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
      · funext j
        by_cases hj : j = port <;> simp [Function.update, hj]

end KS.W20.Wire

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedStackPortLift
attribute [-simp] _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedLoop.dispatch_body _root_.OAI.KS.W29.FixedLoop.dispatch_guard _root_.OAI.KS.W29.FixedLoop.loop_initial _root_.OAI.KS.W29.FixedLoop.loop_input _root_.OAI.KS.W29.FixedLoop.loop_output _root_.OAI.KS.W29.FixedLoop.loop_states _root_.OAI.KS.W29.FixedLoop.loop_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01.FixedStack

def portPreimage {k K : ℕ} (ports : Fin k ↪ Fin K) (j : Fin K) : Option (Fin k) :=
  (List.ofFn (fun i : Fin k => i)).find? (fun i => ports i == j)

@[simp] theorem portPreimage_on_port {k K : ℕ} (ports : Fin k ↪ Fin K) (i : Fin k) :
    portPreimage ports (ports i) = some i := by
  cases he : portPreimage ports (ports i) with
  | none =>
      unfold portPreimage at he
      have hn := List.find?_eq_none.mp he
      have hi : i ∈ List.ofFn (fun i : Fin k => i) := by simp
      have hf := hn i hi
      simp at hf
  | some r =>
      unfold portPreimage at he
      have hr := List.find?_some he
      have hri : ports r = ports i := by simpa using hr
      have h : r = i := ports.injective hri
      subst r
      rfl

@[simp] theorem portPreimage_off_port {k K : ℕ} (ports : Fin k ↪ Fin K) (j : Fin K)
    (hj : ∀ i : Fin k, j ≠ ports i) : portPreimage ports j = none := by
  unfold portPreimage
  apply List.find?_eq_none.mpr
  intro i _
  simpa using (Ne.symm (hj i))

def liftPortsInstruction {k K q : ℕ} (ports : Fin k ↪ Fin K)
    (i : Instruction k q) : Instruction K q :=
  ⟨i.next, Vector.ofFn (fun j => match portPreimage ports j with
    | none => .stay
    | some r => i.action r)⟩

@[simp] theorem liftPortsInstruction_on_port {k K q : ℕ} (ports : Fin k ↪ Fin K)
    (i : Instruction k q) (r : Fin k) :
    (liftPortsInstruction ports i).action (ports r) = i.action r := by
  simp [Instruction.action, liftPortsInstruction]

@[simp] theorem liftPortsInstruction_off_port {k K q : ℕ} (ports : Fin k ↪ Fin K)
    (i : Instruction k q) (j : Fin K) (hj : ∀ r : Fin k, j ≠ ports r) :
    (liftPortsInstruction ports i).action j = .stay := by
  simp [Instruction.action, liftPortsInstruction, portPreimage_off_port ports j hj]

def projectPorts {k K q : ℕ} (ports : Fin k ↪ Fin K) (c : Config K q) : Config k q :=
  ⟨c.state, fun j => c.«stacks» (ports j)⟩

def liftPortsDispatch {K : ℕ} (M : Machine) (ports : Fin M.stackCount ↪ Fin K)
    (s : Fin M.states) (heads : Fin K → Fin 3) (b : Bool) : Instruction K M.states :=
  liftPortsInstruction ports (M.table.getD (tableIndex s (fun j => heads (ports j)) b).val
    (Instruction.halt M.stackCount M.states))

def liftPorts {K : ℕ} (M : Machine) (ports : Fin M.stackCount ↪ Fin K) : Machine :=
  compile M.initial (ports M.inputStack) (ports M.outputStack) (liftPortsDispatch M ports)

theorem liftPorts_step {K : ℕ} (M : Machine) (ports : Fin M.stackCount ↪ Fin K)
    (s : Fin M.states) («stacks» : Fin K → List Bool) (b : Bool) :
    (liftPorts M ports).step ⟨some s, «stacks»⟩ b =
      let c : Config K M.states := ⟨some s, «stacks»⟩
      let i := M.table.getD (tableIndex s (observedHeads (projectPorts ports c)) b).val
        (Instruction.halt M.stackCount M.states)
      Config.mk i.next (fun j => ((liftPortsInstruction ports i).action j).apply («stacks» j)) := by
  unfold liftPorts
  erw [step_compile]
  rfl

theorem liftPorts_project_step {K : ℕ} (M : Machine) (ports : Fin M.stackCount ↪ Fin K)
    (c : Config K M.states) (b : Bool) :
    projectPorts ports ((liftPorts M ports).step c b) = M.step (projectPorts ports c) b := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s =>
      erw [liftPorts_step M ports s «stacks» b]
      change Config.mk _ _ = Config.mk _ _
      congr 1
      funext j
      dsimp only [projectPorts]
      rw [liftPortsInstruction_on_port ports _ j]

theorem liftPorts_step_preserves_other {K : ℕ} (M : Machine)
    (ports : Fin M.stackCount ↪ Fin K) (c : Config K M.states) (b : Bool)
    (j : Fin K) (hj : ∀ r : Fin M.stackCount, j ≠ ports r) :
    ((liftPorts M ports).step c b).«stacks» j = c.«stacks» j := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s =>
      erw [liftPorts_step M ports s «stacks» b]
      change ((liftPortsInstruction ports _).action j).apply («stacks» j) = «stacks» j
      rw [liftPortsInstruction_off_port ports _ j hj]
      rfl

theorem liftPorts_project_run {K : ℕ} (M : Machine) (ports : Fin M.stackCount ↪ Fin K)
    (c : Config K M.states) (bits : List Bool) :
    projectPorts ports ((liftPorts M ports).run c bits) = M.run (projectPorts ports c) bits := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      erw [Machine.run.eq_def, ih]
      erw [liftPorts_project_step M ports c b]
      rfl

theorem liftPorts_run_preserves_other {K : ℕ} (M : Machine)
    (ports : Fin M.stackCount ↪ Fin K) (c : Config K M.states) (bits : List Bool)
    (j : Fin K) (hj : ∀ r : Fin M.stackCount, j ≠ ports r) :
    ((liftPorts M ports).run c bits).«stacks» j = c.«stacks» j := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      erw [Machine.run.eq_def, ih]
      exact liftPorts_step_preserves_other M ports c b j hj

@[simp] theorem liftPorts_project_init {K : ℕ} (M : Machine)
    (ports : Fin M.stackCount ↪ Fin K) (input : List Bool) :
    projectPorts ports ((liftPorts M ports).init input) = M.init input := by
  change Config.mk (some M.initial)
      (fun j => if ports j = ports M.inputStack then input else []) =
    Config.mk (some M.initial) (fun j => if j = M.inputStack then input else [])
  congr 1
  funext j
  simp [ports.injective.eq_iff]

end KS.W01.FixedStack

namespace KS.W29.FixedSequential

def liftPorts {k K : ℕ} (P : Program k) (ports : Fin k ↪ Fin K) : Program K :=
  ofMachine (KS.W01.FixedStack.liftPorts P.toMachine ports)

@[simp] theorem liftPorts_toMachine {k K : ℕ} (P : Program k) (ports : Fin k ↪ Fin K) :
    (liftPorts P ports).toMachine = KS.W01.FixedStack.liftPorts P.toMachine ports :=
  toMachine_ofMachine _

@[simp] theorem liftPorts_input {k K : ℕ} (P : Program k) (ports : Fin k ↪ Fin K) :
    (liftPorts P ports).input = ports P.input := rfl

@[simp] theorem liftPorts_output {k K : ℕ} (P : Program k) (ports : Fin k ↪ Fin K) :
    (liftPorts P ports).output = ports P.output := rfl

end KS.W29.FixedSequential

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedPortRunSpec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01.FixedStack

theorem liftPorts_run_eq {K : ℕ} (M : Machine) (ports : Fin M.stackCount ↪ Fin K)
    (c : Config K M.states) (bits : List Bool) (out : Fin K → List Bool)
    (h : M.run (projectPorts ports c) bits = ⟨none, fun i => out (ports i)⟩)
    (hother : ∀ j, (∀ i, j ≠ ports i) → out j = c.«stacks» j) :
    (liftPorts M ports).run c bits = ⟨none, out⟩ := by
  have hp := liftPorts_project_run M ports c bits
  rw [h] at hp
  have hs : ((liftPorts M ports).run c bits).state = none :=
    congrArg (fun d : Config M.stackCount M.states => d.state) hp
  have ht : ((liftPorts M ports).run c bits).«stacks» = out := by
    funext j
    by_cases hj : ∃ i, j = ports i
    · obtain ⟨i, rfl⟩ := hj
      exact congrArg (fun d : Config M.stackCount M.states => d.«stacks» i) hp
    · have hn : ∀ i, j ≠ ports i := by simpa only [not_exists] using hj
      rw [liftPorts_run_preserves_other M ports c bits j hn, hother j hn]
  exact congrArg₂ Config.mk hs ht

end KS.W01.FixedStack

namespace KS.W01.FixedPortRunSpec
open KS.W01.FixedStack (Config projectPorts)
open KS.W29.FixedSequential (Program)
open KS.W03.MachineCombinators (RunSpec)

theorem lift_runSpec {k K : ℕ} (P : Program k) (ports : Fin k ↪ Fin K)
    (before after : Fin k → List Bool) (largeBefore largeAfter : Fin K → List Bool)
    (ticks : ℕ) (h : RunSpec P before after ticks)
    (hbefore : ∀ i, largeBefore (ports i) = before i)
    (hafter : ∀ i, largeAfter (ports i) = after i)
    (hother : ∀ j, (∀ i, j ≠ ports i) → largeAfter j = largeBefore j) :
    RunSpec (KS.W29.FixedSequential.liftPorts P ports) largeBefore largeAfter ticks := by
  intro bits hbits
  change (KS.W01.FixedStack.liftPorts P.toMachine ports).run
    ⟨some P.initial, largeBefore⟩ bits = ⟨none, largeAfter⟩
  apply KS.W01.FixedStack.liftPorts_run_eq
  · have hi : projectPorts ports (⟨some P.initial, largeBefore⟩ : Config K P.states) =
        ⟨some P.initial, before⟩ := by
      change Config.mk (some P.initial) (fun i => largeBefore (ports i)) =
        Config.mk (some P.initial) before
      exact congrArg (Config.mk (some P.initial)) (funext hbefore)
    erw [hi, h bits hbits]
    congr 1
    funext i
    exact (hafter i).symm
  · exact hother

end KS.W01.FixedPortRunSpec

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_InputHeaderPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W03.InputHeaderPrimitives
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem copy_spec {K : ℕ} (ports : Fin 3 ↪ Fin K) (before : Fin K → List Bool)
    (raw : List Bool) (hs : before (ports 0) = raw)
    (hd : before (ports 1) = []) (hw : before (ports 2) = []) :
    RunSpec (KS.W01.FixedCopy.program ports) before
      (Function.update before (ports 1) raw) (2 * raw.length + 2) := by
  intro bits hbits
  exact KS.W01.FixedCopy.run_copy_restore ports before raw bits hs hd hw hbits

end KS.W03.InputHeaderPrimitives

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_StackTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W12.StackTransfer
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def program {k : ℕ} (source target scratch : Fin k) : Program k :=
  compose (KS.W04.BinaryStackMoves.moveProgram source scratch)
    (KS.W04.BinaryStackMoves.moveProgram scratch target)

def after {k : ℕ} (source target : Fin k) (before : Fin k → List Bool) : Fin k → List Bool :=
  fun j => if j = source then [] else if j = target then before source ++ before target else before j

theorem spec {k : ℕ} (source target scratch : Fin k) (hst : source ≠ target)
    (hs : source ≠ scratch) (ht : target ≠ scratch)
    (before : Fin k → List Bool) (htmp : before scratch = []) :
    RunSpec (program source target scratch) before (after source target before)
      (2 * (before source).length + 2) := by
  have h1 := KS.W15.RationalMultiply.move_spec source scratch hs before
  have h2 := KS.W15.RationalMultiply.move_spec scratch target ht.symm
    (KS.W15.RationalMultiply.moveAfter source scratch before)
  have he : KS.W15.RationalMultiply.moveAfter scratch target
      (KS.W15.RationalMultiply.moveAfter source scratch before) = after source target before := by
    funext j
    by_cases hj : j = source
    · subst j
      simp [KS.W15.RationalMultiply.moveAfter, after, hs, hst]
    · by_cases hk : j = target
      · subst j
        simp [KS.W15.RationalMultiply.moveAfter, after, hs.symm, ht, hst.symm, htmp]
      · by_cases hr : j = scratch
        · subst j
          simp [KS.W15.RationalMultiply.moveAfter, after, hs.symm, ht.symm, htmp]
        · simp [KS.W15.RationalMultiply.moveAfter, after, hj, hk, hr]
  have hlen : (KS.W15.RationalMultiply.moveAfter source scratch before scratch).length =
      (before source).length := by
    simp [KS.W15.RationalMultiply.moveAfter, hs.symm, htmp]
  have htime : ((before source).length + 1) +
      ((KS.W15.RationalMultiply.moveAfter source scratch before scratch).length + 1) =
        2 * (before source).length + 2 := by
    rw [hlen]
    omega
  have hh := h1.compose h2
  rw [he, htime] at hh
  exact hh

end KS.W12.StackTransfer

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_CleanRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.CleanRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

abbrev Word := List Bool

def io {n : ℕ} (w : Word) : Fin (n+1) → Word := fun j => if j.val=0 then w else []

@[simp] lemma io_zero {n : ℕ} (w : Word) : @io n w 0=w := by simp [io]
@[simp] lemma io_ne {n : ℕ} (w : Word) (j : Fin (n+1)) (hj : j.val≠0) : io w j=[] := by simp [io,hj]

structure Routine {α : Type*} (input output : α → Word) (cost : α → ℕ) where
  scratch : ℕ
  program : Program (scratch+1)
  spec : ∀ x,RunSpec program (io (input x)) (io (output x)) (cost x)

def embedding {n m : ℕ} (h : n≤ m) : Fin (n+1) ↪ Fin (m+1) :=
  ⟨Fin.castLE (Nat.add_le_add_right h 1),Fin.castLE_injective _⟩

@[simp] lemma io_embedding {n m : ℕ} (h : n≤ m) (w : Word) (j : Fin (n+1)) :
    io w (embedding h j)=io w j := rfl

lemma io_other {n m : ℕ} (h : n≤ m) (u v : Word) (j : Fin (m+1))
    (hj : ∀ i,j≠embedding h i) : io u j=io v j := by
  have hz : j.val≠0 := by
    intro hz
    exact hj 0 (Fin.ext hz)
  simp [io,hz]

def Routine.pad {α : Type*} {input output : α → Word} {cost : α → ℕ}
    (r : Routine input output cost) (m : ℕ) (hm : r.scratch≤ m) : Routine input output cost where
  scratch := m
  program := liftPorts r.program (embedding hm)
  spec x := KS.W01.FixedPortRunSpec.lift_runSpec r.program (embedding hm)
    _ _ _ _ _ (r.spec x) (io_embedding hm _) (io_embedding hm _) (io_other hm _ _)

def Routine.compose {α : Type*} {first middle last : α → Word} {c d : α → ℕ}
    (r : Routine first middle c) (s : Routine middle last d) :
    Routine first last (fun x => c x+d x) :=
  let r' := r.pad (r.scratch+s.scratch) (Nat.le_add_right _ _)
  let s' := s.pad (r.scratch+s.scratch) (Nat.le_add_left _ _)
  { scratch := r.scratch+s.scratch
    program := KS.W29.FixedSequential.compose r'.program s'.program
    spec := fun x => (r'.spec x).compose (s'.spec x) }

def Routine.reindex {α β : Type*} {input output : α → Word} {cost : α → ℕ}
    (r : Routine input output cost) (f : β → α) :
    Routine (fun x => input (f x)) (fun x => output (f x)) (fun x => cost (f x)) where
  scratch := r.scratch
  program := r.program
  spec x := r.spec (f x)

def transfer {k : ℕ} (source work target : Fin k) : Program k :=
  compose (KS.W04.BinaryStackMoves.moveProgram source work)
    (KS.W04.BinaryStackMoves.moveProgram work target)

lemma transfer_spec {k : ℕ} (source work target : Fin k)
    (hsw : source≠work) (hst : source≠target) (hwt : work≠target)
    (s : Fin k → Word) (hw : s work=[]) (ht : s target=[]) :
    RunSpec (transfer source work target) s
      (Function.update (Function.update s source []) target (s source)) (2*(s source).length+2) := by
  have h₁ := KS.W15.RationalMultiply.move_spec source work hsw s
  have h₂ := KS.W15.RationalMultiply.move_spec work target hwt
    (KS.W15.RationalMultiply.moveAfter source work s)
  have h := h₁.compose h₂
  have he : KS.W15.RationalMultiply.moveAfter work target
      (KS.W15.RationalMultiply.moveAfter source work s) =
      Function.update (Function.update s source []) target (s source) := by
    funext j
    by_cases hjs : j=source
    · subst j
      simp [KS.W15.RationalMultiply.moveAfter,hsw,hst,Function.update]
    · by_cases hjw : j=work
      · subst j
        simp [KS.W15.RationalMultiply.moveAfter,hwt,hw,Function.update]
      · by_cases hjt : j=target
        · subst j
          simp [KS.W15.RationalMultiply.moveAfter,hsw.symm,hst.symm,hwt.symm,
            hw,ht,Function.update]
        · simp [KS.W15.RationalMultiply.moveAfter,hjs,hjw,hjt,Function.update]
  rw [he] at h
  have hc : (s source).length+1+
      (KS.W15.RationalMultiply.moveAfter source work s work).length+1 =
      2*(s source).length+2 := by
    simp [KS.W15.RationalMultiply.moveAfter,hsw.symm,hw]
    omega
  simpa only [Nat.add_assoc] using (hc ▸ h)

end CurrentKS.CleanRoutine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_PairRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.PairRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine

abbrev pair (a b : Word) : Word := KS.W01.frame a++b

def smallState (value saved work : Word) : Fin 3 → Word := ![value,saved,work]
def split : Program 3 := KS.W11.FrameWireCodec.unframeProgram ⟨![0,1,2],by decide⟩
def first : Program 3 := compose split (compose (KS.W04.BinaryStackMoves.clearProgram 0)
  (CleanRoutine.transfer 1 2 0))
def second : Program 3 := compose split (KS.W04.BinaryStackMoves.clearProgram 1)

lemma split_spec (a b : Word) : RunSpec split (io (pair a b)) (smallState b a []) (3*a.length+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec (⟨![0,1,2],by decide⟩ : Fin 3 ↪ Fin 3)
    (fun _ => []) a b
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> simp [io,smallState,KS.W28.FixedPositiveSerializer.registers])

lemma clear_first (a b : Word) :
    RunSpec (KS.W04.BinaryStackMoves.clearProgram (0 : Fin 3)) (smallState b a [])
      (smallState [] a []) (b.length+1) := by
  have h := KS.W15.RationalMultiply.clear_spec (0 : Fin 3) (smallState b a [])
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j;fin_cases j <;> simp [smallState,KS.W15.RationalMultiply.clearAfter]

lemma take_first (a : Word) :
    RunSpec (CleanRoutine.transfer (1 : Fin 3) 2 0) (smallState [] a []) (io a) (2*a.length+2) := by
  have h := CleanRoutine.transfer_spec (1 : Fin 3) 2 0 (by decide) (by decide) (by decide)
    (smallState [] a []) rfl rfl
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j;fin_cases j <;> simp [smallState,io,Function.update]

lemma clear_second (a b : Word) :
    RunSpec (KS.W04.BinaryStackMoves.clearProgram (1 : Fin 3)) (smallState b a [])
      (io b) (a.length+1) := by
  have h := KS.W15.RationalMultiply.clear_spec (1 : Fin 3) (smallState b a [])
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j;fin_cases j <;> simp [smallState,io,KS.W15.RationalMultiply.clearAfter]

def fstRoutine : Routine (fun p : Word×Word => pair p.1 p.2) Prod.fst
    (fun p => 5*p.1.length+p.2.length+5) where
  scratch := 2
  program := first
  spec p := by
    have h := (split_spec p.1 p.2).compose ((clear_first p.1 p.2).compose (take_first p.1))
    convert h using 1 <;> first | rfl | omega

def sndRoutine : Routine (fun p : Word×Word => pair p.1 p.2) Prod.snd
    (fun p => 4*p.1.length+3) where
  scratch := 2
  program := second
  spec p := by
    have h := (split_spec p.1 p.2).compose (clear_second p.1 p.2)
    convert h using 1 <;> first | rfl | omega

abbrev saved (n : ℕ) : Fin (n+4) := ⟨n+1,by omega⟩
abbrev left (n : ℕ) : Fin (n+4) := ⟨n+2,by omega⟩
abbrev work (n : ℕ) : Fin (n+4) := ⟨n+3,by omega⟩
def ports (n : ℕ) : Fin (n+1) ↪ Fin (n+4) := ⟨Fin.castAdd 3,Fin.castAdd_injective _ _⟩
def state (n : ℕ) (value original first : Word) : Fin (n+4) → Word :=
  fun j => if j.val=0 then value else if j.val=n+1 then original else if j.val=n+2 then first else []
def copyPorts (n : ℕ) : Fin 3 ↪ Fin (n+4) :=
  ⟨![0,saved n,work n],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]⟩
def framePorts (n : ℕ) : Fin 3 ↪ Fin (n+4) :=
  ⟨![work n,0,left n],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]⟩

@[simp] lemma copyPorts_apply (n : ℕ) (i : Fin 3) :
    copyPorts n i = ![0,saved n,work n] i := rfl

@[simp] lemma framePorts_apply (n : ℕ) (i : Fin 3) :
    framePorts n i = ![work n,0,left n] i := rfl

lemma projection (n : ℕ) (a b c : Word) (j : Fin (n+1)) :
    state n a b c (ports n j)=io a j := by
  have h₁ : j.val≠n+1 := by omega
  have h₂ : j.val≠n+2 := by omega
  simp [state,ports,io,h₁,h₂]

lemma outside (n : ℕ) (a a' b c : Word) (j : Fin (n+4)) (hj : ∀ i,j≠ports n i) :
    state n a b c j=state n a' b c j := by
  have hz : j.val≠0 := by intro hz;exact hj 0 (Fin.ext hz)
  simp [state,hz]

variable {α : Type*} {input output : α → Word} {cost : α → ℕ}

lemma copy_spec (n : ℕ) (w : Word) :
    RunSpec (KS.W01.FixedCopy.program (copyPorts n)) (io w) (state n w w []) (2*w.length+2) := by
  have h := KS.W03.InputHeaderPrimitives.copy_spec (copyPorts n) (io w) w rfl (by simp [io]) (by simp [io])
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext j
  simp only [copyPorts_apply]
  dsimp [state,io,Function.update]
  simp only [Fin.ext_iff]
  split_ifs <;> simp_all

lemma frame_spec (n : ℕ) (a original : Word) :
    RunSpec (KS.W11.FrameWireCodec.frameProgram (framePorts n)) (state n a original [])
      (state n (KS.W01.frame a) original []) (4*a.length+3) := by
  have h := KS.W11.FrameWireCodec.frame_spec (framePorts n) (state n [] original []) a
  convert h using 1 <;> first | rfl |
    (funext j; simp only [KS.W28.FixedPositiveSerializer.registers,framePorts_apply]
     dsimp [state]
     simp only [Fin.ext_iff,Fin.val_zero]
     split_ifs <;> simp_all)

lemma save_first_spec (n : ℕ) (a original : Word) :
    RunSpec (CleanRoutine.transfer 0 (work n) (left n)) (state n a original [])
      (state n [] original a) (2*a.length+2) := by
  have h := CleanRoutine.transfer_spec (0 : Fin (n+4)) (work n) (left n)
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (state n a original []) (by simp [state]) (by simp [state])
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j
  dsimp [state,Function.update]
  simp only [Fin.ext_iff,Fin.val_zero]
  split_ifs <;> simp_all

lemma restore_spec (n : ℕ) (original first : Word) :
    RunSpec (CleanRoutine.transfer (saved n) (work n) 0) (state n [] original first)
      (state n original [] first) (2*original.length+2) := by
  have h := CleanRoutine.transfer_spec (saved n) (work n) (0 : Fin (n+4))
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (state n [] original first) (by simp [state]) (by simp [state])
  convert h using 1
  · funext j
    dsimp [state,Function.update]
    simp only [Fin.ext_iff,Fin.val_zero]
    split_ifs <;> simp_all
  · simp [state]

lemma prepend_spec (n : ℕ) (a b : Word) :
    RunSpec (KS.W12.StackTransfer.program (left n) 0 (work n)) (state n b [] a)
      (io (a++b)) (2*a.length+2) := by
  have h := KS.W12.StackTransfer.spec (left n) (0 : Fin (n+4)) (work n)
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (state n b [] a) (by simp [state])
  convert h using 1
  · funext j
    dsimp [state,io,KS.W12.StackTransfer.after]
    simp only [Fin.ext_iff,Fin.val_zero]
    split_ifs <;> simp_all
  · simp [state]

variable {outR outS : α → Word} {cR cS : α → ℕ}

def pairingProgram (n : ℕ) (P Q : Program (n+1)) : Program (n+4) :=
  compose (KS.W01.FixedCopy.program (copyPorts n))
    (compose (liftPorts P (ports n))
      (compose (KS.W11.FrameWireCodec.frameProgram (framePorts n))
        (compose (CleanRoutine.transfer 0 (work n) (left n))
          (compose (CleanRoutine.transfer (saved n) (work n) 0)
            (compose (liftPorts Q (ports n))
              (KS.W12.StackTransfer.program (left n) 0 (work n)))))))

def pairingTicks (input outR : α → Word) (cR cS : α → ℕ) (x : α) :=
  (2*(input x).length+2)+cR x+(4*(outR x).length+3)+
    (2*(KS.W01.frame (outR x)).length+2)+(2*(input x).length+2)+cS x+
    (2*(KS.W01.frame (outR x)).length+2)

lemma pairing_spec (n : ℕ) (P Q : Program (n+1)) (w a b : Word) (c d : ℕ)
    (hP : RunSpec P (io w) (io a) c) (hQ : RunSpec Q (io w) (io b) d) :
    RunSpec (pairingProgram n P Q) (io w) (io (pair a b))
      ((2*w.length+2)+c+(4*a.length+3)+(2*(KS.W01.frame a).length+2)+
        (2*w.length+2)+d+(2*(KS.W01.frame a).length+2)) := by
  have hp := KS.W01.FixedPortRunSpec.lift_runSpec P (ports n) _ _
    (state n w w []) (state n a w []) _ hP
    (projection _ _ _ _) (projection _ _ _ _) (outside _ _ _ _ _)
  have hq := KS.W01.FixedPortRunSpec.lift_runSpec Q (ports n) _ _
    (state n w [] (KS.W01.frame a)) (state n b [] (KS.W01.frame a)) _ hQ
    (projection _ _ _ _) (projection _ _ _ _) (outside _ _ _ _ _)
  have h := (copy_spec n w).compose (hp.compose ((frame_spec n a w).compose
    ((save_first_spec n (KS.W01.frame a) w).compose
      ((restore_spec n w (KS.W01.frame a)).compose (hq.compose (prepend_spec n (KS.W01.frame a) b))))))
  simp only [Nat.add_assoc] at h ⊢
  exact h

def pairing (r : Routine input outR cR) (s : Routine input outS cS) :
    Routine input (fun x => pair (outR x) (outS x)) (pairingTicks input outR cR cS) :=
  let n := r.scratch+s.scratch
  let r' := r.pad n (Nat.le_add_right _ _)
  let s' := s.pad n (Nat.le_add_left _ _)
  { scratch := n+3
    program := pairingProgram n r'.program s'.program
    spec := fun x => pairing_spec n r'.program s'.program _ _ _ _ _ (r'.spec x) (s'.spec x) }

end CurrentKS.PairRoutine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_WordOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.WordOperations
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine PairRoutine

def emptyDispatch (_ : Fin 1) (heads : Fin 3 → Fin 3) (_ : Bool) : KS.W01.FixedStack.Instruction 3 1 :=
  ⟨none,Vector.ofFn (fun j => if j=1 then .push (decide (heads 0=0)) else .stay)⟩
def emptyFlag : Program 3 := ofMachine (compile 0 0 1 emptyDispatch)
def emptyProgram : Program 3 := compose emptyFlag (compose (KS.W04.BinaryStackMoves.clearProgram 0)
  (transfer 1 2 0))

lemma emptyFlag_spec (w : Word) : RunSpec emptyFlag (io w) (smallState w [w.isEmpty] []) 1 := by
  intro bits hbits
  obtain ⟨coin,rfl⟩ := List.length_eq_one_iff.mp hbits
  change (compile (0 : Fin 1) 0 1 emptyDispatch).step ⟨some (0 : Fin 1),io w⟩ coin=_
  rw [step_compile]
  apply KS.W19.FixedRun.config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [emptyDispatch,KS.W01.FixedStack.Instruction.action,KS.W29.StackAction.apply,io,smallState,
      observedHeads]
    cases w with
    | nil => rfl
    | cons b bs => cases b <;> rfl

def isEmpty : Routine (fun w : Word => w) (fun w => [w.isEmpty]) (fun w => w.length+6) where
  scratch := 2
  program := emptyProgram
  spec w := by
    have h := (emptyFlag_spec w).compose ((PairRoutine.clear_first [w.isEmpty] w).compose
      (PairRoutine.take_first [w.isEmpty]))
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
    simp
    omega

end CurrentKS.WordOperations

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_ExpressionSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W13.ExpressionMachine
open KS.W17

inductive Op where
  | value : ℚ → Op
  | add | sub | mul | div | neg
  deriving DecidableEq

def Op.encode : Op → List Bool
  | .value q => false :: KS.W01.frame (KS.W01.encodeRat q)
  | .add => [true,false]
  | .sub => [true,true,false]
  | .mul => [true,true,true,false]
  | .div => [true,true,true,true,false]
  | .neg => [true,true,true,true,true]

def encodeOps (ops : List Op) : List Bool := ops.flatMap Op.encode

def encodeStack (s : List ℚ) : List Bool := s.flatMap (fun q => KS.W01.frame (KS.W01.encodeRat q))

@[simp] theorem encodeOps_nil : encodeOps [] = [] := rfl
@[simp] theorem encodeOps_cons (op : Op) (ops : List Op) :
    encodeOps (op::ops) = op.encode ++ encodeOps ops := rfl
@[simp] theorem encodeStack_nil : encodeStack [] = [] := rfl
@[simp] theorem encodeStack_cons (q : ℚ) (qs : List ℚ) :
    encodeStack (q::qs) = KS.W01.frame (KS.W01.encodeRat q) ++ encodeStack qs := rfl

end KS.W13.ExpressionMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FiniteControl
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.FiniteControl
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

abbrev Registers (k : ℕ) := Fin k → List Bool

def guard {k : ℕ} (port : Fin k) (heads : Fin k → Fin 3) (_ : Bool) :
    KS.W29.FixedLoop.GuardInstruction k :=
  ⟨if (heads port).val = 0 then .halt else .call, Vector.ofFn (fun _ => .stay)⟩

def whileNonempty {k : ℕ} (port : Fin k) (body : Program k) : Program k :=
  KS.W29.FixedLoop.loop body (guard port)

lemma step_empty {k : ℕ} (port : Fin k) (body : Program k)
    (s : Registers k) (hs : s port = []) (coin : Bool) :
    (whileNonempty port body).toMachine.step
      ⟨some (whileNonempty port body).initial,s⟩ coin = ⟨none,s⟩ := by
  change (KS.W29.FixedLoop.loop body (guard port)).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState body),s⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  simp [guard, observedHeads, hs, KS.W29.topCode, KS.W29.FixedLoop.guardInstruction,
    KS.W01.FixedStack.Instruction.action, KS.W29.StackAction.apply]
  rfl

lemma step_nonempty {k : ℕ} (port : Fin k) (body : Program k)
    (s : Registers k) (hs : s port ≠ []) (coin : Bool) :
    (whileNonempty port body).toMachine.step
      ⟨some (whileNonempty port body).initial,s⟩ coin =
      KS.W29.FixedLoop.liftBody body ⟨some body.initial,s⟩ := by
  change (KS.W29.FixedLoop.loop body (guard port)).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState body),s⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  cases he : s port with
  | nil => exact (hs he).elim
  | cons b bs =>
    cases b <;> simp [guard, observedHeads, he, KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, KS.W29.FixedLoop.liftBody,
      KS.W01.FixedStack.Instruction.action, KS.W29.StackAction.apply] <;> rfl

inductive Trace {k : ℕ} (port : Fin k) (body : Program k) :
    Registers k → Registers k → ℕ → Prop
  | stop (s : Registers k) (hs : s port = []) : Trace port body s s 1
  | step {s t u : Registers k} {b c : ℕ} (hs : s port ≠ [])
      (hbody : RunSpec body s t b) (htail : Trace port body t u c) :
      Trace port body s u (b+c+1)

theorem run_trace {k : ℕ} {port : Fin k} {body : Program k}
    {s t : Registers k} {ticks : ℕ} (h : Trace port body s t ticks)
    (bits : List Bool) (hlen : ticks ≤ bits.length) :
    (whileNonempty port body).toMachine.run
      ⟨some (whileNonempty port body).initial,s⟩ bits = ⟨none,t⟩ := by
  induction h generalizing bits with
  | stop s hs =>
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      rw [KS.W01.FixedStack.Machine.run,step_empty port body s hs,KS.W01.FixedStack.Machine.run_halted _ _ rfl]
  | @step s t u b c hs hb ht ih =>
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      have hr : b+c ≤ rest.length := by simp only [List.length_cons] at hlen; omega
      obtain ⟨remaining,hlen',hreturn⟩ := hb.loop_body_then (guard port) rest (by omega)
      rw [KS.W01.FixedStack.Machine.run,step_nonempty port body s hs]
      change (KS.W29.FixedLoop.loop body (guard port)).toMachine.run
        (KS.W29.FixedLoop.liftBody body ⟨some body.initial,s⟩) rest = _
      rw [hreturn]
      exact ih remaining (by omega)

theorem trace_spec {k : ℕ} {port : Fin k} {body : Program k}
    {s t : Registers k} {ticks : ℕ} (h : Trace port body s t ticks) :
    RunSpec (whileNonempty port body) s t ticks := by
  intro bits hlen
  exact run_trace h bits hlen.ge

end CurrentKS.FiniteControl

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedBranch
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W29.FixedLoop.dispatch_body _root_.OAI.KS.W29.FixedLoop.dispatch_guard _root_.OAI.KS.W29.FixedLoop.loop_initial _root_.OAI.KS.W29.FixedLoop.loop_input _root_.OAI.KS.W29.FixedLoop.loop_output _root_.OAI.KS.W29.FixedLoop.loop_states _root_.OAI.KS.W29.FixedLoop.loop_toMachine _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W29.FixedBranch
open KS.W29.FixedSequential (Program ofMachine fetch )
open KS.W01.FixedStack (Config Instruction observedHeads)

inductive Choice where
  | halt
  | left
  | right
  deriving DecidableEq

structure SelectInstruction (k : Nat) where
  choice : Choice
  actions : Vector KS.W29.StackAction k

def start {k : Nat} (P Q : Program k) : Fin (P.states + Q.states + 1) := ⟨0, by omega⟩

def leftState {k : Nat} (P Q : Program k) (s : Fin P.states) :
    Fin (P.states + Q.states + 1) := ⟨s.val + 1, by have h := s.isLt; omega⟩

def rightState {k : Nat} (P Q : Program k) (s : Fin Q.states) :
    Fin (P.states + Q.states + 1) := ⟨P.states + s.val + 1, by have h := s.isLt; omega⟩

def selectInstruction {k : Nat} (P Q : Program k) (i : SelectInstruction k) :
    KS.W01.FixedStack.Instruction k (P.states + Q.states + 1) :=
  ⟨match i.choice with
    | .halt => none
    | .left => some (leftState P Q P.initial)
    | .right => some (rightState P Q Q.initial), i.actions⟩

def leftInstruction {k : Nat} (P Q : Program k) (i : KS.W01.FixedStack.Instruction k P.states) :
    KS.W01.FixedStack.Instruction k (P.states + Q.states + 1) := ⟨i.next.map (leftState P Q), i.actions⟩

def rightInstruction {k : Nat} (P Q : Program k) (i : KS.W01.FixedStack.Instruction k Q.states) :
    KS.W01.FixedStack.Instruction k (P.states + Q.states + 1) := ⟨i.next.map (rightState P Q), i.actions⟩

def dispatch {k : Nat} (P Q : Program k)
    (select : (Fin k → Fin 3) → Bool → SelectInstruction k)
    (s : Fin (P.states + Q.states + 1)) (heads : Fin k → Fin 3) (b : Bool) :
    KS.W01.FixedStack.Instruction k (P.states + Q.states + 1) :=
  if h₀ : s.val = 0 then selectInstruction P Q (select heads b)
  else if h₁ : s.val < P.states + 1 then
    leftInstruction P Q (fetch P ⟨s.val - 1, by omega⟩ heads b)
  else
    rightInstruction P Q
      (fetch Q ⟨s.val - (P.states + 1), by have hs := s.isLt; omega⟩ heads b)

def branch {k : Nat} (P Q : Program k) (output : Fin k)
    (select : (Fin k → Fin 3) → Bool → SelectInstruction k) : Program k :=
  ofMachine (KS.W01.FixedStack.compile (start P Q) P.input output (dispatch P Q select))

@[simp] theorem branch_toMachine {k : Nat} (P Q : Program k) (output) (select) :
    (branch P Q output select).toMachine =
      KS.W01.FixedStack.compile (start P Q) P.input output (dispatch P Q select) :=
  KS.W29.FixedSequential.toMachine_ofMachine _

@[simp] theorem branch_initial {k : Nat} (P Q : Program k) (output) (select) :
    (branch P Q output select).initial = start P Q := rfl

@[simp] theorem branch_states {k : Nat} (P Q : Program k) (output) (select) :
    (branch P Q output select).states = P.states + Q.states + 1 := rfl

@[simp] theorem dispatch_start {k : Nat} (P Q : Program k) (select) (heads) (b) :
    dispatch P Q select (start P Q) heads b = selectInstruction P Q (select heads b) := by
  simp [dispatch, start]

@[simp] theorem dispatch_left {k : Nat} (P Q : Program k) (select)
    (s : Fin P.states) (heads) (b) :
    dispatch P Q select (leftState P Q s) heads b = leftInstruction P Q (fetch P s heads b) := by
  have hs : s.val + 1 < P.states + 1 := by have h := s.isLt; omega
  simp [dispatch, leftState, hs]

@[simp] theorem dispatch_right {k : Nat} (P Q : Program k) (select)
    (s : Fin Q.states) (heads) (b) :
    dispatch P Q select (rightState P Q s) heads b = rightInstruction P Q (fetch Q s heads b) := by
  have hs : ¬ P.states + s.val + 1 < P.states + 1 := by omega
  have he : P.states + s.val + 1 - (P.states + 1) = s.val := by omega
  simp [dispatch, rightState, hs, he]

def liftLeft {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k P.states) :
    KS.W01.FixedStack.Config k (P.states + Q.states + 1) := ⟨c.state.map (leftState P Q), c.«stacks»⟩

def liftRight {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k Q.states) :
    KS.W01.FixedStack.Config k (P.states + Q.states + 1) := ⟨c.state.map (rightState P Q), c.«stacks»⟩

theorem step_start {k : Nat} (P Q : Program k) (output) (select)
    («stacks» : Fin k → List Bool) (b : Bool) :
    (branch P Q output select).toMachine.step ⟨some (start P Q), «stacks»⟩ b =
      let i := selectInstruction P Q (select (observedHeads (KS.W01.FixedStack.Config.mk (some (start P Q)) «stacks»)) b)
      KS.W01.FixedStack.Config.mk i.next (fun j => (i.action j).apply («stacks» j)) := by
  change (KS.W01.FixedStack.compile (start P Q) P.input output
    (dispatch P Q select)).step _ _ = _
  erw [KS.W01.FixedStack.step_compile]
  dsimp only
  rw [dispatch_start]

theorem step_left {k : Nat} (P Q : Program k) (output) (select)
    (s : Fin P.states) («stacks» : Fin k → List Bool) (b : Bool) :
    (branch P Q output select).toMachine.step ⟨some (leftState P Q s), «stacks»⟩ b =
      liftLeft P Q (P.toMachine.step ⟨some s, «stacks»⟩ b) := by
  change (KS.W01.FixedStack.compile (start P Q) P.input output
    (dispatch P Q select)).step _ _ = _
  erw [KS.W01.FixedStack.step_compile]
  dsimp only
  rw [dispatch_left]
  rfl

theorem step_right {k : Nat} (P Q : Program k) (output) (select)
    (s : Fin Q.states) («stacks» : Fin k → List Bool) (b : Bool) :
    (branch P Q output select).toMachine.step ⟨some (rightState P Q s), «stacks»⟩ b =
      liftRight P Q (Q.toMachine.step ⟨some s, «stacks»⟩ b) := by
  change (KS.W01.FixedStack.compile (start P Q) P.input output
    (dispatch P Q select)).step _ _ = _
  erw [KS.W01.FixedStack.step_compile]
  dsimp only
  rw [dispatch_right]
  rfl

theorem step_liftLeft {k : Nat} (P Q : Program k) (output) (select)
    (c : KS.W01.FixedStack.Config k P.states) (b : Bool) :
    (branch P Q output select).toMachine.step (liftLeft P Q c) b =
      liftLeft P Q (P.toMachine.step c b) := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s => exact step_left P Q output select s «stacks» b

theorem step_liftRight {k : Nat} (P Q : Program k) (output) (select)
    (c : KS.W01.FixedStack.Config k Q.states) (b : Bool) :
    (branch P Q output select).toMachine.step (liftRight P Q c) b =
      liftRight P Q (Q.toMachine.step c b) := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s => exact step_right P Q output select s «stacks» b

theorem run_left {k : Nat} (P Q : Program k) (output) (select)
    (c : KS.W01.FixedStack.Config k P.states) (bits : List Bool) :
    (branch P Q output select).toMachine.run (liftLeft P Q c) bits =
      liftLeft P Q (P.toMachine.run c bits) := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      change (branch P Q output select).toMachine.run
        ((branch P Q output select).toMachine.step (liftLeft P Q c) b) bs =
        liftLeft P Q (P.toMachine.run (P.toMachine.step c b) bs)
      erw [step_liftLeft P Q output select c b]
      exact ih (P.toMachine.step c b)

theorem run_right {k : Nat} (P Q : Program k) (output) (select)
    (c : KS.W01.FixedStack.Config k Q.states) (bits : List Bool) :
    (branch P Q output select).toMachine.run (liftRight P Q c) bits =
      liftRight P Q (Q.toMachine.run c bits) := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      change (branch P Q output select).toMachine.run
        ((branch P Q output select).toMachine.step (liftRight P Q c) b) bs =
        liftRight P Q (Q.toMachine.run (Q.toMachine.step c b) bs)
      erw [step_liftRight P Q output select c b]
      exact ih (Q.toMachine.step c b)

end KS.W29.FixedBranch

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_LiteralProgram
attribute [-simp] _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W23.LiteralProgram
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def pop {k : ℕ} (port : Fin k) : Program k :=
  ofMachine (compile (0 : Fin 1) port port (fun _ _ _ =>
    ⟨none, Vector.ofFn (fun j => if j = port then .pop else .stay)⟩))

theorem pop_spec {k : ℕ} (port : Fin k) (s : Fin k → List Bool) :
    RunSpec (pop port) s (Function.update s port (s port).tail) 1 := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin rest =>
      have hr : rest = [] := List.length_eq_zero_iff.mp (by simpa using hbits)
      subst rest
      change (compile (0 : Fin 1) port port (fun _ _ _ =>
        ⟨none, Vector.ofFn (fun j => if j = port then .pop else .stay)⟩)).step
          ⟨some (0 : Fin 1), s⟩ coin = _
      rw [step_compile]
      apply congrArg (Config.mk none)
      funext j
      by_cases hj : j = port <;>
        simp [Function.update, Instruction.action, KS.W29.StackAction.apply, hj]

end KS.W23.LiteralProgram

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PSDSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open Matrix

def psdCutEval {n : ℕ} (q : Fin n → ℚ) (M : Matrix (Fin n) (Fin n) ℚ) : ℚ :=
  -(q ⬝ᵥ (M *ᵥ q))

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RealDecode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.HermitianCoordinates
open Matrix
open scoped BigOperators

variable {d : ℕ}

def realDecode {R : Type*} [Ring R] (x : Fin d × Fin d → R) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) R :=
  let re := fun i j => x (min i j,max i j)
  let im := fun i j => if i < j then x (j,i) else if j < i then -x (i,j) else 0
  Matrix.fromBlocks re (-im) im re

lemma realDecode_inl_inl {R : Type*} [Ring R]
    (x : Fin d × Fin d → R) (i j : Fin d) :
    realDecode x (Sum.inl i) (Sum.inl j) = x (min i j, max i j) := rfl

lemma realDecode_inl_inr {R : Type*} [Ring R]
    (x : Fin d × Fin d → R) (i j : Fin d) :
    realDecode x (Sum.inl i) (Sum.inr j) =
      -(if i < j then x (j, i) else if j < i then -x (i, j) else 0) := rfl

lemma realDecode_inr_inl {R : Type*} [Ring R]
    (x : Fin d × Fin d → R) (i j : Fin d) :
    realDecode x (Sum.inr i) (Sum.inl j) =
      (if i < j then x (j, i) else if j < i then -x (i, j) else 0) := rfl

lemma realDecode_inr_inr {R : Type*} [Ring R]
    (x : Fin d × Fin d → R) (i j : Fin d) :
    realDecode x (Sum.inr i) (Sum.inr j) = x (min i j, max i j) := rfl

lemma realDecode_isSymm {R : Type*} [Ring R] (x : Fin d × Fin d → R) :
    (realDecode x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [realDecode_inl_inl,min_comm,max_comm]
    | inr j =>
      rcases lt_trichotomy i j with h | h | h
      · simp [realDecode_inl_inr, realDecode_inr_inl,h,not_lt.mpr h.le]
      · subst j; simp [realDecode_inl_inr, realDecode_inr_inl]
      · simp [realDecode_inl_inr, realDecode_inr_inl,h,not_lt.mpr h.le]
  | inr i =>
    cases j with
    | inl j =>
      rcases lt_trichotomy i j with h | h | h
      · simp [realDecode_inl_inr, realDecode_inr_inl,h,not_lt.mpr h.le]
      · subst j; simp [realDecode_inl_inr, realDecode_inr_inl]
      · simp [realDecode_inl_inr, realDecode_inr_inl,h,not_lt.mpr h.le]
    | inr j => simp [realDecode_inr_inr,min_comm,max_comm]

lemma realDecode_add {R : Type*} [Ring R] (x y : Fin d × Fin d → R) :
    realDecode (x+y)=realDecode x+realDecode y := by
  ext i j
  cases i <;> cases j <;> simp [realDecode_inl_inl, realDecode_inl_inr, realDecode_inr_inl, realDecode_inr_inr] <;> split_ifs <;> abel

lemma realDecode_smul {R : Type*} [CommRing R] (r : R) (x : Fin d × Fin d → R) :
    realDecode (r • x)=r • realDecode x := by
  ext i j
  cases i <;> cases j <;> simp [realDecode_inl_inl, realDecode_inl_inr, realDecode_inr_inl, realDecode_inr_inr]

end CurrentKS.HermitianCoordinates

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_UniformElimination
attribute [-simp] _root_.OAI.KS.W17.schurEntryExpr_eval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

@[simp] theorem schurTail_zero_pivot {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (h : M 0 0 = 0) :
    schurTail M = trailingMatrix M := by
  funext i j
  simp [schurTail, trailingMatrix, h]

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS

/-- The two binary fields are a numerator and a positive denominator. -/
structure RationalEntry where
  numerator : ℤ
  denominator : ℕ
  denominator_pos : 0 < denominator

def RationalEntry.value (a : RationalEntry) : ℚ :=
  (a.numerator : ℚ) / (a.denominator : ℚ)

abbrev RationalComplex := RationalEntry × RationalEntry

structure Input where
  d : ℕ
  N : ℕ
  entries : Fin N → Matrix (Fin d) (Fin d) RationalComplex

end CurrentKS

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Pencil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix
open scoped BigOperators

structure Pencil (n m : ℕ) where
  constant : Matrix (Fin m) (Fin m) ℚ
  coeff : Fin n → Matrix (Fin m) (Fin m) ℚ
  symmetric_constant : constant.IsSymm
  symmetric_coeff : ∀ i, (coeff i).IsSymm

variable {n m : ℕ}

def Pencil.eval (B : Pencil n m) (y : Fin n → ℚ) : Matrix (Fin m) (Fin m) ℚ :=
  B.constant + ∑ i, y i • B.coeff i

def Pencil.witness (B : Pencil n m) (y : Fin n → ℚ) : Option (Fin m → ℚ) :=
  KS.W17.rationalNegativeWitness m (B.eval y)

def Pencil.normal (B : Pencil n m) (v : Fin m → ℚ) : Fin n → ℚ :=
  fun i => KS.W17.psdCutEval v (B.coeff i)

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Affine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix
open scoped BigOperators

variable {n m p : ℕ}

def Pencil.ofAffine (C : Matrix (Fin m) (Fin m) ℚ)
    (L : (Fin n → ℚ) →ₗ[ℚ] Matrix (Fin m) (Fin m) ℚ)
    (hC : C.IsSymm) (hL : ∀ y,(L y).IsSymm) : Pencil n m where
  constant := C
  coeff i := L (Pi.single i 1)
  symmetric_constant := hC
  symmetric_coeff index := hL (Pi.single index 1)

def blockDiagonal {R : Type*} [Zero R] (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin p) (Fin p) R) : Matrix (Fin (m+p)) (Fin (m+p)) R :=
  (Matrix.fromBlocks A 0 0 B).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

lemma blockDiagonal_symm {R : Type*} [AddMonoid R] (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin p) (Fin p) R) (hA : A.IsSymm) (hB : B.IsSymm) :
    (blockDiagonal A B).IsSymm :=
  (Matrix.IsSymm.fromBlocks hA (by simp) hB).submatrix _

def Pencil.blockDiagonal (A : Pencil n m) (B : Pencil n p) : Pencil n (m+p) where
  constant := CurrentKS.RationalSDP.blockDiagonal A.constant B.constant
  coeff i := CurrentKS.RationalSDP.blockDiagonal (A.coeff i) (B.coeff i)
  symmetric_constant := blockDiagonal_symm _ _ A.symmetric_constant B.symmetric_constant
  symmetric_coeff i := blockDiagonal_symm _ _ (A.symmetric_coeff i) (B.symmetric_coeff i)

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_BlockScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix
open scoped BigOperators

variable {n m : ℕ}

def blockScalar {R : Type*} [Zero R] (A : Matrix (Fin m) (Fin m) R) (b : R) :
    Matrix (Fin (m+1)) (Fin (m+1)) R :=
  (Matrix.fromBlocks A 0 0 (Matrix.of fun (_ _ : Fin 1) => b)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

lemma blockScalar_symm (A : Matrix (Fin m) (Fin m) ℚ) (hA : A.IsSymm) (b : ℚ) :
    (blockScalar A b).IsSymm := by
  exact (Matrix.IsSymm.fromBlocks hA (by simp) (by rfl)).submatrix _

def Pencil.withLevel (B : Pencil n m) (f : Fin n → ℚ) (q : ℚ) : Pencil n (m+1) where
  constant := blockScalar B.constant q
  coeff i := blockScalar (B.coeff i) (-f i)
  symmetric_constant := blockScalar_symm _ B.symmetric_constant _
  symmetric_coeff i := blockScalar_symm _ (B.symmetric_coeff i) _

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalInput
open scoped BigOperators ComplexOrder
open CurrentKS.HermitianCoordinates

def coordinates (x : Input) (i : Fin x.N) : Fin x.d × Fin x.d → ℚ := fun p =>
  if p.1 ≤ p.2 then (x.entries i p.1 p.2).1.value else (x.entries i p.2 p.1).2.value

def trace (x : Input) (i : Fin x.N) : ℚ := ∑ j,(x.entries i j j).1.value

def orientation (x : Input) (i : Fin x.N) : ℚ := if 0 ≤ trace x i then 1 else -1

def scale (x : Input) : ℚ := ∑ i,|trace x i|

def indices (x : Input) : List (Fin x.N) :=
  (List.finRange x.N).filter (fun i => decide (trace x i ≠ 0))

def index (x : Input) : Fin (indices x).length → Fin x.N := (indices x).get

def normalizedCoordinates (x : Input) (j : Fin (indices x).length) : Fin x.d × Fin x.d → ℚ :=
  (scale x)⁻¹ • (orientation x (index x j) • coordinates x (index x j))

end CurrentKS.RationalInput

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_SquareInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot

def squareInterval (q : ℚ) : ℕ → ℚ × ℚ
  | 0 => (0,1)
  | k+1 =>
    let s := squareInterval q k
    let m := (s.1+s.2)/2
    if m^2 ≤ q then (m,s.2) else (s.1,m)

def upperSqrt (q δ : ℚ) : ℚ := (squareInterval q δ.den.size).2

end CurrentKS.RationalRoot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_SqSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot
open scoped BigOperators

variable {N : ℕ}

def sqSum (v : Fin N → ℚ) : ℚ := ∑ i,(v i)^2

def initialScale (v : Fin N → ℚ) : Fin N → ℚ := fun i => v i/(1+sqSum v)

def normalize (v : Fin N → ℚ) (β : ℚ) : Fin N → ℚ :=
  let u := initialScale v
  fun i => u i/upperSqrt (sqSum u) (β*sqSum u)

end CurrentKS.RationalRoot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_NegativeDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot

section
open Matrix
open scoped BigOperators

variable {N : ℕ}

def negativeDirection (M : Matrix (Fin N) (Fin N) ℚ) (β : ℚ) : Option (Fin N → ℚ) :=
  (KS.W17.rationalNegativeWitness N M).map (fun v => normalize v β)

end

open scoped BigOperators

variable {N : ℕ}

def nearest (t : ℚ) : ℤ :=
  if 0 ≤ t then ⌈t-1/2⌉ else -⌈-t-1/2⌉

def roundMesh (ρ : ℚ) (v : Fin N → ℚ) : Fin N → ℚ :=
  fun i => ρ*(nearest (v i/ρ):ℚ)

end CurrentKS.RationalRoot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ShiftedHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot
open Matrix
open scoped BigOperators

variable {N : ℕ}

def shiftedHessian (H : Matrix (Fin N) (Fin N) ℚ) (a : ℚ) : Matrix (Fin N) (Fin N) ℚ :=
  H+(7*a) • 1

def computedCurvature (H : Matrix (Fin N) (Fin N) ℚ) (a M s ρ : ℚ) : Option (Fin N → ℚ) :=
  (negativeDirection (shiftedHessian H a) (a/(4096*M))).map
    (fun w => roundMesh ρ (fun i => s*(1-a/(1024*M))*w i))

end CurrentKS.RationalRoot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Select
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Descent
variable {α : Type*}

def select (score : α → ℚ) (a : α) : List α → α
  | [] => a
  | b :: bs => select score (if score b < score a then b else a) bs

def run (step : α → Option α) : ℕ → α → α
  | 0,x => x
  | k+1,x => match step x with
    | none => x
    | some y => run step k y

end CurrentKS.Descent

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ChooseCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference

section
open scoped BigOperators

def chooseCoordinate {N : ℕ} [NeZero N] (g : Fin N → ℚ) : Fin N :=
  CurrentKS.Descent.select (fun i => -|g i|) 0 (List.finRange N)

end

open Set
open scoped ContDiff

variable {N : ℕ}

def rationalGradientDirection [NeZero N] (g : Fin N → ℚ) : Fin N → ℚ :=
  (if 0 ≤ g (chooseCoordinate g) then (-1:ℚ) else 1) • (Pi.single (chooseCoordinate g) 1 : Fin N → ℚ)

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_RationalBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference
open Set Matrix
open scoped BigOperators ContDiff

variable {N : ℕ}

def rationalBasis (i : Fin N) : Fin N → ℚ := Pi.single i 1

def stencilValue (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (h : ℚ)
    (v : Fin N → ℚ) : ℚ := query (x+h • v)

def stencilGradient (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (h : ℚ) (i : Fin N) : ℚ :=
  (stencilValue query x h (rationalBasis i)-stencilValue query x h (-rationalBasis i))/(2*h)

def stencilHessian (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (h : ℚ) : Matrix (Fin N) (Fin N) ℚ :=
  fun i j => if i=j then
    (stencilValue query x h (rationalBasis i)-2*query x+stencilValue query x h (-rationalBasis i))/h^2
  else
    (stencilValue query x h (rationalBasis i+rationalBasis j)-
     stencilValue query x h (rationalBasis i-rationalBasis j)-
     stencilValue query x h (-rationalBasis i+rationalBasis j)+
     stencilValue query x h (-rationalBasis i-rationalBasis j))/(4*h^2)

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_EuclideanForget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference
open scoped ContDiff

variable {N : ℕ}

open CurrentKS.RationalRoot Matrix Set

def interiorCandidates [NeZero N] (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ)
    (h a M s ρ : ℚ) : List (Fin N → ℚ) :=
  let g := stencilGradient query x h
  let H := stencilHessian query x h
  (x+s • rationalGradientDirection g) ::
    match computedCurvature H a M s ρ with
    | none => []
    | some q => [x+q,x-q]

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_EndpointCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference
open CurrentKS.RationalRoot

variable {N : ℕ}

def endpointCandidates (x : Fin N → ℚ) : List (Fin N → ℚ) :=
  (List.finRange N).flatMap fun i => [Function.update x i (-1),Function.update x i 1]

def allCandidates [NeZero N] (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ)
    (h a M s ρ : ℚ) : List (Fin N → ℚ) :=
  endpointCandidates x++interiorCandidates query x h a M s ρ

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_MovementBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Schedule

def movementBudget (n : ℕ) (ε : ℚ) : ℚ :=
  let s₀ := ε/40000
  let J := 1+(3*(n:ℚ))^2/s₀
  let E₀ := 2*J^2*(1+3*(n:ℚ))^2
  max 1 (max (48*E₀/23) (4*(1+9*(n:ℚ)^2)))

def threshold (n : ℕ) (ε lam : ℚ) : ℚ := lam/(512*(movementBudget n ε)^2)

def stepSize (a M σ : ℚ) : ℚ := min (σ/4) (min (a/(4*M)) (1/4))
def stencilSize (n : ℕ) (a M σ : ℚ) : ℚ := min (σ/8) (min 1 (a/(64*M*n)))
def meshSize (n : ℕ) (a M s : ℚ) : ℚ := s*a/(4096*M*n)

def coarseBudgetQ (d n : ℕ) (ε σ : ℚ) : ℚ :=
  200+((d:ℚ)+1)+|ε|+(200/ε)*((d:ℚ)+1)+200*((d:ℚ)+1)+
    (((d:ℚ)+1)+n)+384*n*(1+800/σ^3)

def valueCurve2Q (d n : ℕ) (ε σ : ℚ) : ℚ :=
  let B := coarseBudgetQ d n ε σ
  let Jb := 10^18*((d:ℚ)+1)*(1+ε⁻¹)^4
  let D := 300*B^5
  (1+|ε| *(2*((d:ℚ)+1)))*(Jb*D*(1+Jb*D)^2)

def valueCurve3Q (d n : ℕ) (ε σ : ℚ) : ℚ :=
  let B := coarseBudgetQ d n ε σ
  let Jb := 10^18*((d:ℚ)+1)*(1+ε⁻¹)^4
  let D := 300*B^5
  (1+|ε| *(2*((d:ℚ)+1)))*
    (Jb*D*((1+Jb*D)^3+3*(1+Jb*D)*(Jb*D*(1+Jb*D)^2)))

def curveBudget (d n : ℕ) (ε σ lam : ℚ) : ℚ :=
  1+valueCurve2Q d n ε σ+valueCurve3Q d n ε σ+|lam| *(n:ℚ)*(1+800/σ^3)

end CurrentKS.Schedule

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Lookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
variable {N n : ℕ}

def lookup (e : Fin n → Fin N) (i : Fin N) : Option (Fin n) :=
  (List.finRange n).find? (fun j => e j == i)

def extend {β : Type*} (e : Fin n → Fin N) (base : Fin N → β) (y : Fin n → β) : Fin N → β :=
  fun i => (lookup e i).elim (base i) y

def activeIndices (x : Fin N → ℚ) : List (Fin N) :=
  (List.finRange N).filter (fun i => decide (|x i|<1))

def activeIndex (x : Fin N → ℚ) : Fin (activeIndices x).length → Fin N :=
  (activeIndices x).get

end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_RealVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

def l1 (a : Fin n → ℚ) : ℚ := ∑ i, |a i|

def roundScalar (ρ x : ℚ) : ℚ := ρ * ⌊x/ρ⌋

def roundVector (ρ : ℚ) (y : Fin n → ℚ) : Fin n → ℚ := fun i => roundScalar ρ (y i)

def Pencil.next (B : Pencil n m) (step mesh : ℚ) (y : Fin n → ℚ) : Fin n → ℚ :=
  match B.witness y with
  | none => y
  | some v => roundVector mesh (fun i => y i-step*B.normal v i/l1 (B.normal v))

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_SearchStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

def searchStep (n : ℕ) (r : ℚ) : ℚ := r/(n+1)
def searchMesh (n : ℕ) (r R : ℚ) : ℚ :=
  (searchStep n r)^2/(16*(n+1)*(R+searchStep n r+1))
def searchFuel (n : ℕ) (r R : ℚ) : ℕ :=
  ⌈4*R^2/(searchStep n r)^2⌉₊+1

def Pencil.search (B : Pencil n m) (r R : ℚ) (y : Fin n → ℚ) : Fin n → ℚ :=
  (B.next (searchStep n r) (searchMesh n r R))^[searchFuel n r R] y

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Level
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

def level (δ U : ℚ) (k : ℕ) : ℚ := -U+k*δ

def Pencil.levelCandidate (B : Pencil n m) (f : Fin n → ℚ) (δ r R U : ℚ) (k : ℕ) :
    Fin n → ℚ := (B.withLevel f (level δ U k)).search r R 0

def Pencil.optimize (B : Pencil n m) (f : Fin n → ℚ) (δ r R U : ℚ) : ℕ → Fin n → ℚ
  | 0 => B.levelCandidate f δ r R U 0
  | k+1 =>
      let y := B.optimize f δ r R U k
      if (B.withLevel f (level δ U k)).witness y = none then y
      else B.levelCandidate f δ r R U (k+1)

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ObjectiveCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

def nearRadius (δ L R r : ℚ) : ℚ := δ/(L*(2*R+r))*r

def optimizeFuel (δ U : ℚ) : ℕ := ⌈2*U/δ⌉₊+3

end
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ValueDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates
open scoped BigOperators

variable {d N n m p : ℕ}

def valueDimension (d : ℕ) := 1+(d*d+d*d)

def valueIndex (d : ℕ) :
    Fin 1 ⊕ ((Fin d × Fin d) ⊕ (Fin d × Fin d)) ≃ Fin (valueDimension d) :=
  ((Equiv.refl (Fin 1)).sumCongr (finProdFinEquiv.sumCongr finProdFinEquiv)).trans
    (((Equiv.refl (Fin 1)).sumCongr finSumFinEquiv).trans finSumFinEquiv)

def timeCoordinate {R : Type*} [Semiring R] (d : ℕ) :
    (Fin (valueDimension d) → R) →ₗ[R] R := LinearMap.proj (valueIndex d (.inl 0))

def matrixCoordinate {R : Type*} [Semiring R] (d : ℕ) (second : Bool) :
    (Fin (valueDimension d) → R) →ₗ[R] (Fin d × Fin d → R) :=
  LinearMap.pi fun ij => LinearMap.proj (valueIndex d
    (.inr (if second then .inr ij else .inl ij)))

def realFinDecode {R : Type*} [CommRing R] (d : ℕ) :
    (Fin d × Fin d → R) →ₗ[R] Matrix (Fin (d+d)) (Fin (d+d)) R where
  toFun x := (realDecode x).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  map_add' x y := by simp only [realDecode_add,Matrix.submatrix_add,Pi.add_apply]
  map_smul' r x := by simp only [realDecode_smul,Matrix.submatrix_smul,Pi.smul_apply,RingHom.id_apply]

lemma realFinDecode_symm {R : Type*} [CommRing R] (x : Fin d × Fin d → R) :
    (realFinDecode d x).IsSymm := (realDecode_isSymm x).submatrix _

def matrixVariable {R : Type*} [CommRing R] (d : ℕ) (second : Bool) :
    (Fin (valueDimension d) → R) →ₗ[R] Matrix (Fin (d+d)) (Fin (d+d)) R :=
  (realFinDecode d).comp (matrixCoordinate d second)

lemma matrixVariable_symm {R : Type*} [CommRing R] (second : Bool)
    (v : Fin (valueDimension d) → R) : (matrixVariable d second v).IsSymm :=
  realFinDecode_symm _

variable {R : Type*} [CommRing R]

def sandwichLinear (A : Matrix (Fin m) (Fin m) R) :
    Matrix (Fin m) (Fin m) R →ₗ[R] Matrix (Fin m) (Fin m) R where
  toFun Z := A*Z*A
  map_add' Z W := by simp only [mul_add,add_mul]
  map_smul' r Z := by simp only [Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply]

lemma sandwichLinear_symm (A Z : Matrix (Fin m) (Fin m) R)
    (hA : A.IsSymm) (hZ : Z.IsSymm) : (sandwichLinear A Z).IsSymm := by
  change (A*Z*A).transpose=A*Z*A
  rw [Matrix.transpose_mul,Matrix.transpose_mul,hA,hZ,Matrix.mul_assoc]

def rationalSum (coords : Fin N → Fin d × Fin d → R) (x : Fin N → R) :
    Matrix (Fin (d+d)) (Fin (d+d)) R := ∑ i,x i • realFinDecode d (coords i)

lemma rationalSum_symm (coords : Fin N → Fin d × Fin d → R) (x : Fin N → R) :
    (rationalSum coords x).IsSymm := by
  change (∑ i,x i • realFinDecode d (coords i)).transpose= _
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (realFinDecode_symm _).smul _

def rationalEta (coords : Fin N → Fin d × Fin d → R) (θ : Fin N → R) :
    Matrix (Fin (d+d)) (Fin (d+d)) R →ₗ[R] Matrix (Fin (d+d)) (Fin (d+d)) R :=
  ∑ i,(384*θ i) • sandwichLinear (realFinDecode d (coords i))

lemma rationalEta_symm (coords : Fin N → Fin d × Fin d → R) (θ : Fin N → R)
    (Z : Matrix (Fin (d+d)) (Fin (d+d)) R) (hZ : Z.IsSymm) :
    (rationalEta coords θ Z).IsSymm := by
  simp only [rationalEta,LinearMap.sum_apply,LinearMap.smul_apply]
  change (∑ i,(384*θ i) • (sandwichLinear (realFinDecode d (coords i)) Z)).transpose= _
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (sandwichLinear_symm _ _ (realFinDecode_symm _) hZ).smul _

def identityLinear (m : ℕ) (L : (Fin n → R) →ₗ[R] R) :
    (Fin n → R) →ₗ[R] Matrix (Fin m) (Fin m) R where
  toFun v := L v • (1 : Matrix (Fin m) (Fin m) R)
  map_add' v w := by simp only [map_add,add_smul]
  map_smul' r v := by simp only [map_smul,RingHom.id_apply,smul_smul,smul_eq_mul]

def diagonalLinear (L : (Fin n → R) →ₗ[R] Matrix (Fin m) (Fin m) R)
    (K : (Fin n → R) →ₗ[R] Matrix (Fin p) (Fin p) R) :
    (Fin n → R) →ₗ[R] Matrix (Fin (m+p)) (Fin (m+p)) R where
  toFun v := blockDiagonal (L v) (K v)
  map_add' v w := by
    ext i j
    cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
      simp [blockDiagonal,hi,hj,Matrix.add_apply]
  map_smul' r v := by
    ext i j
    cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
      simp [blockDiagonal,hi,hj,Matrix.smul_apply]

def schurPencil (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (second : Bool) : Pencil (valueDimension d) ((d+d)+(d+d)) :=
  let S := if second then rationalSum coords x else -rationalSum coords x
  let C := (Matrix.fromBlocks S (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℚ) 1 0).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm
  let L := diagonalLinear (identityLinear (d+d) (timeCoordinate d)-
    (rationalEta coords θ).comp (matrixVariable d (!second))) (matrixVariable d second)
  Pencil.ofAffine C L
    ((Matrix.IsSymm.fromBlocks
      (by dsimp [S]; split
          · exact rationalSum_symm _ _
          · exact (rationalSum_symm _ _).neg)
      (by simp) (by simp)).submatrix _)
    (fun v => by
      apply blockDiagonal_symm
      · change (timeCoordinate d v • (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℚ)-
          rationalEta coords θ (matrixVariable d (!second) v)).IsSymm
        exact (Matrix.isSymm_one.smul _).sub
          (rationalEta_symm coords θ _ (matrixVariable_symm _ _))
      · exact matrixVariable_symm _ _)

def lowerMatrixPencil (d : ℕ) (second : Bool) : Pencil (valueDimension d) (d+d) :=
  Pencil.ofAffine ((-1/400 : ℚ) • (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℚ))
    (matrixVariable d second) (Matrix.isSymm_one.smul _) (matrixVariable_symm second)

def upperMatrixPencil (d : ℕ) (ε : ℚ) (second : Bool) : Pencil (valueDimension d) (d+d) :=
  Pencil.ofAffine ((200/ε : ℚ) • (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℚ))
    (-(matrixVariable (R := ℚ) d second)) (Matrix.isSymm_one.smul _) (fun v => (matrixVariable_symm second v).neg)

def lowerTimePencil (d : ℕ) : Pencil (valueDimension d) 1 :=
  Pencil.ofAffine 0 (identityLinear 1 (timeCoordinate d)) (by simp) (fun _ => Matrix.isSymm_one.smul _)

def upperTimePencil (d : ℕ) : Pencil (valueDimension d) 1 :=
  Pencil.ofAffine ((100 : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ))
    (-(identityLinear (R := ℚ) 1 (timeCoordinate d))) (Matrix.isSymm_one.smul _)
    (fun _ => (Matrix.isSymm_one.smul _).neg)

def valuePencil (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ) :=
  (((((((schurPencil coords x θ false).blockDiagonal (schurPencil coords x θ true)).blockDiagonal
    (lowerMatrixPencil d false)).blockDiagonal (upperMatrixPencil d ε false)).blockDiagonal
    (lowerMatrixPencil d true)).blockDiagonal (upperMatrixPencil d ε true)).blockDiagonal
    (lowerTimePencil d)).blockDiagonal (upperTimePencil d)

def valueObjective (d : ℕ) (ε : ℚ) : (Fin (valueDimension d) → ℚ) →ₗ[ℚ] ℚ :=
  timeCoordinate d+ ε • (∑ i : Fin d, ((LinearMap.proj (i,i)).comp
    (matrixCoordinate d false)+(LinearMap.proj (i,i)).comp (matrixCoordinate d true)))

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ValueOuterRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
noncomputable section
open CurrentKS.HermitianCoordinates Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d n : ℕ}

def valueOuterRadius (d : ℕ) (ε : ℚ) : ℚ :=
  ((valueDimension d:ℚ)+1)*(100+400/ε*((d:ℚ)+1))
def valueInnerRadius (d : ℕ) : ℚ := 1/(4000*((d:ℚ)^2+1))

end
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ValueObjectiveCoeffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
noncomputable section
open CurrentKS.HermitianCoordinates Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

def valueObjectiveCoeffs (d : ℕ) (ε : ℚ) : Fin (valueDimension d) → ℚ :=
  Pi.single (valueIndex d (.inl 0)) 1 + ε •
    ∑ i : Fin d, (Pi.single (valueIndex d (.inr (.inl (i,i)))) 1 +
      Pi.single (valueIndex d (.inr (.inr (i,i)))) 1)

def valueLipschitz (d : ℕ) (ε : ℚ) : ℚ := ((valueDimension d:ℚ)+1)*(1+2*ε*d)

end
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_RationalAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.RationalSDP
open CurrentKS.HermitianCoordinates
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}


def valueQueryPoint (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (ν δ : ℚ) : Fin (valueDimension d) → ℚ :=
  let ε := ν/d
  let L := valueLipschitz d ε
  let R := valueOuterRadius d ε
  let r := valueInnerRadius d
  (valuePencil coords x θ ε).optimize (valueObjectiveCoeffs d ε) δ
    (nearRadius δ L R r) R 100 (optimizeFuel δ 100)

def valueQuery (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ) (ν δ : ℚ) : ℚ :=
  valueObjective d (ν/d) (valueQueryPoint coords x θ ν δ)

end CurrentKS.RationalSDP

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_RootTolerance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators

variable {d N : ℕ}

def rootTolerance (d N : ℕ) (lam error : ℚ) : ℚ :=
  error/(2*(38400*d+lam*N+1))

def potentialQuery (coords : Fin N → Fin d × Fin d → ℚ) (x : Fin N → ℚ)
    (ν lam error : ℚ) : ℚ :=
  let θ := fun i => CurrentKS.Scalar.approxPsi (x i) (rootTolerance d N lam error)
  valueQuery coords x θ ν (error/4)+lam*∑ i,θ i

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_FixedPart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.RationalSDP
open CurrentKS.RationalFace

variable {d N n : ℕ}

def faceQuery (coords : Fin N → Fin d × Fin d → ℚ) (base : Fin N → ℚ)
    (y : Fin (activeIndices base).length → ℚ) (ν lam error : ℚ) : ℚ :=
  potentialQuery coords (extend (activeIndex base) base y) ν lam error

open CurrentKS.HermitianCoordinates CurrentKS.Scalar
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

end CurrentKS.RationalSDP

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_FaceState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
noncomputable section
open CurrentKS.Scalar
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d N : ℕ}

def faceState (base : Fin N → ℚ) : Fin (activeIndices base).length → ℚ :=
  fun j => base (activeIndex base j)

end
end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Parameters2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Schedule

structure Parameters where
  ε : ℚ
  σ : ℚ
  a : ℚ
  M : ℚ
  s : ℚ
  h : ℚ
  ρ : ℚ
  stencilError : ℚ
  selectionError : ℚ
  deriving DecidableEq

def parameters (d n : ℕ) (ν lam : ℚ) : Parameters :=
  let ε := ν/(d:ℚ)
  let σ := lam^2/ν
  let a := threshold n ε lam
  let M := curveBudget d n ε σ lam
  let s := stepSize a M σ
  let h := stencilSize n a M σ
  let ρ := meshSize n a M s
  ⟨ε,σ,a,M,s,h,ρ,a*h^2/(128*n),a*s^2/4⟩

end CurrentKS.Schedule

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_FaceStencil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference CurrentKS.Descent

variable {d N : ℕ}

def faceStencil (coords : Fin N → Fin d × Fin d → ℚ) (base : Fin N → ℚ) (ν lam : ℚ) :
    (Fin (activeIndices base).length → ℚ) → ℚ :=
  fun y => faceQuery coords base y ν lam (parameters d (activeIndices base).length ν lam).stencilError

def faceScore (coords : Fin N → Fin d × Fin d → ℚ) (base : Fin N → ℚ) (ν lam : ℚ) :
    (Fin (activeIndices base).length → ℚ) → ℚ :=
  fun y => faceQuery coords base y ν lam (parameters d (activeIndices base).length ν lam).selectionError

def faceCandidates (coords : Fin N → Fin d × Fin d → ℚ) (base : Fin N → ℚ) (ν lam : ℚ)
    [NeZero (activeIndices base).length] : List (Fin (activeIndices base).length → ℚ) :=
  let p := parameters d (activeIndices base).length ν lam
  allCandidates (faceStencil coords base ν lam) (faceState base) p.h p.a p.M p.s p.ρ

def faceChoice (coords : Fin N → Fin d × Fin d → ℚ) (base : Fin N → ℚ) (ν lam : ℚ)
    [NeZero (activeIndices base).length] : Fin (activeIndices base).length → ℚ :=
  select (faceScore coords base ν lam) (faceState base) (faceCandidates coords base ν lam)

end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_MinList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Descent

def minList : List ℚ → ℚ
  | [] => 1
  | a::as => min a (minList as)

def fuel (r : ℚ) : ℕ := ⌈100/r⌉₊+1

end CurrentKS.Descent

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_NearestEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
variable {N : ℕ}

def nearestEndpoint (r : ℚ) : ℚ := if 0 ≤ r then 1 else -1

def freezeOne (σ : ℚ) (x : Fin N → ℚ) (i : Fin N) : Fin N → ℚ :=
  if 1-|x i|≤σ then Function.update x i (nearestEndpoint (x i)) else x

def freezeList (σ : ℚ) : (Fin N → ℚ) → List (Fin N) → (Fin N → ℚ)
  | x,[] => x
  | x,i::is => freezeList σ (freezeOne σ x i) is

def freezeAll (σ : ℚ) (x : Fin N → ℚ) : Fin N → ℚ := freezeList σ x (List.finRange N)

end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Transition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference CurrentKS.Descent

variable {d N : ℕ}

def transition (coords : Fin N → Fin d × Fin d → ℚ) (ν lam : ℚ)
    (x : Fin N → ℚ) : Option (Fin N → ℚ) :=
  if hn : (activeIndices x).length=0 then none else
    letI : NeZero (activeIndices x).length := ⟨hn⟩
    some (freezeAll (lam^2/ν) (extend (activeIndex x) x (faceChoice coords x ν lam)))

def uniformDrop (d N : ℕ) (ν lam : ℚ) : ℚ :=
  minList ((List.range (N+1)).map fun n =>
    let p := parameters d n ν lam
    p.a*p.s^2)

def rationalRun (coords : Fin N → Fin d × Fin d → ℚ) (ν lam : ℚ) : Fin N → ℚ :=
  run (transition coords ν lam) (fuel (uniformDrop d N ν lam)) (freezeAll (lam^2/ν) 0)

end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_UpperIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalGrid

def upperIndex (den : ℕ) (test : ℚ → Bool) : ℕ → ℕ
  | 0 => 0
  | k+1 => if test ((k:ℚ)/den) then upperIndex den test k else k+1

def upper (den : ℕ) (test : ℚ → Bool) : ℚ := (upperIndex den test den:ℚ)/den

end CurrentKS.RationalGrid

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates
open scoped BigOperators

variable {d N : ℕ}

def rationalVariance (coords : Fin N → Fin d × Fin d → ℚ) :
    Matrix (Fin (d+d)) (Fin (d+d)) ℚ :=
  ∑ i,realFinDecode d (coords i)*realFinDecode d (coords i)

def varianceTest (coords : Fin N → Fin d × Fin d → ℚ) (q : ℚ) : Bool :=
  (KS.W17.rationalNegativeWitness (d+d) (q • 1-rationalVariance coords)).isNone

def varianceQuery (coords : Fin N → Fin d × Fin d → ℚ) : ℚ :=
  CurrentKS.RationalGrid.upper (1000*N*d^2) (varianceTest coords)

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_PenaltyParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Schedule
open CurrentKS.RationalRoot

def penaltyParameter (N : ℕ) (ν : ℚ) : ℚ := upperSqrt ν ν/(200*N)

end CurrentKS.Schedule

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_NormalizedRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.RationalFace

open CurrentKS.RationalSDP CurrentKS.Schedule

variable {d N : ℕ}

def normalizedRun (coords : Fin N → Fin d × Fin d → ℚ) : Fin N → ℚ :=
  let ν := varianceQuery coords
  rationalRun coords ν (penaltyParameter N ν)

open CurrentKS.Difference
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

end CurrentKS.RationalFace

open Matrix

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Signing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalInput
open CurrentKS.RationalFace CurrentKS.RationalSDP
open scoped BigOperators

def signing (x : Input) : List Bool :=
  if (indices x).length=0 then List.replicate x.N true else
    let s := normalizedRun (normalizedCoordinates x)
    List.ofFn fun i => decide (orientation x i*extend (index x) (fun _ => 1) s i=1)

end CurrentKS.RationalInput

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_IterateRoutine
attribute [-simp] _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.IterateRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine

variable {α : Type*} {encode : α → Word} {next : α → α} {cost : α → ℕ}

abbrev counter (n : ℕ) : Fin (n+3) := ⟨n+1,by omega⟩
abbrev work (n : ℕ) : Fin (n+3) := ⟨n+2,by omega⟩
def corePorts (n : ℕ) : Fin (n+1) ↪ Fin (n+3) := ⟨Fin.castAdd 2,Fin.castAdd_injective _ _⟩
def parsePorts (n : ℕ) : Fin 3 ↪ Fin (n+3) :=
  ⟨![0,counter n,work n],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]⟩
@[simp] lemma parsePorts_apply (n : ℕ) (i : Fin 3) :
    parsePorts n i = ![0,counter n,work n] i := rfl

def state (n : ℕ) (value count : Word) : Fin (n+3) → Word :=
  fun j => if j.val=0 then value else if j.val=n+1 then count else []
def parse (n : ℕ) : Program (n+3) := KS.W11.FrameWireCodec.unframeProgram (parsePorts n)
def body (r : Routine encode (fun x => encode (next x)) cost) : Program (r.scratch+3) :=
  compose (KS.W23.LiteralProgram.pop (counter r.scratch)) (liftPorts r.program (corePorts r.scratch))
def program (r : Routine encode (fun x => encode (next x)) cost) : Program (r.scratch+3) :=
  compose (parse r.scratch) (FiniteControl.whileNonempty (counter r.scratch) (body r))
def input (encode : α → Word) (p : ℕ×α) : Word :=
  KS.W01.frame (List.replicate p.1 true)++encode p.2

lemma parse_spec (n : ℕ) (value : Word) (k : ℕ) :
    RunSpec (parse n) (io (KS.W01.frame (List.replicate k true)++value))
      (state n value (List.replicate k true)) (3*k+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec (parsePorts n) (fun _ => []) (List.replicate k true) value
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  · funext j
    simp only [KS.W28.FixedPositiveSerializer.registers,parsePorts_apply]
    dsimp [io]
    simp only [Fin.ext_iff,Fin.val_zero]
    split_ifs <;> simp_all
  · funext j
    simp only [KS.W28.FixedPositiveSerializer.registers,parsePorts_apply]
    dsimp [state]
    simp only [Fin.ext_iff,Fin.val_zero]
    split_ifs <;> simp_all
  · simp

lemma element_spec (r : Routine encode (fun x => encode (next x)) cost) (x : α) (count : Word) :
    RunSpec (liftPorts r.program (corePorts r.scratch))
      (state r.scratch (encode x) count) (state r.scratch (encode (next x)) count) (cost x) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (r.spec x)
  · intro j
    have hj : j.val≠r.scratch+1 := by omega
    simp [state,io,corePorts,hj]
  · intro j
    have hj : j.val≠r.scratch+1 := by omega
    simp [state,io,corePorts,hj]
  · intro j hj
    have hz : j.val≠0 := by intro hz;exact hj 0 (Fin.ext hz)
    simp [state,hz]

lemma pop_spec (n : ℕ) (value : Word) (k : ℕ) :
    RunSpec (KS.W23.LiteralProgram.pop (counter n)) (state n value (List.replicate (k+1) true))
      (state n value (List.replicate k true)) 1 := by
  have h := KS.W23.LiteralProgram.pop_spec (counter n) (state n value (List.replicate (k+1) true))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext j
  dsimp [state,Function.update]
  simp only [Fin.ext_iff]
  split_ifs <;> simp_all

def loopTicks (cost : α → ℕ) (next : α → α) : ℕ → α → ℕ
  | 0,_ => 1
  | k+1,x => (1+cost x)+loopTicks cost next k (next x)+1

lemma loop_trace (r : Routine encode (fun x => encode (next x)) cost) (k : ℕ) (x : α) :
    FiniteControl.Trace (counter r.scratch) (body r)
      (state r.scratch (encode x) (List.replicate k true))
      (io (encode (next^[k] x))) (loopTicks cost next k x) := by
  induction k generalizing x with
  | zero =>
    have he : state r.scratch (encode x) []=io (encode x) := by funext j;simp [state,io]
    simpa only [List.replicate_zero,Function.iterate_zero_apply,loopTicks,he] using
      (FiniteControl.Trace.stop (body:=body r) (port:=counter r.scratch)
        (state r.scratch (encode x) []) (by simp [state]))
  | succ k ih =>
    have hb := (pop_spec r.scratch (encode x) k).compose (element_spec r x (List.replicate k true))
    have h := FiniteControl.Trace.step (show state r.scratch (encode x)
        (List.replicate (k+1) true) (counter r.scratch)≠[] by simp [state]) hb (ih (next x))
    simp only [Function.iterate_succ_apply,loopTicks] at h ⊢
    exact h

def routine (r : Routine encode (fun x => encode (next x)) cost) :
    Routine (input encode) (fun p : ℕ×α => encode (next^[p.1] p.2))
      (fun p => 3*p.1+2+loopTicks cost next p.1 p.2) where
  scratch := r.scratch+2
  program := program r
  spec p := (parse_spec r.scratch (encode p.2) p.1).compose
    (FiniteControl.trace_spec (loop_trace r p.1 p.2))

end CurrentKS.IterateRoutine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FramedMapRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.FramedMapRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine

variable {α : Type*} {input output : α → Word} {cost : α → ℕ}

def tape (encode : α → Word) (xs : List α) := xs.flatMap (fun x => KS.W01.frame (encode x))

end CurrentKS.FramedMapRoutine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FoldRoutine
attribute [-simp] _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.FoldRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine PairRoutine

abbrev source (n : ℕ) : Fin (n+5) := ⟨n+1,by omega⟩
abbrev accumulator (n : ℕ) : Fin (n+5) := ⟨n+2,by omega⟩
abbrev work (n : ℕ) : Fin (n+5) := ⟨n+3,by omega⟩
abbrev temp (n : ℕ) : Fin (n+5) := ⟨n+4,by omega⟩
def ports (n : ℕ) : Fin (n+1) ↪ Fin (n+5) := ⟨Fin.castAdd 4,Fin.castAdd_injective _ _⟩
def state (n : ℕ) (value stored tail : Word) : Fin (n+5) → Word :=
  fun j => if j.val=0 then value else if j.val=n+1 then tail else if j.val=n+2 then stored else []

def initialPorts (n : ℕ) : Fin 3 ↪ Fin (n+5) :=
  ⟨![0,accumulator n,work n],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]⟩
def decodePorts (n : ℕ) : Fin 3 ↪ Fin (n+5) :=
  ⟨![source n,0,work n],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]⟩
def framePorts (n : ℕ) : Fin 3 ↪ Fin (n+5) :=
  ⟨![work n,accumulator n,temp n],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]⟩

@[simp] lemma initialPorts_apply (n : ℕ) (i : Fin 3) :
    initialPorts n i = ![0,accumulator n,work n] i := rfl

@[simp] lemma decodePorts_apply (n : ℕ) (i : Fin 3) :
    decodePorts n i = ![source n,0,work n] i := rfl

@[simp] lemma framePorts_apply (n : ℕ) (i : Fin 3) :
    framePorts n i = ![work n,accumulator n,temp n] i := rfl

def setup (n : ℕ) : Program (n+5) :=
  compose (KS.W11.FrameWireCodec.unframeProgram (initialPorts n))
    (CleanRoutine.transfer 0 (work n) (source n))
def decode (n : ℕ) := KS.W11.FrameWireCodec.unframeProgram (decodePorts n)
def frame (n : ℕ) := KS.W11.FrameWireCodec.frameProgram (framePorts n)
def prepend (n : ℕ) := KS.W12.StackTransfer.program (accumulator n) 0 (work n)
def save (n : ℕ) := CleanRoutine.transfer 0 (work n) (accumulator n)
def finish (n : ℕ) := CleanRoutine.transfer (accumulator n) (work n) 0

variable {α β : Type*} {encS : β → Word} {encE : α → Word} {F : β → α → β}
variable {cost : β×α → ℕ}

def body (r : Routine (fun p : β×α => pair (encS p.1) (encE p.2))
    (fun p => encS (F p.1 p.2)) cost) : Program (r.scratch+5) :=
  compose (decode r.scratch) (compose (frame r.scratch) (compose (prepend r.scratch)
    (compose (liftPorts r.program (ports r.scratch)) (save r.scratch))))
def scan (r : Routine (fun p : β×α => pair (encS p.1) (encE p.2))
    (fun p => encS (F p.1 p.2)) cost) :=
  FiniteControl.whileNonempty (source r.scratch) (body r)
def program (r : Routine (fun p : β×α => pair (encS p.1) (encE p.2))
    (fun p => encS (F p.1 p.2)) cost) :=
  compose (setup r.scratch) (compose (scan r) (finish r.scratch))

lemma state_ports (n : ℕ) (a b c : Word) (j : Fin (n+1)) :
    state n a b c (ports n j)=io a j := by
  have h₁ : j.val≠n+1 := by omega
  have h₂ : j.val≠n+2 := by omega
  simp [state,ports,io,h₁,h₂]
lemma state_other (n : ℕ) (a a' b c : Word) (j : Fin (n+5)) (hj : ∀ i,j≠ports n i) :
    state n a b c j=state n a' b c j := by
  have hz : j.val≠0 := by intro hz;exact hj 0 (Fin.ext hz)
  simp [state,hz]

lemma setup_spec (n : ℕ) (a xs : Word) :
    RunSpec (setup n) (io (pair a xs)) (state n [] a xs)
      ((3*a.length+2)+(2*xs.length+2)) := by
  have hd : RunSpec (KS.W11.FrameWireCodec.unframeProgram (initialPorts n))
      (io (pair a xs)) (state n xs a []) (3*a.length+2) := by
    have h := KS.W11.FrameWireCodec.unframe_spec (initialPorts n) (fun _ => []) a xs
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (funext j <;> simp only [KS.W28.FixedPositiveSerializer.registers,initialPorts_apply] <;> dsimp [state,io] <;> simp only [Fin.ext_iff] <;> split_ifs <;> simp_all)
  have ht : RunSpec (CleanRoutine.transfer 0 (work n) (source n))
      (state n xs a []) (state n [] a xs) (2*xs.length+2) := by
    have h := CleanRoutine.transfer_spec (0 : Fin (n+5)) (work n) (source n)
      (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (state n xs a []) (by simp [state]) (by simp [state])
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
    funext j;dsimp [state,Function.update];simp only [Fin.ext_iff];split_ifs <;> simp_all
  exact hd.compose ht

lemma decode_spec (n : ℕ) (s x tail : Word) :
    RunSpec (decode n) (state n [] s (KS.W01.frame x++tail)) (state n x s tail) (3*x.length+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec (decodePorts n) (state n [] s []) x tail
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl) <;> funext j <;> simp only [KS.W28.FixedPositiveSerializer.registers,decodePorts_apply] <;> dsimp [state] <;> simp only [Fin.ext_iff] <;> split_ifs <;> simp_all)

lemma frame_spec (n : ℕ) (s x tail : Word) :
    RunSpec (frame n) (state n x s tail) (state n x (KS.W01.frame s) tail) (4*s.length+3) := by
  have h := KS.W11.FrameWireCodec.frame_spec (framePorts n) (state n x [] tail) s
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl) <;> funext j <;> simp only [KS.W28.FixedPositiveSerializer.registers,framePorts_apply] <;> dsimp [state] <;> simp only [Fin.ext_iff] <;> split_ifs <;> simp_all)

lemma prepend_spec (n : ℕ) (s x tail : Word) :
    RunSpec (prepend n) (state n x s tail) (state n (s++x) [] tail) (2*s.length+2) := by
  have h := KS.W12.StackTransfer.spec (accumulator n) (0 : Fin (n+5)) (work n)
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (state n x s tail) (by simp [state])
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  · funext j;dsimp [state,KS.W12.StackTransfer.after];simp only [Fin.ext_iff];split_ifs <;> simp_all
  · simp [state]

lemma save_spec (n : ℕ) (s tail : Word) :
    RunSpec (save n) (state n s [] tail) (state n [] s tail) (2*s.length+2) := by
  have h := CleanRoutine.transfer_spec (0 : Fin (n+5)) (work n) (accumulator n)
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (state n s [] tail) (by simp [state]) (by simp [state])
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j;dsimp [state,Function.update];simp only [Fin.ext_iff];split_ifs <;> simp_all

lemma finish_spec (n : ℕ) (s : Word) :
    RunSpec (finish n) (state n [] s []) (io s) (2*s.length+2) := by
  have h := CleanRoutine.transfer_spec (accumulator n) (work n) (0 : Fin (n+5))
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (state n [] s []) (by simp [state]) (by simp [state])
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  · funext j;dsimp [state,io,Function.update];simp only [Fin.ext_iff];split_ifs <;> simp_all
  · simp [state]

def bodyTicks (encS : β → Word) (encE : α → Word) (F : β → α → β) (cost : β×α → ℕ)
    (s : β) (x : α) : ℕ :=
  (3*(encE x).length+2)+(4*(encS s).length+3)+(2*(KS.W01.frame (encS s)).length+2)+
    cost (s,x)+(2*(encS (F s x)).length+2)

lemma body_spec (r : Routine (fun p : β×α => pair (encS p.1) (encE p.2))
    (fun p => encS (F p.1 p.2)) cost) (s : β) (x : α) (tail : Word) :
    RunSpec (body r) (state r.scratch [] (encS s) (KS.W01.frame (encE x)++tail))
      (state r.scratch [] (encS (F s x)) tail) (bodyTicks encS encE F cost s x) := by
  have hc := KS.W01.FixedPortRunSpec.lift_runSpec _ (ports r.scratch) _ _
    (state r.scratch (pair (encS s) (encE x)) [] tail)
    (state r.scratch (encS (F s x)) [] tail) _ (r.spec (s,x))
    (state_ports _ _ _ _) (state_ports _ _ _ _) (state_other _ _ _ _ _)
  have h := (decode_spec r.scratch (encS s) (encE x) tail).compose
    ((frame_spec r.scratch (encS s) (encE x) tail).compose
      ((prepend_spec r.scratch (KS.W01.frame (encS s)) (encE x) tail).compose
        (hc.compose (save_spec r.scratch (encS (F s x)) tail))))
  simp only [bodyTicks,Nat.add_assoc] at h ⊢
  exact h

def scanTicks (encS : β → Word) (encE : α → Word) (F : β → α → β) (cost : β×α → ℕ) : β → List α → ℕ
  | _,[] => 1
  | s,x::xs => bodyTicks encS encE F cost s x+scanTicks encS encE F cost (F s x) xs+1

lemma scan_trace (r : Routine (fun p : β×α => pair (encS p.1) (encE p.2))
    (fun p => encS (F p.1 p.2)) cost) (s : β) (xs : List α) :
    FiniteControl.Trace (source r.scratch) (body r)
      (state r.scratch [] (encS s) (FramedMapRoutine.tape encE xs))
      (state r.scratch [] (encS (xs.foldl F s)) []) (scanTicks encS encE F cost s xs) := by
  induction xs generalizing s with
  | nil =>
    exact FiniteControl.Trace.stop _ (by simp [state,FramedMapRoutine.tape])
  | cons x xs ih =>
    apply FiniteControl.Trace.step ?_ (body_spec r s x (FramedMapRoutine.tape encE xs)) (ih (F s x))
    intro hz
    have hh := congrArg List.length hz
    simp [state,KS.W01.length_frame] at hh

def ticks (encS : β → Word) (encE : α → Word) (F : β → α → β) (cost : β×α → ℕ)
    (s : β) (xs : List α) : ℕ :=
  ((3*(encS s).length+2)+(2*(FramedMapRoutine.tape encE xs).length+2))+
    scanTicks encS encE F cost s xs+(2*(encS (xs.foldl F s)).length+2)

def routine (r : Routine (fun p : β×α => pair (encS p.1) (encE p.2))
    (fun p => encS (F p.1 p.2)) cost) :
    Routine (fun p : β×List α => pair (encS p.1) (FramedMapRoutine.tape encE p.2))
      (fun p => encS (p.2.foldl F p.1)) (fun p => ticks encS encE F cost p.1 p.2) where
  scratch := r.scratch+4
  program := program r
  spec p := by
    have h := (setup_spec r.scratch (encS p.1) (FramedMapRoutine.tape encE p.2)).compose
      ((FiniteControl.trace_spec (scan_trace r p.1 p.2)).compose
        (finish_spec r.scratch (encS (p.2.foldl F p.1))))
    simp only [ticks,Nat.add_assoc] at h ⊢
    exact h

end CurrentKS.FoldRoutine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_Realization
attribute [-simp] _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

structure Realizes {α β : Type*} (encA : α → Word) (encB : β → Word) (f : α → β) where
  cost : α → ℕ
  routine : Routine encA (fun x => encB (f x)) cost

variable {α β γ δ : Type*} {encA : α → Word} {encB : β → Word}
  {encC : γ → Word} {encD : δ → Word}

def prodCode (ea : α → Word) (eb : β → Word) (p : α×β) : Word := PairRoutine.pair (ea p.1) (eb p.2)
def listCode (ea : α → Word) : List α → Word := FramedMapRoutine.tape ea

def identity (ea : α → Word) : Realizes ea ea id where
  cost := fun _ => 1
  routine := {
    scratch := 0
    program := KS.W20.Wire.halt 0
    spec := fun x => KS.W20.Wire.halt_spec 0 (io (ea x)) }

def constant (ea : α → Word) (eb : β → Word) (y : β) : Realizes ea eb (fun _ => y) where
  cost := fun x => (ea x).length+1+((eb y).length+1)
  routine := {
    scratch := 0
    program := KS.W29.FixedSequential.compose (KS.W04.BinaryStackMoves.clearProgram 0)
      (KS.W20.Wire.writeBits 0 (eb y))
    spec := fun x => by
      have hc : KS.W03.MachineCombinators.RunSpec (KS.W04.BinaryStackMoves.clearProgram (0 : Fin 1))
          (io (ea x)) (io []) ((ea x).length+1) := by
        have h := KS.W15.RationalMultiply.clear_spec (0 : Fin 1) (io (ea x))
        convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
        funext j;fin_cases j;rfl
      have hw : KS.W03.MachineCombinators.RunSpec (KS.W20.Wire.writeBits (0 : Fin 1) (eb y))
          (io []) (io (eb y)) ((eb y).length+1) := by
        have h := KS.W20.Wire.writeBits_spec (0 : Fin 1) (eb y) (io [])
        convert h using 1
        all_goals try with_reducible_and_instances rfl
        funext j;fin_cases j;simp [io,Function.update]
      exact hc.compose hw }

def Realizes.then {f : α → β} {g : β → γ} (r : Realizes encA encB f)
    (s : Realizes encB encC g) : Realizes encA encC (fun x => g (f x)) where
  cost := fun x => r.cost x+s.cost (f x)
  routine := r.routine.compose (s.routine.reindex f)

def Realizes.both {f : α → β} {g : α → γ} (r : Realizes encA encB f)
    (s : Realizes encA encC g) : Realizes encA (prodCode encB encC) (fun x => (f x,g x)) where
  cost := PairRoutine.pairingTicks encA (fun x => encB (f x)) r.cost s.cost
  routine := PairRoutine.pairing r.routine s.routine

def first (ea : α → Word) (eb : β → Word) : Realizes (prodCode ea eb) ea Prod.fst where
  cost := fun p => 5*(ea p.1).length+(eb p.2).length+5
  routine := PairRoutine.fstRoutine.reindex (fun p : α×β => (ea p.1,eb p.2))

def second (ea : α → Word) (eb : β → Word) : Realizes (prodCode ea eb) eb Prod.snd where
  cost := fun p => 4*(ea p.1).length+3
  routine := PairRoutine.sndRoutine.reindex (fun p : α×β => (ea p.1,eb p.2))

def Realizes.congr {f g : α → β} (r : Realizes encA encB f) (h : ∀ x,f x=g x) :
    Realizes encA encB g := by
  have he : f=g := funext h
  exact he ▸ r

def Realizes.fold {f : α×β → α} (r : Realizes (prodCode encA encB) encA f) :
    Realizes (prodCode encA (listCode encB)) encA
      (fun p : α×List β => p.2.foldl (fun a b => f (a,b)) p.1) where
  cost := fun p => FoldRoutine.ticks encA encB (fun a b => f (a,b)) r.cost p.1 p.2
  routine := FoldRoutine.routine r.routine

def Realizes.changeOutput {f : α → β} (r : Realizes encA encB f)
    (ed : δ → Word) (g : α → δ) (h : ∀ x,encB (f x)=ed (g x)) :
    Realizes encA ed g where
  cost := r.cost
  routine := {
    scratch := r.routine.scratch
    program := r.routine.program
    spec := fun x => by simpa only [h x] using r.routine.spec x }

def Realizes.reindex {f : α → β} (r : Realizes encA encB f)
    (ed : δ → Word) (g : δ → α) (h : ∀ x,ed x=encA (g x)) :
    Realizes ed encB (fun x => f (g x)) where
  cost := fun x => r.cost (g x)
  routine := {
    scratch := r.routine.scratch
    program := r.routine.program
    spec := fun x => by simpa only [h x] using r.routine.spec (g x) }

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ListRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

variable {α β γ : Type*}

@[simp] lemma listCode_cons (ea : α → Word) (x : α) (xs : List α) :
    listCode ea (x::xs)=prodCode ea (listCode ea) (x,xs) := rfl

@[simp] lemma listCode_nil (ea : α → Word) : listCode ea []=[] := rfl

def consList (ea : α → Word) :
    Realizes (prodCode ea (listCode ea)) (listCode ea) (fun p => p.1::p.2) :=
  (identity (prodCode ea (listCode ea))).changeOutput (listCode ea) (fun p => p.1::p.2) (fun _ => rfl)

def reverseBody (ea : α → Word) :
    Realizes (prodCode (listCode ea) ea) (listCode ea) (fun p => p.2::p.1) :=
  ((second (listCode ea) ea).both (first (listCode ea) ea)).then (consList ea)

def reverseList (ea : α → Word) : Realizes (listCode ea) (listCode ea) List.reverse :=
  (((constant (listCode ea) (listCode ea) []).both (identity (listCode ea))).then
    (reverseBody ea).fold).congr (fun xs => by simp)

def mapCtxUpdate (f : γ×α → β) (p : (γ×List β)×α) : γ×List β :=
  (p.1.1,f (p.1.1,p.2)::p.1.2)

def mapCtxBody (ec : γ → Word) (ea : α → Word) (eb : β → Word)
    {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) :
    Realizes (prodCode (prodCode ec (listCode eb)) ea) (prodCode ec (listCode eb)) (mapCtxUpdate f) :=
  let old := first (prodCode ec (listCode eb)) ea
  let context := old.then (first ec (listCode eb))
  let acc := old.then (second ec (listCode eb))
  let element := second (prodCode ec (listCode eb)) ea
  context.both ((((context.both element).then r).both acc).then (consList eb))

lemma fold_mapCtx (f : γ×α → β) (c : γ) (xs : List α) (acc : List β) :
    xs.foldl (fun s x => mapCtxUpdate f (s,x)) (c,acc)=
      (c,(xs.map (fun x => f (c,x))).reverse++acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons]
    change xs.foldl (fun s x => mapCtxUpdate f (s,x)) (c,f (c,x)::acc)=_
    rw [ih]
    simp only [List.map_cons,List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

def Realizes.mapCtx {ec : γ → Word} {ea : α → Word} {eb : β → Word}
    {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) :
    Realizes (prodCode ec (listCode ea)) (listCode eb) (fun p => p.2.map (fun x => f (p.1,x))) :=
  let context := first ec (listCode ea)
  let xs := second ec (listCode ea)
  let init := context.both (constant (prodCode ec (listCode ea)) (listCode eb) [])
  let loop := (init.both xs).then (mapCtxBody ec ea eb r).fold
  ((loop.then (second ec (listCode eb))).then (reverseList eb)).congr (fun p => by
    simp only [fold_mapCtx,List.append_nil,List.reverse_reverse])

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_NaturalRealization
attribute [-simp] _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

abbrev natCode (k : ℕ) : Word := List.replicate k true

def natSucc : Realizes natCode natCode Nat.succ where
  cost := fun _ => 1
  routine := {
    scratch := 0
    program := KS.W20.Wire.push 0 true
    spec := fun k => by
      have h := KS.W20.Wire.push_spec (0 : Fin 1) true (io (natCode k))
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      funext j;fin_cases j;simp [io,natCode,Function.update,List.replicate_succ] }

def natPred : Realizes natCode natCode Nat.pred where
  cost := fun _ => 1
  routine := {
    scratch := 0
    program := KS.W23.LiteralProgram.pop 0
    spec := fun k => by
      have h := KS.W23.LiteralProgram.pop_spec (0 : Fin 1) (io (natCode k))
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      funext j;fin_cases j;cases k <;> simp [io,natCode,Function.update] }

variable {α : Type*} {ea : α → Word}
def Realizes.iterate {f : α → α} (r : Realizes ea ea f) :
    Realizes (prodCode natCode ea) ea (fun p => f^[p.1] p.2) where
  cost := fun p => 3*p.1+2+IterateRoutine.loopTicks r.cost f p.1 p.2
  routine := IterateRoutine.routine r.routine

def rangeStep (p : ℕ×List ℕ) : ℕ×List ℕ := (p.1+1,p.1::p.2)
def rangeStepRealizes : Realizes (prodCode natCode (listCode natCode))
    (prodCode natCode (listCode natCode)) rangeStep :=
  let idx := first natCode (listCode natCode)
  let acc := second natCode (listCode natCode)
  (idx.then natSucc).both ((idx.both acc).then (consList natCode))

lemma rangeStep_iterate (n : ℕ) : rangeStep^[n] (0,[])=(n,(List.range n).reverse) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    simp [rangeStep,List.range_succ]

def range : Realizes natCode (listCode natCode) List.range :=
  let init := constant natCode (prodCode natCode (listCode natCode)) (0,[])
  let run := ((identity natCode).both init).then rangeStepRealizes.iterate
  ((run.then (second natCode (listCode natCode))).then (reverseList natCode)).congr (by
    intro n
    simp only [rangeStep_iterate,List.reverse_reverse,id_eq])

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_CompareRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.CompareRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine

abbrev encode := KS.W01.encodeRat

def parsed (q r : ℚ) : Fin 13 → Word :=
  fun j => if j=0 then encode r else if j=11 then encode q else []

end CurrentKS.CompareRoutine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ConditionalRoutine
attribute [-simp] _root_.OAI.CurrentKS.Realization.listCode_cons _root_.OAI.CurrentKS.Realization.listCode_nil _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.ConditionalRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine KS.W29.FixedBranch

abbrev flag (n : ℕ) : Fin (n+3) := ⟨n+1,by omega⟩
abbrev work (n : ℕ) : Fin (n+3) := ⟨n+2,by omega⟩
def ports (n : ℕ) : Fin (n+1) ↪ Fin (n+3) := ⟨Fin.castAdd 2,Fin.castAdd_injective _ _⟩
def parsePorts (n : ℕ) : Fin 3 ↪ Fin (n+3) :=
  ⟨![0,flag n,work n],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]⟩
@[simp] lemma parsePorts_apply (n : ℕ) (i : Fin 3) :
    parsePorts n i = ![0,flag n,work n] i := rfl

def state (n : ℕ) (w : Word) (b : Bool) : Fin (n+3) → Word :=
  fun j => if j.val=0 then w else if j.val=n+1 then [b] else []
def parse (n : ℕ) : Program (n+3) := KS.W11.FrameWireCodec.unframeProgram (parsePorts n)
def select (n : ℕ) (heads : Fin (n+3) → Fin 3) (_ : Bool) : SelectInstruction (n+3) :=
  ⟨if heads (flag n)=2 then .left else .right,
    Vector.ofFn (fun j => if j=flag n then .pop else .stay)⟩

def choose (n : ℕ) (P Q : Program (n+1)) : Program (n+3) :=
  branch (liftPorts P (ports n)) (liftPorts Q (ports n)) 0 (select n)

def program (n : ℕ) (P Q : Program (n+1)) : Program (n+3) := compose (parse n) (choose n P Q)

lemma parse_spec (n : ℕ) (w : Word) (b : Bool) :
    RunSpec (parse n) (io (PairRoutine.pair [b] w)) (state n w b) 5 := by
  have h := KS.W11.FrameWireCodec.unframe_spec (parsePorts n) (fun _ => []) [b] w
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl) <;> funext j <;> simp only [KS.W28.FixedPositiveSerializer.registers,parsePorts_apply] <;> dsimp [state,io] <;> simp only [Fin.ext_iff] <;> split_ifs <;> simp_all)

lemma choose_true (n : ℕ) (P Q : Program (n+3)) (w out : Word) (cost : ℕ)
    (h : RunSpec P (io w) (io out) cost) :
    RunSpec (branch P Q 0 (select n)) (state n w true) (io out) (cost+1) := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin tail =>
    have ht : tail.length=cost := by simpa using hbits
    have hs : (branch P Q 0 (select n)).toMachine.step
        ⟨some (start P Q),state n w true⟩ coin =
        KS.W29.FixedBranch.liftLeft P Q ⟨some P.initial,io w⟩ := by
      rw [step_start]
      apply KS.W19.FixedRun.config_ext
      · simp [select,observedHeads,state,flag,KS.W29.topCode,selectInstruction,KS.W29.FixedBranch.liftLeft]
      · intro j
        simp only [select,selectInstruction,KS.W01.FixedStack.Instruction.action,Vector.getElem_ofFn]
        dsimp [KS.W29.FixedBranch.liftLeft]
        by_cases hj : j=flag n
        · subst j;simp [state,io,flag,KS.W29.StackAction.apply]
        · have hjv : j.val≠n+1 := by simpa [Fin.ext_iff,flag] using hj
          simp [hj,KS.W29.StackAction.apply]
          dsimp only [state,io]
          simp [hjv]
    change (branch P Q 0 (select n)).toMachine.run
      ⟨some (start P Q),state n w true⟩ (coin::tail)=_
    rw [KS.W01.FixedStack.Machine.run,hs,run_left]
    erw [h tail ht]
    rfl

lemma choose_false (n : ℕ) (P Q : Program (n+3)) (w out : Word) (cost : ℕ)
    (h : RunSpec Q (io w) (io out) cost) :
    RunSpec (branch P Q 0 (select n)) (state n w false) (io out) (cost+1) := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin tail =>
    have ht : tail.length=cost := by simpa using hbits
    have hs : (branch P Q 0 (select n)).toMachine.step
        ⟨some (start P Q),state n w false⟩ coin =
        KS.W29.FixedBranch.liftRight P Q ⟨some Q.initial,io w⟩ := by
      rw [step_start]
      apply KS.W19.FixedRun.config_ext
      · simp [select,observedHeads,state,flag,KS.W29.topCode,selectInstruction,KS.W29.FixedBranch.liftRight]
      · intro j
        simp only [select,selectInstruction,KS.W01.FixedStack.Instruction.action,Vector.getElem_ofFn]
        dsimp [KS.W29.FixedBranch.liftRight]
        by_cases hj : j=flag n
        · subst j;simp [state,io,flag,KS.W29.StackAction.apply]
        · have hjv : j.val≠n+1 := by simpa [Fin.ext_iff,flag] using hj
          simp [hj,KS.W29.StackAction.apply]
          dsimp only [state,io]
          simp [hjv]
    change (branch P Q 0 (select n)).toMachine.run
      ⟨some (start P Q),state n w false⟩ (coin::tail)=_
    rw [KS.W01.FixedStack.Machine.run,hs,run_right]
    erw [h tail ht]
    rfl

lemma core_spec (n : ℕ) (P : Program (n+1)) (w out : Word) (cost : ℕ)
    (h : RunSpec P (io w) (io out) cost) :
    RunSpec (liftPorts P (ports n)) (io w) (io out) cost := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ h
  · intro j;rfl
  · intro j;rfl
  · intro j hj
    have hz : j.val≠0 := by intro hz;exact hj 0 (Fin.ext hz)
    simp [io,hz]

variable {α : Type*} {encode yes no : α → Word} {c d : α → ℕ}
def routine (r : Routine encode yes c) (s : Routine encode no d) :
    Routine (fun p : Bool×α => PairRoutine.pair [p.1] (encode p.2))
      (fun p => if p.1 then yes p.2 else no p.2)
      (fun p => 5+(if p.1 then c p.2 else d p.2)+1) :=
  let n := r.scratch+s.scratch
  let r' := r.pad n (Nat.le_add_right _ _)
  let s' := s.pad n (Nat.le_add_left _ _)
  { scratch := n+2
    program := program n r'.program s'.program
    spec := fun p => by
      obtain ⟨b,x⟩ := p
      cases b
      · have h := (parse_spec n (encode x) false).compose
          (choose_false n (liftPorts r'.program (ports n)) _ _ _ _ (core_spec n _ _ _ _ (s'.spec x)))
        simp only [Bool.false_eq_true,ite_false, if_false,Nat.add_assoc] at h ⊢
        exact h
      · have h := (parse_spec n (encode x) true).compose
          (choose_true n _ (liftPorts s'.program (ports n)) _ _ _ (core_spec n _ _ _ _ (r'.spec x)))
        simp only [ite_true, if_true,Nat.add_assoc] at h ⊢
        exact h }

end CurrentKS.ConditionalRoutine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ScalarRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

abbrev ratCode : ℚ → Word := KS.W01.encodeRat
def boolCode (b : Bool) : Word := [b]

variable {α β : Type*} {encA : α → Word} {encB : β → Word}

def conditional {f g : α → β} (r : Realizes encA encB f) (s : Realizes encA encB g) :
    Realizes (prodCode boolCode encA) encB (fun p => if p.1 then f p.2 else g p.2) where
  cost := fun p => 5+(if p.1 then r.cost p.2 else s.cost p.2)+1
  routine := by
    have h := ConditionalRoutine.routine r.routine s.routine
    refine { scratch := h.scratch,program := h.program,spec := ?_ }
    intro p
    have hp := h.spec p
    simp only [apply_ite] at hp ⊢
    exact hp

def Realizes.ite {p : α → Bool} {f g : α → β}
    (b : Realizes encA boolCode p) (r : Realizes encA encB f) (s : Realizes encA encB g) :
    Realizes encA encB (fun x => if p x then f x else g x) :=
  (b.both (identity encA)).then (conditional r s)

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ArrayRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def natIsZero : Realizes natCode boolCode (fun n => decide (n=0)) where
  cost := fun n => n+6
  routine := by
    have h := WordOperations.isEmpty.reindex natCode
    refine { scratch := h.scratch,program := h.program,spec := ?_ }
    intro n
    simpa [natCode,boolCode,List.replicate_eq_nil_iff] using h.spec n

variable {α γ : Type*}
def lookupStep (p : (ℕ×α)×α) : ℕ×α :=
  if p.1.1=0 then p.1 else (p.1.1-1,if p.1.1-1=0 then p.2 else p.1.2)

lemma lookupStep_zero (xs : List α) (a : α) :
    (xs.foldl (fun s x => lookupStep (s,x)) (0,a))=(0,a) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [lookupStep] using ih

def Realizes.tabulate {ec : γ → Word} {ea : α → Word} {f : γ×ℕ → α}
    (r : Realizes (prodCode ec natCode) ea f) :
    Realizes (prodCode ec natCode) (listCode ea)
      (fun p => (List.range p.2).map (fun i => f (p.1,i))) :=
  ((first ec natCode).both ((second ec natCode).then range)).then r.mapCtx

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_VectorRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix

variable {α β γ : Type*}

abbrev vectorCode := listCode ratCode
abbrev matrixCode := listCode vectorCode
abbrev MatrixData := List (List ℚ)

def matrixData {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℚ) : MatrixData :=
  List.ofFn (fun i => List.ofFn (M i))

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceArrayRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

abbrev indicesCode := listCode natCode

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_DependentRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α β : Type*}

def finFamilyCode (ea : α → Word) (n : α → ℕ) (p : Σ a,Fin (n a)) : Word :=
  prodCode ea natCode (p.1,p.2.val)

def familyFirst {ea : α → Word} {n : α → ℕ} :
    Realizes (finFamilyCode ea n) ea (fun p => p.1) :=
  (first ea natCode).reindex (finFamilyCode ea n) (fun p => (p.1,p.2.val)) (fun _ => rfl)
def familyIndex {ea : α → Word} {n : α → ℕ} :
    Realizes (finFamilyCode ea n) natCode (fun p => p.2.val) :=
  (second ea natCode).reindex (finFamilyCode ea n) (fun p => (p.1,p.2.val)) (fun _ => rfl)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_LevelPencilRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix

variable {α : Type*}

def replicateList (ea : α → Word) :
    Realizes (prodCode ea natCode) (listCode ea) (fun p => List.replicate p.2 p.1) :=
  (first ea natCode).tabulate.congr (by intro p;simp)

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_Squares
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational squares. -/

section

namespace AlgorithmicThinTrees.RationalGram

def base4Squares : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k+1,n => List.replicate (n%4) 1 ++ (base4Squares k (n/4)).map (2*·)

def scalarFactors (q : ℚ) : List ℚ :=
  let n := q.num.natAbs*q.den
  (base4Squares n.size n).map (fun a : ℕ => (a:ℚ)/q.den)

end AlgorithmicThinTrees.RationalGram
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_Gram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational gram. -/

section

namespace AlgorithmicThinTrees.RationalGram
open Matrix
variable {n : ℕ}

def factorColumns : (n : ℕ) → Matrix (Fin n) (Fin n) ℚ → List (Fin n → ℚ)
  | 0,_ => []
  | n+1,A => (scalarFactors (A 0 0)⁻¹).map (fun a i => a*A i 0) ++
      (factorColumns n (KS.W17.schurTail A)).map (Fin.cons 0)

def factorMatrix (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin (factorColumns n A).length) ℚ :=
  fun i j => (factorColumns n A).get j i

end AlgorithmicThinTrees.RationalGram
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_PartitionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition geometry. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical

variable {V : Type*} [Fintype V]

variable {n m : ℕ}

def crossing (G : MultiGraph n m) (p : Setoid (Fin n)) : Finset (Fin m) :=
  univ.filter (fun e => ¬p (G.left e) (G.right e))

@[simp] lemma mem_crossing (G : MultiGraph n m) (p : Setoid (Fin n)) (e : Fin m) :
    e ∈ crossing G p ↔ ¬p (G.left e) (G.right e) := by simp [crossing]

end
end AlgorithmicThinTrees.Partitions
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_GraphRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Graph realization. -/

section

namespace AlgorithmicThinTrees.GraphStack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open scoped BigOperators

structure Graph where
  n : ℕ
  m : ℕ
  G : MultiGraph n m

abbrev graphDataCode := prodCode natCode (prodCode indicesCode indicesCode)
def Graph.data (a : Graph) :=
  (a.n,(List.ofFn (fun e => (a.G.left e).val),List.ofFn (fun e => (a.G.right e).val)))
def graphCode (a : Graph) : Word := graphDataCode a.data
abbrev view : Realizes graphCode graphDataCode Graph.data :=
  (identity graphDataCode).reindex graphCode Graph.data (fun _ => rfl)
abbrev endpoints := view.then (second natCode (prodCode indicesCode indicesCode))
abbrev lefts := endpoints.then (first indicesCode indicesCode)

abbrev Edge := Σ a : Graph, Fin a.m
abbrev edgeCode := finFamilyCode graphCode Graph.m
abbrev edgeGraph : Realizes edgeCode graphCode (fun a : Edge => a.1) := familyFirst
abbrev edgeIndex : Realizes edgeCode natCode (fun a : Edge => a.2.val) := familyIndex

def constantMatrix : Realizes (prodCode natCode ratCode) matrixCode
    (fun p => matrixData (Matrix.of (fun (_ _ : Fin p.1) => p.2))) :=
  let n := first natCode ratCode
  let q := second natCode ratCode
  ((((q.both n).then (replicateList ratCode)).both n).then
    (replicateList vectorCode)).congr (fun p => by
      change List.replicate p.1 (List.replicate p.1 p.2)=
        List.ofFn (fun _ : Fin p.1 => List.ofFn (fun _ : Fin p.1 => p.2))
      simp)

end AlgorithmicThinTrees.GraphStack

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_Inverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational inverse. -/

section


namespace AlgorithmicThinTrees.RationalInverse
open Matrix Finset
variable {n : ℕ}

def liftSolve (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ) (b : Fin (n+1) → ℚ) : Fin (n+1) → ℚ :=
  let y := B*ᵥ(fun i => b i.succ-A i.succ 0*(b 0/A 0 0))
  Fin.cons ((b 0-(fun j => A 0 j.succ) ⬝ᵥ y)/A 0 0) y

def inverse : (n : ℕ) → Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ
  | 0,_ => 1
  | n+1,A =>
    let B := inverse n (KS.W17.schurTail A)
    fun i j => liftSolve A B (Pi.single j 1) i

end AlgorithmicThinTrees.RationalInverse
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_GramWhitening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram whitening. -/

section

namespace AlgorithmicThinTrees.GramWhitening
open Matrix Finset
open scoped MatrixOrder
variable {n d m : ℕ}

def rationalFactor (P : Matrix (Fin n) (Fin n) ℚ) :=
  RationalGram.factorMatrix (RationalInverse.inverse n P)

end AlgorithmicThinTrees.GramWhitening
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_RationalSigning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational signing. -/

section

namespace AlgorithmicThinTrees.RationalSigning
open Matrix Finset CurrentKS
open scoped MatrixOrder ComplexOrder
variable {d m : ℕ}

def entry (q : ℚ) : RationalEntry := ⟨q.num,q.den,q.den_pos⟩

def input (v : Fin m → Fin d → ℚ) : CurrentKS.Input where
  d := d
  N := m
  entries e i j := (entry (v e i*v e j),entry 0)

def selected (v : Fin m → Fin d → ℚ) : Finset (Fin m) :=
  univ.filter (fun e => (CurrentKS.RationalInput.signing (input v)).getD e.val false)

end AlgorithmicThinTrees.RationalSigning
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_StackedSigning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stacked signing. -/

section

namespace AlgorithmicThinTrees.StackedSigning
open Matrix Finset
open scoped MatrixOrder
variable {a b m : ℕ}

def stack {K : Type*} (u : Fin a → K) (v : Fin b → K) : Fin (a+b) → K :=
  Fin.addCases u v

@[simp] lemma stack_left {K : Type*} (u : Fin a → K) (v : Fin b → K) (i : Fin a) :
    stack u v (Fin.castAdd b i)=u i := Fin.addCases_left i

@[simp] lemma stack_right {K : Type*} (u : Fin a → K) (v : Fin b → K) (i : Fin b) :
    stack u v (Fin.natAdd a i)=v i := Fin.addCases_right i

def selected (u : Fin m → Fin a → ℚ) (v : Fin m → Fin b → ℚ) : Finset (Fin m) :=
  RationalSigning.selected (fun e => stack (u e) (v e))

end AlgorithmicThinTrees.StackedSigning
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_FormSigning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Form signing. -/

section

namespace AlgorithmicThinTrees.FormSigning
open Matrix Finset GramWhitening StackedSigning RationalSigning
open scoped MatrixOrder
variable {a b m : ℕ}

def whiten (P : Matrix (Fin a) (Fin a) ℚ) (v : Fin m → Fin a → ℚ) :=
  fun e => (rationalFactor P)ᵀ*ᵥv e

def selected (P : Matrix (Fin a) (Fin a) ℚ) (Q : Matrix (Fin b) (Fin b) ℚ)
    (u : Fin m → Fin a → ℚ) (v : Fin m → Fin b → ℚ) : Finset (Fin m) :=
  StackedSigning.selected (whiten P u) (whiten Q v)

end AlgorithmicThinTrees.FormSigning
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_BinaryReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Binary reduction. -/

section

namespace AlgorithmicThinTrees
open StrongThinTree Finset

namespace BinaryInput

def crossing (x : BinaryInput) (S : Finset (Fin x.n)) : Finset (Fin x.p) :=
  univ.filter fun i => (x.left i ∈ S ∧ x.right i ∉ S) ∨
    (x.right i ∈ S ∧ x.left i ∉ S)

abbrev reduced (x : BinaryInput) : BinaryInput where
  n := x.n
  p := x.p
  k := x.n ^ 2
  left := x.left
  right := x.right
  ordered := x.ordered
  distinct := x.distinct
  multiplicity i := 2 * x.n ^ 2 * min (x.multiplicity i) x.k / x.k

end BinaryInput
end AlgorithmicThinTrees

namespace AlgorithmicThinTrees.BinaryInput
open StrongThinTree Finset

lemma original_copy_exists (x : BinaryInput) (e : x.reduced.Edge) :
    0 < x.multiplicity e.1 := by
  by_contra h
  have hzero : x.multiplicity e.1 = 0 := Nat.eq_zero_of_not_pos h
  have := e.2.isLt
  simp [reduced, hzero] at this

def liftCopy (x : BinaryInput) (e : x.reduced.Edge) : x.Edge :=
  ⟨e.1, ⟨0, x.original_copy_exists e⟩⟩

noncomputable def liftLabel (x : BinaryInput) (e : Fin (Fintype.card x.reduced.Edge)) :
    Fin (Fintype.card x.Edge) :=
  x.edgeEquiv (x.liftCopy (x.reduced.edgeEquiv.symm e))

end AlgorithmicThinTrees.BinaryInput

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_CanonicalExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical expansion. -/

section

namespace AlgorithmicThinTrees.BinaryInput
open StrongThinTree Finset

def copies (x : BinaryInput) : List x.Edge :=
  (List.ofFn fun i : Fin x.p => List.ofFn fun j : Fin (x.multiplicity i) =>
    (⟨i,j⟩ : x.Edge)).flatten

lemma mem_copies (x : BinaryInput) (e : x.Edge) : e ∈ x.copies := by
  rcases e with ⟨i,j⟩
  apply List.mem_flatten.mpr
  exact ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,List.mem_ofFn.mpr ⟨j,rfl⟩⟩

lemma copies_nodup (x : BinaryInput) : x.copies.Nodup := by
  rw [copies, List.nodup_flatten]
  constructor
  · intro l hl
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
    exact List.nodup_ofFn.mpr (fun j k h => by cases h; rfl)
  · apply List.pairwise_iff_get.mpr
    intro i j hij
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    apply List.disjoint_left.mpr
    intro e he hf
    obtain ⟨a,ha⟩ := List.mem_ofFn.mp he
    obtain ⟨b,hb⟩ := List.mem_ofFn.mp hf
    have heq := congrArg Sigma.fst (ha.trans hb.symm)
    exact (ne_of_lt hij) (Fin.ext (by simpa using congrArg Fin.val heq))

noncomputable def copiesEquiv (x : BinaryInput) : Fin x.copies.length ≃ x.Edge :=
  Equiv.ofBijective x.copies.get ⟨x.copies_nodup.injective_get,
    fun e => List.mem_iff_get.mp (x.mem_copies e)⟩

@[simp] lemma copiesEquiv_apply (x : BinaryInput) (e : Fin x.copies.length) :
    x.copiesEquiv e = x.copies.get e := rfl

def expanded (x : BinaryInput) : MultiGraph x.n x.copies.length where
  left e := x.left (x.copies.get e).1
  right e := x.right (x.copies.get e).1
  loopless e := ne_of_lt (x.ordered (x.copies.get e).1)

noncomputable def labelEquiv (x : BinaryInput) :
    Fin x.copies.length ≃ Fin (Fintype.card x.Edge) := x.copiesEquiv.trans x.edgeEquiv

@[simp] lemma labelEquiv_left (x : BinaryInput) (e : Fin x.copies.length) :
    x.graph.left (x.labelEquiv e) = x.expanded.left e := by
  simp [graph,labelEquiv,expanded]
@[simp] lemma labelEquiv_right (x : BinaryInput) (e : Fin x.copies.length) :
    x.graph.right (x.labelEquiv e) = x.expanded.right e := by
  simp [graph,labelEquiv,expanded]

def originalCopy (x : BinaryInput) (e : Fin x.reduced.copies.length) : x.Edge :=
  x.liftCopy (x.reduced.copies.get e)

noncomputable def originalLabel (x : BinaryInput) (e : Fin x.reduced.copies.length) :
    Fin (Fintype.card x.Edge) := x.edgeEquiv (x.originalCopy e)

lemma copies_map (x : BinaryInput) {α : Type*} (f : Fin x.p → α) :
    x.copies.map (fun e => f e.1) =
      (List.ofFn fun i : Fin x.p => List.replicate (x.multiplicity i) (f i)).flatten := by
  simp only [copies,List.map_flatten,List.map_ofFn,Function.comp_def]
  simp

lemma expanded_lefts (x : BinaryInput) :
    List.ofFn (fun e => (x.expanded.left e).val) =
      (List.ofFn fun i : Fin x.p => List.replicate (x.multiplicity i) (x.left i).val).flatten := by
  rw [←copies_map]
  simpa only [List.map_ofFn,Function.comp_def,expanded] using
    congrArg (List.map (fun e : x.Edge => (x.left e.1).val)) (List.ofFn_get x.copies)
lemma expanded_rights (x : BinaryInput) :
    List.ofFn (fun e => (x.expanded.right e).val) =
      (List.ofFn fun i : Fin x.p => List.replicate (x.multiplicity i) (x.right i).val).flatten := by
  rw [←copies_map]
  simpa only [List.map_ofFn,Function.comp_def,expanded] using
    congrArg (List.map (fun e : x.Edge => (x.right e.1).val)) (List.ofFn_get x.copies)
lemma expanded_records (x : BinaryInput) :
    List.ofFn (fun e : Fin x.copies.length => (x.copies.get e).1.val) =
      (List.ofFn fun i : Fin x.p => List.replicate (x.multiplicity i) i.val).flatten := by
  rw [←copies_map]
  simpa only [List.map_ofFn,Function.comp_def,expanded] using
    congrArg (List.map (fun e : x.Edge => e.1.val)) (List.ofFn_get x.copies)

end AlgorithmicThinTrees.BinaryInput
end

end OAI
end


