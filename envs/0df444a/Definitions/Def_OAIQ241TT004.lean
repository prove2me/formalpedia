-- Prove2me | Definitions.Def_OAIQ241TT004
-- name    : OAIQ241TT004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:51:15.042223+00:00
-- url     : https://prove2.me/theorems/842deec3-08e2-4523-aa28-78fa1b6edf03
-- title:
--   Definitions bundle OAIQ241TT004 of the split of OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 378 declarations of OpenAI's Lean: 225 definitions and 153 theorems. The definitions and types are `OAI.AlgorithmicThinTrees.GraphStack.edgeLeft`, `OAI.AlgorithmicThinTrees.GraphStack.edgeRight`, `OAI.AlgorithmicThinTrees.GraphStack.numVertices`, `OAI.AlgorithmicThinTrees.GraphStack.rights`, `OAI.CurrentKS.ArithmeticRoutine.decodeLeft`, `OAI.CurrentKS.ArithmeticRoutine.encode`, `OAI.CurrentKS.ArithmeticRoutine.program`, `OAI.CurrentKS.ArithmeticRoutine.ticks`, `OAI.CurrentKS.CompareRoutine.decode`, `OAI.CurrentKS.CompareRoutine.extract`, `OAI.CurrentKS.CompareRoutine.prepend`, `OAI.CurrentKS.CompareRoutine.program`, `OAI.CurrentKS.CompareRoutine.routine`, `OAI.CurrentKS.CompareRoutine.ticks`, `OAI.CurrentKS.Realization.Realizes.le`, `OAI.CurrentKS.Realization.binaryNatCode`, `OAI.CurrentKS.Realization.getD`, `OAI.CurrentKS.Realization.lookupStepRealizes`, `OAI.CurrentKS.Realization.ratLE`, `OAI.KS.W01.BinaryAdder.addEntry`, `OAI.KS.W01.BinaryAdder.cfg`, `OAI.KS.W01.BinaryAdder.dispatch`, `OAI.KS.W01.BinaryAdder.finishEntry`, `OAI.KS.W01.BinaryAdder.machine`, `OAI.KS.W01.BinaryAdder.normalizedMachine`, `OAI.KS.W01.MagnitudeProgram.carryMachine`, `OAI.KS.W01.MagnitudeProgram.program`, `OAI.KS.W01.SignedRationalSerializer.negativeBranch`, `OAI.KS.W01.SignedRationalSerializer.positiveBranch`, `OAI.KS.W01.SignedRationalSerializer.program`, `OAI.KS.W01.SignedRationalSerializer.pushDispatch`, `OAI.KS.W01.SignedRationalSerializer.pushOne`, `OAI.KS.W01.SignedRationalSerializer.rawWire`, `OAI.KS.W01.SignedRationalSerializer.selector`, `OAI.KS.W01.SignedRationalSerializer.signedWire`, `OAI.KS.W01.SignedSerializePrimitives.pairMachine`, `OAI.KS.W01.SignedSerializePrimitives.pairProgram`, `OAI.KS.W01.SignedSerializePrimitives.subtractProgram`, `OAI.KS.W01.WireMagnitude.wireInt`, `OAI.KS.W01.WireMagnitude.wireRat` and 185 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `MatrixSigning_Arithmetic_ArithmeticEncodingSize`, `MatrixSigning_Arithmetic_BinaryAdder`, `MatrixSigning_Arithmetic_BinaryAdderCompose`, `MatrixSigning_Arithmetic_BinaryDivision`, `MatrixSigning_Arithmetic_BinaryMultiply`, `MatrixSigning_Arithmetic_BinarySubtractor`, `MatrixSigning_Arithmetic_BorrowSubtractor`, `MatrixSigning_Arithmetic_CanonicalSubtraction`, `MatrixSigning_Arithmetic_CleanRationalCompare`, `MatrixSigning_Arithmetic_DivisionMachine`, `MatrixSigning_Arithmetic_FixedSubtraction`, `MatrixSigning_Arithmetic_GCDMachine`, `MatrixSigning_Arithmetic_MultiplicationBody`, `MatrixSigning_Arithmetic_MultiplicationLoop`, `MatrixSigning_Arithmetic_MultiplicationNormalize`, `MatrixSigning_Arithmetic_RationalAddPrimitives`, `MatrixSigning_Arithmetic_RationalAddProducts`, `MatrixSigning_Arithmetic_RationalAddProgram`, `MatrixSigning_Arithmetic_RationalAddSigned`, `MatrixSigning_Arithmetic_RationalCompareBranch`, `MatrixSigning_Arithmetic_RationalCompareCorrectness`, `MatrixSigning_Arithmetic_RationalCompareParser`, `MatrixSigning_Arithmetic_RationalComparePrimitives`, `MatrixSigning_Arithmetic_RationalCompareProgram`, `MatrixSigning_Arithmetic_RationalDivisionMachine`, `MatrixSigning_Arithmetic_RationalDivisionStages`, `MatrixSigning_Arithmetic_RationalMagnitudeMachine`, `MatrixSigning_Arithmetic_RationalMultiplicationMachine`, `MatrixSigning_Arithmetic_RationalMultiplyNormalize`, `MatrixSigning_Arithmetic_RationalMultiplyProducts`, `MatrixSigning_Arithmetic_RationalReciprocalCore`, `MatrixSigning_Arithmetic_RationalReciprocalMachine`, `MatrixSigning_Arithmetic_RationalReciprocalSerialize`, `MatrixSigning_Arithmetic_RationalReciprocalSwap`, `MatrixSigning_Arithmetic_RationalSignAction`, `MatrixSigning_Arithmetic_RationalSubtractProgram`, `MatrixSigning_Arithmetic_SignedRationalSerializer`, `MatrixSigning_Arithmetic_SingleRationalParser`, `MatrixSigning_Arithmetic_SubtractorSequential`, `MatrixSigning_Encoding_BinaryEncoding`, `MatrixSigning_Encoding_PositiveWireSerializer`, `MatrixSigning_Encoding_UnsignedPairSerializer`, `MatrixSigning_Encoding_WireMagnitude`, `MatrixSigning_Encoding_WireProgramPrimitives`, `MatrixSigning_Machines_BinaryMachine`, `MatrixSigning_Machines_BinaryNormalize`, `MatrixSigning_Machines_BinaryTrimMachine`, `MatrixSigning_Machines_ExpressionPrimitives`, `MatrixSigning_Machines_FixedCanonicalize`, `MatrixSigning_Machines_FixedCompare`, `MatrixSigning_Machines_FixedCopyRestore`, `MatrixSigning_Machines_FixedDotPrimitives`, `MatrixSigning_Machines_FixedRun`, `MatrixSigning_Machines_FixedStackMachine`, `MatrixSigning_Machines_LittleEndianCompare`, `MatrixSigning_Machines_MachineCombinators`, `MatrixSigning_Machines_MachineRoundTrip`, `MatrixSigning_Machines_MagnitudeProgram`, `MatrixSigning_Machines_NormalizeOutput`, `MatrixSigning_Machines_Sequential`, `MatrixSigning_Machines_SignedSerializePrimitives`, `MatrixSigning_Realization_ArithmeticRoutine`, `MatrixSigning_Realization_ArrayRealization`, `MatrixSigning_Realization_BinaryNaturalRealization`, `MatrixSigning_Realization_CompareRoutine`, `MatrixSigning_Realization_ScalarRealization`, `ThinTrees_Encoding_GraphRealization`.
--
--   **Imports.** It imports the published bundle `Def_AlgorithmicThinTrees`; the bundles `OAIQ241TT000` and `OAIQ241TT001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ241TT007`, `OAIQ241TT008` and `OAIQ241TT009`.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT000
import Definitions.Def_OAIQ241TT001

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_BinaryEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01

@[simp] theorem natPayloadLength_eq_size (n : ℕ) : natPayloadLength n = Nat.size n := by
  unfold natPayloadLength Computability.encodeNat
  rw [length_encodeNum, Num.natSize_to_nat, Num.to_of_nat]

end KS.W01

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ArithmeticEncodingSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01

def ratLength (q : ℚ) : ℕ := (encodeRat q).length

end KS.W01

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19

theorem encodeNat_length_eq_size (n : ℕ) : (Computability.encodeNat n).length = Nat.size n :=
  KS.W01.natPayloadLength_eq_size n

end KS.W19

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_BinaryMachine
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W29

theorem StackAction.length_apply_le (a : StackAction) (xs : List Bool) :
    (a.apply xs).length ≤ xs.length + 1 := by
  cases a <;> cases xs <;> simp [StackAction.apply]
  omega

end KS.W29

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryAdder
attribute [-simp] _root_.OAI.KS.W01.FixedStack.lift3_project_init _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.BinaryMachine.withEntry_init_stacks _root_.OAI.KS.W29.BinaryMachine.withEntry_init_state _root_.OAI.KS.W29.BinaryMachine.withEntry_initial _root_.OAI.KS.W29.BinaryMachine.withEntry_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W01.BinaryAdder
open KS.W29
open KS.W19 (bitsValue digit)

def finishEntry (c : Bool) : Instruction 2 :=
  ⟨none, .stay, .stay, if c then .push true else .stay⟩

def addEntry (c a b : Bool) : Instruction 2 :=
  ⟨some (carryState (carryBit a b c)), .pop, .pop, .push (sumBit a b c)⟩

def dispatch (s : Fin 2) (heads : Fin 27) (_coin : Bool) : Instruction 2 :=
  let c := s.val == 1
  let left := heads.val % 3
  let right := heads.val / 3 % 3
  if left = 0 ∧ right = 0 then finishEntry c
  else addEntry c (left == 2) (right == 2)

def machine : BinaryMachine := FiniteDispatch.compile 0 dispatch

def cfg (state : Option (Fin 2)) (xs ys zs : List Bool) : Config 2 :=
  ⟨state, fun j => if j = 0 then xs else if j = 1 then ys else zs⟩

theorem table_lookup (s : Fin 2) (c : Config 2) (coin : Bool) :
    machine.table.getD (transitionIndex s c coin) (Instruction.halt 2) =
      if topCode (c.«stacks» 0) = 0 ∧ topCode (c.«stacks» 1) = 0 then
        finishEntry (s.val == 1)
      else addEntry (s.val == 1) (topCode (c.«stacks» 0) == 2)
        (topCode (c.«stacks» 1) == 2) := by
  have h0 := topCode_lt_three (c.«stacks» 0)
  have h1 := topCode_lt_three (c.«stacks» 1)
  have h2 := topCode_lt_three (c.«stacks» 2)
  have hl : headCode c % 3 = topCode (c.«stacks» 0) := by unfold headCode; omega
  have hr : headCode c / 3 % 3 = topCode (c.«stacks» 1) := by unfold headCode; omega
  unfold machine
  rw [FiniteDispatch.lookup_compile]
  simp only [dispatch, hl, hr]
  rfl

theorem step_left_cons (c a : Bool) (xs ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some (carryState c)) (a :: xs) ys zs) coin =
      cfg (some (carryState (carryBit a (ys.headD false) c))) xs ys.tail
        (sumBit a (ys.headD false) c :: zs) := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases c <;> cases a <;> cases ys with
  | nil =>
      change Config.mk _ _ = Config.mk _ _
      congr 1
      funext j
      fin_cases j <;> rfl
  | cons b ys =>
      cases b <;> change Config.mk _ _ = Config.mk _ _
      all_goals
        congr 1
        funext j
        fin_cases j <;> rfl

theorem step_right_cons (c b : Bool) (ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some (carryState c)) [] (b :: ys) zs) coin =
      cfg (some (carryState (carryBit false b c))) [] ys
        (sumBit false b c :: zs) := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases c <;> cases b <;> change Config.mk _ _ = Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem step_done (c : Bool) (zs : List Bool) (coin : Bool) :
    machine.step (cfg (some (carryState c)) [] [] zs) coin =
      cfg none [] [] ((if c then [true] else []) ++ zs) := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases c <;> change Config.mk none _ = Config.mk none _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem run_add (c : Bool) (xs ys zs bits : List Bool)
    (hlen : bits.length = max xs.length ys.length + 1) :
    machine.run (cfg (some (carryState c)) xs ys zs) bits =
      cfg none [] [] ((addBits c xs ys).reverse ++ zs) := by
  induction xs generalizing c ys zs bits with
  | nil =>
      induction ys generalizing c zs bits with
      | nil =>
          cases bits with
          | nil => simp at hlen
          | cons coin rest =>
              have hr : rest = [] := by
                apply List.length_eq_zero_iff.mp
                simp only [List.length_cons, List.length_nil, max_self] at hlen
                omega
              subst rest
              erw [BinaryMachine.run.eq_2, step_done]
              cases c <;> simp [BinaryMachine.run, addBits] <;> rfl
      | cons b ys ih =>
          cases bits with
          | nil => simp at hlen
          | cons coin rest =>
              have hr : rest.length = max ([] : List Bool).length ys.length + 1 := by
                simp only [List.length_nil, List.length_cons, Nat.zero_max] at hlen ⊢
                omega
              erw [BinaryMachine.run.eq_2, step_right_cons, ih _ _ _ hr]
              simp [addBits, List.reverse_cons, List.append_assoc]
              rfl
  | cons a xs ih =>
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
          cases ys with
          | nil =>
              have hr : rest.length = max xs.length ([] : List Bool).length + 1 := by
                simp only [List.length_nil, List.length_cons, Nat.max_zero] at hlen ⊢
                omega
              erw [BinaryMachine.run.eq_2, step_left_cons]
              simp only [List.headD_nil, List.tail_nil]
              rw [ih _ _ _ _ hr]
              simp [addBits, List.reverse_cons, List.append_assoc]
              rfl
          | cons b ys =>
              have hr : rest.length = max xs.length ys.length + 1 := by
                simp only [List.length_cons] at hlen
                omega
              erw [BinaryMachine.run.eq_2, step_left_cons]
              simp only [List.headD_cons, List.tail_cons]
              rw [ih _ _ _ _ hr]
              simp [addBits, List.reverse_cons, List.append_assoc]
              rfl

end KS.W01.BinaryAdder

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_Sequential
attribute [-simp] _root_.OAI.KS.W01.FixedStack.lift3_project_init _root_.OAI.KS.W01.FixedStack.liftInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftInstruction_on_port _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.BinaryMachine.withEntry_init_stacks _root_.OAI.KS.W29.BinaryMachine.withEntry_init_state _root_.OAI.KS.W29.BinaryMachine.withEntry_initial _root_.OAI.KS.W29.BinaryMachine.withEntry_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W29
namespace Sequential

def leftState (M N : BinaryMachine) (s : Fin M.states) : Fin (M.states + N.states) :=
  ⟨s.val, by have h := s.isLt; omega⟩

def rightState (M N : BinaryMachine) (s : Fin N.states) : Fin (M.states + N.states) :=
  ⟨M.states + s.val, by have h := s.isLt; omega⟩

def liftLeft (M N : BinaryMachine) (c : Config M.states) : Config (M.states + N.states) :=
  ⟨some (match c.state with
      | none => rightState M N N.initial
      | some s => leftState M N s), c.«stacks»⟩

def liftRight (M N : BinaryMachine) (c : Config N.states) : Config (M.states + N.states) :=
  ⟨c.state.map (rightState M N), c.«stacks»⟩

def leftInstruction (M N : BinaryMachine) (i : Instruction M.states) :
    Instruction (M.states + N.states) :=
  ⟨some (match i.next with
      | none => rightState M N N.initial
      | some s => leftState M N s), i.first, i.second, i.third⟩

def rightInstruction (M N : BinaryMachine) (i : Instruction N.states) :
    Instruction (M.states + N.states) :=
  ⟨i.next.map (rightState M N), i.first, i.second, i.third⟩

def fetch (M : BinaryMachine) (s : Fin M.states) (heads : Fin 27) (b : Bool) :
    Instruction M.states :=
  M.table.getD (54 * s.val + 2 * heads.val + bitCode b) (Instruction.halt M.states)

def dispatch (M N : BinaryMachine) (s : Fin (M.states + N.states))
    (heads : Fin 27) (b : Bool) : Instruction (M.states + N.states) :=
  if h : s.val < M.states then
    leftInstruction M N (fetch M ⟨s.val, h⟩ heads b)
  else
    rightInstruction M N
      (fetch N ⟨s.val - M.states, by have hs := s.isLt; omega⟩ heads b)

def compose (M N : BinaryMachine) : BinaryMachine :=
  FiniteDispatch.compile (leftState M N M.initial) (dispatch M N)

theorem dispatch_left (M N : BinaryMachine) (s : Fin M.states) (heads : Fin 27) (b : Bool) :
    dispatch M N (leftState M N s) heads b = leftInstruction M N (fetch M s heads b) := by
  simp [dispatch, leftState, s.isLt]

theorem dispatch_right (M N : BinaryMachine) (s : Fin N.states) (heads : Fin 27) (b : Bool) :
    dispatch M N (rightState M N s) heads b = rightInstruction M N (fetch N s heads b) := by
  simp [dispatch, rightState]

theorem step_left (M N : BinaryMachine) (s : Fin M.states) («stacks» : Fin 3 → List Bool)
    (b : Bool) :
    (compose M N).step ⟨some (leftState M N s), «stacks»⟩ b =
      liftLeft M N (M.step ⟨some s, «stacks»⟩ b) := by
  unfold compose
  rw [FiniteDispatch.step_compile]
  dsimp only
  rw [dispatch_left]
  rfl

theorem step_right (M N : BinaryMachine) (s : Fin N.states) («stacks» : Fin 3 → List Bool)
    (b : Bool) :
    (compose M N).step ⟨some (rightState M N s), «stacks»⟩ b =
      liftRight M N (N.step ⟨some s, «stacks»⟩ b) := by
  unfold compose
  rw [FiniteDispatch.step_compile]
  dsimp only
  rw [dispatch_right]
  rfl

theorem step_liftRight (M N : BinaryMachine) (c : Config N.states) (b : Bool) :
    (compose M N).step (liftRight M N c) b = liftRight M N (N.step c b) := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s => exact step_right M N s «stacks» b

theorem run_liftRight (M N : BinaryMachine) (c : Config N.states) (bits : List Bool) :
    (compose M N).run (liftRight M N c) bits = liftRight M N (N.run c bits) := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      change (compose M N).run ((compose M N).step (liftRight M N c) b) bs =
        liftRight M N (N.run (N.step c b) bs)
      erw [step_liftRight M N c b]
      exact ih (N.step c b)

def ActiveFor (M : BinaryMachine) : Config M.states → List Bool → Prop
  | _, [] => True
  | c, b :: bs => c.state ≠ none ∧ ActiveFor M (M.step c b) bs

def HaltsAfter (M : BinaryMachine) (c : Config M.states) (bits : List Bool) : Prop :=
  ActiveFor M c bits ∧ (M.run c bits).state = none

theorem step_liftLeft (M N : BinaryMachine) (c : Config M.states) (b : Bool)
    (h : c.state ≠ none) :
    (compose M N).step (liftLeft M N c) b = liftLeft M N (M.step c b) := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => exact (h rfl).elim
  | some s => exact step_left M N s «stacks» b

theorem run_liftLeft (M N : BinaryMachine) (c : Config M.states) (bits : List Bool)
    (h : ActiveFor M c bits) :
    (compose M N).run (liftLeft M N c) bits = liftLeft M N (M.run c bits) := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      change (compose M N).run ((compose M N).step (liftLeft M N c) b) bs =
        liftLeft M N (M.run (M.step c b) bs)
      erw [step_liftLeft M N c b h.1]
      exact ih _ h.2

theorem run_compose (M N : BinaryMachine) (c : Config M.states) (first second : List Bool)
    (h : HaltsAfter M c first) :
    (compose M N).run (liftLeft M N c) (first ++ second) =
      liftRight M N (N.run ⟨some N.initial, (M.run c first).«stacks»⟩ second) := by
  erw [BinaryMachine.run_append, run_liftLeft M N c first h.1]
  have he : liftLeft M N (M.run c first) =
      liftRight M N ⟨some N.initial, (M.run c first).«stacks»⟩ := by
    simp [liftLeft, liftRight, h.2]
  rw [he, run_liftRight]

end Sequential
end KS.W29

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_NormalizeOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W29
namespace NormalizeOutput

theorem compose_result (M : BinaryMachine) (c : Config M.states)
    (first second input result : List Bool)
    (hfirst : Sequential.HaltsAfter M c first)
    (hstack : (M.run c first).«stacks» =
      (FrameDecoder.config (some machine.initial) input [] result.reverse).«stacks»)
    (hsecond : second.length = result.length + 1) :
    (Sequential.compose M machine).run (Sequential.liftLeft M machine c) (first ++ second) =
      Sequential.liftRight M machine (FrameDecoder.config none input result []) := by
  rw [Sequential.run_compose M machine c first second hfirst]
  have hc : (⟨some machine.initial, (M.run c first).«stacks»⟩ : Config machine.states) =
      FrameDecoder.config (some machine.initial) input [] result.reverse := by
    rw [hstack]
    rfl
  rw [hc, run_reversed input result second hsecond]

end NormalizeOutput
end KS.W29

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryAdderCompose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W01.BinaryAdder
open KS.W29
open KS.W19 (bitsValue digit)

theorem activeFor_of_length_le (c : Bool) (xs ys zs bits : List Bool)
    (hlen : bits.length ≤ max xs.length ys.length + 1) :
    Sequential.ActiveFor machine (cfg (some (carryState c)) xs ys zs) bits := by
  induction bits generalizing c xs ys zs with
  | nil => trivial
  | cons coin rest ih =>
      constructor
      · exact Option.some_ne_none _
      · cases xs with
        | nil =>
            cases ys with
            | nil =>
                have hr : rest = [] := by
                  apply List.length_eq_zero_iff.mp
                  simp only [List.length_cons, List.length_nil, max_self] at hlen
                  omega
                subst rest
                trivial
            | cons b ys =>
                rw [step_right_cons]
                apply ih
                simp only [List.length_nil, List.length_cons, Nat.zero_max] at hlen ⊢
                omega
        | cons a xs =>
            rw [step_left_cons]
            apply ih
            cases ys with
            | nil =>
                simp only [List.tail_nil, List.length_nil, List.length_cons, Nat.max_zero]
                  at hlen ⊢
                omega
            | cons b ys =>
                simp only [List.tail_cons, List.length_cons] at hlen ⊢
                omega

theorem haltsAfter (c : Bool) (xs ys zs bits : List Bool)
    (hlen : bits.length = max xs.length ys.length + 1) :
    Sequential.HaltsAfter machine (cfg (some (carryState c)) xs ys zs) bits := by
  constructor
  · exact activeFor_of_length_le c xs ys zs bits hlen.le
  · rw [run_add c xs ys zs bits hlen]
    rfl

def normalizedMachine : BinaryMachine := Sequential.compose machine NormalizeOutput.machine

end KS.W01.BinaryAdder

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_BinaryNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19

theorem trimBits_length_eq_size (xs : List Bool) :
    (trimBits xs).length = Nat.size (bitsValue xs) := by
  rw [trimBits_eq_encodeNat, encodeNat_length_eq_size]

theorem trimBits_length_le_of_value_lt (xs : List Bool) (k : ℕ)
    (hx : bitsValue xs < 2 ^ k) : (trimBits xs).length ≤ k := by
  rw [trimBits_length_eq_size]
  exact Nat.size_le.mpr hx

end KS.W19

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryMultiply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W03.BinaryMultiply

open KS.W19
open KS.W01.BinaryAdder

theorem multiply_length_le (xs ys : List Bool) :
    (multiply xs ys).length ≤ xs.length + ys.length := by
  apply trimBits_length_le_of_value_lt
  rw [multiplyRaw_correct, pow_add]
  have hx := bitsValue_lt_two_pow_length xs
  have hy := bitsValue_lt_two_pow_length ys
  have hp : 0 < 2 ^ ys.length := pow_pos (by decide) _
  exact lt_of_le_of_lt (Nat.mul_le_mul_left (bitsValue xs) hy.le)
    (Nat.mul_lt_mul_of_pos_right hx hp)

end KS.W03.BinaryMultiply

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinarySubtractor
attribute [-simp] _root_.OAI.KS.W01.FixedStack.lift3_project_init _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.BinaryMachine.withEntry_init_stacks _root_.OAI.KS.W29.BinaryMachine.withEntry_init_state _root_.OAI.KS.W29.BinaryMachine.withEntry_initial _root_.OAI.KS.W29.BinaryMachine.withEntry_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.BinarySubtractor
open KS.W29
open KS.W19 (bitsValue digit differenceDigit nextBorrow subtractBits)

def finishEntry (_ : Bool) : Instruction 2 :=
  ⟨none, .stay, .stay, .stay⟩

def subEntry (c a b : Bool) : Instruction 2 :=
  ⟨some (borrowState (nextBorrow a b c)), .pop, .pop, .push (differenceDigit a b c)⟩

def dispatch (s : Fin 2) (heads : Fin 27) (_coin : Bool) : Instruction 2 :=
  let c := s.val == 1
  let left := heads.val % 3
  let right := heads.val / 3 % 3
  if left = 0 ∧ right = 0 then finishEntry c
  else subEntry c (left == 2) (right == 2)

def machine : BinaryMachine := FiniteDispatch.compile 0 dispatch

def cfg (state : Option (Fin 2)) (xs ys zs : List Bool) : Config 2 :=
  ⟨state, fun j => if j = 0 then xs else if j = 1 then ys else zs⟩

theorem table_lookup (s : Fin 2) (c : Config 2) (coin : Bool) :
    machine.table.getD (transitionIndex s c coin) (Instruction.halt 2) =
      if topCode (c.«stacks» 0) = 0 ∧ topCode (c.«stacks» 1) = 0 then
        finishEntry (s.val == 1)
      else subEntry (s.val == 1) (topCode (c.«stacks» 0) == 2)
        (topCode (c.«stacks» 1) == 2) := by
  have h0 := topCode_lt_three (c.«stacks» 0)
  have h1 := topCode_lt_three (c.«stacks» 1)
  have h2 := topCode_lt_three (c.«stacks» 2)
  have hl : headCode c % 3 = topCode (c.«stacks» 0) := by unfold headCode; omega
  have hr : headCode c / 3 % 3 = topCode (c.«stacks» 1) := by unfold headCode; omega
  unfold machine
  rw [FiniteDispatch.lookup_compile]
  simp only [dispatch, hl, hr]
  rfl

theorem step_left_cons (c a : Bool) (xs ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some (borrowState c)) (a :: xs) ys zs) coin =
      cfg (some (borrowState (nextBorrow a (ys.headD false) c))) xs ys.tail
        (differenceDigit a (ys.headD false) c :: zs) := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases c <;> cases a <;> cases ys with
  | nil =>
      change Config.mk _ _ = Config.mk _ _
      congr 1
      funext j
      fin_cases j <;> rfl
  | cons b ys =>
      cases b <;> change Config.mk _ _ = Config.mk _ _
      all_goals
        congr 1
        funext j
        fin_cases j <;> rfl

theorem step_right_cons (c b : Bool) (ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some (borrowState c)) [] (b :: ys) zs) coin =
      cfg (some (borrowState (nextBorrow false b c))) [] ys
        (differenceDigit false b c :: zs) := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases c <;> cases b <;> change Config.mk _ _ = Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem step_done (c : Bool) (zs : List Bool) (coin : Bool) :
    machine.step (cfg (some (borrowState c)) [] [] zs) coin =
      cfg none [] [] zs := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases c <;> change Config.mk none _ = Config.mk none _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem run_sub (c : Bool) (xs ys zs bits : List Bool)
    (hlen : bits.length = max xs.length ys.length + 1) :
    machine.run (cfg (some (borrowState c)) xs ys zs) bits =
      cfg none [] [] ((subtractBits xs ys c).reverse ++ zs) := by
  induction xs generalizing c ys zs bits with
  | nil =>
      induction ys generalizing c zs bits with
      | nil =>
          cases bits with
          | nil => simp at hlen
          | cons coin rest =>
              have hr : rest = [] := by
                apply List.length_eq_zero_iff.mp
                simp only [List.length_cons, List.length_nil, max_self] at hlen
                omega
              subst rest
              erw [BinaryMachine.run.eq_2, step_done]
              cases c <;> simp [BinaryMachine.run, subtractBits] <;> rfl
      | cons b ys ih =>
          cases bits with
          | nil => simp at hlen
          | cons coin rest =>
              have hr : rest.length = max ([] : List Bool).length ys.length + 1 := by
                simp only [List.length_nil, List.length_cons, Nat.zero_max] at hlen ⊢
                omega
              erw [BinaryMachine.run.eq_2, step_right_cons, ih _ _ _ hr]
              simp [subtractBits, List.reverse_cons, List.append_assoc]
              rfl
  | cons a xs ih =>
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
          cases ys with
          | nil =>
              have hr : rest.length = max xs.length ([] : List Bool).length + 1 := by
                simp only [List.length_nil, List.length_cons, Nat.max_zero] at hlen ⊢
                omega
              erw [BinaryMachine.run.eq_2, step_left_cons]
              simp only [List.headD_nil, List.tail_nil]
              rw [ih _ _ _ _ hr]
              simp [subtractBits, List.reverse_cons, List.append_assoc]
              rfl
          | cons b ys =>
              have hr : rest.length = max xs.length ys.length + 1 := by
                simp only [List.length_cons] at hlen
                omega
              erw [BinaryMachine.run.eq_2, step_left_cons]
              simp only [List.headD_cons, List.tail_cons]
              rw [ih _ _ _ _ hr]
              simp [subtractBits, List.reverse_cons, List.append_assoc]
              rfl

end KS.W19.BinarySubtractor

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BorrowSubtractor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.BorrowSubtractor
open KS.W29
open KS.W19 (bitsValue digit differenceDigit nextBorrow subtractBits)

def finishEntry (c : Bool) : Instruction 2 :=
  ⟨none, .push c, .stay, .stay⟩

def subEntry (c a b : Bool) : Instruction 2 :=
  ⟨some (borrowState (nextBorrow a b c)), .pop, .pop, .push (differenceDigit a b c)⟩

def dispatch (s : Fin 2) (heads : Fin 27) (_coin : Bool) : Instruction 2 :=
  let c := s.val == 1
  let left := heads.val % 3
  let right := heads.val / 3 % 3
  if left = 0 ∧ right = 0 then finishEntry c
  else subEntry c (left == 2) (right == 2)

def machine : BinaryMachine := FiniteDispatch.compile 0 dispatch

end KS.W19.BorrowSubtractor

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_SubtractorSequential
attribute [-simp] _root_.OAI.KS.W01.FixedStack.lift3_project_init _root_.OAI.KS.W19.FixedRun.pack_on_port
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.BinarySubtractor
open KS.W29
open KS.W29.Sequential

theorem activeFor_sub (c : Bool) (xs ys zs bits : List Bool)
    (hlen : bits.length = max xs.length ys.length + 1) :
    ActiveFor machine (cfg (some (borrowState c)) xs ys zs) bits := by
  induction xs generalizing c ys zs bits with
  | nil =>
    induction ys generalizing c zs bits with
    | nil =>
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
        have hr : rest = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons, List.length_nil, max_self] at hlen
          omega
        subst rest
        exact ⟨Option.some_ne_none _, trivial⟩
    | cons b ys ih =>
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
        have hr : rest.length = max ([] : List Bool).length ys.length + 1 := by
          simp only [List.length_cons, List.length_nil, Nat.zero_max] at hlen ⊢
          omega
        refine ⟨Option.some_ne_none _, ?_⟩
        rw [step_right_cons]
        exact ih _ _ _ hr
  | cons a xs ih =>
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      refine ⟨Option.some_ne_none _, ?_⟩
      cases ys with
      | nil =>
        have hr : rest.length = max xs.length ([] : List Bool).length + 1 := by
          simp only [List.length_cons, List.length_nil, Nat.max_zero] at hlen ⊢
          omega
        rw [step_left_cons]
        simp only [List.headD_nil, List.tail_nil]
        exact ih _ _ _ _ hr
      | cons b ys =>
        have hr : rest.length = max xs.length ys.length + 1 := by
          simp only [List.length_cons] at hlen
          omega
        rw [step_left_cons]
        simp only [List.headD_cons, List.tail_cons]
        exact ih _ _ _ _ hr

theorem haltsAfter_sub (c : Bool) (xs ys zs bits : List Bool)
    (hlen : bits.length = max xs.length ys.length + 1) :
    HaltsAfter machine (cfg (some (borrowState c)) xs ys zs) bits := by
  refine ⟨activeFor_sub c xs ys zs bits hlen, ?_⟩
  rw [run_sub c xs ys zs bits hlen]
  rfl

end KS.W19.BinarySubtractor

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_BinaryTrimMachine
attribute [-simp] _root_.OAI.KS.W01.FixedStack.lift3_project_init _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.BinaryMachine.withEntry_init_stacks _root_.OAI.KS.W29.BinaryMachine.withEntry_init_state _root_.OAI.KS.W29.BinaryMachine.withEntry_initial _root_.OAI.KS.W29.BinaryMachine.withEntry_step _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.BinaryTrimMachine
open KS.W29

def cfg (s : Option (Fin 2)) (input output scratch : List Bool) : Config 2 :=
  ⟨s, fun j => if j = 0 then input else if j = 1 then output else scratch⟩

theorem table_lookup (s : Fin 2) (c : Config 2) (coin : Bool) :
    machine.table.getD (transitionIndex s c coin) (Instruction.halt 2) =
      if topCode (c.«stacks» 2) = 0 then Instruction.halt 2
      else if s = 0 ∧ topCode (c.«stacks» 2) = 1 then ⟨some 0, .stay, .stay, .pop⟩
      else ⟨some 1, .stay, .push (topCode (c.«stacks» 2) == 2), .pop⟩ := by
  have h0 := topCode_lt_three (c.«stacks» 0)
  have h1 := topCode_lt_three (c.«stacks» 1)
  have h2 := topCode_lt_three (c.«stacks» 2)
  have htop : headCode c / 9 = topCode (c.«stacks» 2) := by unfold headCode; omega
  unfold machine
  rw [FiniteDispatch.lookup_compile]
  simp only [dispatch, htop]
  rfl

theorem step_skip (input output scratch : List Bool) (coin : Bool) :
    machine.step (cfg (some 0) input output (false :: scratch)) coin =
      cfg (some 0) input output scratch := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  change Config.mk _ _ = Config.mk _ _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem step_first_one (input output scratch : List Bool) (coin : Bool) :
    machine.step (cfg (some 0) input output (true :: scratch)) coin =
      cfg (some 1) input (true :: output) scratch := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  change Config.mk _ _ = Config.mk _ _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem step_copy (b : Bool) (input output scratch : List Bool) (coin : Bool) :
    machine.step (cfg (some 1) input output (b :: scratch)) coin =
      cfg (some 1) input (b :: output) scratch := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases b <;> change Config.mk _ _ = Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem step_done (s : Fin 2) (input output : List Bool) (coin : Bool) :
    machine.step (cfg (some s) input output []) coin = cfg none input output [] := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  change Config.mk none _ = Config.mk none _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem run_copy (input output scratch bits : List Bool)
    (hlen : bits.length = scratch.length + 1) :
    machine.run (cfg (some 1) input output scratch) bits =
      cfg none input (scratch.reverse ++ output) [] := by
  induction scratch generalizing output bits with
  | nil =>
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      have hr : rest = [] := by apply List.length_eq_zero_iff.mp; simpa using hlen
      subst rest
      simpa [BinaryMachine.run] using step_done 1 input output coin
  | cons b bs ih =>
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      have hr : rest.length = bs.length + 1 := by simpa using hlen
      erw [BinaryMachine.run.eq_2, step_copy, ih _ _ hr]
      simp [List.reverse_cons, List.append_assoc]
      rfl

theorem run_trim (input output scratch bits : List Bool)
    (hlen : bits.length = scratch.length + 1) :
    machine.run (cfg (some 0) input output scratch) bits =
      cfg none input (trimBits scratch.reverse ++ output) [] := by
  induction scratch generalizing output bits with
  | nil =>
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      have hr : rest = [] := by apply List.length_eq_zero_iff.mp; simpa using hlen
      subst rest
      simpa [BinaryMachine.run, trimBits] using step_done 0 input output coin
  | cons b bs ih =>
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      have hr : rest.length = bs.length + 1 := by simpa using hlen
      cases b
      · erw [BinaryMachine.run.eq_2, step_skip, ih _ _ hr]
        simp [List.reverse_cons, trimBits_append_false]
        rfl
      · erw [BinaryMachine.run.eq_2, step_first_one, run_copy input (true :: output) bs rest hr]
        simp [List.reverse_cons, trimBits_append_true, List.append_assoc]
        rfl

theorem run_payload (input raw bits : List Bool)
    (hlen : bits.length = raw.length + 1) :
    machine.run (cfg (some 0) input [] raw.reverse) bits =
      cfg none input (Computability.encodeNat (bitsValue raw)) [] := by
  have h := run_trim input [] raw.reverse bits (by simpa using hlen)
  simpa [trimBits_eq_encodeNat] using h

end KS.W19.BinaryTrimMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_CanonicalSubtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.CanonicalSubtraction
open KS.W29 KS.W29.Sequential

def machine : BinaryMachine := Sequential.compose BinarySubtractor.machine BinaryTrimMachine.machine

theorem run_exact (xs ys first second : List Bool)
    (hfirst : first.length = max xs.length ys.length + 1)
    (hsecond : second.length = max xs.length ys.length + 1) :
    machine.run
      (liftLeft BinarySubtractor.machine BinaryTrimMachine.machine
        (BinarySubtractor.cfg (some 0) xs ys [])) (first ++ second) =
      liftRight BinarySubtractor.machine BinaryTrimMachine.machine
        (BinaryTrimMachine.cfg none []
          (Computability.encodeNat (bitsValue (subtractBits xs ys false))) []) := by
  unfold machine
  have hhalt : HaltsAfter BinarySubtractor.machine
      (BinarySubtractor.cfg (some 0) xs ys []) first := by
    simpa only [BinarySubtractor.borrowState, Bool.false_eq_true, ↓reduceIte] using
      BinarySubtractor.haltsAfter_sub false xs ys [] first hfirst
  rw [run_compose BinarySubtractor.machine BinaryTrimMachine.machine
    (BinarySubtractor.cfg (some 0) xs ys []) first second hhalt]
  have hrun := BinarySubtractor.run_sub false xs ys [] first hfirst
  change BinarySubtractor.machine.run (BinarySubtractor.cfg (some 0) xs ys []) first = _ at hrun
  rw [hrun]
  change liftRight BinarySubtractor.machine BinaryTrimMachine.machine
    (BinaryTrimMachine.machine.run
      (BinaryTrimMachine.cfg (some 0) [] [] ((subtractBits xs ys false).reverse ++ [])) second) = _
  simp only [List.append_nil]
  rw [BinaryTrimMachine.run_payload [] (subtractBits xs ys false) second
    (by simpa only [subtractBits_length] using hsecond)]

end KS.W19.CanonicalSubtraction

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedStackMachine
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedLoop.dispatch_body _root_.OAI.KS.W29.FixedLoop.dispatch_guard _root_.OAI.KS.W29.FixedLoop.loop_toMachine _root_.OAI.KS.W29.FixedSequential.compose_toMachine _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine _root_.OAI.KS.W29.FixedSequential.ofMachine_toMachine _root_.OAI.KS.W29.FixedSequential.toMachine_ofMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01.FixedStack
open KS.W29 (StackAction polynomialFuel)

theorem Machine.step_stack_length_le (M : Machine) (c : Config M.stackCount M.states)
    (b : Bool) (j : Fin M.stackCount) :
    ((M.step c b).«stacks» j).length ≤ (c.«stacks» j).length + 1 := by
  unfold Machine.step
  cases hs : c.state with
  | none => simp
  | some s => exact StackAction.length_apply_le _ _

theorem Machine.run_stack_length_le (M : Machine) (c : Config M.stackCount M.states)
    (bits : List Bool) (j : Fin M.stackCount) :
    ((M.run c bits).«stacks» j).length ≤ (c.«stacks» j).length + bits.length := by
  induction bits generalizing c with
  | nil => simp [Machine.run]
  | cons b bs ih =>
      have hstep := M.step_stack_length_le c b j
      have hrun := ih (M.step c b)
      simp only [Machine.run, List.length_cons]
      omega

end KS.W01.FixedStack

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_LittleEndianCompare
attribute [-simp] _root_.OAI.KS.W01.FixedStack.lift3_project_init _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.BinaryMachine.withEntry_init_stacks _root_.OAI.KS.W29.BinaryMachine.withEntry_init_state _root_.OAI.KS.W29.BinaryMachine.withEntry_initial _root_.OAI.KS.W29.BinaryMachine.withEntry_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W28.LittleEndianCompare
open KS.W29
open KS.W19 (bitsValue compareBits compareDigit OrderingCorrect)

def dispatch (s : Fin 3) (heads : Fin 27) (_coin : Bool) : Instruction 3 :=
  let l := heads.val % 3
  let r := heads.val / 3 % 3
  if l = 0 ∧ r = 0 then ⟨none, .stay, .stay, .push (result (decode s))⟩
  else ⟨some (encode (update (decode s) (l == 2) (r == 2))), .pop, .pop, .stay⟩

def machine : BinaryMachine := FiniteDispatch.compile (encode .eq) dispatch

def cfg (state : Option (Fin 3)) (xs ys zs : List Bool) : Config 3 :=
  ⟨state, fun j => if j = 0 then xs else if j = 1 then ys else zs⟩

theorem table_lookup (s : Fin 3) (c : Config 3) (coin : Bool) :
    machine.table.getD (transitionIndex s c coin) (Instruction.halt 3) =
      if topCode (c.«stacks» 0) = 0 ∧ topCode (c.«stacks» 1) = 0 then
        ⟨none, .stay, .stay, .push (result (decode s))⟩
      else ⟨some (encode (update (decode s) (topCode (c.«stacks» 0) == 2)
        (topCode (c.«stacks» 1) == 2))), .pop, .pop, .stay⟩ := by
  have h0 := topCode_lt_three (c.«stacks» 0)
  have h1 := topCode_lt_three (c.«stacks» 1)
  have h2 := topCode_lt_three (c.«stacks» 2)
  have hl : headCode c % 3 = topCode (c.«stacks» 0) := by unfold headCode; omega
  have hr : headCode c / 3 % 3 = topCode (c.«stacks» 1) := by unfold headCode; omega
  unfold machine
  rw [FiniteDispatch.lookup_compile]
  simp only [dispatch, hl, hr]
  rfl

theorem step_left (o : Ordering) (a : Bool) (xs ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some (encode o)) (a :: xs) ys zs) coin =
      cfg (some (encode (update o a (ys.headD false)))) xs ys.tail zs := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases o <;> cases a <;> cases ys with
  | nil =>
      change Config.mk _ _ = Config.mk _ _
      congr 1
      funext j
      fin_cases j <;> rfl
  | cons b ys =>
      cases b <;> change Config.mk _ _ = Config.mk _ _
      all_goals
        congr 1
        funext j
        fin_cases j <;> rfl

theorem step_right (o : Ordering) (b : Bool) (ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some (encode o)) [] (b :: ys) zs) coin =
      cfg (some (encode (update o false b))) [] ys zs := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases o <;> cases b <;> change Config.mk _ _ = Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem step_done (o : Ordering) (zs : List Bool) (coin : Bool) :
    machine.step (cfg (some (encode o)) [] [] zs) coin =
      cfg none [] [] (result o :: zs) := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases o <;> change Config.mk none _ = Config.mk none _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem run_scan (o : Ordering) (xs ys zs coins : List Bool)
    (hlen : coins.length = max xs.length ys.length + 1) :
    machine.run (cfg (some (encode o)) xs ys zs) coins =
      cfg none [] [] (result (scan o xs ys) :: zs) := by
  induction xs generalizing o ys zs coins with
  | nil =>
      induction ys generalizing o zs coins with
      | nil =>
          cases coins with
          | nil => simp at hlen
          | cons coin rest =>
              have hr : rest = [] := by
                apply List.length_eq_zero_iff.mp
                simp only [List.length_cons, List.length_nil, max_self] at hlen
                omega
              subst rest
              erw [BinaryMachine.run.eq_2, step_done]
              simp only [BinaryMachine.run, scan]
              rfl
      | cons b ys ih =>
          cases coins with
          | nil => simp at hlen
          | cons coin rest =>
              have hr : rest.length = max ([] : List Bool).length ys.length + 1 := by
                simp only [List.length_nil, List.length_cons, Nat.zero_max] at hlen ⊢
                omega
              erw [BinaryMachine.run.eq_2, step_right, ih _ _ _ hr]
              simp only [scan]
              rfl
  | cons a xs ih =>
      cases coins with
      | nil => simp at hlen
      | cons coin rest =>
          cases ys with
          | nil =>
              have hr : rest.length = max xs.length ([] : List Bool).length + 1 := by
                simp only [List.length_nil, List.length_cons, Nat.max_zero] at hlen ⊢
                omega
              erw [BinaryMachine.run.eq_2, step_left]
              simp only [List.headD_nil, List.tail_nil]
              rw [ih _ _ _ _ hr]
              simp only [scan]
              rfl
          | cons b ys =>
              have hr : rest.length = max xs.length ys.length + 1 := by
                simp only [List.length_cons] at hlen
                omega
              erw [BinaryMachine.run.eq_2, step_left]
              simp only [List.headD_cons, List.tail_cons]
              rw [ih _ _ _ _ hr]
              simp only [scan]
              rfl

theorem run_correct (xs ys zs coins : List Bool)
    (hlen : coins.length = max xs.length ys.length + 1) :
    machine.run (cfg (some (encode .eq)) xs ys zs) coins =
      cfg none [] [] (decide (bitsValue xs ≤ bitsValue ys) :: zs) := by
  rw [run_scan .eq xs ys zs coins hlen, result_correct]

end KS.W28.LittleEndianCompare

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

theorem RunSpec.mono {k : ℕ} {P : Program k} {before after : Fin k → List Bool}
    {ticks larger : ℕ} (h : RunSpec P before after ticks) (hle : ticks ≤ larger) :
    RunSpec P before after larger := by
  intro bits hbits
  exact h.run_of_le bits (by simpa only [hbits] using hle)

end KS.W03.MachineCombinators

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedCompare
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.BinaryMachine.withEntry_init_stacks _root_.OAI.KS.W29.BinaryMachine.withEntry_init_state _root_.OAI.KS.W29.BinaryMachine.withEntry_initial _root_.OAI.KS.W29.BinaryMachine.withEntry_step _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W28.FixedCompare
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def program {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 LittleEndianCompare.machine ports)

@[simp] theorem after_result {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (registerMap : Fin k → List Bool) (b : Bool) :
    after ports registerMap b (ports 2) = b :: registerMap (ports 2) := by
  simp [after, ports.injective.eq_iff]

theorem after_other {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (registerMap : Fin k → List Bool) (b : Bool) (j : Fin k)
    (hj : ∀ i, j ≠ ports i) : after ports registerMap b j = registerMap j := by
  simp [after, hj 0, hj 1, hj 2]

theorem compare_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (registerMap : Fin k → List Bool) :
    RunSpec (program ports) registerMap
      (after ports registerMap (decide
        (KS.W19.bitsValue (registerMap (ports 0)) ≤ KS.W19.bitsValue (registerMap (ports 1)))))
      (max (registerMap (ports 0)).length (registerMap (ports 1)).length + 1) := by
  intro bits hbits
  change (lift3 LittleEndianCompare.machine ports).run ⟨some (0 : Fin 3), registerMap⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some 0, registerMap⟩ : Config k 3) =
        LittleEndianCompare.cfg (some 0) (registerMap (ports 0)) (registerMap (ports 1))
          (registerMap (ports 2)) := by
      change KS.W29.Config.mk (some (0 : Fin 3)) _ = KS.W29.Config.mk (some (0 : Fin 3)) _
      apply congrArg (KS.W29.Config.mk (some (0 : Fin 3)))
      funext j
      fin_cases j <;> rfl
    erw [hp]
    have hr := LittleEndianCompare.run_correct (registerMap (ports 0)) (registerMap (ports 1))
      (registerMap (ports 2)) bits hbits
    change LittleEndianCompare.machine.run
      (LittleEndianCompare.cfg (some 0) _ _ _) bits = _ at hr
    erw [hr]
    apply congrArg (KS.W29.Config.mk none)
    funext j
    fin_cases j <;> simp
  · intro j hj
    exact after_other ports registerMap _ j hj

theorem compare_spec_linear {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (registerMap : Fin k → List Bool) :
    RunSpec (program ports) registerMap
      (after ports registerMap (decide
        (KS.W19.bitsValue (registerMap (ports 0)) ≤ KS.W19.bitsValue (registerMap (ports 1)))))
      ((registerMap (ports 0)).length + (registerMap (ports 1)).length + 1) := by
  apply (compare_spec ports registerMap).mono
  omega

end KS.W28.FixedCompare

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_MagnitudeProgram
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W01.MagnitudeProgram
open KS.W29
open KS.W03.MachineCombinators
open KS.W01.BinaryAdder

def carryMachine (carry : Bool) : BinaryMachine :=
  normalizedMachine.withEntry
    (Sequential.leftState machine NormalizeOutput.machine (carryState carry))

theorem run_carry (carry : Bool) (xs bits : List Bool)
    (hlen : bits.length = ticks carry xs) :
    (carryMachine carry).run ⟨some (carryMachine carry).initial, ![[], xs, []]⟩ bits =
      ⟨none, ![[], result carry xs, []]⟩ := by
  change (normalizedMachine.withEntry
    (Sequential.leftState machine NormalizeOutput.machine (carryState carry))).run
      ⟨some (carryMachine carry).initial, ![[], xs, []]⟩ bits = _
  erw [BinaryMachine.withEntry_run]
  have hi : (⟨some (carryMachine carry).initial, ![[],xs,[]]⟩ : Config normalizedMachine.states) =
      Sequential.liftLeft machine NormalizeOutput.machine (cfg (some (carryState carry)) [] xs []) := by
    apply congrArg₂ Config.mk
    · rfl
    · funext j; fin_cases j <;> rfl
  erw [hi]
  have hfirst : (bits.take (xs.length + 1)).length = max ([] : List Bool).length xs.length + 1 := by
    simp only [List.length_take, List.length_nil, Nat.zero_max]
    have hh : xs.length + 1 ≤ bits.length := by unfold ticks at hlen; omega
    exact Nat.min_eq_left hh
  have hsecond : (bits.drop (xs.length + 1)).length = (result carry xs).length + 1 := by
    simp only [List.length_drop, hlen, ticks]
    omega
  have h := NormalizeOutput.compose_result machine
    (cfg (some (carryState carry)) [] xs [])
    (bits.take (xs.length + 1)) (bits.drop (xs.length + 1)) [] (result carry xs)
    (BinaryAdder.haltsAfter carry [] xs [] _ hfirst) (by
      rw [run_add carry [] xs [] _ hfirst]
      simp only [List.append_nil]
      rfl) hsecond
  rw [List.take_append_drop] at h
  refine h.trans ?_
  apply congrArg₂ Config.mk
  · rfl
  · funext j; fin_cases j <;> rfl

def program {k : ℕ} (ports : Fin 3 ↪ Fin k) (carry : Bool) : FixedSequential.Program k :=
  FixedSequential.ofMachine (FixedStack.lift3 (carryMachine carry) ports)

theorem runSpec {k : ℕ} (ports : Fin 3 ↪ Fin k) (carry : Bool)
    (store : Fin k → List Bool) (xs : List Bool)
    (hzero : store (ports 0) = []) (hpayload : store (ports 1) = xs)
    (hscratch : store (ports 2) = []) :
    RunSpec (program ports carry) store
      (Function.update store (ports 1) (result carry xs)) (ticks carry xs) := by
  intro bits hbits
  change (FixedStack.lift3 (carryMachine carry) ports).run
    ⟨some (carryMachine carry).initial, store⟩ bits = _
  apply lift3_run_eq
  · have hin : FixedStack.project ports
        (⟨some (carryMachine carry).initial, store⟩ :
          FixedStack.Config k (carryMachine carry).states) =
        ⟨some (carryMachine carry).initial, ![[], xs, []]⟩ := by
      change Config.mk _ (fun j => store (ports j)) = Config.mk _ _
      congr 1
      funext j
      fin_cases j
      · exact hzero
      · exact hpayload
      · exact hscratch
    erw [hin, run_carry carry xs bits hbits]
    congr 1
    funext j
    fin_cases j <;>
      simp [Function.update, ports.injective.eq_iff, hzero, hscratch]
  · intro j hj
    simp [Function.update, hj 1]

theorem runSpec_linear {k : ℕ} (ports : Fin 3 ↪ Fin k) (carry : Bool)
    (store : Fin k → List Bool) (xs : List Bool)
    (hzero : store (ports 0) = []) (hpayload : store (ports 1) = xs)
    (hscratch : store (ports 2) = []) :
    RunSpec (program ports carry) store
      (Function.update store (ports 1) (result carry xs)) (2 * xs.length + 3) :=
  (runSpec ports carry store xs hzero hpayload hscratch).mono (ticks_le carry xs)

end KS.W01.MagnitudeProgram

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalCompareBranch
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W06.RationalCompare
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def stayActions (k : ℕ) : Vector KS.W29.StackAction k := Vector.ofFn (fun _ => .stay)

theorem branch_spec_left {k : ℕ} (P Q : Program k) (output : Fin k)
    (select : (Fin k → Fin 3) → Bool → KS.W29.FixedBranch.SelectInstruction k)
    (before after : Fin k → List Bool) (ticks : ℕ)
    (hselect : ∀ coin, select (observedHeads
      (⟨some (KS.W29.FixedBranch.start P Q), before⟩ : Config k (P.states + Q.states + 1))) coin =
      ⟨.left, stayActions k⟩)
    (hP : RunSpec P before after ticks) :
    RunSpec (KS.W29.FixedBranch.branch P Q output select) before after (ticks + 1) := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin rest =>
    have hr : rest.length = ticks := by simpa using hbits
    rw [Machine.run]
    erw [KS.W29.FixedBranch.step_start]
    rw [hselect coin]
    simp only [KS.W29.FixedBranch.selectInstruction, Instruction.action,
      stayActions, Vector.getElem_ofFn, KS.W29.StackAction.apply]
    change (KS.W29.FixedBranch.branch P Q output select).toMachine.run
      (KS.W29.FixedBranch.liftLeft P Q ⟨some P.initial, before⟩) rest = _
    rw [KS.W29.FixedBranch.run_left]
    exact congrArg (KS.W29.FixedBranch.liftLeft P Q) (hP rest hr)

theorem branch_spec_right {k : ℕ} (P Q : Program k) (output : Fin k)
    (select : (Fin k → Fin 3) → Bool → KS.W29.FixedBranch.SelectInstruction k)
    (before after : Fin k → List Bool) (ticks : ℕ)
    (hselect : ∀ coin, select (observedHeads
      (⟨some (KS.W29.FixedBranch.start P Q), before⟩ : Config k (P.states + Q.states + 1))) coin =
      ⟨.right, stayActions k⟩)
    (hQ : RunSpec Q before after ticks) :
    RunSpec (KS.W29.FixedBranch.branch P Q output select) before after (ticks + 1) := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin rest =>
    have hr : rest.length = ticks := by simpa using hbits
    rw [Machine.run]
    erw [KS.W29.FixedBranch.step_start]
    rw [hselect coin]
    simp only [KS.W29.FixedBranch.selectInstruction, Instruction.action,
      stayActions, Vector.getElem_ofFn, KS.W29.StackAction.apply]
    change (KS.W29.FixedBranch.branch P Q output select).toMachine.run
      (KS.W29.FixedBranch.liftRight P Q ⟨some Q.initial, before⟩) rest = _
    rw [KS.W29.FixedBranch.run_right]
    exact congrArg (KS.W29.FixedBranch.liftRight P Q) (hQ rest hr)

def signSelect {k : ℕ} (signPort : Fin k) (heads : Fin k → Fin 3)
    (_ : Bool) : KS.W29.FixedBranch.SelectInstruction k :=
  ⟨if (heads signPort).val = 2 then .right else .left, stayActions k⟩

def magnitudeProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) (signPort : Fin k) : Program k :=
  KS.W29.FixedBranch.branch (KS.W01.MagnitudeProgram.program ports false)
    (KS.W01.MagnitudeProgram.program ports true) (ports 1) (signSelect signPort)

theorem magnitude_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (signPort : Fin k)
    (before : Fin k → List Bool) (sign : Bool) (xs : List Bool)
    (hsign : before signPort = [sign]) (hzero : before (ports 0) = [])
    (hpayload : before (ports 1) = xs) (hscratch : before (ports 2) = []) :
    RunSpec (magnitudeProgram ports signPort) before
      (Function.update before (ports 1) (KS.W01.MagnitudeProgram.result sign xs))
      (2 * xs.length + 4) := by
  have h := KS.W01.MagnitudeProgram.runSpec_linear ports sign before xs hzero hpayload hscratch
  cases sign
  · apply branch_spec_left _ _ _ _ _ _ (2 * xs.length + 3) _ h
    intro coin
    simp [signSelect, observedHeads, hsign, KS.W29.topCode]
  · apply branch_spec_right _ _ _ _ _ _ (2 * xs.length + 3) _ h
    intro coin
    simp [signSelect, observedHeads, hsign, KS.W29.topCode]

def compareSelect {k : ℕ} (signLeft signRight output : Fin k)
    (heads : Fin k → Fin 3) (_ : Bool) : KS.W29.FixedBranch.SelectInstruction k :=
  let a := (heads signLeft).val == 2
  let b := (heads signRight).val == 2
  if a = b then ⟨if a then .right else .left, stayActions k⟩
  else ⟨.halt, Vector.ofFn (fun j => if j = output then .push a else .stay)⟩

def signedCompareProgram {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (signLeft signRight : Fin k) : Program k :=
  KS.W29.FixedBranch.branch (KS.W28.FixedCompare.program ports)
    (KS.W28.FixedCompare.program (swapFirstTwo.trans ports)) (ports 2)
    (compareSelect signLeft signRight (ports 2))

def signedCompareAfter {k : ℕ} (ports : Fin 3 ↪ Fin k) (before : Fin k → List Bool)
    (a b : Bool) : Fin k → List Bool :=
  if a = b then
    if a then KS.W28.FixedCompare.after (swapFirstTwo.trans ports) before
      (decide (KS.W19.bitsValue (before (ports 1)) ≤ KS.W19.bitsValue (before (ports 0))))
    else KS.W28.FixedCompare.after ports before
      (decide (KS.W19.bitsValue (before (ports 0)) ≤ KS.W19.bitsValue (before (ports 1))))
  else Function.update before (ports 2) (a :: before (ports 2))

theorem signedCompare_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (signLeft signRight : Fin k)
    (before : Fin k → List Bool) (a b : Bool)
    (ha : before signLeft = [a]) (hb : before signRight = [b]) :
    RunSpec (signedCompareProgram ports signLeft signRight) before
      (signedCompareAfter ports before a b)
      ((before (ports 0)).length + (before (ports 1)).length + 2) := by
  cases a <;> cases b
  · have h := KS.W28.FixedCompare.compare_spec_linear ports before
    apply branch_spec_left _ _ _ _ _ _ _ _ h
    intro coin
    simp [compareSelect, observedHeads, ha, hb, KS.W29.topCode]
  · intro bits hbits
    cases bits with
    | nil => simp at hbits
    | cons coin rest =>
      rw [Machine.run]
      erw [KS.W29.FixedBranch.step_start]
      simp only [compareSelect, observedHeads, ha, hb, KS.W29.topCode]
      erw [Machine.run_halted _ _ rfl]
      apply congrArg (Config.mk none)
      funext j
      by_cases hj : j = ports 2 <;>
        simp [KS.W29.FixedBranch.selectInstruction, Instruction.action,
          KS.W29.StackAction.apply, signedCompareAfter, Function.update, hj]
  · intro bits hbits
    cases bits with
    | nil => simp at hbits
    | cons coin rest =>
      rw [Machine.run]
      erw [KS.W29.FixedBranch.step_start]
      simp only [compareSelect, observedHeads, ha, hb, KS.W29.topCode]
      erw [Machine.run_halted _ _ rfl]
      apply congrArg (Config.mk none)
      funext j
      by_cases hj : j = ports 2 <;>
        simp [KS.W29.FixedBranch.selectInstruction, Instruction.action,
          KS.W29.StackAction.apply, signedCompareAfter, Function.update, hj]
  · have h := KS.W28.FixedCompare.compare_spec_linear (swapFirstTwo.trans ports) before
    have h' := branch_spec_right (KS.W28.FixedCompare.program ports)
      (KS.W28.FixedCompare.program (swapFirstTwo.trans ports)) (ports 2)
      (compareSelect signLeft signRight (ports 2)) before _ _ (by
        intro coin
        simp [compareSelect, observedHeads, ha, hb, KS.W29.topCode]) h
    convert h' using 1 <;>
      simp [signedCompareProgram, signedCompareAfter, swapFirstTwo, Nat.add_comm]
    omega

theorem signedCompareAfter_output {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (before : Fin k → List Bool) (a b : Bool) :
    signedCompareAfter ports before a b (ports 2) =
      signedCrossLE a b (KS.W19.bitsValue (before (ports 0)))
        (KS.W19.bitsValue (before (ports 1))) :: before (ports 2) := by
  cases a <;> cases b <;>
    simp [signedCompareAfter, signedCrossLE, KS.W28.FixedCompare.after,
      swapFirstTwo, ports.injective.eq_iff]

end KS.W06.RationalCompare

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedCopyRestore
attribute [-simp] _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.BinaryMachine.withEntry_init_stacks _root_.OAI.KS.W29.BinaryMachine.withEntry_init_state _root_.OAI.KS.W29.BinaryMachine.withEntry_initial _root_.OAI.KS.W29.BinaryMachine.withEntry_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W01.FixedCopy
open KS.W29

theorem activeFor_append (M : BinaryMachine) (c : Config M.states) (xs ys : List Bool) :
    Sequential.ActiveFor M c (xs ++ ys) ↔
      Sequential.ActiveFor M c xs ∧ Sequential.ActiveFor M (M.run c xs) ys := by
  induction xs generalizing c with
  | nil => simp [Sequential.ActiveFor, BinaryMachine.run]
  | cons b bs ih => simp [Sequential.ActiveFor, BinaryMachine.run, ih, and_assoc]

end KS.W01.FixedCopy

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_MachineRoundTrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W03.MachineRoundTrip
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem runSpec_ofMachine (M : Machine) (before after : Fin M.stackCount → List Bool) (ticks : ℕ)
    (h : ∀ bits : List Bool, bits.length = ticks →
      M.run ⟨some M.initial,before⟩ bits = ⟨none,after⟩) :
    RunSpec (ofMachine M) before after ticks := by
  cases M
  exact h

end KS.W03.MachineRoundTrip

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_MultiplicationBody
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W03.MultiplicationBody

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W03.BinaryAccumulator KS.W03.BinaryMultiply

def copyProgram : Program 7 := KS.W01.FixedCopy.program copyPorts

def addProgram : Program 7 := ofMachine (lift3 KS.W01.BinaryAdder.machine addPorts)

def reverseProgram : Program 7 := ofMachine (lift3 KS.W29.NormalizeOutput.machine reversePorts)

def shiftInstruction : Instruction 7 1 :=
  ⟨none, Vector.ofFn (fun j => if j = 2 then .push false else .stay)⟩

def shiftProgram : Program 7 :=
  ofMachine (compile (0 : Fin 1) (0 : Fin 7) (3 : Fin 7) (fun _ _ _ => shiftInstruction))

def body : Program 7 :=
  compose (compose (compose copyProgram addProgram) reverseProgram) shiftProgram

theorem copy_spec (input xs operand acc : List Bool) :
    RunSpec copyProgram (registers input xs operand acc [] [] [])
      (registers input xs operand acc operand [] []) (2 * operand.length + 2) := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hbits
  erw [KS.W01.FixedCopy.run_copy_restore copyPorts _ operand bits rfl rfl rfl hbits]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem add_spec (input xs operand acc : List Bool) :
    RunSpec addProgram (registers input xs operand acc operand [] [])
      (registers input xs operand [] [] [] (KS.W01.BinaryAdder.addBits false acc operand).reverse)
      (max acc.length operand.length + 1) := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hbits
  apply lift3_run_eq
  · have hp : project addPorts
        (⟨some 0, registers input xs operand acc operand [] []⟩ : Config 7 2) =
        KS.W01.BinaryAdder.cfg (some 0) acc operand [] := by
      change KS.W29.Config.mk (some (0 : Fin 2)) _ = KS.W29.Config.mk (some (0 : Fin 2)) _
      congr 1
      funext j
      fin_cases j <;> rfl
    erw [hp]
    have hr := KS.W01.BinaryAdder.run_add false acc operand [] bits hbits
    simp only [KS.W01.BinaryAdder.carryState, Bool.false_eq_true, ↓reduceIte,
      List.append_nil] at hr
    rw [hr]
    change KS.W29.Config.mk none _ = KS.W29.Config.mk none _
    congr 1
    funext j
    fin_cases j <;> rfl
  · intro j hj
    have h0 := hj 0
    have h1 := hj 1
    have h2 := hj 2
    fin_cases j <;> simp_all [registers, addPorts]

theorem reverse_spec (input xs operand result : List Bool) :
    RunSpec reverseProgram (registers input xs operand [] [] [] result.reverse)
      (registers input xs operand result [] [] []) (result.length + 1) := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hbits
  apply lift3_run_eq
  · have hp : project reversePorts
        (⟨some 2, registers input xs operand [] [] [] result.reverse⟩ : Config 7 3) =
        KS.W29.FrameDecoder.config (some 2) input [] result.reverse := by
      change KS.W29.Config.mk (some (2 : Fin 3)) _ = KS.W29.Config.mk (some (2 : Fin 3)) _
      congr 1
      funext j
      fin_cases j <;> rfl
    erw [hp, KS.W29.NormalizeOutput.run_reversed input result bits hbits]
    change KS.W29.Config.mk none _ = KS.W29.Config.mk none _
    congr 1
    funext j
    fin_cases j <;> rfl
  · intro j hj
    have h0 := hj 0
    have h1 := hj 1
    have h2 := hj 2
    fin_cases j <;> simp_all [registers, reversePorts]

theorem shift_spec (input xs operand acc : List Bool) :
    RunSpec shiftProgram (registers input xs operand acc [] [] [])
      (registers input xs (shift operand) acc [] [] []) 1 := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons b bs =>
    have hb : bs = [] := by apply List.length_eq_zero_iff.mp; simpa using hbits
    subst bs
    erw [Machine.run.eq_2, step_compile]
    change Config.mk none _ = Config.mk none _
    congr 1
    funext j
    fin_cases j <;> rfl

theorem body_spec (input xs operand acc : List Bool) :
    RunSpec body (registers input xs operand acc [] [] [])
      (registers input xs (shift operand) (KS.W01.BinaryAdder.addBits false acc operand) [] [] [])
      (bodyTicks operand acc) := by
  have h1 := (copy_spec input xs operand acc).compose (add_spec input xs operand acc)
  have h2 := h1.compose
    (reverse_spec input xs operand (KS.W01.BinaryAdder.addBits false acc operand))
  exact h2.compose (shift_spec input xs operand (KS.W01.BinaryAdder.addBits false acc operand))

end KS.W03.MultiplicationBody

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_MultiplicationLoop
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W03.MultiplicationLoop

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W03.MultiplicationBody KS.W03.BinaryAccumulator KS.W03.BinaryMultiply

def guard (heads : Fin 7 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 7 :=
  if (heads 1).val = 0 then
    ⟨.halt, Vector.ofFn (fun _ => .stay)⟩
  else if (heads 1).val = 1 then
    ⟨.restart, Vector.ofFn (fun j =>
      if j = 1 then .pop else if j = 2 then .push false else .stay)⟩
  else
    ⟨.call, Vector.ofFn (fun j => if j = 1 then .pop else .stay)⟩

def program : Program 7 := KS.W29.FixedLoop.loop body guard

def cfg (input xs operand acc : List Bool) : Config 7 program.states :=
  ⟨some program.initial, registers input xs operand acc [] [] []⟩

theorem step_empty (input operand acc : List Bool) (coin : Bool) :
    program.toMachine.step (cfg input [] operand acc) coin =
      ⟨none, registers input [] operand acc [] [] []⟩ := by
  change (KS.W29.FixedLoop.loop body guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState body), registers input [] operand acc [] [] []⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  change Config.mk none _ = Config.mk none _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem step_false (input xs operand acc : List Bool) (coin : Bool) :
    program.toMachine.step (cfg input (false :: xs) operand acc) coin =
      cfg input xs (shift operand) acc := by
  change (KS.W29.FixedLoop.loop body guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState body), registers input (false :: xs) operand acc [] [] []⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  change Config.mk (some (KS.W29.FixedLoop.guardState body)) _ =
    Config.mk (some (KS.W29.FixedLoop.guardState body)) _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem step_true (input xs operand acc : List Bool) (coin : Bool) :
    program.toMachine.step (cfg input (true :: xs) operand acc) coin =
      KS.W29.FixedLoop.liftBody body
        ⟨some body.initial, registers input xs operand acc [] [] []⟩ := by
  change (KS.W29.FixedLoop.loop body guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState body), registers input (true :: xs) operand acc [] [] []⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  change Config.mk (some (KS.W29.FixedLoop.bodyState body body.initial)) _ =
    Config.mk (some (KS.W29.FixedLoop.bodyState body body.initial)) _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem run_loop (input xs operand acc bits : List Bool)
    (hlen : loopTicks xs operand acc ≤ bits.length) :
    program.toMachine.run (cfg input xs operand acc) bits =
      ⟨none, registers input [] (advance xs operand) (loop xs operand acc) [] [] []⟩ := by
  induction xs generalizing operand acc bits with
  | nil =>
    cases bits with
    | nil => simp [loopTicks] at hlen
    | cons coin rest =>
      erw [Machine.run.eq_2, step_empty, Machine.run_halted _ _ rfl]
      rfl
  | cons b xs ih =>
    cases bits with
    | nil => simp [loopTicks] at hlen
    | cons coin rest =>
      cases b
      · have ht : loopTicks xs (shift operand) acc ≤ rest.length := by
          simp [loopTicks, roundTicks, nextAccumulator] at hlen
          omega
        erw [Machine.run.eq_2, step_false]
        simpa [advance, loop, nextAccumulator] using
          ih (shift operand) acc rest ht
      · have ht : bodyTicks operand acc +
            loopTicks xs (shift operand) (KS.W01.BinaryAdder.addBits false acc operand) ≤ rest.length := by
          simp [loopTicks, roundTicks, nextAccumulator] at hlen
          omega
        obtain ⟨remaining, hremaining, hreturn⟩ :=
          (body_spec input xs operand acc).loop_body_then guard rest (by omega)
        erw [Machine.run.eq_2, step_true]
        erw [hreturn]
        have hn : loopTicks xs (shift operand) (KS.W01.BinaryAdder.addBits false acc operand) ≤
            remaining.length := by omega
        simp only [advance, loop, nextAccumulator]
        exact ih (shift operand) (KS.W01.BinaryAdder.addBits false acc operand) remaining hn

theorem loop_spec (input xs operand acc : List Bool) :
    RunSpec program (registers input xs operand acc [] [] [])
      (registers input [] (advance xs operand) (loop xs operand acc) [] [] [])
      (loopTicks xs operand acc) := by
  intro bits hbits
  exact run_loop input xs operand acc bits (by omega)

end KS.W03.MultiplicationLoop

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_MultiplicationNormalize
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W03.MultiplicationNormalize

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W03.MultiplicationBody

theorem reverse_spec (input xs operand raw : List Bool) :
    RunSpec reverseProgram (registers input xs operand raw [] [] [])
      (registers input xs operand [] [] [] raw.reverse) (raw.length + 1) := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hbits
  apply lift3_run_eq
  · have hp : project reversePorts
        (⟨some 2, registers input xs operand raw [] [] []⟩ : Config 7 3) =
        KS.W29.FrameDecoder.config (some 2) input [] raw := by
      change KS.W29.Config.mk (some (2 : Fin 3)) _ = KS.W29.Config.mk (some (2 : Fin 3)) _
      congr 1
      funext j
      fin_cases j <;> rfl
    erw [hp, KS.W29.NormalizeOutput.run_normalize input [] raw bits hbits]
    simp only [List.append_nil]
    change KS.W29.Config.mk none _ = KS.W29.Config.mk none _
    congr 1
    funext j
    fin_cases j <;> rfl
  · intro j hj
    have h0 := hj 0
    have h1 := hj 1
    have h2 := hj 2
    fin_cases j <;> simp_all [registers, reversePorts]

theorem trim_spec (input xs operand raw : List Bool) :
    RunSpec trimProgram (registers input xs operand [] [] [] raw.reverse)
      (registers input xs operand (Computability.encodeNat (KS.W19.bitsValue raw)) [] [] [])
      (raw.length + 1) := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hbits
  apply lift3_run_eq
  · have hp : project trimPorts
        (⟨some 0, registers input xs operand [] [] [] raw.reverse⟩ : Config 7 2) =
        KS.W19.BinaryTrimMachine.cfg (some 0) input [] raw.reverse := by
      change KS.W29.Config.mk (some (0 : Fin 2)) _ = KS.W29.Config.mk (some (0 : Fin 2)) _
      congr 1
      funext j
      fin_cases j <;> rfl
    erw [hp, KS.W19.BinaryTrimMachine.run_payload input raw bits hbits]
    change KS.W29.Config.mk none _ = KS.W29.Config.mk none _
    congr 1
    funext j
    fin_cases j <;> rfl
  · intro j hj
    have h0 := hj 0
    have h1 := hj 1
    have h2 := hj 2
    fin_cases j <;> simp_all [registers, trimPorts]

theorem normalize_spec (input xs operand raw : List Bool) :
    RunSpec program (registers input xs operand raw [] [] [])
      (registers input xs operand (Computability.encodeNat (KS.W19.bitsValue raw)) [] [] [])
      (2 * raw.length + 2) := by
  have h := (reverse_spec input xs operand raw).compose (trim_spec input xs operand raw)
  convert h using 1 <;> first | rfl | omega

end KS.W03.MultiplicationNormalize

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalComparePrimitives
attribute [-simp] _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W06.RationalCompare

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def replacePorts {k K : ℕ} (ports : Fin k ↪ Fin K)
    (before : Fin K → List Bool) (after : Fin k → List Bool) : Fin K → List Bool :=
  fun j => match portPreimage ports j with
    | none => before j
    | some i => after i

@[simp] theorem replacePorts_on {k K : ℕ} (ports : Fin k ↪ Fin K)
    (before : Fin K → List Bool) (after : Fin k → List Bool) (i : Fin k) :
    replacePorts ports before after (ports i) = after i := by
  simp [replacePorts]

theorem replacePorts_off {k K : ℕ} (ports : Fin k ↪ Fin K)
    (before : Fin K → List Bool) (after : Fin k → List Bool) (j : Fin K)
    (hj : ∀ i, j ≠ ports i) : replacePorts ports before after j = before j := by
  simp [replacePorts, portPreimage_off_port ports j hj]

theorem runSpec_liftPorts {k K : ℕ} (P : Program k) (ports : Fin k ↪ Fin K)
    (before : Fin K → List Bool) (after : Fin k → List Bool) (ticks : ℕ)
    (h : RunSpec P (fun i => before (ports i)) after ticks) :
    RunSpec (KS.W29.FixedSequential.liftPorts P ports) before
      (replacePorts ports before after) ticks := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec P ports
    (fun i => before (ports i)) after before
    (replacePorts ports before after) ticks h
  · intro i; rfl
  · intro i; exact replacePorts_on ports before after i
  · intro j hj; exact replacePorts_off ports before after j hj

@[simp] theorem replace3_on {k : ℕ} (ports : Fin 3 ↪ Fin k) (before : Fin k → List Bool)
    (a b c : List Bool) (i : Fin 3) : replace3 ports before a b c (ports i) = ![a,b,c] i := by
  fin_cases i <;> simp [replace3, ports.injective.eq_iff]

def decodeProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 KS.W29.FrameDecoder.machine ports)

theorem decode_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (before : Fin k → List Bool)
    (payload tail : List Bool)
    (hin : before (ports 0) = KS.W01.frame payload ++ tail)
    (hout : before (ports 1) = []) (hscratch : before (ports 2) = []) :
    RunSpec (decodeProgram ports) before (replace3 ports before tail payload [])
      (3 * payload.length + 2) := by
  intro bits hbits
  change (lift3 KS.W29.FrameDecoder.machine ports).run ⟨some (0 : Fin 3), before⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some 0, before⟩ : Config k 3) =
        KS.W29.FrameDecoder.machine.init (KS.W01.frame payload ++ tail) := by
      change KS.W29.Config.mk (some (0 : Fin 3)) _ = KS.W29.Config.mk (some (0 : Fin 3)) _
      apply congrArg (KS.W29.Config.mk (some (0 : Fin 3)))
      funext i
      fin_cases i <;> simp [hin, hout, hscratch]
    erw [hp, KS.W29.FrameDecoder.run_frame payload tail bits hbits]
    apply congrArg (KS.W29.Config.mk none)
    funext i
    fin_cases i <;> simp
  · intro j hj
    simp [replace3, hj 0, hj 1, hj 2]

def signDispatch {k : ℕ} (source target : Fin k) (_ : Fin 1)
    (heads : Fin k → Fin 3) (_ : Bool) : Instruction k 1 :=
  ⟨none, Vector.ofFn (fun j => if j = source then .pop
    else if j = target then .push ((heads source).val == 2) else .stay)⟩

def signProgram {k : ℕ} (source target : Fin k) : Program k :=
  ofMachine (compile (0 : Fin 1) source target (signDispatch source target))

theorem sign_spec {k : ℕ} (source target : Fin k) (hst : source ≠ target)
    (before : Fin k → List Bool) (sign : Bool) (tail : List Bool)
    (hin : before source = sign :: tail) :
    RunSpec (signProgram source target) before (signAfter source target before sign tail) 1 := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin rest =>
      have hr : rest = [] := List.length_eq_zero_iff.mp (by simpa using hbits)
      subst rest
      change (compile (0 : Fin 1) source target (signDispatch source target)).step
        ⟨some (0 : Fin 1), before⟩ coin = _
      rw [step_compile]
      apply congrArg (Config.mk none)
      funext j
      by_cases hjs : j = source
      · subst j
        simp [signDispatch, Instruction.action, signAfter, hin, KS.W29.StackAction.apply]
      · by_cases hjt : j = target
        · subst j
          cases sign <;> simp [signDispatch, Instruction.action, signAfter, hin,
            Ne.symm hst, observedHeads, KS.W29.topCode, KS.W29.StackAction.apply]
        · simp [signDispatch, Instruction.action, signAfter, hjs, hjt, KS.W29.StackAction.apply]

def productProgram : Program 7 :=
  compose KS.W03.MultiplicationLoop.program KS.W03.MultiplicationNormalize.program

theorem product_spec (input xs ys : List Bool) :
    RunSpec productProgram (KS.W03.MultiplicationBody.registers input xs ys [] [] [] [])
      (KS.W03.MultiplicationBody.registers input [] (KS.W03.MultiplicationLoop.advance xs ys)
        (Computability.encodeNat (KS.W19.bitsValue xs * KS.W19.bitsValue ys)) [] [] [])
      (productTicks xs ys) := by
  have h := (KS.W03.MultiplicationLoop.loop_spec input xs ys []).compose
    (KS.W03.MultiplicationNormalize.normalize_spec input []
      (KS.W03.MultiplicationLoop.advance xs ys) (KS.W03.BinaryAccumulator.loop xs ys []))
  rw [KS.W03.BinaryAccumulator.loop_zero_correct] at h
  exact h

end KS.W06.RationalCompare

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalCompareParser
attribute [-simp] _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W06.RationalCompare
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def pairBits (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : List Bool :=
  sa :: (KS.W01.frame na ++ KS.W01.frame da ++
    (sb :: (KS.W01.frame nb ++ KS.W01.frame db)))

def parseProgram : Program 13 :=
  compose (compose (compose (compose (compose
    (signProgram 0 1) (decodeProgram leftNumeratorPorts))
      (decodeProgram leftDenominatorPorts)) (signProgram 0 4))
        (decodeProgram rightNumeratorPorts)) (decodeProgram rightDenominatorPorts)

theorem parse_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec parseProgram (fields (pairBits sa na da sb nb db) [] [] [] [] [] [])
      (fields [] [sa] na da [sb] nb db) (parseTicks na da nb db) := by
  let tailB := sb :: (KS.W01.frame nb ++ KS.W01.frame db)
  let tailA := KS.W01.frame na ++ KS.W01.frame da ++ tailB
  have h1 : RunSpec (signProgram (0 : Fin 13) 1)
      (fields (pairBits sa na da sb nb db) [] [] [] [] [] [])
      (fields tailA [sa] [] [] [] [] []) 1 := by
    have h := sign_spec (0 : Fin 13) 1 (by decide)
      (fields (pairBits sa na da sb nb db) [] [] [] [] [] []) sa tailA rfl
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext index; fin_cases index <;> rfl)
  have h2 : RunSpec (decodeProgram leftNumeratorPorts)
      (fields tailA [sa] [] [] [] [] [])
      (fields (KS.W01.frame da ++ tailB) [sa] na [] [] [] []) (3 * na.length + 2) := by
    have h := decode_spec leftNumeratorPorts (fields tailA [sa] [] [] [] [] [])
      na (KS.W01.frame da ++ tailB) (by simp [fields, leftNumeratorPorts, tailA, List.append_assoc]) rfl rfl
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext index; fin_cases index <;> rfl)
  have h3 : RunSpec (decodeProgram leftDenominatorPorts)
      (fields (KS.W01.frame da ++ tailB) [sa] na [] [] [] [])
      (fields tailB [sa] na da [] [] []) (3 * da.length + 2) := by
    have h := decode_spec leftDenominatorPorts
      (fields (KS.W01.frame da ++ tailB) [sa] na [] [] [] []) da tailB rfl rfl rfl
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext index; fin_cases index <;> rfl)
  have h4 : RunSpec (signProgram (0 : Fin 13) 4)
      (fields tailB [sa] na da [] [] [])
      (fields (KS.W01.frame nb ++ KS.W01.frame db) [sa] na da [sb] [] []) 1 := by
    have h := sign_spec (0 : Fin 13) 4 (by decide) (fields tailB [sa] na da [] [] [])
      sb (KS.W01.frame nb ++ KS.W01.frame db) rfl
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext index; fin_cases index <;> rfl)
  have h5 : RunSpec (decodeProgram rightNumeratorPorts)
      (fields (KS.W01.frame nb ++ KS.W01.frame db) [sa] na da [sb] [] [])
      (fields (KS.W01.frame db) [sa] na da [sb] nb []) (3 * nb.length + 2) := by
    have h := decode_spec rightNumeratorPorts
      (fields (KS.W01.frame nb ++ KS.W01.frame db) [sa] na da [sb] [] [])
      nb (KS.W01.frame db) rfl rfl rfl
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext index; fin_cases index <;> rfl)
  have h6 : RunSpec (decodeProgram rightDenominatorPorts)
      (fields (KS.W01.frame db) [sa] na da [sb] nb [])
      (fields [] [sa] na da [sb] nb db) (3 * db.length + 2) := by
    have h := decode_spec rightDenominatorPorts
      (fields (KS.W01.frame db) [sa] na da [sb] nb [])
      db [] (by simp [fields, rightDenominatorPorts]) rfl rfl
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext index; fin_cases index <;> rfl)
  have h := ((((h1.compose h2).compose h3).compose h4).compose h5).compose h6
  convert h using 1 <;> first | rfl | (unfold parseTicks; omega)

def constructorBits (z : ℤ) : List Bool := Computability.encodeNat (KS.W01.intPayload z)

theorem pairBits_encodeRat (q r : ℚ) :
    pairBits (negativeBit q.num) (constructorBits q.num) (Computability.encodeNat q.den)
      (negativeBit r.num) (constructorBits r.num) (Computability.encodeNat r.den) =
      KS.W01.encodeRat q ++ KS.W01.encodeRat r := by
  have hi (z : ℤ) : KS.W01.encodeInt z = negativeBit z :: KS.W01.frame (constructorBits z) := by
    cases z <;> simp [KS.W01.encodeInt, KS.W01.encodeNat, KS.W01.intPayload,
      negativeBit, constructorBits]
  simp [pairBits, KS.W01.encodeRat, hi, KS.W01.encodeNat, List.append_assoc]

theorem pairBits_length (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    (pairBits sa na da sb nb db).length =
      2 * (na.length + da.length + nb.length + db.length) + 6 := by
  simp only [pairBits, List.length_cons, List.length_append, KS.W01.length_frame]
  omega

end KS.W06.RationalCompare

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalCompareProgram
attribute [-simp] _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W06.RationalCompare
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def prepareProgram : Program 13 :=
  compose (compose parseProgram (magnitudeProgram leftMagnitudePorts 1))
    (magnitudeProgram rightMagnitudePorts 4)

theorem prepare_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec prepareProgram (fields (pairBits sa na da sb nb db) [] [] [] [] [] [])
      (workFields [sa] (magnitude sa na) da [sb] (magnitude sb nb) db [] [])
      (parseTicks na da nb db + (2 * na.length + 4) + (2 * nb.length + 4)) := by
  have hleft : RunSpec (magnitudeProgram leftMagnitudePorts 1)
      (fields [] [sa] na da [sb] nb db)
      (fields [] [sa] (magnitude sa na) da [sb] nb db) (2 * na.length + 4) := by
    have h := magnitude_spec leftMagnitudePorts 1 (fields [] [sa] na da [sb] nb db)
      sa na rfl rfl rfl rfl
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext index; fin_cases index <;> rfl)
  have hright : RunSpec (magnitudeProgram rightMagnitudePorts 4)
      (fields [] [sa] (magnitude sa na) da [sb] nb db)
      (workFields [sa] (magnitude sa na) da [sb] (magnitude sb nb) db [] [])
      (2 * nb.length + 4) := by
    have h := magnitude_spec rightMagnitudePorts 4
      (fields [] [sa] (magnitude sa na) da [sb] nb db) sb nb rfl rfl rfl rfl
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext index; fin_cases index <;> rfl)
  exact ((parse_spec sa na da sb nb db).compose hleft).compose hright

def productsProgram : Program 13 :=
  compose (KS.W29.FixedSequential.liftPorts productProgram leftProductPorts)
    (KS.W29.FixedSequential.liftPorts productProgram rightProductPorts)

theorem products_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec productsProgram (workFields [sa] na da [sb] nb db [] [])
      (productsAfter sa na da sb nb db) (productTicks na db + productTicks nb da) := by
  let middle := workFields [sa] [] da [sb] nb
    (KS.W03.MultiplicationLoop.advance na db) (product na db) []
  have hleft : RunSpec (KS.W29.FixedSequential.liftPorts productProgram leftProductPorts)
      (workFields [sa] na da [sb] nb db [] []) middle (productTicks na db) := by
    have hlocal : RunSpec productProgram
        (fun i => workFields [sa] na da [sb] nb db [] [] (leftProductPorts i))
        (KS.W03.MultiplicationBody.registers [] [] (KS.W03.MultiplicationLoop.advance na db)
          (product na db) [] [] []) (productTicks na db) := by
      convert product_spec [] na db using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)
    have h := runSpec_liftPorts productProgram leftProductPorts
      (workFields [sa] na da [sb] nb db [] []) _ _ hlocal
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext index; fin_cases index <;> rfl)
  have hright : RunSpec (KS.W29.FixedSequential.liftPorts productProgram rightProductPorts)
      middle (productsAfter sa na da sb nb db) (productTicks nb da) := by
    have hlocal : RunSpec productProgram (fun i => middle (rightProductPorts i))
        (KS.W03.MultiplicationBody.registers [] [] (KS.W03.MultiplicationLoop.advance nb da)
          (product nb da) [] [] []) (productTicks nb da) := by
      convert product_spec [] nb da using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)
    have h := runSpec_liftPorts productProgram rightProductPorts middle _ _ hlocal
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext index; fin_cases index <;> rfl)
  exact hleft.compose hright

def program : Program 13 :=
  compose (compose prepareProgram productsProgram) (signedCompareProgram resultPorts 1 4)

def machine : Machine := program.toMachine

def finalStacks (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : Fin 13 → List Bool :=
  signedCompareAfter resultPorts
    (productsAfter sa (magnitude sa na) da sb (magnitude sb nb) db) sa sb

theorem full_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec program (fields (pairBits sa na da sb nb db) [] [] [] [] [] [])
      (finalStacks sa na da sb nb db) (totalTicks sa na da sb nb db) := by
  have hparse := prepare_spec sa na da sb nb db
  have hprod := products_spec sa (magnitude sa na) da sb (magnitude sb nb) db
  have hcompare := signedCompare_spec resultPorts 1 4
    (productsAfter sa (magnitude sa na) da sb (magnitude sb nb) db) sa sb rfl rfl
  exact (hparse.compose hprod).compose hcompare

theorem final_output (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    finalStacks sa na da sb nb db 9 =
      [signedCrossLE sa sb
        (KS.W19.bitsValue (magnitude sa na) * KS.W19.bitsValue db)
        (KS.W19.bitsValue (magnitude sb nb) * KS.W19.bitsValue da)] := by
  have h := signedCompareAfter_output resultPorts
    (productsAfter sa (magnitude sa na) da sb (magnitude sb nb) db) sa sb
  simpa [finalStacks, productsAfter, workFields, resultPorts, product,
    KS.W19.bitsValue_encodeNat] using h

@[simp] theorem machine_stackCount : machine.stackCount = 13 := rfl
@[simp] theorem machine_inputStack : machine.inputStack = (0 : Fin 13) := rfl
@[simp] theorem machine_outputStack : machine.outputStack = (9 : Fin 13) := rfl

end KS.W06.RationalCompare

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalCompareCorrectness
attribute [-simp] _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W06.RationalCompare
open KS.W01.FixedStack KS.W01

theorem magnitude_constructor_value (z : ℤ) :
    KS.W19.bitsValue (magnitude (negativeBit z) (constructorBits z)) = z.natAbs := by
  rw [magnitude, KS.W01.MagnitudeProgram.result_value]
  simp only [constructorBits, KS.W19.bitsValue_encodeNat]
  cases z <;> simp [negativeBit, intPayload, KS.W19.digit]

theorem canonical_final_output (q r : ℚ) :
    finalStacks (negativeBit q.num) (constructorBits q.num) (Computability.encodeNat q.den)
      (negativeBit r.num) (constructorBits r.num) (Computability.encodeNat r.den) 9 =
      [decide (q ≤ r)] := by
  rw [final_output, magnitude_constructor_value, magnitude_constructor_value,
    KS.W19.bitsValue_encodeNat, KS.W19.bitsValue_encodeNat,
    signedCrossLE_correct _ _ _ _ _ _ (negativeBit_pos q.num) (negativeBit_pos r.num)
      q.den_pos r.den_pos, signedFraction_num_den, signedFraction_num_den]

theorem product_length_le (xs ys : List Bool) :
    (product xs ys).length ≤ xs.length + ys.length := by
  simpa [product, KS.W03.BinaryMultiply.multiply, KS.W19.trimBits_eq_encodeNat,
    KS.W03.BinaryMultiply.multiplyRaw_correct] using KS.W03.BinaryMultiply.multiply_length_le xs ys

theorem totalTicks_le_polynomial (sa : Bool) (na da : List Bool)
    (sb : Bool) (nb db : List Bool) :
    totalTicks sa na da sb nb db ≤
      KS.W29.polynomialFuel 128 2 (pairBits sa na da sb nb db).length := by
  let S := na.length + da.length + nb.length + db.length
  have hma := magnitude_length_le sa na
  have hmb := magnitude_length_le sb nb
  have hla := product_length_le (magnitude sa na) db
  have hlb := product_length_le (magnitude sb nb) da
  have hpa := productTicks_le (magnitude sa na) db
  have hpb := productTicks_le (magnitude sb nb) da
  have hwa : (magnitude sa na).length + db.length + 2 ≤ S + 3 := by unfold S; omega
  have hwb : (magnitude sb nb).length + da.length + 2 ≤ S + 3 := by unfold S; omega
  have hpa' := hpa.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hwa 2))
  have hpb' := hpb.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hwb 2))
  have hbound : totalTicks sa na da sb nb db ≤ 64 * (S + 3) ^ 2 := by
    unfold totalTicks parseTicks
    dsimp only
    unfold S at hpa' hpb' ⊢
    nlinarith [Nat.zero_le ((na.length + da.length + nb.length + db.length) ^ 2)]
  apply hbound.trans
  unfold KS.W29.polynomialFuel
  rw [pairBits_length]
  have hL : S + 3 ≤ 2 * (na.length + da.length + nb.length + db.length) + 6 + 1 := by
    unfold S
    omega
  exact Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hL 2)

end KS.W06.RationalCompare

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_CleanRationalCompare
attribute [-simp] _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W19.FixedRun.pack_on_port
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W04.CleanRationalCompare
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

variable {k : Nat}

def haltProgram (output : Fin k) : Program k :=
  ofMachine (compile (0 : Fin 1) output output (fun _ _ _ => Instruction.halt k 1))

def clearListProgram (output : Fin k) : List (Fin k) → Program k
  | [] => haltProgram output
  | port :: ports => compose (BinaryStackMoves.clearProgram port) (clearListProgram output ports)

theorem halt_spec (output : Fin k) (before : Fin k → List Bool) :
    RunSpec (haltProgram output) before before 1 := by
  intro bits hlen
  obtain ⟨coin, rfl⟩ := List.length_eq_one_iff.mp hlen
  change (compile (0 : Fin 1) output output (fun _ _ _ => Instruction.halt k 1)).step
    ⟨some (0 : Fin 1), before⟩ coin = ⟨none, before⟩
  erw [step_compile]
  apply congrArg (Config.mk none)
  funext j
  simp [Instruction.halt, Instruction.action, KS.W29.StackAction.apply]

theorem clear_spec (port : Fin k) (before : Fin k → List Bool) :
    RunSpec (BinaryStackMoves.clearProgram port) before (clearState port before)
      ((before port).length + 1) := by
  intro bits hlen
  exact BinaryStackMoves.run_clear_stacks port before bits hlen

theorem clearList_spec (output : Fin k) (ports : List (Fin k)) (before : Fin k → List Bool) :
    RunSpec (clearListProgram output ports) before (clearListState ports before)
      (clearListTicks ports before) := by
  induction ports generalizing before with
  | nil => exact halt_spec output before
  | cons p ps ih => exact (clear_spec p before).compose (ih (clearState p before))

def cleanupProgram : Program 13 := clearListProgram 9 scratchPorts

def canonicalFinal (q r : ℚ) : Fin 13 → List Bool :=
  KS.W06.RationalCompare.finalStacks
    (KS.W06.RationalCompare.negativeBit q.num) (KS.W06.RationalCompare.constructorBits q.num)
    (Computability.encodeNat q.den) (KS.W06.RationalCompare.negativeBit r.num)
    (KS.W06.RationalCompare.constructorBits r.num) (Computability.encodeNat r.den)

def inputState (q r : ℚ) : Fin 13 → List Bool :=
  KS.W06.RationalCompare.fields (KS.W01.encodeRat q ++ KS.W01.encodeRat r) [] [] [] [] [] []

def comparisonTicks (q r : ℚ) : Nat :=
  KS.W29.polynomialFuel 128 2 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length

theorem canonical_spec (q r : ℚ) :
    RunSpec KS.W06.RationalCompare.program (inputState q r) (canonicalFinal q r)
      (comparisonTicks q r) := by
  have h := KS.W06.RationalCompare.full_spec
    (KS.W06.RationalCompare.negativeBit q.num) (KS.W06.RationalCompare.constructorBits q.num)
    (Computability.encodeNat q.den) (KS.W06.RationalCompare.negativeBit r.num)
    (KS.W06.RationalCompare.constructorBits r.num) (Computability.encodeNat r.den)
  rw [KS.W06.RationalCompare.pairBits_encodeRat] at h
  apply h.mono
  have ht := KS.W06.RationalCompare.totalTicks_le_polynomial
    (KS.W06.RationalCompare.negativeBit q.num) (KS.W06.RationalCompare.constructorBits q.num)
    (Computability.encodeNat q.den) (KS.W06.RationalCompare.negativeBit r.num)
    (KS.W06.RationalCompare.constructorBits r.num) (Computability.encodeNat r.den)
  simp only [KS.W06.RationalCompare.pairBits_encodeRat] at ht
  exact ht

theorem canonicalFinal_length (q r : ℚ) (j : Fin 13) :
    (canonicalFinal q r j).length ≤
      (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length + comparisonTicks q r := by
  let bits := List.replicate (comparisonTicks q r) false
  have hr := canonical_spec q r bits (by simp [bits])
  have hg := KS.W06.RationalCompare.program.toMachine.run_stack_length_le
    ⟨some KS.W06.RationalCompare.program.initial, inputState q r⟩ bits j
  rw [hr] at hg
  have hi : (inputState q r j).length ≤ (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length := by
    fin_cases j <;> simp [inputState, KS.W06.RationalCompare.fields]
  simpa only [bits, List.length_replicate] using hg.trans (Nat.add_le_add_right hi _)

theorem clear_canonicalFinal (q r : ℚ) :
    clearListState scratchPorts (canonicalFinal q r) = flagState (decide (q ≤ r)) := by
  funext j
  rw [clearListState_apply]
  fin_cases j <;> simp [scratchPorts, flagState]
  exact KS.W06.RationalCompare.canonical_final_output q r

def cleanedComparator : Program 13 := compose KS.W06.RationalCompare.program cleanupProgram

def totalTicks (q r : ℚ) : Nat :=
  comparisonTicks q r + clearListTicks scratchPorts (canonicalFinal q r)

theorem cleaned_spec (q r : ℚ) :
    RunSpec cleanedComparator (inputState q r) (flagState (decide (q ≤ r))) (totalTicks q r) := by
  have h := (canonical_spec q r).compose (clearList_spec 9 scratchPorts (canonicalFinal q r))
  rw [clear_canonicalFinal] at h
  exact h

theorem totalTicks_le_polynomial (q r : ℚ) :
    totalTicks q r ≤ KS.W29.polynomialFuel 2048 2
      (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length := by
  have h := clearListTicks_le scratchPorts (canonicalFinal q r)
    ((KS.W01.encodeRat q ++ KS.W01.encodeRat r).length + comparisonTicks q r)
    (canonicalFinal_length q r)
  change clearListTicks scratchPorts (canonicalFinal q r) ≤
    12 * ((KS.W01.encodeRat q ++ KS.W01.encodeRat r).length + comparisonTicks q r + 1) + 1 at h
  dsimp only [totalTicks, comparisonTicks, KS.W29.polynomialFuel] at h ⊢
  nlinarith [Nat.zero_le ((KS.W01.encodeRat q ++ KS.W01.encodeRat r).length ^ 2)]

theorem cleaned_polynomial_spec (q r : ℚ) :
    RunSpec cleanedComparator (inputState q r) (flagState (decide (q ≤ r)))
      (KS.W29.polynomialFuel 2048 2 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) :=
  (cleaned_spec q r).mono (totalTicks_le_polynomial q r)

@[simp] theorem cleaned_output : cleanedComparator.output = 9 := rfl

end KS.W04.CleanRationalCompare

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedRun
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W29.BinaryMachine.withEntry_init_stacks _root_.OAI.KS.W29.BinaryMachine.withEntry_init_state _root_.OAI.KS.W29.BinaryMachine.withEntry_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.FixedRun
open KS.W01.FixedStack

@[simp] theorem project_pack {k q : Nat} (ports : Fin 3 ↪ Fin k) (c : KS.W29.Config q)
    (rest : Fin k → List Bool) : project ports (pack ports c rest) = c := by
  cases c with
  | mk state «stacks» =>
    change KS.W29.Config.mk state _ = KS.W29.Config.mk state «stacks»
    congr 1
    funext j
    exact pack_on_port ports _ rest j

end KS.W19.FixedRun

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_DivisionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.DivisionMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun

def copyTrial : Program 10 := KS.W01.FixedCopy.program trialPorts
def copyDivisor : Program 10 := KS.W01.FixedCopy.program divisorPorts
def subtract : Program 10 := ofMachine (lift3 BorrowSubtractor.machine subtractPorts)
def prepareTail : Program 10 := compose copyDivisor subtract
def prepare : Program 10 := compose copyTrial prepareTail

def keepTrial : Program 10 := KS.W04.BinaryStackMoves.clearProgram 8
def trimCandidate : Program 10 := ofMachine (lift3 BinaryTrimMachine.machine trimPorts)
def useCandidate : Program 10 := compose (KS.W04.BinaryStackMoves.clearProgram 4) trimCandidate

def select (heads : Fin 10 → Fin 3) (_coin : Bool) : KS.W29.FixedBranch.SelectInstruction 10 :=
  let borrowed := (heads 6).val == 2
  ⟨if borrowed then .left else .right,
    Vector.ofFn (fun j => if j = 6 then .pop else if j = 5 then .push (!borrowed) else .stay)⟩

def choose : Program 10 := KS.W29.FixedBranch.branch keepTrial useCandidate 5 select
def body : Program 10 := compose prepare choose

def guard (heads : Fin 10 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 10 :=
  if (heads 3).val = 0 then ⟨.halt, Vector.ofFn (fun _ => .stay)⟩
  else ⟨.call, Vector.ofFn (fun j => if j = 3 then .pop
    else if j = 4 then .push ((heads 3).val == 2) else .stay)⟩

def loop : Program 10 := KS.W29.FixedLoop.loop body guard

end KS.W19.DivisionMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_PositiveWireSerializer
attribute [-simp] _root_.OAI.KS.W01.FixedStack.lift3_project_init _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W19.FixedRun.project_pack _root_.OAI.KS.W29.BinaryMachine.withEntry_init_stacks _root_.OAI.KS.W29.BinaryMachine.withEntry_init_state _root_.OAI.KS.W29.BinaryMachine.withEntry_initial _root_.OAI.KS.W29.BinaryMachine.withEntry_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W28.PositiveWireSerializer
open KS.W29

theorem step_num_prefix (a : Bool) (xs ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some 0) (a :: xs) ys zs) coin =
      cfg (some 1) (a :: xs) ys (false :: zs) := by
  unfold machine
  erw [FiniteDispatch.step_compile]
  simp only [dispatch, head_left]
  cases a <;> change Config.mk _ _ = Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem step_num_digit (a : Bool) (xs ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some 1) (a :: xs) ys zs) coin =
      cfg (some 0) xs ys (a :: zs) := by
  unfold machine
  erw [FiniteDispatch.step_compile]
  simp only [dispatch, head_left]
  cases a <;> change Config.mk _ _ = Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem step_num_done (ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some 0) [] ys zs) coin = cfg (some 2) [] ys (true :: zs) := by
  unfold machine
  erw [FiniteDispatch.step_compile]
  simp only [dispatch, head_left]
  change Config.mk _ _ = Config.mk _ _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem run_num (xs ys zs coins : List Bool)
    (hlen : coins.length = 2 * xs.length + 2 * ys.length + 2) :
    machine.run (cfg (some 0) xs ys zs) coins =
      cfg none [] [] ((KS.W01.frame xs ++ KS.W01.frame ys).reverse ++ zs) := by
  induction xs generalizing zs coins with
  | nil =>
      cases coins with
      | nil => simp at hlen
      | cons c cs =>
          have hc : cs.length = 2 * ys.length + 1 := by
            simp only [List.length_cons, List.length_nil] at hlen
            omega
          erw [BinaryMachine.run, step_num_done, run_den _ _ _ hc]
          simp [KS.W01.frame, List.reverse_cons, List.append_assoc]
          rfl
  | cons a xs ih =>
      cases coins with
      | nil => simp at hlen
      | cons c cs =>
          cases cs with
          | nil => simp at hlen
          | cons d ds =>
              have hd : ds.length = 2 * xs.length + 2 * ys.length + 2 := by
                simp only [List.length_cons] at hlen
                omega
              erw [BinaryMachine.run, step_num_prefix, BinaryMachine.run, step_num_digit, ih _ _ hd]
              simp [KS.W01.frame, List.reverse_cons, List.reverse_append, List.append_assoc]
              rfl

end KS.W28.PositiveWireSerializer

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_UnsignedPairSerializer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.UnsignedPairSerializer
open KS.W28
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

@[simp] theorem registers_port {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (spare : Fin k → List Bool) (xs ys zs : List Bool) (i : Fin 3) :
    registers ports spare xs ys zs (ports i) =
      if i = 0 then xs else if i = 1 then ys else zs := by
  fin_cases i <;> simp [registers, ports.injective.eq_iff]

theorem registers_other {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (spare : Fin k → List Bool) (xs ys zs : List Bool) (j : Fin k)
    (hj : ∀ i, j ≠ ports i) : registers ports spare xs ys zs j = spare j := by
  simp [registers, hj 0, hj 1, hj 2]

end KS.W19.UnsignedPairSerializer

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_FixedSubtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.FixedSubtraction
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19.UnsignedPairSerializer (registers registers_port registers_other)

def program {k : Nat} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 CanonicalSubtraction.machine ports)

end KS.W19.FixedSubtraction

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_GCDMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.GCDMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

def clearQuotient : Program 10 := KS.W04.BinaryStackMoves.clearProgram 5
def advanceDividend : Program 10 := KS.W04.BinaryStackMoves.moveProgram 2 3
def reverseRemainder : Program 10 := KS.W04.BinaryStackMoves.moveProgram 4 8
def trimRemainder : Program 10 := ofMachine (lift3 BinaryTrimMachine.machine remainderPorts)
def cleanup : Program 10 := compose clearQuotient
  (compose advanceDividend (compose reverseRemainder trimRemainder))
def body : Program 10 := compose DivisionMachine.loop cleanup

def guard (heads : Fin 10 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 10 :=
  ⟨if (heads 2).val = 0 then .halt else .call, Vector.ofFn (fun _ => .stay)⟩
def loop : Program 10 := KS.W29.FixedLoop.loop body guard

def finish : Program 10 := KS.W04.BinaryStackMoves.moveProgram 3 5
def program : Program 10 := compose loop finish

end KS.W30.GCDMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedCanonicalize
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.FixedCanonicalize
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19.UnsignedPairSerializer (registers registers_port registers_other)

def trimProgram {k : Nat} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 BinaryTrimMachine.machine ports)

theorem trim_spec {k : Nat} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (input payload : List Bool) :
    RunSpec (trimProgram ports) (registers ports spare input [] payload.reverse)
      (registers ports spare input (Computability.encodeNat (bitsValue payload)) [])
      (payload.length + 1) := by
  intro bits hb
  change (lift3 BinaryTrimMachine.machine ports).run
    ⟨some (0 : Fin 2), registers ports spare input [] payload.reverse⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some (0 : Fin 2), registers ports spare input [] payload.reverse⟩ : Config k 2) =
        BinaryTrimMachine.cfg (some 0) input [] payload.reverse := by
      apply congrArg (KS.W29.Config.mk (some (0 : Fin 2)))
      funext j
      fin_cases j <;> simp
    have hr := congrArg (fun c => BinaryTrimMachine.machine.run c bits) hp
    refine hr.trans ?_
    refine (BinaryTrimMachine.run_payload input payload bits hb).trans ?_
    apply congrArg (KS.W29.Config.mk none)
    funext j
    fin_cases j <;> simp
  · intro j hj
    exact (registers_other ports spare _ _ _ j hj).trans
      (registers_other ports spare _ _ _ j hj).symm

end KS.W19.FixedCanonicalize

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalAddPrimitives
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W13.RationalAdd

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19
open KS.W19.UnsignedPairSerializer (registers registers_port registers_other)

def rawAddProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 KS.W01.BinaryAdder.machine ports)

def addTrimProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 BinaryTrimMachine.machine ports)

def canonicalAddProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  compose (rawAddProgram ports) (addTrimProgram ports)

theorem rawAdd_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs ys : List Bool) :
    RunSpec (rawAddProgram ports) (registers ports spare xs ys [])
      (registers ports spare [] [] (KS.W01.BinaryAdder.addBits false xs ys).reverse)
      (max xs.length ys.length + 1) := by
  intro bits hbits
  change (lift3 KS.W01.BinaryAdder.machine ports).run
    ⟨some (0 : Fin 2), registers ports spare xs ys []⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some (0 : Fin 2), registers ports spare xs ys []⟩ : Config k 2) =
        KS.W01.BinaryAdder.cfg (some 0) xs ys [] := by
      apply congrArg (KS.W29.Config.mk (some (0 : Fin 2)))
      funext i
      fin_cases i <;> simp
    have hr := congrArg (fun c => KS.W01.BinaryAdder.machine.run c bits) hp
    have h := KS.W01.BinaryAdder.run_add false xs ys [] bits hbits
    change KS.W01.BinaryAdder.machine.run (KS.W01.BinaryAdder.cfg (some 0) xs ys []) bits = _ at h
    refine hr.trans (h.trans ?_)
    apply congrArg₂ KS.W29.Config.mk rfl
    funext i
    fin_cases i <;> simp
  · intro j hj
    change registers ports spare [] [] (KS.W01.BinaryAdder.addBits false xs ys).reverse j =
      registers ports spare xs ys [] j
    simp only [registers_other _ _ _ _ _ _ hj]

theorem canonicalAdd_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs ys : List Bool) :
    RunSpec (canonicalAddProgram ports) (registers ports spare xs ys [])
      (registers ports spare [] (addResult xs ys) []) (canonicalAddTicks xs ys) := by
  have htrim := KS.W19.FixedCanonicalize.trim_spec ports spare []
    (KS.W01.BinaryAdder.addBits false xs ys)
  have h := (rawAdd_spec ports spare xs ys).compose htrim
  have he : bitsValue (KS.W01.BinaryAdder.addBits false xs ys) = bitsValue xs + bitsValue ys := by
    simpa using KS.W01.BinaryAdder.addBits_correct false xs ys
  simpa only [canonicalAddProgram, addTrimProgram, KS.W19.FixedCanonicalize.trimProgram,
    canonicalAddTicks, addResult, he] using h

end KS.W13.RationalAdd

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMagnitudeMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.RationalMagnitudeMachine
open KS.W01.FixedStack KS.W29.FixedSequential
open KS.W19

def copyNumerator : Program 13 := KS.W01.FixedCopy.program numeratorCopyPorts
def reverseNumeratorCopy : Program 13 := KS.W04.BinaryStackMoves.moveProgram 1 3
def copyDenominator : Program 13 := KS.W01.FixedCopy.program denominatorCopyPorts
def gcd : Program 13 := KS.W29.FixedSequential.liftPorts GCDMachine.program corePorts
def reverseGCD : Program 13 := KS.W04.BinaryStackMoves.moveProgram 5 8
def placeGCD : Program 13 := KS.W04.BinaryStackMoves.moveProgram 8 2
def takeNumerator : Program 13 := KS.W04.BinaryStackMoves.moveProgram 10 3
def takeDenominator : Program 13 := KS.W04.BinaryStackMoves.moveProgram 11 3
def divide : Program 13 := KS.W29.FixedSequential.liftPorts DivisionMachine.loop corePorts
def reverseQuotient : Program 13 := KS.W04.BinaryStackMoves.moveProgram 5 8
def trimNumerator : Program 13 := ofMachine (lift3 BinaryTrimMachine.machine numeratorTrimPorts)
def trimDenominator : Program 13 := ofMachine (lift3 BinaryTrimMachine.machine denominatorTrimPorts)
def clearRemainder : Program 13 := KS.W04.BinaryStackMoves.clearProgram 4
def clearGCD : Program 13 := KS.W04.BinaryStackMoves.clearProgram 2

def signDispatch (s : Fin 2) (heads : Fin 13 → Fin 3) (_coin : Bool) : Instruction 13 2 :=
  if s = 0 then
    if (heads 10).val = 0 then
      ⟨some 1, Vector.ofFn (fun j => if j = 12 then .pop else .stay)⟩
    else Instruction.halt 13 2
  else ⟨none, Vector.ofFn (fun j => if j = 12 then .push false else .stay)⟩
def normalizeSign : Program 13 := ofMachine (compile 0 10 10 signDispatch)

def oneDispatch (_s : Fin 1) (_heads : Fin 13 → Fin 3) (_coin : Bool) : Instruction 13 1 :=
  ⟨none, Vector.ofFn (fun j => if j = 11 then .push true else .stay)⟩
def insertOne : Program 13 := ofMachine (compile 0 10 10 oneDispatch)
def zeroBranch : Program 13 := compose (KS.W04.BinaryStackMoves.clearProgram 10)
  (compose insertOne normalizeSign)

def prepare : Program 13 := compose copyNumerator (compose reverseNumeratorCopy copyDenominator)
def computeGCD : Program 13 := compose prepare (compose gcd (compose reverseGCD placeGCD))
def reduceNumerator : Program 13 := compose takeNumerator
  (compose divide (compose reverseQuotient (compose trimNumerator clearRemainder)))
def reduceDenominator : Program 13 := compose takeDenominator
  (compose divide (compose reverseQuotient (compose trimDenominator clearRemainder)))
def positiveBranch : Program 13 := compose computeGCD
  (compose reduceNumerator (compose reduceDenominator (compose clearGCD normalizeSign)))

def selector (heads : Fin 13 → Fin 3) (_coin : Bool) : KS.W29.FixedBranch.SelectInstruction 13 :=
  ⟨if (heads 11).val = 0 then .left else .right, Vector.ofFn (fun _ => .stay)⟩
def program : Program 13 := KS.W29.FixedBranch.branch zeroBranch positiveBranch 10 selector

end KS.W30.RationalMagnitudeMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMultiplyProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W15.RationalMultiply
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare (workFields product productProgram productTicks runSpec_liftPorts)

def productsProgram : Program 13 :=
  compose (KS.W29.FixedSequential.liftPorts productProgram numeratorPorts)
    (KS.W29.FixedSequential.liftPorts productProgram denominatorPorts)

def xorDispatch (_ : Fin 1) (heads : Fin 13 → Fin 3) (_coin : Bool) : Instruction 13 1 :=
  ⟨none, Vector.ofFn (fun j => if j = 1 ∨ j = 4 then .pop
    else if j = 12 then .push (((heads 1).val == 2) ^^ ((heads 4).val == 2)) else .stay)⟩

def xorProgram : Program 13 := ofMachine (compile 0 1 12 xorDispatch)

def cleanupProgram : Program 13 :=
  compose (compose (compose (compose (compose (compose
    (KS.W04.BinaryStackMoves.clearProgram 5) (KS.W04.BinaryStackMoves.clearProgram 6))
      xorProgram) (KS.W04.BinaryStackMoves.moveProgram 7 0))
        (KS.W04.BinaryStackMoves.moveProgram 0 10))
          (KS.W04.BinaryStackMoves.moveProgram 8 0))
            (KS.W04.BinaryStackMoves.moveProgram 0 11)

end KS.W15.RationalMultiply

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalAddProducts
attribute [-simp] _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W13.RationalAdd

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare (product productProgram productTicks)
open KS.W15.RationalMultiply (clear_spec clearAfter)

theorem core_spec (P : Program 13) (before after : Fin 13 → List Bool)
    (a b c : List Bool) (ticks : ℕ) (h : RunSpec P before after ticks) :
    RunSpec (KS.W29.FixedSequential.liftPorts P corePorts)
      (extend before a b c) (extend after a b c) ticks := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec P corePorts before after _ _ ticks h
  · intro i; exact extend_core before a b c i
  · intro i; exact extend_core after a b c i
  · intro j hj
    by_cases hsmall : j.val < 13
    · exact (hj ⟨j.val, hsmall⟩ (Fin.ext rfl)).elim
    · simp [extend, hsmall]

def prepareProgram : Program 16 :=
  KS.W29.FixedSequential.liftPorts KS.W06.RationalCompare.prepareProgram corePorts

theorem prepare_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec prepareProgram (inputState (KS.W06.RationalCompare.pairBits sa na da sb nb db))
      (preparedState sa (KS.W06.RationalCompare.magnitude sa na) da
        sb (KS.W06.RationalCompare.magnitude sb nb) db)
      (KS.W06.RationalCompare.parseTicks na da nb db + (2 * na.length + 4) + (2 * nb.length + 4)) :=
  core_spec _ _ _ [] [] [] _ (KS.W06.RationalCompare.prepare_spec sa na da sb nb db)

def saveDenominators : Program 16 :=
  compose (KS.W01.FixedCopy.program leftDenCopyPorts) (KS.W01.FixedCopy.program rightDenCopyPorts)

theorem saveDenominators_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec saveDenominators (preparedState sa na da sb nb db) (savedState sa na da sb nb db)
      ((2 * da.length + 2) + (2 * db.length + 2)) := by
  let middle := extend (KS.W06.RationalCompare.workFields [sa] na da [sb] nb db [] []) da [] []
  have hl : RunSpec (KS.W01.FixedCopy.program leftDenCopyPorts)
      (preparedState sa na da sb nb db) middle (2 * da.length + 2) := by
    apply KS.W03.MachineRoundTrip.runSpec_ofMachine (KS.W01.FixedCopy.machine leftDenCopyPorts)
    intro bits hb
    have h := KS.W01.FixedCopy.run_copy_restore leftDenCopyPorts (preparedState sa na da sb nb db)
      da bits rfl rfl rfl hb
    refine h.trans ?_
    apply congrArg (Config.mk none)
    funext j
    fin_cases j <;> rfl
  have hr : RunSpec (KS.W01.FixedCopy.program rightDenCopyPorts)
      middle (savedState sa na da sb nb db) (2 * db.length + 2) := by
    apply KS.W03.MachineRoundTrip.runSpec_ofMachine (KS.W01.FixedCopy.machine rightDenCopyPorts)
    intro bits hb
    have h := KS.W01.FixedCopy.run_copy_restore rightDenCopyPorts middle db bits rfl rfl rfl hb
    refine h.trans ?_
    apply congrArg (Config.mk none)
    funext j
    fin_cases j <;> rfl
  exact hl.compose hr

def crossProductsProgram : Program 16 :=
  KS.W29.FixedSequential.liftPorts KS.W06.RationalCompare.productsProgram corePorts

def denominatorProductProgram : Program 16 :=
  KS.W29.FixedSequential.liftPorts productProgram denominatorProductPorts

theorem denominatorProduct_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec denominatorProductProgram
      (extend (KS.W06.RationalCompare.productsAfter sa na da sb nb db) da db [])
      (productsAfter sa na da sb nb db) (productTicks da db) := by
  let before := extend (KS.W06.RationalCompare.productsAfter sa na da sb nb db) da db []
  have hlocal : RunSpec productProgram (fun i => before (denominatorProductPorts i))
      (KS.W03.MultiplicationBody.registers [] [] (KS.W03.MultiplicationLoop.advance da db)
        (product da db) [] [] []) (productTicks da db) := by
    convert KS.W06.RationalCompare.product_spec [] da db using 1 <;>
      first | rfl | (funext i; fin_cases i <;> rfl)
  have h := KS.W06.RationalCompare.runSpec_liftPorts productProgram denominatorProductPorts before _ _ hlocal
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)

def productsProgram : Program 16 :=
  compose (compose saveDenominators crossProductsProgram) denominatorProductProgram

theorem products_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec productsProgram (preparedState sa na da sb nb db) (productsAfter sa na da sb nb db)
      (productsTicks na da nb db) := by
  have hcross := core_spec KS.W06.RationalCompare.productsProgram _ _ da db [] _
    (KS.W06.RationalCompare.products_spec sa na da sb nb db)
  exact ((saveDenominators_spec sa na da sb nb db).compose hcross).compose
    (denominatorProduct_spec sa na da sb nb db)

def clearProductsProgram : Program 16 :=
  compose (compose (KS.W04.BinaryStackMoves.clearProgram 3) (KS.W04.BinaryStackMoves.clearProgram 6))
    (KS.W04.BinaryStackMoves.clearProgram 14)

theorem clearProducts_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec clearProductsProgram (productsAfter sa na da sb nb db)
      (signedState sa (product na db) sb (product nb da) (product da db))
      (clearProductsTicks na da nb db) := by
  have h1 := clear_spec (3 : Fin 16) (productsAfter sa na da sb nb db)
  have h2 := clear_spec (6 : Fin 16) (clearAfter 3 (productsAfter sa na da sb nb db))
  have h3 := clear_spec (14 : Fin 16) (clearAfter 6 (clearAfter 3 (productsAfter sa na da sb nb db)))
  have h := (h1.compose h2).compose h3
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)

end KS.W13.RationalAdd

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalAddSigned
attribute [-simp] _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W13.RationalAdd
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W15.RationalMultiply (move_spec moveAfter clear_spec clearAfter)
open KS.W06.RationalCompare (sign_spec signAfter signProgram branch_spec_left branch_spec_right)
open KS.W19.UnsignedPairSerializer (registers)

def finishNumeratorProgram (loc signPort : Fin 16) : Program 16 :=
  compose (compose (compose (compose (compose (compose
    (KS.W04.BinaryStackMoves.moveProgram loc 0)
    (KS.W04.BinaryStackMoves.moveProgram 0 10))
    (signProgram signPort 12))
    (KS.W04.BinaryStackMoves.clearProgram 1))
    (KS.W04.BinaryStackMoves.clearProgram 4))
    (KS.W04.BinaryStackMoves.moveProgram 15 0))
    (KS.W04.BinaryStackMoves.moveProgram 0 11)

theorem finishNumerator_spec (sa sb : Bool) (loc signPort : Fin 16) (num den : List Bool)
    (hloc : loc = 7 ∨ loc = 8) (hsp : signPort = 1 ∨ signPort = 4) :
    RunSpec (finishNumeratorProgram loc signPort) (numeratorAt sa sb loc num den)
      (readyState (if signPort = 1 then sa else sb) num den)
      (2 * num.length + 2 * den.length + 8) := by
  let chosen := if signPort = 1 then sa else sb
  have h1 := move_spec loc (0 : Fin 16) (by rcases hloc with rfl | rfl <;> decide)
    (numeratorAt sa sb loc num den)
  have h2 := move_spec (0 : Fin 16) 10 (by decide)
    (moveAfter loc 0 (numeratorAt sa sb loc num den))
  have h3 := sign_spec signPort (12 : Fin 16) (by rcases hsp with rfl | rfl <;> decide)
    (moveAfter 0 10 (moveAfter loc 0 (numeratorAt sa sb loc num den))) chosen []
    (by rcases hloc with rfl | rfl <;> rcases hsp with rfl | rfl <;> rfl)
  have h4 := clear_spec (1 : Fin 16) (signAfter signPort 12
    (moveAfter 0 10 (moveAfter loc 0 (numeratorAt sa sb loc num den))) chosen [])
  have h5 := clear_spec (4 : Fin 16) (clearAfter 1 (signAfter signPort 12
    (moveAfter 0 10 (moveAfter loc 0 (numeratorAt sa sb loc num den))) chosen []))
  have h6 := move_spec (15 : Fin 16) 0 (by decide) (clearAfter 4 (clearAfter 1 (signAfter signPort 12
    (moveAfter 0 10 (moveAfter loc 0 (numeratorAt sa sb loc num den))) chosen [])))
  have h7 := move_spec (0 : Fin 16) 11 (by decide) (moveAfter 15 0
    (clearAfter 4 (clearAfter 1 (signAfter signPort 12
      (moveAfter 0 10 (moveAfter loc 0 (numeratorAt sa sb loc num den))) chosen []))))
  have h := (((((h1.compose h2).compose h3).compose h4).compose h5).compose h6).compose h7
  rcases hloc with rfl | rfl <;> rcases hsp with rfl | rfl
  all_goals
    convert h using 1 <;>
      first
      | rfl
      | (funext j; fin_cases j <;> simp [chosen, numeratorAt, signedState, readyState, extend,
          KS.W30.RationalMagnitudeMachine.state, KS.W30.RationalMagnitudeMachine.«stacks», moveAfter, clearAfter, signAfter])
      | (simp [numeratorAt, signedState, moveAfter, clearAfter, signAfter]; omega)

def equalProgram : Program 16 := compose (canonicalAddProgram addPorts) (finishNumeratorProgram 8 1)
def leftLargeProgram : Program 16 := compose (KS.W19.FixedSubtraction.program addPorts) (finishNumeratorProgram 8 1)
def rightLargeProgram : Program 16 := compose (KS.W19.FixedSubtraction.program rightSubtractPorts) (finishNumeratorProgram 7 4)

def copyCompareProgram : Program 16 := compose
  (compose (KS.W01.FixedCopy.program compareLeftCopyPorts) (KS.W01.FixedCopy.program compareRightCopyPorts))
  (KS.W28.FixedCompare.program comparePorts)

theorem copyCompare_spec (sa sb : Bool) (xs ys den : List Bool) :
    RunSpec copyCompareProgram (signedState sa xs sb ys den) (comparedState sa xs sb ys den)
      (3 * xs.length + 3 * ys.length + 5) := by
  let middle := Function.update (signedState sa xs sb ys den) 10 xs
  let copied := Function.update middle 11 ys
  have hl : RunSpec (KS.W01.FixedCopy.program compareLeftCopyPorts)
      (signedState sa xs sb ys den) middle (2 * xs.length + 2) := by
    apply KS.W03.MachineRoundTrip.runSpec_ofMachine (KS.W01.FixedCopy.machine compareLeftCopyPorts)
    intro bits hb
    exact KS.W01.FixedCopy.run_copy_restore compareLeftCopyPorts _ xs bits rfl rfl rfl hb
  have hr : RunSpec (KS.W01.FixedCopy.program compareRightCopyPorts)
      middle copied (2 * ys.length + 2) := by
    apply KS.W03.MachineRoundTrip.runSpec_ofMachine (KS.W01.FixedCopy.machine compareRightCopyPorts)
    intro bits hb
    exact KS.W01.FixedCopy.run_copy_restore compareRightCopyPorts _ ys bits rfl rfl rfl hb
  have hc : RunSpec (KS.W28.FixedCompare.program comparePorts) copied
      (comparedState sa xs sb ys den) (xs.length + ys.length + 1) := by
    convert KS.W28.FixedCompare.compare_spec_linear comparePorts copied using 1 <;>
      first | rfl | (funext j; fin_cases j <;> rfl)
  convert (hl.compose hr).compose hc using 1 <;> first | rfl | omega

def orderedBranch : Program 16 := KS.W29.FixedBranch.branch
  (compose (KS.W04.BinaryStackMoves.clearProgram 12) leftLargeProgram)
  (compose (KS.W04.BinaryStackMoves.clearProgram 12) rightLargeProgram)
  10 (KS.W06.RationalCompare.signSelect 12)

def differentProgram : Program 16 := compose copyCompareProgram orderedBranch

def equalSignSelect (heads : Fin 16 → Fin 3) (_coin : Bool) : KS.W29.FixedBranch.SelectInstruction 16 :=
  ⟨if heads 1 = heads 4 then .left else .right, KS.W06.RationalCompare.stayActions 16⟩

def signedProgram : Program 16 := KS.W29.FixedBranch.branch equalProgram differentProgram 10 equalSignSelect

end KS.W13.RationalAdd

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_WireMagnitude
attribute [-simp] _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01.WireMagnitude
open KS.W19

def wireInt (negative : Bool) (magnitude : List Bool) : List Bool :=
  negative :: frame (constructorPayload negative magnitude)

theorem constructorPayload_encode (n : ℤ) :
    constructorPayload (decide (n < 0)) (Computability.encodeNat n.natAbs) =
      Computability.encodeNat (intPayload n) := by
  cases n with
  | ofNat n =>
      simp [constructorPayload, intPayload, trimBits_eq_encodeNat, bitsValue_encodeNat]
  | negSucc n =>
      simpa [constructorPayload, intPayload] using decrement_encode_succ n

theorem wireInt_encode (n : ℤ) :
    wireInt (decide (n < 0)) (Computability.encodeNat n.natAbs) = encodeInt n := by
  unfold wireInt
  rw [constructorPayload_encode]
  cases n <;> simp [encodeInt, encodeNat, intPayload]

def wireRat (negative : Bool) (numerator denominator : List Bool) : List Bool :=
  wireInt negative numerator ++ frame (trimBits denominator)

theorem wireRat_encode (q : ℚ) :
    wireRat (decide (q.num < 0)) (Computability.encodeNat q.num.natAbs)
      (Computability.encodeNat q.den) = encodeRat q := by
  rw [wireRat, wireInt_encode]
  simp [encodeRat, encodeNat, trimBits_eq_encodeNat, bitsValue_encodeNat]

end KS.W01.WireMagnitude

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SignedSerializePrimitives
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W19.FixedRun.project_pack _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W01.SignedSerializePrimitives
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W28.FixedPositiveSerializer (registers registers_other)

def pairMachine : KS.W29.BinaryMachine := KS.W28.PositiveWireSerializer.machine.withEntry (0 : Fin 5)

def pairProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 pairMachine ports)

theorem pair_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs ys zs : List Bool) :
    RunSpec (pairProgram ports) (registers ports spare xs ys zs)
      (registers ports spare [] [] ((frame xs ++ frame ys).reverse ++ zs))
      (2 * xs.length + 2 * ys.length + 2) := by
  intro bits hbits
  change (lift3 pairMachine ports).run
    ⟨some (0 : Fin 5), registers ports spare xs ys zs⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some 0, registers ports spare xs ys zs⟩ : Config k 5) =
        KS.W28.PositiveWireSerializer.cfg (some 0) xs ys zs := by
      change KS.W29.Config.mk _ (fun j => registers ports spare xs ys zs (ports j)) =
        KS.W29.Config.mk _ _
      congr 1
      funext j
      fin_cases j <;> simp
    erw [hp]
    change (KS.W28.PositiveWireSerializer.machine.withEntry (0 : Fin 5)).run _ bits = _
    erw [KS.W29.BinaryMachine.withEntry_run,
      KS.W28.PositiveWireSerializer.run_num xs ys zs bits hbits]
    change KS.W29.Config.mk none
      (KS.W28.PositiveWireSerializer.cfg none [] [] ((frame xs ++ frame ys).reverse ++ zs)).«stacks» = _
    congr 1
    funext j
    fin_cases j <;> simp [KS.W28.PositiveWireSerializer.cfg]
  · intro j hj
    change registers ports spare [] [] ((frame xs ++ frame ys).reverse ++ zs) j =
      registers ports spare xs ys zs j
    rw [registers_other _ _ _ _ _ _ hj, registers_other _ _ _ _ _ _ hj]

def subtractProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 KS.W19.CanonicalSubtraction.machine ports)

theorem decrement_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs : List Bool) :
    RunSpec (subtractProgram ports) (registers ports spare xs [true] [])
      (registers ports spare [] (WireMagnitude.decrement xs) [])
      (2 * (max xs.length 1 + 1)) := by
  intro bits hbits
  let cut := max xs.length 1 + 1
  have ht : (bits.take cut).length = max xs.length ([true] : List Bool).length + 1 := by
    simp only [List.length_cons, List.length_nil, List.length_take]
    change min cut bits.length = cut
    apply Nat.min_eq_left
    dsimp [cut]
    omega
  have hd : (bits.drop cut).length = max xs.length ([true] : List Bool).length + 1 := by
    simp only [List.length_drop, List.length_cons, List.length_nil]
    dsimp [cut]
    omega
  change (lift3 KS.W19.CanonicalSubtraction.machine ports).run
    ⟨some KS.W19.CanonicalSubtraction.machine.initial,
      registers ports spare xs [true] []⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports
        (⟨some KS.W19.CanonicalSubtraction.machine.initial,
          registers ports spare xs [true] []⟩ :
            Config k KS.W19.CanonicalSubtraction.machine.states) =
        KS.W29.Sequential.liftLeft KS.W19.BinarySubtractor.machine KS.W19.BinaryTrimMachine.machine
          (KS.W19.BinarySubtractor.cfg (some 0) xs [true] []) := by
      change KS.W29.Config.mk _ (fun j => registers ports spare xs [true] [] (ports j)) =
        KS.W29.Config.mk _ _
      congr 1
      funext j
      fin_cases j <;> simp [KS.W19.BinarySubtractor.cfg]
    erw [hp, ← List.take_append_drop cut bits,
      KS.W19.CanonicalSubtraction.run_exact xs [true] _ _ ht hd]
    change KS.W29.Config.mk none
      (KS.W19.BinaryTrimMachine.cfg none []
        (Computability.encodeNat (KS.W19.bitsValue (KS.W19.subtractBits xs [true] false))) []).«stacks» = _
    congr 1
    funext j
    fin_cases j <;> simp [KS.W19.BinaryTrimMachine.cfg,
      WireMagnitude.decrement, KS.W19.trimBits_eq_encodeNat]
  · intro j hj
    change registers ports spare [] (WireMagnitude.decrement xs) [] j =
      registers ports spare xs [true] [] j
    rw [registers_other _ _ _ _ _ _ hj, registers_other _ _ _ _ _ _ hj]

end KS.W01.SignedSerializePrimitives

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_SignedRationalSerializer
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01.SignedRationalSerializer
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W28.FixedPositiveSerializer (registers reverseProgram reverse_spec)
open SignedSerializePrimitives

def signedWire (sgn : Bool) (num den : List Bool) : List Bool :=
  sgn :: (frame num ++ frame den)
def rawWire (sgn : Bool) (num den : List Bool) : List Bool :=
  signedWire sgn (if sgn then WireMagnitude.decrement num else num) den

theorem signedWire_length (sgn : Bool) (num den : List Bool) :
    (signedWire sgn num den).length = 2 * num.length + 2 * den.length + 3 := by
  simp only [signedWire, List.length_cons, List.length_append, length_frame]
  omega

def pushDispatch (_ : Fin 1) (_ : Fin 13 → Fin 3) (_ : Bool) : Instruction 13 1 :=
  ⟨none, Vector.ofFn (fun j => if j = 9 then .push true else .stay)⟩
def pushOne : Program 13 := ofMachine (compile (0 : Fin 1) (10 : Fin 13) 9 pushDispatch)
def positiveBranch : Program 13 := compose (pairProgram positivePorts) (reverseProgram reversePorts)
def negativeBranch : Program 13 := compose pushOne
  (compose (subtractProgram subtractPorts)
    (compose (pairProgram negativePorts) (reverseProgram reversePorts)))

def selector (heads : Fin 13 → Fin 3) (_ : Bool) : KS.W29.FixedBranch.SelectInstruction 13 :=
  ⟨if (heads 12).val = 2 then .right else .left,
    Vector.ofFn (fun j => if j = 12 then .pop
      else if j = 8 then .push (decide ((heads 12).val = 2)) else .stay)⟩
def program : Program 13 := KS.W29.FixedBranch.branch positiveBranch negativeBranch 10 selector

@[simp] theorem stackCount : program.toMachine.stackCount = 13 := rfl
@[simp] theorem inputPort : program.toMachine.inputStack = (10 : Fin 13) := rfl
@[simp] theorem outputPort : program.toMachine.outputStack = (10 : Fin 13) := rfl

theorem selector_false (num den : List Bool) (coin : Bool) :
    program.toMachine.step ⟨some program.initial, inputState num den false⟩ coin =
      KS.W29.FixedBranch.liftLeft positiveBranch negativeBranch
        ⟨some positiveBranch.initial, selectedState num den false⟩ := by
  change (KS.W29.FixedBranch.branch positiveBranch negativeBranch 10 selector).toMachine.step
    ⟨some (KS.W29.FixedBranch.start positiveBranch negativeBranch),inputState num den false⟩ coin = _
  erw [KS.W29.FixedBranch.step_start]
  change Config.mk _ _ = Config.mk _ _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem selector_true (num den : List Bool) (coin : Bool) :
    program.toMachine.step ⟨some program.initial, inputState num den true⟩ coin =
      KS.W29.FixedBranch.liftRight positiveBranch negativeBranch
        ⟨some negativeBranch.initial, selectedState num den true⟩ := by
  change (KS.W29.FixedBranch.branch positiveBranch negativeBranch 10 selector).toMachine.step
    ⟨some (KS.W29.FixedBranch.start positiveBranch negativeBranch),inputState num den true⟩ coin = _
  erw [KS.W29.FixedBranch.step_start]
  change Config.mk _ _ = Config.mk _ _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem pushOne_spec (num den : List Bool) :
    RunSpec pushOne (selectedState num den true) (oneState num den) 1 := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
    (compile (0 : Fin 1) (10 : Fin 13) 9 pushDispatch)
  intro bits hb
  cases bits with
  | nil => simp at hb
  | cons coin tail =>
    have ht : tail = [] := by simpa using hb
    subst tail
    change (compile (0 : Fin 1) (10 : Fin 13) 9 pushDispatch).step
      ⟨some (0 : Fin 1), selectedState num den true⟩ coin = _
    erw [step_compile]
    change Config.mk none _ = Config.mk none _
    congr 1
    funext j
    fin_cases j <;> rfl

theorem positive_emit_spec (num den : List Bool) :
    RunSpec (pairProgram positivePorts) (selectedState num den false)
      (reverseState (signedWire false num den)) (2 * num.length + 2 * den.length + 2) := by
  have h := pair_spec positivePorts (fun _ => []) num den [false]
  have hb : registers positivePorts (fun _ => []) num den [false] = selectedState num den false := by
    funext j
    fin_cases j <;> rfl
  have ha : registers positivePorts (fun _ => []) [] []
      ((frame num ++ frame den).reverse ++ [false]) = reverseState (signedWire false num den) := by
    funext j
    fin_cases j <;> simp [registers, positivePorts, reverseState, signedWire]
  rwa [hb, ha] at h

theorem subtract_spec (num den : List Bool) :
    RunSpec (subtractProgram subtractPorts) (oneState num den) (decrementedState num den)
      (2 * (max num.length 1 + 1)) := by
  have h := decrement_spec subtractPorts (fun j => if j = 8 then [true] else if j = 11 then den else []) num
  have hb : registers subtractPorts (fun j => if j = 8 then [true] else if j = 11 then den else [])
      num [true] [] = oneState num den := by
    funext j
    fin_cases j <;> rfl
  have ha : registers subtractPorts (fun j => if j = 8 then [true] else if j = 11 then den else [])
      [] (WireMagnitude.decrement num) [] = decrementedState num den := by
    funext j
    fin_cases j <;> rfl
  rwa [hb, ha] at h

theorem negative_emit_spec (num den : List Bool) :
    RunSpec (pairProgram negativePorts) (decrementedState num den)
      (reverseState (signedWire true (WireMagnitude.decrement num) den))
      (2 * (WireMagnitude.decrement num).length + 2 * den.length + 2) := by
  have h := pair_spec negativePorts (fun _ => []) (WireMagnitude.decrement num) den [true]
  have hb : registers negativePorts (fun _ => []) (WireMagnitude.decrement num) den [true] =
      decrementedState num den := by
    funext j
    fin_cases j <;> rfl
  have ha : registers negativePorts (fun _ => []) [] []
      ((frame (WireMagnitude.decrement num) ++ frame den).reverse ++ [true]) =
      reverseState (signedWire true (WireMagnitude.decrement num) den) := by
    funext j
    fin_cases j <;> simp [registers, negativePorts, reverseState, signedWire]
  rwa [hb, ha] at h

theorem finish_spec (wire : List Bool) :
    RunSpec (reverseProgram reversePorts) (reverseState wire) (outputState wire) (wire.length + 1) := by
  have h := reverse_spec reversePorts (fun _ => []) wire
  have hb : registers reversePorts (fun _ => []) [] [] wire.reverse = reverseState wire := by
    funext j
    fin_cases j <;> rfl
  have ha : registers reversePorts (fun _ => []) [] wire [] = outputState wire := by
    funext j
    fin_cases j <;> rfl
  rwa [hb, ha] at h

theorem positive_spec (num den : List Bool) :
    RunSpec positiveBranch (selectedState num den false)
      (outputState (signedWire false num den)) (4 * num.length + 4 * den.length + 6) := by
  have h := (positive_emit_spec num den).compose (finish_spec (signedWire false num den))
  have ht : (2 * num.length + 2 * den.length + 2) + ((signedWire false num den).length + 1) =
      4 * num.length + 4 * den.length + 6 := by rw [signedWire_length]; omega
  rwa [ht] at h

theorem negative_spec (num den : List Bool) :
    RunSpec negativeBranch (selectedState num den true)
      (outputState (signedWire true (WireMagnitude.decrement num) den))
      (2 * max num.length 1 + 4 * (WireMagnitude.decrement num).length + 4 * den.length + 9) := by
  have h := (pushOne_spec num den).compose ((subtract_spec num den).compose
    ((negative_emit_spec num den).compose (finish_spec (signedWire true (WireMagnitude.decrement num) den))))
  have ht : 1 + (2 * (max num.length 1 + 1) +
      ((2 * (WireMagnitude.decrement num).length + 2 * den.length + 2) +
        ((signedWire true (WireMagnitude.decrement num) den).length + 1))) =
      2 * max num.length 1 + 4 * (WireMagnitude.decrement num).length + 4 * den.length + 9 := by
    rw [signedWire_length]
    omega
  rwa [ht] at h

theorem program_spec (num den : List Bool) (sgn : Bool) :
    RunSpec program (inputState num den sgn) (outputState (rawWire sgn num den))
      (16 * (num.length + den.length + 1)) := by
  intro bits hlen
  cases bits with
  | nil => simp at hlen
  | cons coin tail =>
    simp only [List.length_cons] at hlen
    cases sgn
    · have ht : 4 * num.length + 4 * den.length + 6 ≤ tail.length := by omega
      rw [Machine.run, selector_false]
      change (KS.W29.FixedBranch.branch positiveBranch negativeBranch 10 selector).toMachine.run
        (KS.W29.FixedBranch.liftLeft positiveBranch negativeBranch
          ⟨some positiveBranch.initial, selectedState num den false⟩) tail = _
      rw [KS.W29.FixedBranch.run_left]
      erw [(positive_spec num den).run_of_le tail ht]
      rfl
    · have hn := WireMagnitude.decrement_length_le num
      have ht : 2 * max num.length 1 + 4 * (WireMagnitude.decrement num).length +
          4 * den.length + 9 ≤ tail.length := by omega
      rw [Machine.run, selector_true]
      change (KS.W29.FixedBranch.branch positiveBranch negativeBranch 10 selector).toMachine.run
        (KS.W29.FixedBranch.liftRight positiveBranch negativeBranch
          ⟨some negativeBranch.initial, selectedState num den true⟩) tail = _
      rw [KS.W29.FixedBranch.run_right]
      erw [(negative_spec num den).run_of_le tail ht]
      rfl

theorem rawWire_canonical (q : ℚ) :
    rawWire (decide (q.num < 0)) (Computability.encodeNat q.num.natAbs)
      (Computability.encodeNat q.den) = encodeRat q := by
  have h := WireMagnitude.wireRat_encode q
  simpa only [WireMagnitude.wireRat, WireMagnitude.wireInt, WireMagnitude.constructorPayload,
    KS.W19.trimBits_eq_encodeNat, KS.W19.bitsValue_encodeNat, rawWire, signedWire,
    List.cons_append] using h

theorem serializes_rational (q : ℚ) :
    RunSpec program
      (inputState (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den)
        (decide (q.num < 0))) (outputState (encodeRat q))
      (16 * ((Computability.encodeNat q.num.natAbs).length +
        (Computability.encodeNat q.den).length + 1)) := by
  have h := program_spec (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den)
    (decide (q.num < 0))
  rwa [rawWire_canonical] at h

end KS.W01.SignedRationalSerializer

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalAddProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W13.RationalAdd
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare (magnitude product negativeBit constructorBits pairBits)

def preNormalizeProgram : Program 16 :=
  compose (compose (compose prepareProgram productsProgram) clearProductsProgram) signedProgram

def normalizeProgram : Program 16 :=
  KS.W29.FixedSequential.liftPorts KS.W30.RationalMagnitudeMachine.program corePorts

def serializeProgram : Program 16 :=
  KS.W29.FixedSequential.liftPorts KS.W01.SignedRationalSerializer.program corePorts

def program : Program 16 := compose (compose preNormalizeProgram normalizeProgram) serializeProgram

end KS.W13.RationalAdd

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMultiplyNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W15.RationalMultiply
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare (magnitude product productTicks parseTicks prepareProgram

  negativeBit constructorBits pairBits fields signedFraction)

def normalizeProgram : Program 13 :=
  compose (compose (compose prepareProgram productsProgram) cleanupProgram)
    KS.W30.RationalMagnitudeMachine.program

end KS.W15.RationalMultiply

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMultiplicationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W15.RationalMultiply
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def program : Program 13 :=
  compose normalizeProgram KS.W01.SignedRationalSerializer.program

def machine : Machine := program.toMachine

@[simp] theorem machine_stackCount : machine.stackCount = 13 := rfl

end KS.W15.RationalMultiply

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalReciprocalSwap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W30.RationalReciprocal
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

def transfer (source target scratch : Fin 13) : Program 13 :=
  compose (KS.W04.BinaryStackMoves.moveProgram source scratch)
    (KS.W04.BinaryStackMoves.moveProgram scratch target)

def saveNumerator : Program 13 := transfer 10 9 8
def shiftDenominator : Program 13 := transfer 11 10 8
def restoreNumerator : Program 13 := transfer 9 11 8
def swap : Program 13 := compose saveNumerator (compose shiftDenominator restoreNumerator)

end KS.W30.RationalReciprocal

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalReciprocalCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.RationalReciprocal
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19
open KS.W03.MachineCombinators KS.W30.BinaryRational

def core : Program 13 := compose swap RationalMagnitudeMachine.program

end KS.W30.RationalReciprocal

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalReciprocalSerialize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.RationalReciprocal
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19
open KS.W03.MachineCombinators

def serializeCore : Program 13 := compose core KS.W01.SignedRationalSerializer.program

end KS.W30.RationalReciprocal

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_SingleRationalParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W06.SingleRationalParser

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare

def baseProgram : Program 6 :=
  compose (compose (compose (signProgram 0 5) (decodeProgram numeratorPorts))
    (decodeProgram denominatorPorts)) (magnitudeProgram magnitudePorts 5)

def onPorts {k : ℕ} (ports : Fin 6 ↪ Fin k) : Program k :=
  KS.W29.FixedSequential.liftPorts baseProgram ports

def program : Program 13 := onPorts normalizerPorts

end KS.W06.SingleRationalParser

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalReciprocalMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W30.RationalReciprocal
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def program : Program 13 := compose KS.W06.SingleRationalParser.program serializeCore

end KS.W30.RationalReciprocal

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_WireProgramPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W15.WireProgram
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def transferProgram {k : Nat} (source target scratch : Fin k) : Program k :=
  compose (KS.W04.BinaryStackMoves.moveProgram source scratch)
    (KS.W04.BinaryStackMoves.moveProgram scratch target)

end KS.W15.WireProgram

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalDivisionStages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W30.RationalDivision
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def liftCore (P : Program 13) : Program 15 := KS.W29.FixedSequential.liftPorts P corePorts

def parseNumerator : Program 15 := liftCore KS.W06.SingleRationalParser.program
def storeDenominator : Program 15 := KS.W15.WireProgram.transferProgram 0 13 8
def serializeNumerator : Program 15 := liftCore KS.W01.SignedRationalSerializer.program
def storeNumerator : Program 15 := KS.W15.WireProgram.transferProgram 10 14 8
def restoreDenominator : Program 15 := KS.W15.WireProgram.transferProgram 13 0 8
def reciprocal : Program 15 := liftCore RationalReciprocal.program
def prepareInverse : Program 15 := KS.W15.WireProgram.transferProgram 10 0 8
def prependNumerator : Program 15 := KS.W15.WireProgram.transferProgram 14 0 8
def multiply : Program 15 := liftCore KS.W15.RationalMultiply.program

end KS.W30.RationalDivision

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalDivisionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.RationalDivision
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def program : Program 15 := compose parseNumerator (compose storeDenominator
  (compose serializeNumerator (compose storeNumerator (compose restoreDenominator
    (compose reciprocal (compose prepareInverse (compose prependNumerator multiply)))))))

end KS.W30.RationalDivision

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalSignAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W16.RationalSignAction
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def toggleDispatch (s : Fin 3) (heads : Fin 14 → Fin 3) (_ : Bool) : Instruction 14 3 :=
  if s.val = 0 then
    ⟨some (if headSign heads then 2 else 1),
      Vector.ofFn (fun j => if j = 12 then .pop else .stay)⟩
  else ⟨none, Vector.ofFn (fun j => if j = 12 then .push (s.val == 2) else .stay)⟩

def toggleMachine : Machine := compile (0 : Fin 3) (0 : Fin 14) (12 : Fin 14) toggleDispatch
def toggleProgram : Program 14 := ofMachine toggleMachine

def parseProgram : Program 14 :=
  KS.W29.FixedSequential.liftPorts KS.W06.SingleRationalParser.program corePorts
def serializeProgram : Program 14 :=
  KS.W29.FixedSequential.liftPorts KS.W01.SignedRationalSerializer.program corePorts
def program : Program 14 := compose (compose parseProgram toggleProgram) serializeProgram

end KS.W16.RationalSignAction

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedDotPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W12.FixedDot

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def transferProgram (source target : Fin 19) : Program 19 :=
  compose (KS.W04.BinaryStackMoves.moveProgram source 18)
    (KS.W04.BinaryStackMoves.moveProgram 18 target)

end KS.W12.FixedDot

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalSubtractProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W13.RationalSubtract
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def parseProgram : Program 19 := KS.W29.FixedSequential.liftPorts
  KS.W06.SingleRationalParser.program (firstPorts 13 (by decide))
def serializeProgram : Program 19 := KS.W29.FixedSequential.liftPorts
  KS.W01.SignedRationalSerializer.program (firstPorts 13 (by decide))
def negateProgram : Program 19 := KS.W29.FixedSequential.liftPorts
  KS.W16.RationalSignAction.program (firstPorts 14 (by decide))
def addProgram : Program 19 := KS.W29.FixedSequential.liftPorts
  KS.W13.RationalAdd.program (firstPorts 16 (by decide))

def markDispatch (_ : Fin 1) (_ : Fin 19 → Fin 3) (_ : Bool) : Instruction 19 1 :=
  ⟨none,Vector.ofFn (fun j => if j=13 then .push false else .stay)⟩
def markProgram : Program 19 := ofMachine (compile 0 0 13 markDispatch)

def prepareProgram : Program 19 := compose (compose (compose (compose
  parseProgram (KS.W12.FixedDot.transferProgram 0 16)) serializeProgram)
  (KS.W12.FixedDot.transferProgram 10 17)) (KS.W12.FixedDot.transferProgram 16 0)
def changeSignProgram : Program 19 := compose (compose (compose (compose markProgram negateProgram)
  (KS.W04.BinaryStackMoves.clearProgram 13)) (KS.W12.FixedDot.transferProgram 10 0))
  (KS.W12.FixedDot.transferProgram 17 0)
def program : Program 19 := compose (compose prepareProgram changeSignProgram) addProgram

end KS.W13.RationalSubtract

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_ExpressionPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W13.ExpressionMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def leftPrepend : Program 24 := KS.W12.StackTransfer.program 23 0 22

def binaryArithmetic : BinaryOp → Program 24
  | .add => KS.W29.FixedSequential.liftPorts KS.W13.RationalAdd.program (firstPorts 16 (by decide))
  | .sub => KS.W29.FixedSequential.liftPorts KS.W13.RationalSubtract.program (firstPorts 19 (by decide))
  | .mul => KS.W29.FixedSequential.liftPorts KS.W15.RationalMultiply.program (firstPorts 13 (by decide))
  | .div => KS.W29.FixedSequential.liftPorts KS.W30.RationalDivision.program (firstPorts 15 (by decide))

def binaryBudget (q r : ℚ) : ℕ := 2000000*(KS.W01.ratLength q+KS.W01.ratLength r+1)^3

end KS.W13.ExpressionMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ArithmeticRoutine
attribute [-simp] _root_.OAI.CurrentKS.Realization.listCode_cons _root_.OAI.CurrentKS.Realization.listCode_nil _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.ArithmeticRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine PairRoutine
open KS.W13.ExpressionMachine

abbrev encode := KS.W01.encodeRat

def decodeLeft : Program 24 :=
  KS.W11.FrameWireCodec.unframeProgram ⟨![0,23,22],by decide⟩
def program (op : BinaryOp) : Program 24 :=
  compose decodeLeft (compose leftPrepend
    (compose (binaryArithmetic op) (CleanRoutine.transfer 10 19 0)))

lemma decode_spec (q r : ℚ) :
    RunSpec decodeLeft (io (pair (encode q) (encode r)))
      (registers [] [] (encode r) [] (encode q) []) (3*(encode q).length+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec
    (⟨![0,23,22],by decide⟩ : Fin 3 ↪ Fin 24) (fun _ => []) (encode q) (encode r)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl) <;> funext j <;> fin_cases j <;> rfl)

lemma prepend_spec (q r : ℚ) :
    RunSpec leftPrepend (registers [] [] (encode r) [] (encode q) [])
      (registers [] [] (encode q++encode r) [] [] []) (2*(encode q).length+2) := by
  have h := KS.W12.StackTransfer.spec (23 : Fin 24) 0 22 (by decide) (by decide) (by decide)
    (registers [] [] (encode r) [] (encode q) []) rfl
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j;fin_cases j <;> simp [registers,KS.W12.StackTransfer.after]

lemma extract_spec (q : ℚ) :
    RunSpec (CleanRoutine.transfer (10 : Fin 24) 19 0)
      (registers [] [] [] (encode q) [] []) (io (encode q)) (2*(encode q).length+2) := by
  have h := CleanRoutine.transfer_spec (10 : Fin 24) 19 0 (by decide) (by decide) (by decide)
    (registers [] [] [] (encode q) [] []) rfl rfl
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j;fin_cases j <;> simp [registers,io,Function.update]

def ticks (op : BinaryOp) (q r : ℚ) : ℕ :=
  (3*(encode q).length+2)+(2*(encode q).length+2)+binaryBudget q r+
    (2*(encode (op.eval q r)).length+2)

end CurrentKS.ArithmeticRoutine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_CompareRoutine
attribute [-simp] _root_.OAI.CurrentKS.Realization.listCode_cons _root_.OAI.CurrentKS.Realization.listCode_nil _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.CompareRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine KS.W04.CleanRationalCompare

def decode : Program 13 := KS.W11.FrameWireCodec.unframeProgram ⟨![0,11,12],by decide⟩
def prepend : Program 13 := KS.W12.StackTransfer.program 11 0 12
def extract : Program 13 := CleanRoutine.transfer 9 12 0
def program : Program 13 := compose decode (compose prepend (compose cleanedComparator extract))

lemma decode_spec (q r : ℚ) : RunSpec decode (io (PairRoutine.pair (encode q) (encode r)))
    (parsed q r) (3*(encode q).length+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec (⟨![0,11,12],by decide⟩ : Fin 3 ↪ Fin 13)
    (fun _ => []) (encode q) (encode r)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl) <;> funext j <;> fin_cases j <;> rfl)
lemma prepend_spec (q r : ℚ) : RunSpec prepend (parsed q r) (inputState q r)
    (2*(encode q).length+2) := by
  have h := KS.W12.StackTransfer.spec (11 : Fin 13) 0 12 (by decide) (by decide) (by decide)
    (parsed q r) rfl
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j;fin_cases j <;> simp [parsed,inputState,KS.W06.RationalCompare.fields,KS.W12.StackTransfer.after]
lemma extract_spec (b : Bool) : RunSpec extract (flagState b) (io [b]) 4 := by
  have h := CleanRoutine.transfer_spec (9 : Fin 13) 12 0 (by decide) (by decide) (by decide)
    (flagState b) rfl rfl
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j;fin_cases j <;> simp [flagState,io,Function.update]

def ticks (q r : ℚ) : ℕ :=
  (3*(encode q).length+2)+(2*(encode q).length+2)+
    KS.W29.polynomialFuel 2048 2 (encode q++encode r).length+4

def routine : Routine (fun p : ℚ×ℚ => PairRoutine.pair (encode p.1) (encode p.2))
    (fun p => [decide (p.1≤p.2)]) (fun p => ticks p.1 p.2) where
  scratch := 12
  program := program
  spec p := by
    have h := (decode_spec p.1 p.2).compose ((prepend_spec p.1 p.2).compose
      ((cleaned_polynomial_spec p.1 p.2).compose (extract_spec (decide (p.1≤p.2)))))
    simp only [ticks,Nat.add_assoc] at h ⊢
    exact h

end CurrentKS.CompareRoutine

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

def ratLE : Realizes (prodCode ratCode ratCode) boolCode (fun p => decide (p.1≤p.2)) where
  cost := fun p => CompareRoutine.ticks p.1 p.2
  routine := CompareRoutine.routine

variable {α β : Type*} {encA : α → Word} {encB : β → Word}

def Realizes.le {f g : α → ℚ} (r : Realizes encA ratCode f) (s : Realizes encA ratCode g) :
    Realizes encA boolCode (fun x => decide (f x≤g x)) := (r.both s).then ratLE

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

variable {α γ : Type*}

def lookupStepRealizes (ea : α → Word) :
    Realizes (prodCode (prodCode natCode ea) ea) (prodCode natCode ea) lookupStep :=
  let old := first (prodCode natCode ea) ea
  let k := old.then (first natCode ea)
  let prev := old.then (second natCode ea)
  let x := second (prodCode natCode ea) ea
  let km := k.then natPred
  ((k.then natIsZero).ite old (km.both ((km.then natIsZero).ite x prev))).congr (by
    intro p
    simp [lookupStep,Nat.pred_eq_sub_one])

lemma lookupStep_getD (xs : List α) (k : ℕ) (a : α) :
    (xs.foldl (fun s x => lookupStep (s,x)) (k+1,a)).2=xs.getD k a := by
  induction xs generalizing k a with
  | nil => simp
  | cons x xs ih =>
    cases k with
    | zero =>
      rw [List.foldl_cons]
      change (xs.foldl (fun s x => lookupStep (s,x)) (0,x)).2=_
      rw [lookupStep_zero]
      simp
    | succ k => simpa [lookupStep,Nat.add_sub_cancel] using ih k a

def getD (ea : α → Word) (a : α) :
    Realizes (prodCode natCode (listCode ea)) ea (fun p => p.2.getD p.1 a) :=
  let k := first natCode (listCode ea)
  let xs := second natCode (listCode ea)
  let init := (k.then natSucc).both (constant (prodCode natCode (listCode ea)) ea a)
  (((init.both xs).then (lookupStepRealizes ea).fold).then (second natCode ea)).congr (by
    intro p
    exact lookupStep_getD p.2 p.1 a)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_BinaryNaturalRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

abbrev binaryNatCode : ℕ → Word := Computability.encodeNat

end CurrentKS.Realization

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
open AlgorithmicThinTrees.MetricTests.RationalStep
open scoped BigOperators

abbrev numVertices := view.then (first natCode (prodCode indicesCode indicesCode))
abbrev rights := endpoints.then (second indicesCode indicesCode)

def edgeLeft : Realizes edgeCode natCode (fun a : Edge => (a.1.G.left a.2).val) :=
  ((edgeIndex.both (edgeGraph.then lefts)).then (getD natCode 0)).congr
    (fun a => getD_ofFn _ a.2 0)
def edgeRight : Realizes edgeCode natCode (fun a : Edge => (a.1.G.right a.2).val) :=
  ((edgeIndex.both (edgeGraph.then rights)).then (getD natCode 0)).congr
    (fun a => getD_ofFn _ a.2 0)

end AlgorithmicThinTrees.GraphStack

end

end OAI
end


