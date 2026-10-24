-- Prove2me | Definitions.Def_PricingWithTips3DM_6182ef626f3702ab6991d1fa
-- name    : PricingWithTips3DM_6182ef626f3702ab6991d1fa
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:54:27.224766+00:00
-- url     : https://prove2.me/theorems/6bb907e3-6c86-4159-94f2-14e08dfdc522
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.Steps
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_2bce466372bdbafcf882c219
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Guarded circuit normalizer: one-step contracts

These lemmas expose the nested TM2 statements as ordinary transformations of
the named stacks.  Later proofs do not unfold `program` directly.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

attribute [local simp] setInput setNormalized setCounter inputIs hasInput
  hasNormalized hasCounter bufferedNormalized popCounter pushCounter boundStack
  go reject normalizedGateTag gateReturn startGate finishRowPrefix finishOperand
  retainOperandTick finishOperandField

/-- Install one selected bound while leaving the unselected counter explicit. -/
def withBound : Return → Nat → Nat → Nat → Nat × Nat
  | .inputGate, bound, _, gateCount => (bound, gateCount)
  | _, bound, inputCount, _ => (inputCount, bound)

@[simp] theorem withBound_input (bound inputCount gateCount : Nat) :
    withBound .inputGate bound inputCount gateCount = (bound, gateCount) := rfl

def afterRowPrefixLabel : GateKind → Label
  | .input => .parseOperand .inputGate
  | .constFalse | .constTrue => .gates
  | .not => .parseOperand .notGate
  | .and => .parseOperand .andLeft
  | .or => .parseOperand .orLeft

def afterRowPrefixRows (kind : GateKind)
    (rows : List NormalizedCircuitSym) : List NormalizedCircuitSym :=
  match kind with
  | .constFalse | .constTrue => .rowEnd :: normalizedGateTag kind :: rows
  | _ => normalizedGateTag kind :: rows

def afterRowPrefixGateCount (kind : GateKind) (gateCount : Nat) : Nat :=
  match kind with
  | .constFalse | .constTrue => gateCount + 1
  | _ => gateCount

def rawGateTag : GateKind → CircuitSym
  | .input => .inputMark
  | .constFalse => .constFalseMark
  | .constTrue => .constTrueMark
  | .not => .notMark
  | .and => .andMark
  | .or => .orMark

def afterBoundLabel : Return → Label
  | .andLeft => .parseOperand .andRight
  | .orLeft => .parseOperand .orRight
  | .outputGate => .rowsToOutput
  | _ => .gates

def afterBoundRows (ret : Return)
    (rows : List NormalizedCircuitSym) : List NormalizedCircuitSym :=
  match ret with
  | .inputGate | .notGate | .andRight | .orRight => .rowEnd :: rows
  | .andLeft | .orLeft | .outputGate => rows

def afterBoundGateCount (ret : Return) (gateCount : Nat) : Nat :=
  match ret with
  | .inputGate | .notGate | .andRight | .orRight => gateCount + 1
  | .andLeft | .orLeft | .outputGate => gateCount


theorem input_count_arg_step (state : State) (input : List CircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .inputCount) state (.argMark :: input) output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .inputCount)
        { state with inputBuffer := some .argMark }
        input output rows (inputCount + 1) gateCount operand saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem input_count_end_step (state : State) (input : List CircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .inputCount) state (.endMark :: input) output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .gates)
        { state with inputBuffer := some .endMark }
        input output rows inputCount gateCount operand saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem input_count_empty_step (state : State)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .inputCount) state [] output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearInput) { state with inputBuffer := none }
        [] output rows inputCount gateCount operand saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem input_count_bad_step (state : State) (symbol : CircuitSym)
    (harg : symbol ≠ .argMark) (hend : symbol ≠ .endMark)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .inputCount) state (symbol :: input) output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearInput) { state with inputBuffer := some symbol }
        input output rows inputCount gateCount operand saved outputIndex) := by
  cases symbol <;> simp_all <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem gates_tag_step (state : State) (kind : GateKind)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .gates) state (rawGateTag kind :: input) output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some (.rowIndexCopy kind))
        { state with inputBuffer := some (rawGateTag kind) }
        input output (.gateRowMark :: rows) inputCount gateCount operand saved
        outputIndex) := by
  cases kind <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem gates_output_step (state : State) (input : List CircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .gates) state (.outputMark :: input) output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some (.parseOperand .outputGate))
        { state with inputBuffer := some .outputMark }
        input output rows inputCount gateCount operand saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem gates_empty_step (state : State)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .gates) state [] output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearInput) { state with inputBuffer := none }
        [] output rows inputCount gateCount operand saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem gates_bad_step (state : State) (symbol : CircuitSym)
    (hbad : symbol = .argMark ∨ symbol = .endMark)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .gates) state (symbol :: input) output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearInput) { state with inputBuffer := some symbol }
        input output rows inputCount gateCount operand saved outputIndex) := by
  rcases hbad with rfl | rfl <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem check_trailing_empty_step (state : State)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .checkTrailing) state [] output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some (.compareOperand .outputGate))
        { state with inputBuffer := none }
        [] output rows inputCount gateCount operand saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem check_trailing_nonempty_step (state : State) (head : CircuitSym)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .checkTrailing) state (head :: input) output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearInput) { state with inputBuffer := some head }
        input output rows inputCount gateCount operand saved outputIndex) := by
  cases head <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem row_index_copy_tick_step (state : State) (kind : GateKind)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some (.rowIndexCopy kind)) state input output rows
      inputCount (gateCount + 1) operand saved outputIndex) =
      some (cfg (some (.rowIndexCopy kind))
        { state with counterPresent := true }
        input output (.tick :: rows) inputCount gateCount operand (saved + 1)
        outputIndex) := by
  cases kind <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem row_index_copy_done_step (state : State) (kind : GateKind)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount operand saved outputIndex : Nat) :
    step (cfg (some (.rowIndexCopy kind)) state input output rows
      inputCount 0 operand saved outputIndex) =
      some (cfg (some (.rowIndexRestore kind))
        { state with counterPresent := false }
        input output (.fieldEnd :: rows) inputCount 0 operand saved outputIndex) := by
  cases kind <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem row_index_restore_tick_step (state : State) (kind : GateKind)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some (.rowIndexRestore kind)) state input output rows
      inputCount gateCount operand (saved + 1) outputIndex) =
      some (cfg (some (.rowIndexRestore kind))
        { state with counterPresent := true }
        input output rows inputCount (gateCount + 1) operand saved outputIndex) := by
  cases kind <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem row_index_restore_done_step (state : State) (kind : GateKind)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand outputIndex : Nat) :
    step (cfg (some (.rowIndexRestore kind)) state input output rows
      inputCount gateCount operand 0 outputIndex) =
      some (cfg (some (afterRowPrefixLabel kind))
        { state with counterPresent := false }
        input output (afterRowPrefixRows kind rows) inputCount
        (afterRowPrefixGateCount kind gateCount) operand 0 outputIndex) := by
  cases kind <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem operand_arg_step (state : State) (ret : Return)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some (.parseOperand ret)) state (.argMark :: input) output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some (.parseOperand ret))
        { state with inputBuffer := some .argMark }
        input output
        (match ret with | .outputGate => rows | _ => .tick :: rows)
        inputCount gateCount (operand + 1) saved
        (match ret with | .outputGate => outputIndex + 1 | _ => outputIndex)) := by
  cases ret <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem operand_end_step (state : State) (ret : Return)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some (.parseOperand ret)) state (.endMark :: input) output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg
        (some (match ret with
          | .outputGate => .checkTrailing
          | _ => .compareOperand ret))
        { state with inputBuffer := some .endMark }
        input output
        (match ret with | .outputGate => rows | _ => .fieldEnd :: rows)
        inputCount gateCount operand saved outputIndex) := by
  cases ret <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem operand_empty_step (state : State) (ret : Return)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some (.parseOperand ret)) state [] output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearInput) { state with inputBuffer := none }
        [] output rows inputCount gateCount operand saved outputIndex) := by
  cases ret <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem operand_bad_step (state : State) (ret : Return) (symbol : CircuitSym)
    (harg : symbol ≠ .argMark) (hend : symbol ≠ .endMark)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some (.parseOperand ret)) state (symbol :: input) output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearInput) { state with inputBuffer := some symbol }
        input output rows inputCount gateCount operand saved outputIndex) := by
  cases ret <;> cases symbol <;> simp_all <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

/-- One comparison tick consumes one operand unit and one selected bound unit. -/
theorem compare_operand_tick_step (state : State) (ret : Return)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (bound inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some (.compareOperand ret)) state input output rows
      (withBound ret (bound + 1) inputCount gateCount).1
      (withBound ret (bound + 1) inputCount gateCount).2
      (operand + 1) saved outputIndex) =
      some (cfg (some (.compareOperand ret))
        { state with counterPresent := true }
        input output rows
        (withBound ret bound inputCount gateCount).1
        (withBound ret bound inputCount gateCount).2
        operand (saved + 1) outputIndex) := by
  cases ret <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

/-- An empty operand plus one remaining bound unit establishes strictness. -/
theorem compare_operand_done_step (state : State) (ret : Return)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (bound inputCount gateCount saved outputIndex : Nat) :
    step (cfg (some (.compareOperand ret)) state input output rows
      (withBound ret (bound + 1) inputCount gateCount).1
      (withBound ret (bound + 1) inputCount gateCount).2
      0 saved outputIndex) =
      some (cfg (some (.restoreBound ret))
        { state with counterPresent := true }
        input output rows
        (withBound ret bound inputCount gateCount).1
        (withBound ret bound inputCount gateCount).2
        0 (saved + 1) outputIndex) := by
  cases ret <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem compare_operand_zero_bound_zero_step (state : State) (ret : Return)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount saved outputIndex : Nat) :
    step (cfg (some (.compareOperand ret)) state input output rows
      (withBound ret 0 inputCount gateCount).1
      (withBound ret 0 inputCount gateCount).2
      0 saved outputIndex) =
      some (cfg (some .clearInput) { state with counterPresent := false }
        input output rows
        (withBound ret 0 inputCount gateCount).1
        (withBound ret 0 inputCount gateCount).2
        0 saved outputIndex) := by
  cases ret <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem compare_operand_positive_bound_zero_step (state : State) (ret : Return)
    (remaining : Nat) (input : List CircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount saved outputIndex : Nat) :
    step (cfg (some (.compareOperand ret)) state input output rows
      (withBound ret 0 inputCount gateCount).1
      (withBound ret 0 inputCount gateCount).2
      (remaining + 1) saved outputIndex) =
      some (cfg (some .clearInput) { state with counterPresent := false }
        input output rows
        (withBound ret 0 inputCount gateCount).1
        (withBound ret 0 inputCount gateCount).2
        remaining saved outputIndex) := by
  cases ret <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem restore_bound_tick_step (state : State) (ret : Return)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (bound inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some (.restoreBound ret)) state input output rows
      (withBound ret bound inputCount gateCount).1
      (withBound ret bound inputCount gateCount).2
      operand (saved + 1) outputIndex) =
      some (cfg (some (.restoreBound ret))
        { state with counterPresent := true }
        input output rows
        (withBound ret (bound + 1) inputCount gateCount).1
        (withBound ret (bound + 1) inputCount gateCount).2
        operand saved outputIndex) := by
  cases ret <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem restore_bound_done_step (state : State) (ret : Return)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand outputIndex : Nat) :
    step (cfg (some (.restoreBound ret)) state input output rows
      inputCount gateCount operand 0 outputIndex) =
      some (cfg (some (afterBoundLabel ret))
        { state with counterPresent := false }
        input output (afterBoundRows ret rows) inputCount
        (afterBoundGateCount ret gateCount) operand 0 outputIndex) := by
  cases ret <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem rows_to_output_step (state : State) (head : NormalizedCircuitSym)
    (rows output : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .rowsToOutput) state [] output (head :: rows)
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .rowsToOutput)
        { state with normalizedBuffer := some head }
        [] (head :: output) rows inputCount gateCount operand saved outputIndex) := by
  cases head <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem rows_to_output_done_step (state : State)
    (output : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .rowsToOutput) state [] output []
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .emitGateCount)
        { state with normalizedBuffer := none }
        [] (.fieldEnd :: output) [] inputCount gateCount operand saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem emit_gate_count_tick_step (state : State)
    (output : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .emitGateCount) state [] output []
      inputCount (gateCount + 1) operand saved outputIndex) =
      some (cfg (some .emitGateCount) { state with counterPresent := true }
        [] (.tick :: output) [] inputCount gateCount operand saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem emit_gate_count_done_step (state : State)
    (output : List NormalizedCircuitSym)
    (inputCount operand saved outputIndex : Nat) :
    step (cfg (some .emitGateCount) state [] output []
      inputCount 0 operand saved outputIndex) =
      some (cfg (some .emitOutputIndex) { state with counterPresent := false }
        [] (.fieldEnd :: .gateCountMark :: output) []
        inputCount 0 operand saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem emit_output_index_tick_step (state : State)
    (output : List NormalizedCircuitSym)
    (inputCount operand saved outputIndex : Nat) :
    step (cfg (some .emitOutputIndex) state [] output []
      inputCount 0 operand saved (outputIndex + 1)) =
      some (cfg (some .emitOutputIndex) { state with counterPresent := true }
        [] (.tick :: output) [] inputCount 0 operand saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem emit_output_index_done_step (state : State)
    (output : List NormalizedCircuitSym)
    (inputCount operand saved : Nat) :
    step (cfg (some .emitOutputIndex) state [] output []
      inputCount 0 operand saved 0) =
      some (cfg (some .emitInputCount) { state with counterPresent := false }
        [] (.fieldEnd :: .outputIndexMark :: output) []
        inputCount 0 operand saved 0) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem emit_input_count_tick_step (state : State)
    (output : List NormalizedCircuitSym)
    (inputCount operand saved : Nat) :
    step (cfg (some .emitInputCount) state [] output []
      (inputCount + 1) 0 operand saved 0) =
      some (cfg (some .emitInputCount) { state with counterPresent := true }
        [] (.tick :: output) [] inputCount 0 operand saved 0) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem emit_input_count_done_step (state : State)
    (output : List NormalizedCircuitSym) (operand saved : Nat) :
    step (cfg (some .emitInputCount) state [] output [] 0 0 operand saved 0) =
      some (cfg (some .done) { state with counterPresent := false }
        [] (.validMark :: .inputCountMark :: output) [] 0 0 operand saved 0) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem clear_input_step (state : State) (head : CircuitSym)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .clearInput) state (head :: input) output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearInput) { state with inputBuffer := some head }
        input output rows inputCount gateCount operand saved outputIndex) := by
  cases head <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem clear_input_done_step (state : State)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .clearInput) state [] output rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearOutput) { state with inputBuffer := none }
        [] output rows inputCount gateCount operand saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem clear_output_step (state : State) (head : NormalizedCircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .clearOutput) state [] (head :: output) rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearOutput) { state with normalizedBuffer := some head }
        [] output rows inputCount gateCount operand saved outputIndex) := by
  cases head <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem clear_output_done_step (state : State) (rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .clearOutput) state [] [] rows
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearRows) { state with normalizedBuffer := none }
        [] [] rows inputCount gateCount operand saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem clear_rows_step (state : State) (head : NormalizedCircuitSym)
    (rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .clearRows) state [] [] (head :: rows)
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearRows) { state with normalizedBuffer := some head }
        [] [] rows inputCount gateCount operand saved outputIndex) := by
  cases head <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem clear_rows_done_step (state : State)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .clearRows) state [] [] []
      inputCount gateCount operand saved outputIndex) =
      some (cfg (some .clearInputCount) { state with normalizedBuffer := none }
        [] [] [] inputCount gateCount operand saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem clear_input_count_tick_step (state : State)
    (inputCount gateCount operand saved outputIndex : Nat) :
    step (cfg (some .clearInputCount) state [] [] []
      (inputCount + 1) gateCount operand saved outputIndex) =
      some (cfg (some .clearInputCount) { state with counterPresent := true }
        [] [] [] inputCount gateCount operand saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem clear_input_count_done_step (state : State)
    (gateCount operand saved outputIndex : Nat) :
    step (cfg (some .clearInputCount) state [] [] []
      0 gateCount operand saved outputIndex) =
      some (cfg (some .clearGateCount) { state with counterPresent := false }
        [] [] [] 0 gateCount operand saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem clear_gate_count_tick_step (state : State)
    (gateCount operand saved outputIndex : Nat) :
    step (cfg (some .clearGateCount) state [] [] []
      0 (gateCount + 1) operand saved outputIndex) =
      some (cfg (some .clearGateCount) { state with counterPresent := true }
        [] [] [] 0 gateCount operand saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem clear_gate_count_done_step (state : State)
    (operand saved outputIndex : Nat) :
    step (cfg (some .clearGateCount) state [] [] []
      0 0 operand saved outputIndex) =
      some (cfg (some .clearOperand) { state with counterPresent := false }
        [] [] [] 0 0 operand saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem clear_operand_tick_step (state : State)
    (operand saved outputIndex : Nat) :
    step (cfg (some .clearOperand) state [] [] []
      0 0 (operand + 1) saved outputIndex) =
      some (cfg (some .clearOperand) { state with counterPresent := true }
        [] [] [] 0 0 operand saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem clear_operand_done_step (state : State) (saved outputIndex : Nat) :
    step (cfg (some .clearOperand) state [] [] [] 0 0 0 saved outputIndex) =
      some (cfg (some .clearSaved) { state with counterPresent := false }
        [] [] [] 0 0 0 saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem clear_saved_tick_step (state : State) (saved outputIndex : Nat) :
    step (cfg (some .clearSaved) state [] [] [] 0 0 0 (saved + 1) outputIndex) =
      some (cfg (some .clearSaved) { state with counterPresent := true }
        [] [] [] 0 0 0 saved outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem clear_saved_done_step (state : State) (outputIndex : Nat) :
    step (cfg (some .clearSaved) state [] [] [] 0 0 0 0 outputIndex) =
      some (cfg (some .clearOutputIndex) { state with counterPresent := false }
        [] [] [] 0 0 0 0 outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem clear_output_index_tick_step (state : State) (outputIndex : Nat) :
    step (cfg (some .clearOutputIndex) state [] [] [] 0 0 0 0 (outputIndex + 1)) =
      some (cfg (some .clearOutputIndex) { state with counterPresent := true }
        [] [] [] 0 0 0 0 outputIndex) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem clear_output_index_done_step (state : State) :
    step (cfg (some .clearOutputIndex) state [] [] [] 0 0 0 0 0) =
      some (cfg (some .emitInvalid) { state with counterPresent := false }
        [] [] [] 0 0 0 0 0) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem emit_invalid_step (state : State) :
    step (cfg (some .emitInvalid) state [] [] [] 0 0 0 0 0) =
      some (cfg (some .done) state [] [.invalidMark] [] 0 0 0 0 0) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, withBound,
        afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
        rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
        List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, withBound,
          afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
          rawGateTag, afterBoundLabel, afterBoundRows, afterBoundGateCount,
          List.replicate_succ,
          Function.update]
)

theorem done_step (state : State) (result : List NormalizedCircuitSym) :
    step (cfg (some .done) state [] result [] 0 0 0 0 0) =
      some (_root_.Turing.haltList machine result) := by
  apply congrArg some
  apply _root_.Turing.TM2Comp.Cfg_ext
  · simp [step, cfg, machine, program, stackContents, initialState,
      _root_.Turing.haltList, Function.update]
  · simp [step, cfg, machine, program, stackContents, initialState,
      _root_.Turing.haltList, Function.update]
  · funext stack
    cases stack <;>
      simp [step, cfg, machine, program, stackContents, initialState,
        _root_.Turing.haltList, Function.update]

theorem done_invalid_step (state : State) :
    step (cfg (some .done) state [] [.invalidMark] [] 0 0 0 0 0) =
      some (_root_.Turing.haltList machine [.invalidMark]) := by
  exact done_step state [.invalidMark]

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer


