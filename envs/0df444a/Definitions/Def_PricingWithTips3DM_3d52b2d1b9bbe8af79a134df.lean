-- Prove2me | Definitions.Def_PricingWithTips3DM_3d52b2d1b9bbe8af79a134df
-- name    : PricingWithTips3DM_3d52b2d1b9bbe8af79a134df
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:49:08.208292+00:00
-- url     : https://prove2.me/theorems/dd85e56c-6e29-4198-a4fa-08b00386595e
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.RejectSteps
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_dc530da3af266ce325fbfb37
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Concrete verifier: rejecting one-step contracts
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

attribute [local simp] setInput setBool setCounter inputIs hasInput hasBool
  hasCounter bufferedBool hasEncodedSymbol bufferedAssignmentValue
  noteAssignmentSymbol go reject finishGate finishLookup popBool pushBool
  moveBufferedBool


theorem scan_eof_reject_step (state : State)
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .scanCertificate) state [] output certificate values scratch
      gateCount index saved) =
      some (cfg (some (.clearInput false))
        { state with inputBuffer := none }
        [] output certificate values scratch gateCount index saved) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, List.replicate_succ,
          Function.update]
)

theorem input_count_arg_underflow_step (state : State)
    (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool) (index saved : Nat) :
    step (cfg (some .inputCount) state (some .argMark :: input)
      output certificate values scratch 0 index saved) =
      some (cfg (some (.clearInput false))
        { state with inputBuffer := some (some .argMark), counterPresent := false }
        input output certificate values scratch 0 index saved) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, List.replicate_succ,
          Function.update]
)

theorem input_count_end_nonempty_step (state : State)
    (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .inputCount) state (some .endMark :: input)
      output certificate values scratch (gateCount + 1) index saved) =
      some (cfg (some (.clearInput false))
        { state with inputBuffer := some (some .endMark), counterPresent := true }
        input output certificate values scratch gateCount index saved) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, List.replicate_succ,
          Function.update]
)

theorem input_count_end_invalid_step (state : State)
    (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool) (index saved : Nat)
    (hinvalid : state.validAssignment = false) :
    step (cfg (some .inputCount) state (some .endMark :: input)
      output certificate values scratch 0 index saved) =
      some (cfg (some (.clearInput false))
        { state with inputBuffer := some (some .endMark), counterPresent := false }
        input output certificate values scratch 0 index saved) := by
  rcases state with ⟨inputBuffer, boolBuffer, counterPresent, validAssignment⟩
  simp only [State.validAssignment] at hinvalid
  subst validAssignment
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, List.replicate_succ,
          Function.update]
)

theorem input_count_eof_reject_step (state : State)
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .inputCount) state [] output certificate values scratch
      gateCount index saved) =
      some (cfg (some (.clearInput false)) { state with inputBuffer := none }
        [] output certificate values scratch gateCount index saved) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, List.replicate_succ,
          Function.update]
)

theorem input_count_bad_symbol_reject_step (state : State) (symbol : CircuitSym)
    (harg : symbol ≠ .argMark) (hend : symbol ≠ .endMark)
    (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .inputCount) state (some symbol :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some (.clearInput false))
        { state with inputBuffer := some (some symbol) }
        input output certificate values scratch gateCount index saved) := by
  cases symbol <;> simp_all <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, List.replicate_succ,
          Function.update]
)

theorem parse_nat_eof_reject_step (state : State) (ret : Return)
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.parseNat ret)) state [] output certificate values scratch
      gateCount index saved) =
      some (cfg (some (.clearInput false)) { state with inputBuffer := none }
        [] output certificate values scratch gateCount index saved) := by
  cases ret <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, List.replicate_succ,
          Function.update]
)

theorem parse_nat_bad_symbol_reject_step (state : State) (ret : Return)
    (symbol : CircuitSym) (harg : symbol ≠ .argMark) (hend : symbol ≠ .endMark)
    (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some (.parseNat ret)) state (some symbol :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some (.clearInput false))
        { state with inputBuffer := some (some symbol) }
        input output certificate values scratch gateCount index saved) := by
  cases ret <;> cases symbol <;> simp_all <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, List.replicate_succ,
          Function.update]
)

theorem gates_eof_reject_step (state : State)
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .gates) state [] output certificate values scratch
      gateCount index saved) =
      some (cfg (some (.clearInput false)) { state with inputBuffer := none }
        [] output certificate values scratch gateCount index saved) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, List.replicate_succ,
          Function.update]
)

theorem gates_bad_marker_reject_step (state : State) (symbol : CircuitSym)
    (harg : symbol = .argMark ∨ symbol = .endMark)
    (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .gates) state (some symbol :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some (.clearInput false))
        { state with inputBuffer := some (some symbol) }
        input output certificate values scratch gateCount index saved) := by
  rcases harg with rfl | rfl <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, List.replicate_succ,
          Function.update]
)

theorem certificate_lookup_prefix_underflow_step (state : State)
    (input : List (Option CircuitSym)) (output values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .certificateLookup) state input output [] values scratch
      gateCount (index + 1) saved) =
      some (cfg (some (.clearInput false))
        { state with boolBuffer := none, counterPresent := true }
        input output [] values scratch gateCount index saved) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, List.replicate_succ,
          Function.update]
)

theorem certificate_lookup_target_underflow_step (state : State)
    (input : List (Option CircuitSym)) (output values scratch : List Bool)
    (gateCount saved : Nat) :
    step (cfg (some .certificateLookup) state input output [] values scratch
      gateCount 0 saved) =
      some (cfg (some (.clearInput false))
        { state with boolBuffer := none, counterPresent := false }
        input output [] values scratch gateCount 0 saved) := by
  exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, List.replicate_succ,
          Function.update]
)

theorem gate_subtract_underflow_step (state : State) (ret : Return)
    (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool)
    (index saved : Nat) :
    step (cfg (some (.gateSubtract ret)) state input output certificate values scratch
      0 (index + 1) saved) =
      some (cfg (some (.clearInput false))
        { state with counterPresent := false }
        input output certificate values scratch 0 index saved) := by
  cases ret <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, List.replicate_succ,
          Function.update]
)

theorem gate_transfer_first_underflow_step (state : State) (ret : Return)
    (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool) (saved : Nat) :
    step (cfg (some (.gateTransferFirst ret)) state input output certificate values scratch
      0 0 saved) =
      some (cfg (some (.clearInput false))
        { state with counterPresent := false }
        input output certificate values scratch 0 0 saved) := by
  cases ret <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, List.replicate_succ,
          Function.update]
)

theorem check_trailing_nonempty_step (state : State)
    (head : Option CircuitSym) (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    step (cfg (some .checkTrailing) state (head :: input)
      output certificate values scratch gateCount index saved) =
      some (cfg (some (.clearInput false))
        { state with inputBuffer := some head }
        input output certificate values scratch gateCount index saved) := by
  cases head with
  | none => exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, List.replicate_succ,
          Function.update]
)
  | some sym => cases sym <;> exact (by
    apply congrArg some
    apply _root_.Turing.TM2Comp.Cfg_ext
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · simp [step, cfg, machine, program, stackContents, List.replicate_succ,
        Function.update]
    · funext stack
      cases stack <;>
        simp [step, cfg, machine, program, stackContents, List.replicate_succ,
          Function.update]
)

end CLRS.Chapter34.Turing.GeneralCircuitVerifier


