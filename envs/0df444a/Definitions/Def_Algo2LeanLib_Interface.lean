-- Prove2me | Definitions.Def_Algo2LeanLib_Interface
-- name    : Algo2LeanLib_Interface
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:39:31.544504+00:00
-- url     : https://prove2.me/theorems/e9c56c0f-f969-435e-9c63-c0f5ee34269f
-- title:
--   Algo2LeanLib.Interface definitions
-- statement:
--   Definitions and required structural lemmas from `Algo2LeanLib.Interface`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/Interface.lean

import Definitions.Def_Algo2LeanLib_Modules

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
An abstract interface carries executable code separately from behavioral laws.
A concrete implementation retains its own transition relation and internal
calls. The adapter only decodes the selected method's final result, and never
replaces its execution by an atomic contract.
-/

namespace Algo2LeanCore

/-- The execution portion of an interface. Generated interface records add
    reference validity and typed method entries with a fixed result type. -/
structure InterfaceCode (Heap Result : Type) where
  Frame : Type
  Step : Config Heap Frame Result → Config Heap Frame Result → Prop
  terminal : ∀ heap result, Terminal Step (.done heap result)

/-- Optional determinism evidence, kept separate from the code and its laws. -/
structure InterfaceFacts {Heap Result : Type} (code : InterfaceCode Heap Result) where
  next : Config Heap code.Frame Result → Config Heap code.Frame Result
  step_next : ∀ {before after}, code.Step before after → next before = after

theorem InterfaceFacts.deterministic {Heap Result : Type} {code : InterfaceCode Heap Result}
    (facts : InterfaceFacts code) : Deterministic code.Step := by
  intro before left right first second
  exact (facts.step_next first).symm.trans (facts.step_next second)

namespace InterfaceAdapter

/-- Concrete control stays intact until its selected method returns. -/
inductive Frame (SourceFrame SourceResult Result : Type) where
  | imported (frame : SourceFrame) (inner : Stack SourceFrame SourceResult)
      (resume : SourceResult → Frame SourceFrame SourceResult Result)
  | returned (result : Result)
  | invalid

variable {Heap SourceFrame SourceResult Result : Type}

/-- Delegation carries through the concrete transition's heap effects. The
    separate return rule delivers the decoded result without changing the heap. -/
inductive Step
    (sourceStep : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult → Prop) :
    Config Heap (Frame SourceFrame SourceResult Result) Result →
      Config Heap (Frame SourceFrame SourceResult Result) Result → Prop where
  | imported (heap : Heap) (frame : SourceFrame) (inner : Stack SourceFrame SourceResult)
      (resume : SourceResult → Frame SourceFrame SourceResult Result)
      (caller : Stack (Frame SourceFrame SourceResult Result) Result)
      (after : Config Heap SourceFrame SourceResult)
      (transition : sourceStep (.active heap frame inner) after) :
      Step sourceStep (.active heap (.imported frame inner resume) caller)
        (ModuleCall.config Frame.imported resume caller after)
  | returned (heap : Heap) (result : Result)
      (caller : Stack (Frame SourceFrame SourceResult Result) Result) :
      Step sourceStep (.active heap (.returned result) caller) (resumeConfig heap result caller)

theorem terminal
    (sourceStep : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult → Prop)
    (heap : Heap) (result : Result) : Terminal (Step sourceStep) (.done heap result) := by
  intro next transition
  cases transition

/-- A fixed interface result type can be backed by any independently compiled
    concrete module, even if that module exports other functions or methods. -/
def code
    (sourceStep : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult → Prop) :
    InterfaceCode Heap Result where
  Frame := Frame SourceFrame SourceResult Result
  Step := Step sourceStep
  terminal := terminal sourceStep

/-- A rejected result produces an invalid frame with no outgoing transitions. -/
def decodeFrame (decode : SourceResult → Option Result) (result : SourceResult) :
    Frame SourceFrame SourceResult Result :=
  match decode result with
  | some result => .returned result
  | none => .invalid

/-- A typed method entry starts the original concrete implementation. -/
def entry (frame : SourceFrame) (decode : SourceResult → Option Result) :
    Frame SourceFrame SourceResult Result :=
  .imported frame [] (decodeFrame decode)

theorem simulates
    {sourceStep : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult → Prop}
    (sourceTerminal : ∀ heap result, Terminal sourceStep (.done heap result)) :
    ModuleCall.Simulates (Frame.imported (Result := Result)) sourceStep (Step sourceStep) := by
  apply ModuleCall.Delegates.simulates
  · exact Step.imported
  · exact sourceTerminal

/-- An existing concrete summary supplies the interface summary unchanged apart
    from its checked final result constructor. This preserves all heap effects,
    clock increments, and arbitrary suspended interface callers. -/
theorem summary
    {sourceStep : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult → Prop}
    (sourceTerminal : ∀ heap result, Terminal sourceStep (.done heap result))
    {before after : Heap} {frame : SourceFrame} {original : SourceResult} {result : Result}
    (contract : Summary sourceStep before frame after original)
    (decode : SourceResult → Option Result) (decoded : decode original = some result) :
    Summary (Step sourceStep) before (entry frame decode) after result := by
  intro caller
  have execution := ModuleCall.summary (simulates sourceTerminal) (decodeFrame decode) caller contract
  apply execution.trans
  simpa only [decodeFrame, decoded] using
    (Reaches.single (Step.returned (sourceStep := sourceStep) after result caller))

/-- A projection is used only in the optional determinism certificate. -/
def next (sourceNext : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult) :
    Config Heap (Frame SourceFrame SourceResult Result) Result →
      Config Heap (Frame SourceFrame SourceResult Result) Result
  | .done heap result => .done heap result
  | .active heap (.imported frame inner resume) caller =>
      ModuleCall.config Frame.imported resume caller (sourceNext (.active heap frame inner))
  | .active heap (.returned result) caller => resumeConfig heap result caller
  | .active heap .invalid caller => .active heap .invalid caller

theorem step_next
    {sourceStep : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult → Prop}
    (sourceNext : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult)
    (source_agrees : ∀ {before after}, sourceStep before after → sourceNext before = after)
    {before after : Config Heap (Frame SourceFrame SourceResult Result) Result}
    (transition : Step sourceStep before after) : next sourceNext before = after := by
  cases transition with
  | imported heap frame inner resume caller after transition =>
    exact congrArg (ModuleCall.config Frame.imported resume caller) (source_agrees transition)
  | returned => rfl

/-- Reuse concrete determinism without inspecting any concrete instruction. -/
def facts
    {sourceStep : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult → Prop}
    (sourceNext : Config Heap SourceFrame SourceResult → Config Heap SourceFrame SourceResult)
    (source_agrees : ∀ {before after}, sourceStep before after → sourceNext before = after) :
    InterfaceFacts (code (Result := Result) sourceStep) where
  next := next sourceNext
  step_next := step_next sourceNext source_agrees

end InterfaceAdapter
end Algo2LeanCore


