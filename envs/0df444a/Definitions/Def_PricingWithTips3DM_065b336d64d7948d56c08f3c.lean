-- Prove2me | Definitions.Def_PricingWithTips3DM_065b336d64d7948d56c08f3c
-- name    : PricingWithTips3DM_065b336d64d7948d56c08f3c
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:30:51.559537+00:00
-- url     : https://prove2.me/theorems/00e4d21a-21fe-4e03-836b-bb065ce0c33f
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Trace
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_c894ac46396dd6667b3fc5a6
import Definitions.Def_PricingWithTips3DM_462775031f7266c486622b2c
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Exact local transition-circuit trace

This module exposes the local Cook--Levin transition circuit as five literal
ordered phases: workspace constants, finite-label dispatch, narrowing,
complete-row equality, and the final conjunction.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- Widening appends exactly the shared false/true constant pool. -/
theorem widenCfg_gates_eq {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm H)
    (hvalid : source.ValidIn base) :
    (widenCfg base source hvalid).builder.gates =
      base.gates ++ [CircuitGate.const false, CircuitGate.const true] := by
  simpa [widenCfg] using CircuitBuilder.allocateBoolWirePool_gates_eq base

/-- Literal gate list and output wire of one complete local transition check. -/
structure TransitionCircuitGateTrace where
  gates : List CircuitGate
  wire : CircuitBuilder.Wire

/-- Exact five-phase trace of one local transition circuit. -/
def transitionCircuitGateTrace (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm H)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    TransitionCircuitGateTrace :=
  let widened := widenCfg base current hcurrent
  let dispatched := dispatchLabels tm H widened.builder widened.constants
    widened.wires widened.valid
  let narrowed := narrowCfg dispatched.builder dispatched.wires dispatched.valid
  let prefixExtension := widened.extension.trans
    (dispatched.extension.trans narrowed.extension)
  let hnextNarrowed : next.ValidIn narrowed.builder :=
    hnext.mono prefixExtension
  let equal := cfgEq narrowed.builder narrowed.wires next narrowed.valid
    hnextNarrowed
  { gates :=
      [CircuitGate.const false, CircuitGate.const true] ++
        dispatchLabelsGateTrace tm H widened.builder widened.constants
          widened.wires widened.valid ++
        (narrowCfgGateTrace dispatched.builder.gates.length
          dispatched.wires).gates ++
        (CircuitBuilder.eqFinGateTrace narrowed.builder.gates.length
          (fun i => narrowed.wires
            ((cfgSlotEquivFin tm H).symm i))
          (fun i => next ((cfgSlotEquivFin tm H).symm i))).gates ++
        [CircuitGate.and narrowed.fit equal.wire]
    wire := equal.builder.gates.length }

/-- The semantic local transition builder appends exactly the five-phase
structural trace. -/
theorem transitionCircuit_gates_eq (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm H)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    (transitionCircuit tm H base current next hcurrent hnext).builder.gates =
      base.gates ++
        (transitionCircuitGateTrace tm H base current next hcurrent hnext).gates := by
  simp only [transitionCircuit, transitionCircuitGateTrace]
  rw [CircuitBuilder.and_gates]
  rw [cfgEq_gates_eq]
  rw [narrowCfg_gates_eq]
  rw [dispatchLabels_gates_eq]
  rw [widenCfg_gates_eq]
  simp only [List.append_assoc]

/-- The local transition result wire is the exact trace output. -/
theorem transitionCircuit_wire_eq_trace
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm H)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    (transitionCircuit tm H base current next hcurrent hnext).wire =
      (transitionCircuitGateTrace tm H base current next hcurrent hnext).wire := by
  rfl

/-- The explicit local trace has the advertised exact gate cost. -/
theorem transitionCircuitGateTrace_length
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm H)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    (transitionCircuitGateTrace tm H base current next hcurrent hnext).gates.length =
      transitionCircuitGateCost tm H := by
  have hgates := congrArg List.length
    (transitionCircuit_gates_eq tm H base current next hcurrent hnext)
  rw [transitionCircuit_gate_delta, List.length_append] at hgates
  omega

end

end CLRS.Chapter34.Turing.CookLevin


