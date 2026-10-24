-- Prove2me | Definitions.Def_PricingWithTips3DM_0c9469167e0ca0769953afe0
-- name    : PricingWithTips3DM_0c9469167e0ca0769953afe0
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:45:33.84725+00:00
-- url     : https://prove2.me/theorems/fae5fec0-6197-4495-9d6b-95fa4be2276d
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Narrowing
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_a46ec1070e8b9fcb3ebc4d0c
import Definitions.Def_PricingWithTips3DM_be8874136ebaa60ae7dea5ae
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Executable Cook--Levin narrowing trace

This module connects the pure narrowing trace in `Tableau.Workspace` to one
fixed `PolyBuilder` machine.  The machine emits the false-seeded overflow
disjunction and its final negation in one continuous run; the intermediate OR
phase does not halt and hand its output to a second machine.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

/-- Canonical runtime OR frames for the overflow-height wires inspected by
Cook--Levin narrowing. -/
def affineNarrowCfgFrames {tm : _root_.Turing.FinTM2} {H : Nat}
    (start : Nat) (source : CfgWires tm (workHeight tm H)) :
    List AffineOrFinPairFrame :=
  affineOrFinCanonicalFrames start (narrowCfgOverflowWires source)

/-- The exact input consumed by the continuous OR-then-NOT controller. -/
def encodeAffineNarrowCfgInput {tm : _root_.Turing.FinTM2} {H : Nat}
    (start : Nat) (source : CfgWires tm (workHeight tm H)) :
    List UnaryFrameSym :=
  let disjunction := CircuitBuilder.disjunctionGateTrace start
    (narrowCfgOverflowWires source)
  encodeAffineOrThenNotInput (affineNarrowCfgFrames start source)
    disjunction.wire

/-- The machine's forward byte stream is exactly the semantic narrowing trace. -/
theorem affineNarrowCfgGateStream_eq_trace
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (start : Nat) (source : CfgWires tm (workHeight tm H)) :
    let disjunction := CircuitBuilder.disjunctionGateTrace start
      (narrowCfgOverflowWires source)
    affineOrThenNotGateStream (affineNarrowCfgFrames start source)
        disjunction.wire =
      (narrowCfgGateTrace start source).gates.flatMap encodeCircuitGate := by
  dsimp only
  simpa [affineNarrowCfgFrames, narrowCfgGateTrace] using
    affineOrThenNotGateStream_eq_trace start (narrowCfgOverflowWires source)

/-- One fixed machine emits the complete narrowing gate trace and halts with
all scratch stacks cleared. -/
def affineNarrowCfg_run {tm : _root_.Turing.FinTM2} {H : Nat}
    (start : Nat) (source : CfgWires tm (workHeight tm H))
    (output : List CircuitSym) :
    let disjunction := CircuitBuilder.disjunctionGateTrace start
      (narrowCfgOverflowWires source)
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrThenNotLoopCfg (encodeAffineNarrowCfgInput start source) output)
      (some (haltCfg affineOrFinRevProgram
        (((narrowCfgGateTrace start source).gates.flatMap
          encodeCircuitGate).reverse ++ output)))
      (affineOrThenNotRevSteps (affineNarrowCfgFrames start source)
        disjunction.wire) := by
  dsimp only
  simpa [encodeAffineNarrowCfgInput, affineNarrowCfgFrames,
    narrowCfgGateTrace] using
    affineOrThenNotCanonical_run start (narrowCfgOverflowWires source) output

/-- The exact narrowing controller runtime is linear in its explicit input. -/
theorem affineNarrowCfgRev_steps_le
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (start : Nat) (source : CfgWires tm (workHeight tm H)) :
    let disjunction := CircuitBuilder.disjunctionGateTrace start
      (narrowCfgOverflowWires source)
    affineOrThenNotRevSteps (affineNarrowCfgFrames start source)
        disjunction.wire ≤
      100 * (encodeAffineNarrowCfgInput start source).length + 2 := by
  dsimp only
  simpa [encodeAffineNarrowCfgInput] using
    affineOrThenNotRev_steps_le (affineNarrowCfgFrames start source)
      (CircuitBuilder.disjunctionGateTrace start
        (narrowCfgOverflowWires source)).wire

end CLRS.Chapter34.Turing.PolyBuilder


