-- Prove2me | Definitions.Def_PricingWithTips3DM_ec36918cdeaaf64e94c28c02
-- name    : PricingWithTips3DM_ec36918cdeaaf64e94c28c02
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:32:07.854262+00:00
-- url     : https://prove2.me/theorems/0f653d58-ef2b-4909-8e2f-c84b25883e46
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTail
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_059ce46712187d0906033699
import Definitions.Def_PricingWithTips3DM_2bcb0f394e67282193a1fbc5
import Definitions.Def_PricingWithTips3DM_b083674f1a4da1f12c728249
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Executable post-transition verifier-circuit tail

This module specializes the continuous unary tail controller to the actual
Cook--Levin verifier and identifies its output with the complete circuit
encoding suffix after the transition phase.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

open StateTransition
open PolyBuilder

/-- Exact encoded circuit suffix after all adjacent-row transitions. -/
def verifierCircuitTailGateStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : List CircuitSym :=
  verifierInitialBoundaryGateStream W x ++
    verifierInputBoundaryGateStream W x ++
    verifierAcceptingBoundaryGateStream W x ++
    verifierFinalConjunctionGateStream W x ++
    .outputMark :: encNat (verifierCircuit W x).output

/-- Canonical runtime operands for every post-transition verifier phase. -/
def compileVerifierTailScript
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : AffineVerifierTailScript :=
  { initialFrames := compileVerifierInitialBoundaryFrames W x
    inputShape := verifierInputBoundaryScript W x
    acceptingFrames := compileVerifierAcceptingBoundaryFrames W x
    conjunctionFrame := verifierFinalConjunctionFrame W x
    outputWire := (verifierCircuit W x).output }

/-- The compiled operand script denotes the exact semantic verifier tail. -/
theorem compileVerifierTailScript_gateStream_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) :
    affineVerifierTailGateStream (compileVerifierTailScript W x) =
      verifierCircuitTailGateStream W x := by
  simp only [compileVerifierTailScript, affineVerifierTailGateStream,
    verifierCircuitTailGateStream]
  rw [compileVerifierInitialBoundaryFrames_gateStream_eq]
  rw [show affineInputShapeGateStream (verifierInputBoundaryScript W x) =
      verifierInputBoundaryGateStream W x by
    simpa [affineVerifierInputShapeScriptGateStream] using
      verifierInputBoundaryScript_gateStream_eq W x]
  rw [show affineVerifierTailAcceptingGateStream
        (compileVerifierAcceptingBoundaryFrames W x) =
      verifierAcceptingBoundaryGateStream W x by
    change affineOptionalEqFinGateStream
        (compileVerifierAcceptingBoundaryFrames W x) = _
    exact compileVerifierAcceptingBoundaryFrames_gateStream_eq W x]
  rw [verifierFinalConjunctionFrame_gateStream_eq]

/-- The already frozen transition prefix followed by the generated tail is
the complete verifier-circuit encoding, byte for byte. -/
theorem verifierCircuitTransitionPrefix_append_tail
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) :
    verifierCircuitTransitionPrefix W x ++
        verifierCircuitTailGateStream W x =
      encodeCircuit (verifierCircuit W x) := by
  have hgates :
      ((((verifierTransitions W x).builder.gates ++
          (verifierInitialBoundaryGateTrace W x).gates) ++
          verifierInputBoundaryGateTrace W x) ++
          verifierAcceptingBoundaryGateTrace W x) ++
          (CircuitBuilder.conjunctionGateTrace
            (verifierAcceptingBoundary W x).builder.gates.length
            (verifierConstraintWires W x)).gates =
        (verifierCircuit W x).gates := by
    calc
      _ = (((verifierInitialBoundary W x).builder.gates ++
          verifierInputBoundaryGateTrace W x) ++
          verifierAcceptingBoundaryGateTrace W x) ++
          (CircuitBuilder.conjunctionGateTrace
            (verifierAcceptingBoundary W x).builder.gates.length
            (verifierConstraintWires W x)).gates := by
              rw [verifierInitialBoundary_gates_eq]
      _ = ((verifierInputBoundary W x).builder.gates ++
          verifierAcceptingBoundaryGateTrace W x) ++
          (CircuitBuilder.conjunctionGateTrace
            (verifierAcceptingBoundary W x).builder.gates.length
            (verifierConstraintWires W x)).gates := by
              rw [verifierInputBoundary_gates_eq]
      _ = (verifierAcceptingBoundary W x).builder.gates ++
          (CircuitBuilder.conjunctionGateTrace
            (verifierAcceptingBoundary W x).builder.gates.length
            (verifierConstraintWires W x)).gates := by
              rw [verifierAcceptingBoundary_gates_eq]
      _ = (verifierCircuit W x).gates :=
        (verifierCircuit_gates_eq_finalConjunction W x).symm
  have hstream := congrArg (List.flatMap encodeCircuitGate) hgates
  simp only [List.flatMap_append, List.append_assoc] at hstream
  rw [verifierCircuitTransitionPrefix_eq]
  simp only [verifierCircuitTailGateStream, encodeCircuit,
    verifierInitialBoundaryGateStream, verifierInputBoundaryGateStream,
    verifierAcceptingBoundaryGateStream,
    verifierFinalConjunctionGateStream, List.append_assoc]
  simpa only [List.append_assoc] using congrArg
    (fun gates => encNat (verifierCircuit W x).inputCount ++ gates ++
      (.outputMark :: encNat (verifierCircuit W x).output)) hstream

/-- One fixed program computes the exact complete post-transition suffix. -/
def verifierCircuitTail_run
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) (output : List CircuitSym) :
    EvalsToInTime (step affineVerifierTailRevProgram)
      (affineVerifierTailLoopCfg
        (encodeAffineVerifierTailScript
          (compileVerifierTailScript W x)) output)
      (some (haltCfg affineVerifierTailRevProgram
        ((verifierCircuitTailGateStream W x).reverse ++ output)))
      (affineVerifierTailRevSteps (compileVerifierTailScript W x)) := by
  simpa [compileVerifierTailScript_gateStream_eq] using
    affineVerifierTail_run (compileVerifierTailScript W x) output

/-- The specialized verifier tail inherits the generic quadratic runtime
envelope in its exact combined operand encoding. -/
theorem verifierCircuitTail_steps_le
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) :
    affineVerifierTailRevSteps (compileVerifierTailScript W x) ≤
      5000 * (encodeAffineVerifierTailScript
        (compileVerifierTailScript W x)).length ^ 2 + 100 :=
  affineVerifierTailRev_steps_le (compileVerifierTailScript W x)

end

end CLRS.Chapter34.Turing.CookLevin


