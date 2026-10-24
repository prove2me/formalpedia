-- Prove2me | Definitions.Def_PricingWithTips3DM_5c7c8fbfa87ce3f62c971fa8
-- name    : PricingWithTips3DM_5c7c8fbfa87ce3f62c971fa8
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:29:37.657909+00:00
-- url     : https://prove2.me/theorems/1998dcc7-04c1-453d-8712-a39183645703
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorAcceptingBoundary
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_8cc4e6ffaac785e884f3ea53
import Definitions.Def_PricingWithTips3DM_a1d5f3d65fa5a824042ea4b3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Executable accepting-row boundary

The total accepting boundary has two literal construction branches.  A
representable target appends complete-row equality; an unrepresentable target
reuses the shared false wire and appends no gates.  The optional equality
controller executes exactly this distinction under one fixed program.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

open StateTransition
open PolyBuilder

def verifierAcceptingOutput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    List (W.machine.tm.Γ W.machine.tm.k₁) :=
  List.map W.machine.outputAlphabet.invFun (boolEncoding true)

/-- Static complete halt target used in the representable branch. -/
def verifierAcceptingTargetWires
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ)
    (hfit : AcceptingOutputFits W.machine.tm
      ((verifierHeight W).eval x.length) (verifierAcceptingOutput W)) :=
  let pool := verifierPool W x
  let validity := verifierValidity W x
  let transitions := verifierTransitions W x
  let initial := verifierInitialBoundary W x
  let input := verifierInputBoundary W x
  let output := verifierAcceptingOutput W
  let halphabet := haltList_alphabetBounded_of_fits W.machine.tm
    ((verifierHeight W).eval x.length) output hfit
  let hheight := haltList_height_of_fits W.machine.tm
    ((verifierHeight W).eval x.length) output hfit
  let code := encodeCfg W.machine.tm halphabet hheight
  staticBoundedCfgWires
    (pool.pool.mono (validity.extension.trans
      (transitions.extension.trans (initial.extension.trans input.extension))))
    code

/-- Exact gate list appended by the total accepting boundary. -/
def verifierAcceptingBoundaryGateTrace
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : List CircuitGate := by
  classical
  let H := (verifierHeight W).eval x.length
  let rows := verifierRows W x
  let input := verifierInputBoundary W x
  let output := verifierAcceptingOutput W
  by_cases hfit : AcceptingOutputFits W.machine.tm H output
  · exact (CircuitBuilder.eqFinGateTrace input.builder.gates.length
      (fun i => rows.rows (Fin.last ((verifierHorizon W).eval x.length))
        ((cfgSlotEquivFin W.machine.tm H).symm i))
      (fun i => verifierAcceptingTargetWires W x hfit
        ((cfgSlotEquivFin W.machine.tm H).symm i))).gates
  · exact []

/-- The semantic accepting-boundary builder appends exactly the selected
literal branch. -/
theorem verifierAcceptingBoundary_gates_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) :
    (verifierAcceptingBoundary W x).builder.gates =
      (verifierInputBoundary W x).builder.gates ++
        verifierAcceptingBoundaryGateTrace W x := by
  classical
  let H := (verifierHeight W).eval x.length
  let T := (verifierHorizon W).eval x.length
  let rows := verifierRows W x
  let pool := verifierPool W x
  let validity := verifierValidity W x
  let transitions := verifierTransitions W x
  let initial := verifierInitialBoundary W x
  let input := verifierInputBoundary W x
  let extension := pool.extension.trans (validity.extension.trans
    (transitions.extension.trans (initial.extension.trans input.extension)))
  let row := rows.rows (Fin.last T)
  let hrow := (rows.rowValid (Fin.last T)).mono extension
  let pool' := pool.pool.mono (validity.extension.trans
    (transitions.extension.trans (initial.extension.trans input.extension)))
  let output := verifierAcceptingOutput W
  change (acceptingOutputCircuit W.machine.tm H input.builder pool' row hrow
      output).builder.gates =
    input.builder.gates ++ verifierAcceptingBoundaryGateTrace W x
  by_cases hfit : AcceptingOutputFits W.machine.tm H output
  · have hfit' : AcceptingOutputFits W.machine.tm
        ((verifierHeight W).eval x.length) (verifierAcceptingOutput W) := by
      simpa [H, output] using hfit
    let target := verifierAcceptingTargetWires W x hfit'
    have htarget : target.ValidIn input.builder := by
      exact staticBoundedCfgWires_valid _ _
    rw [show acceptingOutputCircuit W.machine.tm H input.builder pool' row hrow
        output = cfgEqBoundaryCircuit input.builder row target hrow htarget by
      simp only [acceptingOutputCircuit, hfit]
      rfl]
    change (cfgEq input.builder row target hrow htarget).builder.gates = _
    rw [cfgEq_gates_eq]
    have htrace : verifierAcceptingBoundaryGateTrace W x =
        (CircuitBuilder.eqFinGateTrace input.builder.gates.length
          (fun i => row ((cfgSlotEquivFin W.machine.tm H).symm i))
          (fun i => target ((cfgSlotEquivFin W.machine.tm H).symm i))).gates := by
      unfold verifierAcceptingBoundaryGateTrace
      rw [dif_pos hfit']
    rw [htrace]
  · have hfit' : ¬ AcceptingOutputFits W.machine.tm
        ((verifierHeight W).eval x.length) (verifierAcceptingOutput W) := by
      simpa [H, output] using hfit
    rw [show acceptingOutputCircuit W.machine.tm H input.builder pool' row
        hrow output = falseBoundaryCircuit input.builder pool' by
      simp only [acceptingOutputCircuit, hfit]
      rfl]
    change input.builder.gates =
      input.builder.gates ++ verifierAcceptingBoundaryGateTrace W x
    have htrace : verifierAcceptingBoundaryGateTrace W x = [] := by
      unfold verifierAcceptingBoundaryGateTrace
      rw [dif_neg hfit']
    rw [htrace, List.append_nil]

/-- Exact encoded accepting-boundary suffix. -/
def verifierAcceptingBoundaryGateStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : List CircuitSym :=
  (verifierAcceptingBoundaryGateTrace W x).flatMap encodeCircuitGate

/-- Optional canonical equality frames matching the total constructor's two
branches. -/
def compileVerifierAcceptingBoundaryFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : Option (List AffineEqFinPairFrame) := by
  classical
  let H := (verifierHeight W).eval x.length
  let rows := verifierRows W x
  let input := verifierInputBoundary W x
  let output := verifierAcceptingOutput W
  by_cases hfit : AcceptingOutputFits W.machine.tm H output
  · exact some (affineEqFinCanonicalFrames input.builder.gates.length _
      (fun i => rows.rows (Fin.last ((verifierHorizon W).eval x.length))
        ((cfgSlotEquivFin W.machine.tm H).symm i))
      (fun i => verifierAcceptingTargetWires W x hfit
        ((cfgSlotEquivFin W.machine.tm H).symm i)))
  · exact none

theorem compileVerifierAcceptingBoundaryFrames_gateStream_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) :
    affineOptionalEqFinGateStream
        (compileVerifierAcceptingBoundaryFrames W x) =
      verifierAcceptingBoundaryGateStream W x := by
  classical
  simp only [compileVerifierAcceptingBoundaryFrames,
    verifierAcceptingBoundaryGateStream,
    verifierAcceptingBoundaryGateTrace]
  split <;> rename_i hfit
  · simpa [affineOptionalEqFinGateStream] using
      affineEqFinCanonicalGateStream_eq_trace
        (verifierInputBoundary W x).builder.gates.length
        (fun i =>
          (verifierRows W x).rows
            (Fin.last ((verifierHorizon W).eval x.length))
            ((cfgSlotEquivFin W.machine.tm
              ((verifierHeight W).eval x.length)).symm i))
        (fun i =>
          verifierAcceptingTargetWires W x hfit
            ((cfgSlotEquivFin W.machine.tm
              ((verifierHeight W).eval x.length)).symm i))
  · rfl

/-- One fixed optional-equality controller executes either accepting branch
and emits exactly the semantic suffix. -/
def compileVerifierAcceptingBoundaryFrames_run
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) (output : List CircuitSym) :
    EvalsToInTime (step affineOptionalEqFinRevProgram)
      (affineOptionalEqFinLoopCfg
        (encodeAffineOptionalEqFin
          (compileVerifierAcceptingBoundaryFrames W x)) output)
      (some (haltCfg affineOptionalEqFinRevProgram
        ((verifierAcceptingBoundaryGateStream W x).reverse ++ output)))
      (affineOptionalEqFinSteps
        (compileVerifierAcceptingBoundaryFrames W x)) := by
  simpa [compileVerifierAcceptingBoundaryFrames_gateStream_eq] using
    affineOptionalEqFin_run
      (compileVerifierAcceptingBoundaryFrames W x) output

end

end CLRS.Chapter34.Turing.CookLevin


