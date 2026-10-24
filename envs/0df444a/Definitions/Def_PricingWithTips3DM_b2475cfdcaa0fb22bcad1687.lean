-- Prove2me | Definitions.Def_PricingWithTips3DM_b2475cfdcaa0fb22bcad1687
-- name    : PricingWithTips3DM_b2475cfdcaa0fb22bcad1687
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:50:52.856148+00:00
-- url     : https://prove2.me/theorems/5bb8c455-2c6c-485c-9f58-6bfb07267248
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly.Core
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_00c076c7c1c016cf6dc515fa
import Definitions.Def_PricingWithTips3DM_b78c47207fe53b8f94ac22f3
import Definitions.Def_PricingWithTips3DM_3110dc68424c0335dc08bfca
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cook--Levin verifier-circuit assembly

This file gives names to the successive append-only builder stages.  It keeps
the tableau rows public throughout and allocates the Boolean constant pool
once, before all constraint families and boundary circuits.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- First row of every nonempty `T + 1` row tableau. -/
def verifierFirstRow (T : Nat) : Fin (tableauRowCount T) :=
  ⟨0, by simp [tableauRowCount]⟩

/-- Canonical public tableau-row allocation for one verifier instance. -/
def verifierRows {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :=
  allocateTableauRows W.machine.tm ((verifierHeight W).eval x.length)
    ((verifierHorizon W).eval x.length)

/-- The unique shared Boolean constant pool used by the verifier circuit. -/
def verifierPool {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :=
  CircuitBuilder.allocateBoolWirePool (verifierRows W x).builder

/-- Canonical validity constraints for every public tableau row. -/
def verifierValidity {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :=
  let rows := verifierRows W x
  let pool := verifierPool W x
  validCfgCircuitFamily pool.builder rows.rows
    (fun row => (rows.rowValid row).mono pool.extension)

/-- Canonical local-transition constraints for every adjacent row pair. -/
def verifierTransitions {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :=
  let rows := verifierRows W x
  let pool := verifierPool W x
  let validity := verifierValidity W x
  transitionCircuitFamily W.machine.tm ((verifierHeight W).eval x.length)
    validity.builder rows.rows (fun row =>
      (rows.rowValid row).mono (pool.extension.trans validity.extension))

/-- Complete symbolic initial-row equality constraint. -/
def verifierInitialBoundary {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :=
  let rows := verifierRows W x
  let pool := verifierPool W x
  let validity := verifierValidity W x
  let transitions := verifierTransitions W x
  let extension := pool.extension.trans
    (validity.extension.trans transitions.extension)
  let row := rows.rows (verifierFirstRow _)
  let hrow := (rows.rowValid (verifierFirstRow _)).mono extension
  let inputStack := row.stack W.machine.tm.k₀
  symbolicInitialCfgCircuit W.machine.tm ((verifierHeight W).eval x.length)
    transitions.builder (pool.pool.mono (validity.extension.trans
      transitions.extension)) row hrow inputStack (hrow.stack _)

/-- Certificate-shape and fixed-instance constraint on the initial input
stack. -/
def verifierInputBoundary {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :=
  let rows := verifierRows W x
  let pool := verifierPool W x
  let validity := verifierValidity W x
  let transitions := verifierTransitions W x
  let initial := verifierInitialBoundary W x
  let extension := pool.extension.trans (validity.extension.trans
    (transitions.extension.trans initial.extension))
  let row := rows.rows (verifierFirstRow _)
  let hrow := (rows.rowValid (verifierFirstRow _)).mono extension
  verifierInputShapeCircuit W ((verifierHeight W).eval x.length)
    initial.builder (pool.pool.mono (validity.extension.trans
      (transitions.extension.trans initial.extension)))
    (row.stack W.machine.tm.k₀) (hrow.stack _) x

/-- Exact accepting-row equality constraint on the last tableau row. -/
def verifierAcceptingBoundary {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :=
  let rows := verifierRows W x
  let pool := verifierPool W x
  let validity := verifierValidity W x
  let transitions := verifierTransitions W x
  let initial := verifierInitialBoundary W x
  let input := verifierInputBoundary W x
  let extension := pool.extension.trans (validity.extension.trans
    (transitions.extension.trans (initial.extension.trans input.extension)))
  acceptingOutputCircuit W.machine.tm ((verifierHeight W).eval x.length)
    input.builder (pool.pool.mono (validity.extension.trans
      (transitions.extension.trans (initial.extension.trans input.extension))))
    (rows.rows (Fin.last ((verifierHorizon W).eval x.length)))
    ((rows.rowValid _).mono extension)
    (List.map W.machine.outputAlphabet.invFun (boolEncoding true))

/-- All local and boundary outputs, transported to the last pre-conjunction
builder. -/
def verifierConstraintWires {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) : List CircuitBuilder.Wire :=
  let validity := verifierValidity W x
  let transitions := verifierTransitions W x
  let initial := verifierInitialBoundary W x
  let input := verifierInputBoundary W x
  let accepting := verifierAcceptingBoundary W x
  (List.ofFn validity.outputs) ++ (List.ofFn transitions.outputs) ++
    [initial.wire, input.wire, accepting.wire]

/-- Every collected constraint output belongs to the common last builder. -/
theorem verifierConstraintWires_valid {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    let accepting := verifierAcceptingBoundary W x
    ∀ wire ∈ verifierConstraintWires W x,
      accepting.builder.WireValid wire := by
  classical
  dsimp only [verifierConstraintWires]
  intro wire hwire
  simp only [List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil,
    or_false]
    at hwire
  rcases hwire with (⟨row, rfl⟩ | ⟨step, rfl⟩) | hwire
  · exact (verifierAcceptingBoundary W x).extension.wireValid
      ((verifierInputBoundary W x).extension.wireValid
        ((verifierInitialBoundary W x).extension.wireValid
          ((verifierTransitions W x).extension.wireValid
            ((verifierValidity W x).outputsValid row))))
  · exact (verifierAcceptingBoundary W x).extension.wireValid
      ((verifierInputBoundary W x).extension.wireValid
        ((verifierInitialBoundary W x).extension.wireValid
          ((verifierTransitions W x).outputsValid step)))
  · rcases hwire with rfl | rfl | rfl
    · exact (verifierAcceptingBoundary W x).extension.wireValid
        ((verifierInputBoundary W x).extension.wireValid
          ((verifierInitialBoundary W x).valid))
    · exact (verifierAcceptingBoundary W x).extension.wireValid
        ((verifierInputBoundary W x).valid)
    · exact (verifierAcceptingBoundary W x).valid

/-- Final conjunction of every whole-tableau constraint. -/
def verifierConjunction {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :=
  let accepting := verifierAcceptingBoundary W x
  accepting.builder.conjunction (verifierConstraintWires W x)
    (verifierConstraintWires_valid W x)

end

end CLRS.Chapter34.Turing.CookLevin


