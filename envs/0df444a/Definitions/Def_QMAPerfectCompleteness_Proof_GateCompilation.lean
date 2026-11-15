-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
-- name    : QMAPerfectCompleteness_Proof_GateCompilation
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:47:09.153207+00:00
-- url     : https://prove2.me/theorems/b6383eab-2dcd-4423-b84e-500e99d60c48
-- title:
--   Literal G₂ gadgets for the paper’s real simulation
-- statement:
--   Defines the paired-Hadamard instruction and the four-wire controlled-phase simulation gadget in Lemma 3.1. The wire order records the simulation bit, the two source phase-gate wires, and workspace. Rational matrices and register splittings provide exact finite descriptions of the gadget and its intended controlled quarter-turn action.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/GateCompilation.lean, lines 8–225.

/- Generated from Solutions.GateCompilation by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation



open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.GateCompilation

/-- Pair H on the data wire with H on an ignored wire, as in Lemma 3.1. -/
noncomputable def pairedH : Instr gatesG2 2 where
  gate := ⟨3, by decide⟩
  targets := show Fin 2 ↪ Fin 2 from Function.Embedding.refl _





/-- Split a two-wire register into its two one-wire factors. -/
def splitTwo : Basis 2 ≃ Basis 1 × Basis 1 where
  toFun x := (fun _ => x 0, fun _ => x 1)
  invFun x := ![x.1 0, x.2 0]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv x := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl













/-- Four wires are ordered simulation c, two original phase-gate wires a,b, clean workspace d. -/
noncomputable def simulationHH : Instr gatesG2 4 where
  gate := ⟨3, by decide⟩
  targets := show Fin 2 ↪ Fin 4 from
    ⟨![0,3], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

noncomputable def simulationToffoli : Instr gatesG2 4 where
  gate := ⟨2, by decide⟩
  targets := show Fin 3 ↪ Fin 4 from
    ⟨![1,2,0], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

/-- Apply Z then X to c exactly when a=b=1; the workspace d is untouched. -/
def controlledQuarterTurnQ : Matrix (Basis 4) (Basis 4) ℚ := fun y x =>
  if y 0 = xor (x 0) (x 1 && x 2) ∧ y 1 = x 1 ∧ y 2 = x 2 ∧ y 3 = x 3 then
    if x 0 && x 1 && x 2 then -1 else 1
  else 0

def simulationHHQ : Matrix (Basis 4) (Basis 4) ℚ := fun y x =>
  if y 1 = x 1 ∧ y 2 = x 2 then
    if xor (y 0 && x 0) (y 3 && x 3) then -(1 / 2) else 1 / 2
  else 0

def simulationToffoliQ : Matrix (Basis 4) (Basis 4) ℚ := fun y x =>
  if y 0 = xor (x 0) (x 1 && x 2) ∧ y 1 = x 1 ∧ y 2 = x 2 ∧ y 3 = x 3 then 1 else 0







def flipCC (x : Basis 4) : Basis 4 := ![xor (x 0) (x 1 && x 2), x 1, x 2, x 3]









/-- The concrete gate list, with each gate applied in the displayed order. -/
noncomputable def realControlledPhaseCircuit : List (Instr gatesG2 4) :=
  [simulationHH, simulationToffoli, simulationHH, simulationToffoli]









/-- Read four wires as (simulation wire, two original wires), workspace wire. -/
def splitFour : Basis 4 ≃ (Bool × Basis 2) × Bool where
  toFun x := ((x 0, ![x 1, x 2]), x 3)
  invFun x := ![x.1.1, x.1.2 0, x.1.2 1, x.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv x := by
    rcases x with ⟨⟨c,x⟩,d⟩
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i; fin_cases i <;> rfl
    · rfl

/-- The real simulation's controlled phase, embedded back into complex circuit amplitudes. -/
noncomputable def realControlledPhase : Matrix (Bool × Basis 2) (Bool × Basis 2) ℂ :=
  (RealSimulation.realRep controlledPhaseMatrix).map Complex.ofReal







end QMAPerfectCompleteness.Main.GateCompilation


