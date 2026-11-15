-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
-- name    : QMAPerfectCompleteness_Proof_HadamardToffoli
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:49:27.573955+00:00
-- url     : https://prove2.me/theorems/e76d7170-6191-422a-95ca-84f065949c50
-- title:
--   Exact controlled-phase, CNOT, and clean-X HT gadgets
-- statement:
--   Defines concrete Hadamard–Toffoli gate lists for the controlled quarter turn, controlled Z, CNOT, and a clean-workspace bit flip. The controlled-Z construction acts on its designated two wires while preserving the spectators; the bit-flip construction has an explicitly clean borrowed-wire condition. These finite gadgets give the constant-overhead G₂-to-HT translation.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/HadamardToffoli.lean, lines 12–226.

/- Generated from Solutions.HadamardToffoli by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets



/-! Concrete exact G₂-to-Hadamard/Toffoli gadgets. The CZ construction is the controlled
quarter-turn squared, equivalently Takeuchi 2024 Fig.3(a), Appendix B:
https://arxiv.org/html/2312.16433v2 . No general synthesis theorem is used. -/
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.HadamardToffoli
open GateCompilation ReversibleGadgets

def hAt {n : ℕ} (w : Fin n) : Instr gatesHT n where
  gate := ⟨0, by decide⟩
  targets := show Fin 1 ↪ Fin n from ⟨fun _ => w, by intro i j _; exact Subsingleton.elim i j⟩

def tAt {n : ℕ} (e : Fin 3 ↪ Fin n) : Instr gatesHT n where
  gate := ⟨1, by decide⟩
  targets := e







noncomputable def hhAt {n : ℕ} (e : Fin 2 ↪ Fin n) : List (Instr gatesHT n) :=
  [hAt (0 : Fin 2), hAt 1].map (Instr.mapWires e)



noncomputable abbrev simulationWires : Fin 2 ↪ Fin 4 := simulationHH.targets
noncomputable abbrev toffoliWires : Fin 3 ↪ Fin 4 := simulationToffoli.targets

/-- Expand only the H⊗H and Toffoli gates appearing in the quarter-turn gadget. -/
noncomputable def quarterTurn : List (Instr gatesHT 4) :=
  hhAt simulationWires ++ [tAt toffoliWires] ++
    hhAt simulationWires ++ [tAt toffoliWires]









def czQ : Matrix (Basis 4) (Basis 4) ℚ :=
  Matrix.diagonal fun x => if x 1 && x 2 then -1 else 1



/-- A twelve-gate HT circuit applies CZ to wires1,2 and is identity on wires0,3. -/
noncomputable def controlledZ : List (Instr gatesHT 4) := quarterTurn ++ quarterTurn









noncomputable def controlledNot : List (Instr gatesHT 4) :=
  [hAt 2] ++ controlledZ ++ [hAt 2]



def cnotAction (x : Basis 4) : Basis 4 := ![x 0, x 1, xor (x 2) (x 1), x 3]

















/-- Takeuchi's X gadget: wire1 is flipped when the borrowed wire2 starts in zero. -/
noncomputable def bitFlipClean : List (Instr gatesHT 4) :=
  [hAt 1] ++ controlledNot ++ controlledZ ++ controlledNot ++ [hAt 1]

def negativeControlAction (x : Basis 4) : Basis 4 := ![x 0, xor (x 1) (!x 2), x 2, x 3]









end QMAPerfectCompleteness.Main.HadamardToffoli


