-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_HPToffoli
-- name    : QMAPerfectCompleteness_Proof_HPToffoli
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:50:54.476196+00:00
-- url     : https://prove2.me/theorems/582c2028-a2cd-4ab2-ba91-40140fd56000
-- title:
--   Exact Toffoli synthesis from H and controlled phase
-- statement:
--   Defines literal H/controlled-P gate lists for CNOT, a doubly controlled phase, and Toffoli. The Toffoli list contains seventeen gates and uses no additional workspace. This finite synthesis supports the reverse class inclusion by replacing each Hadamard–Toffoli instruction with an exact HP circuit.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/HPToffoli.lean, lines 9–148.

/- Generated from Solutions.HPToffoli by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets



/-! Exact finite synthesis for the reverse inclusion, using only H and controlled P.
The phase identity i^((a xor b)c-ac-bc)=(-1)^(abc) supplies CCZ. -/
open Matrix
namespace QMAPerfectCompleteness.Main.HPToffoli
open ReversibleGadgets

def hAt {n : ℕ} (w : Fin n) : Instr gatesHP n where
  gate := ⟨0, by decide⟩
  targets := show Fin 1 ↪ Fin n from ⟨fun _ => w, by intro i j _; exact Subsingleton.elim i j⟩

def cpAt {n : ℕ} (e : Fin 2 ↪ Fin n) : Instr gatesHP n := ⟨⟨1,by decide⟩,e⟩



noncomputable def cnot : List (Instr gatesHP 2) :=
  [hAt 1,cpAt (Function.Embedding.refl _),cpAt (Function.Embedding.refl _),hAt 1]









def pair (a b : Fin 3) (hab : a ≠ b) : Fin 2 ↪ Fin 3 :=
  ⟨![a,b],by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

noncomputable def cnot01 : List (Instr gatesHP 3) := cnot.map (Instr.mapWires (pair 0 1 (by decide)))
def xor01 (x : Basis 3) : Basis 3 := ![x 0,xor (x 1) (x 0),x 2]








noncomputable def ccZ : List (Instr gatesHP 3) :=
  List.replicate 3 (cpAt (pair 0 2 (by decide))) ++
    List.replicate 3 (cpAt (pair 1 2 (by decide))) ++
    cnot01 ++ [cpAt (pair 1 2 (by decide))] ++ cnot01





/-- A literal seventeen-gate H/controlled-P implementation of Toffoli, with no workspace. -/
noncomputable def toffoli : List (Instr gatesHP 3) := [hAt 2] ++ ccZ ++ [hAt 2]









end QMAPerfectCompleteness.Main.HPToffoli


