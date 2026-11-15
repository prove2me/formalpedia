-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_HTPreservation
-- name    : QMAPerfectCompleteness_Proof_HTPreservation
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:53:09.154358+00:00
-- url     : https://prove2.me/theorems/4fa77c43-17e0-4835-aa56-3c1d36c62857
-- title:
--   Clean shared-workspace embedding for HT compilation
-- statement:
--   Defines the basis injection appending three zero bits, the predicate that those workspace bits are clean, and the corresponding matrix embedding. Register equivalences relate the physical compiled verifier wires to the source wires with this shared workspace. These objects support exact acceptance preservation under G₂-to-HT compilation.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/HTPreservation.lean, lines 9–251.

/- Generated from Solutions.HTPreservation by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding



open Matrix
open scoped Kronecker
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.HTCompiler
open HadamardToffoli ReversibleGadgets

/-- Append the same three zero workspace wires to every source basis state. -/
def basisZero {n : ℕ} (x : Basis n) : Basis (n+3) := Fin.append x (fun _ => false)
def dataPart {n : ℕ} (x : Basis (n+3)) : Basis n := x ∘ dataEmbedding n
def IsClean {n : ℕ} (x : Basis (n+3)) : Prop := ∀ j : Fin 3, x (Fin.natAdd n j) = false
instance {n : ℕ} (x : Basis (n+3)) : Decidable (IsClean x) :=
  inferInstanceAs (Decidable (∀ j : Fin 3, x (Fin.natAdd n j) = false))











/-- Isometry initializing the three globally shared scratch wires. -/
def cleanEmbedding (n : ℕ) : Matrix (Basis (n+3)) (Basis n) ℂ :=
  Matrix.of fun y x => if y = basisZero x then 1 else 0
































def compiledWireEquiv (V : Verifier gatesG2) :
    Fin (V.proofQubits + V.ancillaQubits + 3) ≃ Fin (V.proofQubits + (V.ancillaQubits+3)) :=
  finCongr (Nat.add_assoc _ _ _)

def compiledBasis (V : Verifier gatesG2) : (compileVerifier V).Wire ≃ Basis (V.proofQubits+V.ancillaQubits+3) :=
  Equiv.arrowCongr (compiledWireEquiv V).symm (Equiv.refl Bool)



























end QMAPerfectCompleteness.Main.HTCompiler


