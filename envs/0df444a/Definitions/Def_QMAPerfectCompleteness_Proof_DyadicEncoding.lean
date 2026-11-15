-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_DyadicEncoding
-- name    : QMAPerfectCompleteness_Proof_DyadicEncoding
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:50:00.929554+00:00
-- url     : https://prove2.me/theorems/0c96e485-12d5-4252-828d-a1bf7764c21c
-- title:
--   Executable verifier encoding of the real simulation
-- statement:
--   Defines the numerical raw-circuit and total string versions of the HP-to-G₂ compiler. The raw transformation adds one proof bit and one ancilla bit and shifts the output wire. Erasure and encoding identities identify its output on every valid source code with the semantic real-simulation verifier; malformed inputs have a fixed fallback.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/DyadicEncoding.lean, lines 7–50.

/- Generated from Solutions.DyadicEncoding by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding



/-! Executable unary-code compiler for the paper's real simulation. -/
namespace QMAPerfectCompleteness.Main.DyadicCompiler

def fromTags (i : ℕ × List ℕ) : RawEncoding.Instruction := ⟨i.1,i.2⟩
def rawCompileInstr (n : ℕ) (i : RawEncoding.Instruction) : List RawEncoding.Instruction :=
  (compileTags n (i.gate,i.wires)).map fromTags

def rawCompile (V : RawEncoding.Circuit) : RawEncoding.Circuit :=
  ⟨V.proofQubits+1,V.ancillaQubits+1,V.output+1,
    V.gates.flatMap (rawCompileInstr (V.proofQubits+V.ancillaQubits))⟩

lemma erase_fromTags {G : GateSet} {n : ℕ} (i : Instr G n) :
    RawEncoding.eraseInstr i = fromTags (tags i) := rfl

theorem compileInstr_erase {n : ℕ} (i : Instr gatesHP n) :
    (compileInstr i).map RawEncoding.eraseInstr = rawCompileInstr n (RawEncoding.eraseInstr i) := by
  change (compileInstr i).map RawEncoding.eraseInstr = (compileTags n (tags i)).map fromTags
  have h := congrArg (List.map fromTags) (compileInstr_tags i)
  simpa only [List.map_map, Function.comp_def, ← erase_fromTags] using h

lemma erase_cast {n r : ℕ} (h : n = r) (i : Instr gatesG2 n) :
    RawEncoding.eraseInstr (Instr.mapWires (finCongr h).toEmbedding i) = RawEncoding.eraseInstr i := by
  cases h
  rfl

theorem rawCompile_erase (V : Verifier gatesHP) :
    rawCompile (RawEncoding.eraseVerifier V) = RawEncoding.eraseVerifier (compileVerifier V) := by
  simp only [rawCompile,RawEncoding.eraseVerifier,compileVerifier,List.flatMap_map]
  congr 1
  rw [List.map_map]
  have hmap : (RawEncoding.eraseInstr ∘ Instr.mapWires
      (G := gatesG2) (finCongr (show V.proofQubits + V.ancillaQubits + 2 =
        (V.proofQubits+1)+(V.ancillaQubits+1) by omega)).toEmbedding) = RawEncoding.eraseInstr := by
    funext i
    exact erase_cast _ i
  rw [hmap]
  simp only [compileGates,List.map_flatMap]
  apply List.flatMap_congr
  intro i _
  exact (compileInstr_erase i).symm

def executableCompile : QAlgorithms.Complexity.Str → QAlgorithms.Complexity.Str :=
  RawEncoding.compile RawEncoding.hpTable rawCompile ⟨0,1,0,[]⟩

@[simp] theorem executableCompile_encode (V : Verifier gatesHP) :
    executableCompile V.encode = (compileVerifier V).encode := by
  exact RawEncoding.compile_encode RawEncoding.hpTable RawEncoding.hpTable_correct _ _ _ rawCompile_erase V

end QMAPerfectCompleteness.Main.DyadicCompiler


