-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCompilerInterface
-- name    : QMAPerfectCompleteness_Proof_RepetitionCompilerInterface
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:59:48.403201+00:00
-- url     : https://prove2.me/theorems/53366d05-5dce-4e19-b907-91d6880ac159
-- title:
--   Exact verifier-code interface for the repetition machine
-- statement:
--   Relates the repetition machine’s numerical instruction recipes and copied output bodies to the semantic verifier encoding. The target code consists of remapped copies followed by the flag initialization and AND chain. Resource bounds extracted from valid source encodings discharge the numerical premises of the machine runtime estimates.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RepetitionCompilerInterface.lean, lines 10–115.

/- Generated from Solutions.RepetitionCompilerInterface by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Proof_BinaryComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClassTransport
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_FixedBlockCopy
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_HTEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_HTPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCompilerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Exact verifier-code interface of the repetition transducer. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace QMAPerfectCompleteness.Main.Repetition.CompilerTM
open QAlgorithms.Complexity (Str encNat)

def rawInstr (kind : Fin 4) (a : Fin 3 → ℕ) : RawEncoding.Instruction := ⟨kind.val,rawArgs kind a⟩

noncomputable def instrRecipe {N : ℕ} (i : Instr gatesG2 N) : Recipe :=
  (⟨i.gate.val,by have h := i.gate.isLt; change i.gate.val < 4 at h; exact h⟩,
    fun j => ((RawEncoding.eraseInstr i).wires[j.val]?).getD 0)

lemma rawInstr_instrRecipe {N : ℕ} (i : Instr gatesG2 N) :
    rawInstr (instrRecipe i).1 (instrRecipe i).2 = RawEncoding.eraseInstr i := by
  rcases i with ⟨g,t⟩
  fin_cases g <;> rfl

lemma instructionCode_eq (kind : Fin 4) (a : Fin 3 → ℕ) :
    instructionCode kind a = (rawInstr kind a).encode := rfl

lemma mappedCode_eq (kind : Fin 4) (a : Fin 3 → ℕ) (m b n j : ℕ) :
    mappedCode kind a m b n j = (Encoding.remapInstruction m b n j (rawInstr kind a)).encode := by
  simp only [mappedCode,mappedWires,Encoding.remapInstruction,RawEncoding.Instruction.encode,
    rawInstr,List.flatMap_map,Function.comp_def]

lemma sourceCode_verifier (V : Verifier gatesG2) :
    sourceCode V.proofQubits V.ancillaQubits V.output.val (V.gates.map instrRecipe) = V.encode := by
  simp only [sourceCode,sourceHeader,sourceBody,instructionCode_eq,List.flatMap_map,Function.comp_def,
    rawInstr_instrRecipe,RawEncoding.eraseInstr_encode,List.length_map]
  simp only [Verifier.encode,encodeGates,List.append_assoc]

lemma copiesBody_eq_ofFn (m b n : ℕ) (rs : List Recipe) (r : ℕ) : ∀ j,
    copiesBody m b n rs j r = (List.ofFn (fun i : Fin r => copyBody m b n (j+i.val) rs)).flatten := by
  induction r with
  | zero => intro j; rfl
  | succ r ih =>
    intro j
    simp only [copiesBody,List.ofFn_succ,List.flatten_cons,Fin.val_zero,Nat.add_zero,Fin.val_succ]
    rw [ih]
    congr 2
    congr 1
    funext i
    congr 1
    omega

lemma andBody_eq_ofFn (m b n o : ℕ) (r : ℕ) : ∀ j,
    andBody m b n o j r = (List.ofFn (fun i : Fin r => andCode m b n (j+i.val) o)).flatten := by
  induction r with
  | zero => intro j; rfl
  | succ r ih =>
    intro j
    simp only [andBody,List.ofFn_succ,List.flatten_cons,Fin.val_zero,Nat.add_zero,Fin.val_succ]
    rw [ih]
    congr 2
    congr 1
    funext i
    congr 1
    omega

lemma copiesBody_eq_finRange (m b n : ℕ) (rs : List Recipe) :
    copiesBody m b n rs 0 n = (List.finRange n).flatMap (fun j => copyBody m b n j.val rs) := by
  rw [copiesBody_eq_ofFn,List.ofFn_eq_map]
  simp only [Nat.zero_add,List.flatMap_def]

lemma andBody_eq_finRange (m b n o : ℕ) :
    andBody m b n o 0 n = (List.finRange n).flatMap (fun j => andCode m b n j.val o) := by
  rw [andBody_eq_ofFn,List.ofFn_eq_map]
  simp only [Nat.zero_add,List.flatMap_def]

lemma copyBody_verifier (V : Verifier gatesG2) (n j : ℕ) :
    copyBody V.proofQubits V.ancillaQubits n j (V.gates.map instrRecipe) =
      (V.gates.map (fun i => Encoding.remapInstruction V.proofQubits V.ancillaQubits n j
        (RawEncoding.eraseInstr i))).flatMap RawEncoding.Instruction.encode := by
  simp only [copyBody,List.flatMap_map,Function.comp_def,mappedCode_eq,rawInstr_instrRecipe]

lemma finalBody_verifier (V : Verifier gatesG2) (n : ℕ) :
    finalBody V.proofQubits V.ancillaQubits n V.output.val (V.gates.map instrRecipe) =
      (Encoding.rawRepeat n (RawEncoding.eraseVerifier V)).gates.flatMap RawEncoding.Instruction.encode := by
  simp only [finalBody,copiesBody_eq_finRange,andBody_eq_finRange,copyBody_verifier,
    Encoding.rawRepeat,RawEncoding.eraseVerifier,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,List.flatMap_map,Function.comp_def,List.flatMap_assoc,
    List.map_map,flagCode,andCode,RawEncoding.Instruction.encode]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

lemma targetCode_verifier (V : Verifier gatesG2) (n : ℕ) :
    targetCode V.proofQubits V.ancillaQubits n V.output.val (V.gates.map instrRecipe) =
      (Circuit.verifier V n).encode := by
  have h := RawEncoding.eraseVerifier_encode (Circuit.verifier V n)
  rw [← Encoding.rawRepeat_erase V n] at h
  rw [← h]
  have hc : targetCount n (V.gates.map instrRecipe) =
      (Encoding.rawRepeat n (RawEncoding.eraseVerifier V)).gates.length := by
    rw [Encoding.rawRepeat_erase]
    simp only [targetCount,List.length_map,RawEncoding.eraseVerifier,Circuit.verifier_gate_count]
    omega
  simp only [targetCode,targetHeader,RawEncoding.Circuit.encode,finalBody_verifier,hc]
  rfl

lemma instrRecipe_address_le {N : ℕ} (i : Instr gatesG2 N) (j : Fin 3) :
    (instrRecipe i).2 j ≤ N := by
  rcases i with ⟨g,t⟩
  fin_cases g <;> fin_cases j <;>
    simp only [instrRecipe,RawEncoding.eraseInstr,List.ofFn_succ,List.ofFn_zero,
      List.getElem?_cons_zero,List.getElem?_cons_succ,List.getElem?_nil,Option.getD_some,Option.getD_none]
  all_goals first | exact Nat.le_of_lt (t _).isLt | exact Nat.zero_le _

lemma source_resources_le (V : Verifier gatesG2) :
    V.proofQubits+V.ancillaQubits+V.output.val ≤ V.encode.length ∧ V.gates.length ≤ V.encode.length := by
  have he : V.encode.length = V.proofQubits+1+(V.ancillaQubits+1)+(V.output.val+1)+
      (V.gates.length+1)+(V.gates.flatMap Instr.encode).length := by
    simp only [Verifier.encode,encodeGates,List.length_append,Main.Encoding.encNat_length,Nat.add_assoc]
  constructor <;> omega

end QMAPerfectCompleteness.Main.Repetition.CompilerTM


