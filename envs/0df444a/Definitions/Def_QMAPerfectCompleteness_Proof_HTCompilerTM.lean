-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_HTCompilerTM
-- name    : QMAPerfectCompleteness_Proof_HTCompilerTM
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:57:34.923243+00:00
-- url     : https://prove2.me/theorems/eceb07b9-e53b-41a6-915d-3bde66b13f14
-- title:
--   Finite-plan machine for the Hadamard–Toffoli compiler
-- statement:
--   Instantiates the finite-plan transducer with the exact numerical gate expansions of the G₂-to-HT compiler and the header offset adding three ancilla bits. The recipe-to-encoding identities and an explicit quadratic timed-execution witness connect this finite machine to the semantic compiled verifier. This supplies concrete uniformity infrastructure.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/HTCompilerTM.lean, lines 14–112.

/- Generated from Solutions.HTCompilerTM by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_FinitePlanCompilerTM
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
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Instantiation of the generic finite-plan machine for the exact G₂-to-HT compiler. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
open Turing StateTransition
namespace QMAPerfectCompleteness.Main.HTCompiler.TM
open QAlgorithms.Complexity (Str encNat)
open Uniformity

abbrev Token := Uniformity.FinitePlanCompiler.Token

def emitRef (j : Fin 4) (offset : ℕ) : List Token :=
  List.replicate offset (.bit true)++[.addr j]

def tagsPlan (address : ℕ → List Token) (gs : List RawEncoding.Instruction) : List Token :=
  gs.flatMap (fun i => [.count]++(encNat i.gate).map Uniformity.FinitePlanCompiler.Token.bit++i.wires.flatMap address)

def xAddress (j : ℕ) : List Token :=
  if j=0 then emitRef 3 1 else if j=1 then emitRef 0 0 else if j=2 then emitRef 3 0 else emitRef 3 2

def cnotAddress (j : ℕ) : List Token :=
  if j=0 then emitRef 3 0 else if j=1 then emitRef 0 0 else if j=2 then emitRef 1 0 else emitRef 3 1

def plan (kind : Fin 4) : List Token :=
  if kind=0 then tagsPlan xAddress xTags else if kind=1 then tagsPlan cnotAddress cnotTags else
    if kind=2 then [.count,.bit true,.bit false,.addr 0,.addr 1,.addr 2] else
      [.count,.bit false,.addr 0,.count,.bit false,.addr 1]

def config : Uniformity.FinitePlanCompiler.Config where
  plan := plan
  headerOffset := ![0,3,0]
  plan_bound kind := by fin_cases kind <;> decide

lemma config_delta : Uniformity.FinitePlanCompiler.headerDelta config = 3 := rfl

lemma plan_bits (kind : Fin 4) (a : Fin 4 → ℕ) :
    Uniformity.FinitePlanCompiler.bodyCode config kind a =
      (compileRawInstr (a 3) (Uniformity.FinitePlanCompiler.rawInstr kind a)).flatMap RawEncoding.Instruction.encode := by
  fin_cases kind <;> simp [Uniformity.FinitePlanCompiler.bodyCode,config,plan,tagsPlan,xAddress,cnotAddress,emitRef,Uniformity.FinitePlanCompiler.tokenBits,
    compileRawInstr,Uniformity.FinitePlanCompiler.rawInstr,placeTags,xTags,cnotTags,czTags,quarterTags,
    RawEncoding.Instruction.encode,encNat,List.append_assoc,List.replicate_succ]

lemma plan_count (kind : Fin 4) (a : Fin 4 → ℕ) :
    Uniformity.FinitePlanCompiler.gateCount config kind = (compileRawInstr (a 3) (Uniformity.FinitePlanCompiler.rawInstr kind a)).length := by
  fin_cases kind <;> simp [Uniformity.FinitePlanCompiler.gateCount,config,plan,tagsPlan,xAddress,cnotAddress,emitRef,Uniformity.FinitePlanCompiler.tokenCount,
    compileRawInstr,Uniformity.FinitePlanCompiler.rawInstr,placeTags,xTags,cnotTags,czTags,quarterTags,encNat]

noncomputable def instrRecipe {n : ℕ} (N : ℕ) (i : Instr gatesG2 n) : Uniformity.FinitePlanCompiler.Recipe :=
  (⟨i.gate.val,by have h := i.gate.isLt; change i.gate.val < 4 at h; exact h⟩,
    fun j => if j=3 then N else ((RawEncoding.eraseInstr i).wires[j.val]?).getD 0)

lemma instrRecipe_valid {n : ℕ} (N : ℕ) (i : Instr gatesG2 n) :
    (instrRecipe N i).Valid ∧ (instrRecipe N i).2 3 = N := by
  rcases i with ⟨g,t⟩
  fin_cases g <;> simp [instrRecipe,Uniformity.FinitePlanCompiler.Recipe.Valid,Uniformity.FinitePlanCompiler.Valid,RawEncoding.eraseInstr,List.ofFn_succ]

lemma rawInstr_instrRecipe {n : ℕ} (N : ℕ) (i : Instr gatesG2 n) :
    Uniformity.FinitePlanCompiler.rawInstr (instrRecipe N i).1 (instrRecipe N i).2 = RawEncoding.eraseInstr i := by
  rcases i with ⟨g,t⟩
  fin_cases g <;> rfl

lemma instrRecipe_count {n : ℕ} (N : ℕ) (i : Instr gatesG2 n) :
    Uniformity.FinitePlanCompiler.gateCount config (instrRecipe N i).1 = (compileRawInstr N (RawEncoding.eraseInstr i)).length := by
  rw [plan_count (instrRecipe N i).1 (instrRecipe N i).2,(instrRecipe_valid N i).2,rawInstr_instrRecipe]

lemma instrRecipe_bodyCode {n : ℕ} (N : ℕ) (i : Instr gatesG2 n) :
    Uniformity.FinitePlanCompiler.bodyCode config (instrRecipe N i).1 (instrRecipe N i).2 =
      (compileRawInstr N (RawEncoding.eraseInstr i)).flatMap RawEncoding.Instruction.encode := by
  rw [plan_bits,(instrRecipe_valid N i).2,rawInstr_instrRecipe]

lemma sourceCode_verifier (V : Verifier gatesG2) :
    Uniformity.FinitePlanCompiler.sourceCode V.proofQubits V.ancillaQubits V.output.val
      (V.gates.map (instrRecipe (V.proofQubits+V.ancillaQubits))) = V.encode := by
  simp only [Uniformity.FinitePlanCompiler.sourceCode,Uniformity.FinitePlanCompiler.sourceHeader,Uniformity.FinitePlanCompiler.sourceBody,List.flatMap_map,Function.comp_def,
    rawInstr_instrRecipe,RawEncoding.eraseInstr_encode,List.length_map]
  simp only [Verifier.encode,encodeGates,List.append_assoc]

lemma targetCode_verifier (V : Verifier gatesG2) :
    Uniformity.FinitePlanCompiler.targetCode config V.proofQubits V.ancillaQubits V.output.val
      (V.gates.map (instrRecipe (V.proofQubits+V.ancillaQubits))) = (compileVerifier V).encode := by
  calc
    _ = (compileRaw (RawEncoding.eraseVerifier V)).encode := by
      simp only [Uniformity.FinitePlanCompiler.targetCode,Uniformity.FinitePlanCompiler.targetHeader,Uniformity.FinitePlanCompiler.sourceHeader,Uniformity.FinitePlanCompiler.targetCount,Uniformity.FinitePlanCompiler.targetBody,
        List.map_map,List.flatMap_map,Function.comp_def,instrRecipe_count,instrRecipe_bodyCode,
        compileRaw,RawEncoding.eraseVerifier,RawEncoding.Circuit.encode,List.length_flatMap,
        List.flatMap_assoc,List.append_assoc]
      rfl
    _ = _ := by rw [compileRaw_erase,RawEncoding.eraseVerifier_encode]

noncomputable def timePolynomial : Polynomial ℕ := 100000*(Polynomial.X+4)^2

noncomputable def outputs_verifier (V : Verifier gatesG2) :
    TM2OutputsInTime (Uniformity.FinitePlanCompiler.machine config) V.encode (some (executableCompile V.encode))
      (timePolynomial.eval V.encode.length) where
  steps := Uniformity.FinitePlanCompiler.fullTime config V.proofQubits V.ancillaQubits V.output.val
    (V.gates.map (instrRecipe (V.proofQubits+V.ancillaQubits)))
  evals_in_steps := by
    rw [executableCompile_encode,← targetCode_verifier V,← sourceCode_verifier V]
    exact Uniformity.FinitePlanCompiler.full_run config _ _ _ _ (by
      intro r hr
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
      exact instrRecipe_valid _ i)
  steps_le_m := by
    have h := Uniformity.FinitePlanCompiler.fullTime_bound config V.proofQubits V.ancillaQubits V.output.val
      (V.gates.map (instrRecipe (V.proofQubits+V.ancillaQubits)))
      (by intro r hr; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr; exact instrRecipe_valid _ i)
    simpa only [sourceCode_verifier,config_delta,timePolynomial,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Nat.add_assoc,show (3+1 : ℕ) = 4 from rfl] using h



end QMAPerfectCompleteness.Main.HTCompiler.TM


