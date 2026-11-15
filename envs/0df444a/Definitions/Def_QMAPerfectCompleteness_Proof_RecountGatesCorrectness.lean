-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RecountGatesCorrectness
-- name    : QMAPerfectCompleteness_Proof_RecountGatesCorrectness
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:03:37.66628+00:00
-- url     : https://prove2.me/theorems/261fed2d-8b18-48fe-ade8-96684d087984
-- title:
--   Correct replacement of a gate-count placeholder
-- statement:
--   Defines a finite-plan recounting pass and relates its recipe representation to valid typed-verifier bodies. The resulting machine preserves the emitted instructions and replaces the provisional count by the actual number of gates, with a polynomial-time bound.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RecountGatesCorrectness.lean, retained declaration span lines 10–121.

/- Generated from Solutions.RecountGatesCorrectness by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicMetadataTM
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_FinitePlanCompilerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompilerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_HTEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_HTPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_RecountGatesTM
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerPhases
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion
namespace QMAPerfectCompleteness.Uniformity.UnaryNatArithmetic
end QMAPerfectCompleteness.Uniformity.UnaryNatArithmetic


set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Turing StateTransition
namespace QMAPerfectCompleteness.Main.RecountGates
open QAlgorithms.Complexity (Str encNat)
open QMAPerfectCompleteness.Uniformity
open FinitePlanCompiler

def plan (kind : Fin 4) : List Token :=
  [.count]++(encNat kind.val).map Token.bit++
    (List.range (arity kind)).map (fun j=>Token.addr (Fin.ofNat 4 j))
def config : Config where
  plan:=plan
  headerOffset:=fun _=>0
  plan_bound kind:=by fin_cases kind <;> decide
lemma plan_bits (kind : Fin 4) (a : Fin 4→ℕ) :
    bodyCode config kind a=(rawInstr kind a).encode := by
  fin_cases kind <;> simp [bodyCode,config,plan,arity,tokenBits,rawInstr,RawEncoding.Instruction.encode,encNat,List.append_assoc,List.range_succ]
lemma plan_count (kind : Fin 4) : gateCount config kind=1 := by fin_cases kind <;> rfl
lemma targetCount_eq (rs : List Recipe) : targetCount config rs=rs.length := by
  induction rs with
  | nil=>rfl
  | cons r rs ih=>simpa [targetCount,plan_count,Nat.add_comm] using congrArg (1+·) ih

noncomputable def recipes (V : Verifier gatesG2) : List Recipe :=
  V.gates.map (HTCompiler.TM.instrRecipe (V.proofQubits+V.ancillaQubits))
lemma recipes_valid (V : Verifier gatesG2) : ∀r∈recipes V,r.Valid ∧ r.2 3=V.proofQubits+V.ancillaQubits := by
  intro r hr
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hr
  exact HTCompiler.TM.instrRecipe_valid _ i
lemma sourceBody_recipes (V : Verifier gatesG2) : sourceBody (recipes V)=V.gates.flatMap Instr.encode := by
  simp [sourceBody,recipes,List.flatMap_map,Function.comp_def,HTCompiler.TM.rawInstr_instrRecipe]
lemma targetCode_recipes (V : Verifier gatesG2) :
    targetCode config V.proofQubits V.ancillaQubits V.output.val (recipes V)=V.encode := by
  have hbody : targetBody config (recipes V)=V.gates.flatMap Instr.encode := by
    simp [targetBody,recipes,List.flatMap_map,Function.comp_def,plan_bits,HTCompiler.TM.rawInstr_instrRecipe]
  rw [targetCode,hbody,targetCount_eq]
  simp [targetHeader,sourceHeader,config,recipes,Verifier.encode,encodeGates,List.append_assoc]


noncomputable def provisionalCode (V : Verifier gatesG2) : Str :=
  sourceHeader V.proofQubits V.ancillaQubits V.output.val++encNat 0++V.gates.flatMap Instr.encode
lemma sourceWithCount_recipes (V : Verifier gatesG2) :
    sourceWithCount V.proofQubits V.ancillaQubits V.output.val (recipes V) 0=provisionalCode V := by
  rw [sourceWithCount,sourceBody_recipes]
  rfl

/-- Parse the complete body, with a fuel bound supplied by its bit length. -/
def parseBody (n : ℕ) : ℕ→Str→Option (List RawEncoding.Instruction)
  | 0,s=>if s=[] then some [] else none
  | f+1,s=>if s=[] then some [] else do
      let (i,t)←RawEncoding.parseInstruction RawEncoding.g2Table n s
      let is←parseBody n f t
      pure (i::is)
lemma instruction_length_pos {n : ℕ} (i : Instr gatesG2 n) : 0 < i.encode.length := by
  simp only [Instr.encode,List.length_append,Encoding.encNat_length]
  omega
lemma gates_length_le {n : ℕ} (gs : List (Instr gatesG2 n)) : gs.length≤(gs.flatMap Instr.encode).length := by
  induction gs with
  | nil=>simp
  | cons i gs ih=>simpa only [List.length_cons,List.flatMap_cons,List.length_append,Nat.add_comm] using
      Nat.add_le_add (instruction_length_pos i) ih


def recount (s : Str) : Str :=
  (do
    let (m,s)←Encoding.parseNat s
    let (a,s)←Encoding.parseNat s
    let (o,s)←Encoding.parseNat s
    let (_,body)←Encoding.parseNat s
    let gs←parseBody (m+a) body.length body
    pure (RawEncoding.Circuit.encode ⟨m,a,o,gs⟩)).getD []


noncomputable def timePolynomial : Polynomial ℕ := 500000*(Polynomial.X+1)^2
noncomputable def outputs_verifier (V : Verifier gatesG2) :
    TM2OutputsInTime (machine config) (provisionalCode V) (some V.encode)
      (timePolynomial.eval (provisionalCode V).length) where
  steps:=fullTimeWithCount config V.proofQubits V.ancillaQubits V.output.val (recipes V) 0
  evals_in_steps:=by
    rw [←sourceWithCount_recipes,←targetCode_recipes]
    exact full_run_with_count config _ _ _ _ _ (recipes_valid V)
  steps_le_m:=by
    have hb:=fullTime_bound config V.proofQubits V.ancillaQubits V.output.val (recipes V) (recipes_valid V)
    have hs : sourceCode V.proofQubits V.ancillaQubits V.output.val (recipes V)=V.encode := HTCompiler.TM.sourceCode_verifier V
    rw [hs] at hb
    have hg:=gates_length_le V.gates
    have hl : V.encode.length=(provisionalCode V).length+V.gates.length := by
      simp only [Verifier.encode,encodeGates,provisionalCode,sourceHeader,List.length_append,Encoding.encNat_length]
      omega
    have hg' : V.gates.length≤(provisionalCode V).length := by
      simp only [provisionalCode,List.length_append] at ⊢
      omega
    have ht : fullTimeWithCount config V.proofQubits V.ancillaQubits V.output.val (recipes V) 0≤
        fullTime config V.proofQubits V.ancillaQubits V.output.val (recipes V) := by
      unfold fullTimeWithCount fullTime
      omega
    simp only [timePolynomial,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    have hd : headerDelta config=0 := rfl
    rw [hd] at hb
    nlinarith


end QMAPerfectCompleteness.Main.RecountGates


