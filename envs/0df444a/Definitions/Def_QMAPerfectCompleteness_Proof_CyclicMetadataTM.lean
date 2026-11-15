-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CyclicMetadataTM
-- name    : QMAPerfectCompleteness_Proof_CyclicMetadataTM
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:01:13.623088+00:00
-- url     : https://prove2.me/theorems/8da542c1-e0c8-4c1e-8e96-1ebbec801617
-- title:
--   Verifier headers and Hadamard-count extraction
-- statement:
--   Defines a finite-plan parser that extracts the verifier register headers and counts paired-Hadamard gates while preserving its encoded body. The recipe correspondence and runtime bound provide the first stage of cyclic metadata generation.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CyclicMetadataTM.lean, retained declaration span lines 11–96.

/- Generated from Solutions.CyclicMetadataTM by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompilerTM
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



/-! Actual finite-plan extraction of unary verifier headers and HH count, retaining its body. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Turing StateTransition
namespace QMAPerfectCompleteness.Main.CyclicMetadataTM
open QAlgorithms.Complexity (Str encNat)
open Uniformity
abbrev Token := FinitePlanCompiler.Token

def plan (kind : Fin 4) : List Token :=
  if kind=0 then [.bit false,.addr 0] else
    if kind=1 then [.bit true,.bit false,.addr 0,.addr 1] else
    if kind=2 then [.bit true,.bit true,.bit false,.addr 0,.addr 1,.addr 2] else
      [.count,.bit true,.bit true,.bit true,.bit false,.addr 0,.addr 1]

def config : FinitePlanCompiler.Config where
  plan := plan
  headerOffset := fun _ => 0
  plan_bound kind := by fin_cases kind <;> decide

lemma config_offsets (j : Fin 3) : config.headerOffset j = 0 := rfl
lemma config_delta : FinitePlanCompiler.headerDelta config = 0 := rfl

lemma plan_bits (kind : Fin 4) (a : Fin 4 → ℕ) :
    FinitePlanCompiler.bodyCode config kind a = (FinitePlanCompiler.rawInstr kind a).encode := by
  fin_cases kind <;>
    simp [FinitePlanCompiler.bodyCode,config,plan,FinitePlanCompiler.tokenBits,
      FinitePlanCompiler.rawInstr,RawEncoding.Instruction.encode,encNat,List.append_assoc]

lemma plan_count (kind : Fin 4) :
    FinitePlanCompiler.gateCount config kind = if kind.val==3 then 1 else 0 := by
  fin_cases kind <;> rfl

noncomputable abbrev instrRecipe {n : ℕ} (N : ℕ) (i : Instr gatesG2 n) : FinitePlanCompiler.Recipe :=
  HTCompiler.TM.instrRecipe N i

lemma recipe_body {n : ℕ} (N : ℕ) (i : Instr gatesG2 n) :
    FinitePlanCompiler.bodyCode config (instrRecipe N i).1 (instrRecipe N i).2 = i.encode := by
  rw [plan_bits,HTCompiler.TM.rawInstr_instrRecipe,RawEncoding.eraseInstr_encode]

lemma recipe_count {n : ℕ} (N : ℕ) (i : Instr gatesG2 n) :
    FinitePlanCompiler.gateCount config (instrRecipe N i).1 = if i.gate.val==3 then 1 else 0 :=
  plan_count _

lemma recipe_count_sum {n : ℕ} (N : ℕ) (gs : List (Instr gatesG2 n)) :
    FinitePlanCompiler.targetCount config (gs.map (instrRecipe N)) = gs.countP (fun i => i.gate.val==3) := by
  induction gs with
  | nil => rfl
  | cons i gs ih =>
    simp only [List.map_cons,FinitePlanCompiler.targetCount,List.map_cons,List.sum_cons,List.countP_cons] at *
    rw [recipe_count,ih]
    split_ifs <;> omega

noncomputable def code (V : Verifier gatesG2) : Str :=
  encNat V.proofQubits++encNat V.ancillaQubits++encNat V.output.val++encNat (hhCount V)++V.gates.flatMap Instr.encode

noncomputable def extract (s : Str) : Str :=
  match Encoding.decodeVerifier gatesG2 s with
  | none => []
  | some V => code V

@[simp] theorem extract_encode (V : Verifier gatesG2) : extract V.encode = code V := by simp [extract]

lemma targetCode_verifier (V : Verifier gatesG2) :
    FinitePlanCompiler.targetCode config V.proofQubits V.ancillaQubits V.output.val
      (V.gates.map (instrRecipe (V.proofQubits+V.ancillaQubits))) = code V := by
  simp only [FinitePlanCompiler.targetCode,FinitePlanCompiler.targetHeader,config_offsets,
    FinitePlanCompiler.sourceHeader,Nat.add_zero,FinitePlanCompiler.targetBody,List.flatMap_map,
    Function.comp_def,recipe_body,recipe_count_sum,hhCount,code,List.append_assoc]

noncomputable def timePolynomial : Polynomial ℕ := 100000*(Polynomial.X+1)^2

/-- The actual finite machine emits m,a,out,HH and the unchanged source gate body. -/
noncomputable def outputs_verifier (V : Verifier gatesG2) :
    TM2OutputsInTime (FinitePlanCompiler.machine config) V.encode (some (extract V.encode))
      (timePolynomial.eval V.encode.length) where
  steps := FinitePlanCompiler.fullTime config V.proofQubits V.ancillaQubits V.output.val
    (V.gates.map (instrRecipe (V.proofQubits+V.ancillaQubits)))
  evals_in_steps := by
    rw [extract_encode,← targetCode_verifier V,← HTCompiler.TM.sourceCode_verifier V]
    exact FinitePlanCompiler.full_run config _ _ _ _ (by
      intro r hr
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
      exact HTCompiler.TM.instrRecipe_valid _ i)
  steps_le_m := by
    have h := FinitePlanCompiler.fullTime_bound config V.proofQubits V.ancillaQubits V.output.val
      (V.gates.map (instrRecipe (V.proofQubits+V.ancillaQubits))) (by
        intro r hr
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
        exact HTCompiler.TM.instrRecipe_valid _ i)
    simpa only [HTCompiler.TM.sourceCode_verifier,config_delta,
      Nat.add_zero,timePolynomial,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using h



end QMAPerfectCompleteness.Main.CyclicMetadataTM


