-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CyclicIndexMetadataIO
-- name    : QMAPerfectCompleteness_Proof_CyclicIndexMetadataIO
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:05:57.950087+00:00
-- url     : https://prove2.me/theorems/d1d95d0c-befd-4335-a878-75de9fe1367a
-- title:
--   Reading and writing cyclic metadata fields
-- statement:
--   Defines finite stack routines for reading the six unary metadata fields, emitting the enlarged header and moving the retained source body. The execution identities describe the exact order of fields and payload in the resulting stream.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CyclicIndexMetadataIO.lean, retained declaration span lines 10–95.

/- Generated from Solutions.CyclicIndexMetadataIO by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicClockMetadata
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicClockPrefixTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicIndexMetadataTM
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
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_StackTransfers
import Definitions.Def_QMAPerfectCompleteness_Proof_StructuredStackCode
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryFieldCode
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryMetadataArithmetic
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerPhases
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryStackOps
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
set_option maxRecDepth 10000
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.CyclicIndexMetadataTM
open QAlgorithms.Complexity (Str encNat)
open StructuredStack StructuredStack.Code

def fieldSum (v : Values) : ℕ := v 0+v 1+v 2+v 3+v 4+v 5
def sourceCode (v : Values) (body : Str) : Str :=
  encNat (v 0)++encNat (v 1)++encNat (v 2)++encNat (v 3)++encNat (v 4)++encNat (v 5)++body
abbrev readHeaders : Code Reg := seq (readField .input (.field 0)) (seq (readField .input (.field 1)) (seq (readField .input (.field 2)) (seq (readField .input (.field 3)) (seq (readField .input (.field 4)) (seq (readField .input (.field 5)) (Code.load none))))))

lemma readHeaders_exec (v : Values) (body : Str) :
    readHeaders.Exec (none,bank (fun _=>0) 0 0 0 (sourceCode v body) [])
      (none,bank v 0 0 0 body []) (2*fieldSum v+19) := by
  let w0 : Values := fun _=>0
  let w1 : Values := Function.update w0 0 (v 0)
  let w2 : Values := Function.update w1 1 (v 1)
  let w3 : Values := Function.update w2 2 (v 2)
  let w4 : Values := Function.update w3 3 (v 3)
  let w5 : Values := Function.update w4 4 (v 4)
  let w6 : Values := Function.update w5 5 (v 5)
  have h0 := readField_state w0 0 0 0 [] (encNat (v 1)++(encNat (v 2)++(encNat (v 3)++(encNat (v 4)++(encNat (v 5)++(body)))))) 0 (v 0) none (by simp [w0])
  have h1 := readField_state w1 0 0 0 [] (encNat (v 2)++(encNat (v 3)++(encNat (v 4)++(encNat (v 5)++(body))))) 1 (v 1) none (by simp [w1,w0])
  have h2 := readField_state w2 0 0 0 [] (encNat (v 3)++(encNat (v 4)++(encNat (v 5)++(body)))) 2 (v 2) none (by simp [w2,w1,w0])
  have h3 := readField_state w3 0 0 0 [] (encNat (v 4)++(encNat (v 5)++(body))) 3 (v 3) none (by simp [w3,w2,w1,w0])
  have h4 := readField_state w4 0 0 0 [] (encNat (v 5)++(body)) 4 (v 4) none (by simp [w4,w3,w2,w1,w0])
  have h5 := readField_state w5 0 0 0 [] (body) 5 (v 5) none (by simp [w5,w4,w3,w2,w1,w0])
  have hw : w6=v := by
    funext j
    fin_cases j <;> simp [w6,w5,w4,w3,w2,w1,w0]
  have h6 := load_exec none (none,bank w6 0 0 0 body [])
  have hh := (seq_exec _ _ h0 (seq_exec _ _ h1 (seq_exec _ _ h2 (seq_exec _ _ h3 (seq_exec _ _ h4 (seq_exec _ _ h5 h6))))))
  rw [hw] at hh
  simp only [Prod.snd] at hh
  simpa only [readHeaders,sourceCode,List.append_assoc,w0,fieldSum,show 2*(v 0+v 1+v 2+v 3+v 4+v 5)+19=2*v 0+3+(2*v 1+3+(2*v 2+3+(2*v 3+3+(2*v 4+3+(2*v 5+3+1))))) by ring] using hh

abbrev movePayload : Code Reg := seq (transfer .input .scratch) (transfer .scratch .output)
lemma movePayload_exec (v : Values) (k : ℕ) (body : Str) :
    movePayload.Exec (none,bank v k 0 0 body [])
      (none,bank v k 0 0 [] body) (4*body.length+2) := by
  let S := bank v k 0 0 body []
  let T := Function.update (Function.update S Reg.input []) Reg.scratch body.reverse
  have h1 : (transfer Reg.input Reg.scratch).Exec (none,S) (none,T) (2*body.length+1) := by
    simpa [S,T,bank,unary] using transfer_exec Reg.input Reg.scratch (by decide) body S none rfl
  have h2 := transfer_exec Reg.scratch Reg.output (by decide) body.reverse T none (by simp [T])
  have hh := seq_exec _ _ h1 h2
  have he : Function.update (Function.update T Reg.scratch []) Reg.output (body.reverse.reverse++T Reg.output) =
      bank v k 0 0 [] body := by
    funext r
    cases r <;> simp [T,S,bank,unary]
  rw [he] at hh
  simp only [List.length_reverse] at hh
  convert hh using 1 <;> ring

abbrev emitHeaders : Code Reg := seq (emitField (.field 5) .output) (seq (emitField (.field 4) .output) (seq (emitField (.field 3) .output) (seq (emitField (.field 2) .output) (seq (emitField (.field 1) .output) (seq (emitField (.field 0) .output) (emitField Reg.index Reg.output))))))

lemma emitHeaders_exec (v : Values) (k : ℕ) (body : Str) :
    emitHeaders.Exec (none,bank v k 0 0 [] body)
      (none,bank (fun _=>0) 0 0 0 [] (encNat k++sourceCode v body))
      (2*fieldSum v+2*k+14) := by
  let z0 : Values := v
  let z1 : Values := Function.update z0 5 0
  let z2 : Values := Function.update z1 4 0
  let z3 : Values := Function.update z2 3 0
  let z4 : Values := Function.update z3 2 0
  let z5 : Values := Function.update z4 1 0
  let z6 : Values := Function.update z5 0 0
  have h0 := emitField_state z0 k 0 0 [] (body) 5 none
  have h1 := emitField_state z1 k 0 0 [] (encNat (v 5)++(body)) 4 none
  have hv1 : z1 4=v 4 := by simp [z1,z0]
  rw [hv1] at h1
  have h2 := emitField_state z2 k 0 0 [] (encNat (v 4)++(encNat (v 5)++(body))) 3 none
  have hv2 : z2 3=v 3 := by simp [z2,z1,z0]
  rw [hv2] at h2
  have h3 := emitField_state z3 k 0 0 [] (encNat (v 3)++(encNat (v 4)++(encNat (v 5)++(body)))) 2 none
  have hv3 : z3 2=v 2 := by simp [z3,z2,z1,z0]
  rw [hv3] at h3
  have h4 := emitField_state z4 k 0 0 [] (encNat (v 2)++(encNat (v 3)++(encNat (v 4)++(encNat (v 5)++(body))))) 1 none
  have hv4 : z4 1=v 1 := by simp [z4,z3,z2,z1,z0]
  rw [hv4] at h4
  have h5 := emitField_state z5 k 0 0 [] (encNat (v 1)++(encNat (v 2)++(encNat (v 3)++(encNat (v 4)++(encNat (v 5)++(body)))))) 0 none
  have hv5 : z5 0=v 0 := by simp [z5,z4,z3,z2,z1,z0]
  rw [hv5] at h5
  have hz : z6=(fun _=>0) := by
    funext j
    fin_cases j <;> simp [z6,z5,z4,z3,z2,z1]
  have h6 := emitIndex_state z6 k 0 0 [] (sourceCode v body) none
  simp only [sourceCode,List.append_assoc] at h6
  have hh := (seq_exec _ _ h0 (seq_exec _ _ h1 (seq_exec _ _ h2 (seq_exec _ _ h3 (seq_exec _ _ h4 (seq_exec _ _ h5 h6))))))
  rw [hz] at hh
  simp only [sourceCode,List.append_assoc]
  convert hh using 1 <;> unfold fieldSum <;> ring

end QMAPerfectCompleteness.Uniformity.CyclicIndexMetadataTM


