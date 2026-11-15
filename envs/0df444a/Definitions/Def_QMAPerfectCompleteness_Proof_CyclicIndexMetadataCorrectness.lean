-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CyclicIndexMetadataCorrectness
-- name    : QMAPerfectCompleteness_Proof_CyclicIndexMetadataCorrectness
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:08:06.116876+00:00
-- url     : https://prove2.me/theorems/900e962d-94a4-4e27-b405-14dffb017590
-- title:
--   Execution bounds for cyclic index metadata
-- statement:
--   Packages the complete finite program for adding the even index-register width to the six-field clock metadata. The source and target encodings, full execution and polynomial bound are tied to the actual machine rather than inferred from output size.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CyclicIndexMetadataCorrectness.lean, retained declaration span lines 10–73.

/- Generated from Solutions.CyclicIndexMetadataCorrectness by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicIndexMetadataIO
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

abbrev program : Code Reg := seq readHeaders (seq arithmetic (seq movePayload emitHeaders))
abbrev machine := Code.toMachine program Reg.input Reg.output

def targetCode (v : Values) (body : Str) : Str := encNat (index v)++sourceCode v body
def time (v : Values) (body : Str) : ℕ :=
  arithmeticTime v+4*fieldSum v+2*index v+4*body.length+35

lemma full_exec (v : Values) (body : Str) :
    program.Exec (none,Function.update (fun _=>[]) Reg.input (sourceCode v body))
      (none,Function.update (fun _=>[]) Reg.output (targetCode v body)) (time v body) := by
  have h := seq_exec _ _ (readHeaders_exec v body)
    (seq_exec _ _ (arithmetic_exec v body [] none)
      (seq_exec _ _ (movePayload_exec v (index v) body) (emitHeaders_exec v (index v) body)))
  have hi : bank (fun _=>0) 0 0 0 (sourceCode v body) [] =
      Function.update (fun _=>[]) Reg.input (sourceCode v body) := by
    funext r; cases r <;> rfl
  have ho : bank (fun _=>0) 0 0 0 [] (encNat (index v)++sourceCode v body) =
      Function.update (fun _=>[]) Reg.output (targetCode v body) := by
    funext r; cases r <;> rfl
  rw [hi,ho] at h
  convert h using 1 <;> unfold time <;> ring

noncomputable def timePolynomial : Polynomial ℕ := 1000*(Polynomial.X+1)^2
lemma source_length (v : Values) (body : Str) :
    (sourceCode v body).length=fieldSum v+body.length+6 := by
  simp only [sourceCode,List.length_append,Main.Encoding.encNat_length,fieldSum]
  omega

lemma time_bound (v : Values) (body : Str) :
    time v body ≤ timePolynomial.eval (sourceCode v body).length := by
  have h1 : v 1 ≤ fieldSum v := by unfold fieldSum; omega
  have h5 : v 5 ≤ fieldSum v := by unfold fieldSum; omega
  have hm := Nat.mul_le_mul (show 2*v 5+1≤2*fieldSum v+1 by omega) h1
  have ht := Nat.mul_le_mul (show 2*v 5+1≤2*fieldSum v+1 by omega)
    (show 4*v 1+4≤4*fieldSum v+4 by omega)
  have hr : rawIndex v≤(2*fieldSum v+1)*fieldSum v+4 := by unfold rawIndex; omega
  have hmod := Nat.mod_lt (rawIndex v) (by decide : 0<2)
  simp only [timePolynomial,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,source_length]
  unfold time arithmeticTime index
  nlinarith [sq_nonneg (fieldSum v : ℤ)]

noncomputable def outputs (v : Values) (body : Str) :
    TM2OutputsInTime machine (sourceCode v body) (some (targetCode v body))
      (timePolynomial.eval (sourceCode v body).length) :=
  Code.outputs program Reg.input Reg.output _ _ _
    (exec_mono program (full_exec v body) (time_bound v body))

def values (c ell m a out hh : ℕ) : Values := ![c,ell,m,a,out,hh]

def compile (s : Str) : Str :=
  match Main.Encoding.parseNat s with
  | none=>[]
  | some (c,s)=>match Main.Encoding.parseNat s with
    | none=>[]
    | some (ell,s)=>match Main.Encoding.parseNat s with
      | none=>[]
      | some (m,s)=>match Main.Encoding.parseNat s with
        | none=>[]
        | some (a,s)=>match Main.Encoding.parseNat s with
          | none=>[]
          | some (out,s)=>match Main.Encoding.parseNat s with
            | none=>[]
            | some (hh,body)=>targetCode (values c ell m a out hh) body






end QMAPerfectCompleteness.Uniformity.CyclicIndexMetadataTM


