-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RecipeSerializerSetup
-- name    : QMAPerfectCompleteness_Proof_RecipeSerializerSetup
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:37:08.560201+00:00
-- url     : https://prove2.me/theorems/8032d844-35b4-4c64-bd38-d08337ee88f1
-- title:
--   Serializer registers and source-buffer setup
-- statement:
--   Defines the finite register bank, unary metadata parser and preparation program for a recipe serializer. Setup retains the source body in forward and reverse instruction order, initializes parameter registers and preserves unrelated stacks.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RecipeSerializerSetup.lean, retained declaration span lines 13–137.

/- Generated from Solutions.RecipeSerializerSetup by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Mathlib.Tactic.DeriveFintype
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Proof_BinaryComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockClockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockImplements
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockProgramPlacement
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockStateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockTaggedActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
import Definitions.Def_QMAPerfectCompleteness_Proof_BoundedWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateBlockCompilerCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateBlockCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateClosingActions
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateClosingCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateEtaTransport
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHadamardCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateInitialization
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterHistory
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateOldPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificatePostCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificatePreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateQuantumTransports
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateRangeCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateStageActions
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateThresholdLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidity
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitExprTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClassTransport
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentAcceptance
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ConditionalWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CountedWriterLoops
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicClockMetadata
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicClockPrefixTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicFullMetadata
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicIndexMetadataCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicIndexMetadataIO
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicIndexMetadataTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicMetadataTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicVerifier
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_FinitePlanCompilerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompilerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_HTEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_HTPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_InstructionBuffersTM
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RawG2Gadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeNormalization
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeVerifierContext
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeWriterContext
import Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_SourceBuffersTM
import Definitions.Def_QMAPerfectCompleteness_Proof_StackEmbedding
import Definitions.Def_QMAPerfectCompleteness_Proof_StackTransfers
import Definitions.Def_QMAPerfectCompleteness_Proof_StreamWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_StructuredStackCode
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryEvaluator
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryFieldCode
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryMetadataArithmetic
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerPhases
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryStackOps
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition
namespace QMAPerfectCompleteness.Main.BlockTransport
end QMAPerfectCompleteness.Main.BlockTransport
namespace QMAPerfectCompleteness.Main.BlockHistoryCoordinates
end QMAPerfectCompleteness.Main.BlockHistoryCoordinates
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
end QMAPerfectCompleteness.Main.BlockHadamardCoordinates
namespace QMAPerfectCompleteness.Main.CoordinateFibers
end QMAPerfectCompleteness.Main.CoordinateFibers
namespace QMAPerfectCompleteness.Main.CertificateClaimBits
end QMAPerfectCompleteness.Main.CertificateClaimBits
namespace QMAPerfectCompleteness.Main.CertificateReadoutEffect
end QMAPerfectCompleteness.Main.CertificateReadoutEffect
namespace QMAPerfectCompleteness.Main.CertificateVerifierEffect
end QMAPerfectCompleteness.Main.CertificateVerifierEffect
namespace QMAPerfectCompleteness.Uniformity.UnaryNatArithmetic
end QMAPerfectCompleteness.Uniformity.UnaryNatArithmetic


set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 2048
open Turing StateTransition
namespace QMAPerfectCompleteness.Main.CircuitRecipe.Serializer
open QAlgorithms.Complexity (Str encNat)
open QMAPerfectCompleteness.Uniformity.StructuredStack
open Code

abbrev Registers (n : ℕ) := WriterStacks (ReadOnly 0) n ⊕ Fin 2
instance (n : ℕ) : DecidableEq (Registers n) := by
  unfold Registers WriterStacks ReadOnly Inputs
  infer_instance
instance (n : ℕ) : Fintype (Registers n) := by
  unfold Registers WriterStacks ReadOnly Inputs
  infer_instance
abbrev source (n : ℕ) (j : Fin 2) : Registers n := .inl (.inl (.inr j))
abbrev param (n : ℕ) (p : Param) : Registers n := .inl (.inl (.inl (.inl p)))
abbrev extra (n : ℕ) (j : Fin 2) : Registers n := .inr j
abbrev output (n : ℕ) : Registers n := .inl writerOutput

def store (n : ℕ) (v : Environment) (body reverse out : Str) : Registers n → Str
  | .inl (.inl (.inl (.inl p))) => unary (v p)
  | .inl (.inl (.inl (.inr (.inl j)))) => j.elim0
  | .inl (.inl (.inl (.inr (.inr ())))) => []
  | .inl (.inl (.inr j)) => if j=0 then body else reverse
  | .inl (.inr (.inl ())) => out
  | .inl (.inr (.inr _)) => []
  | .inr _ => []

lemma update_source (n : ℕ) (v : Environment) (body reverse out s : Str) :
    Function.update (store n v body reverse out) (source n 0) s=store n v s reverse out := by
  funext r
  rcases r with ((((p|j|u)|a)|u|w)|t)
  · rfl
  · exact j.elim0
  · cases u; rfl
  · fin_cases a <;> rfl
  · cases u; rfl
  · rfl
  · rfl
lemma update_reverse (n : ℕ) (v : Environment) (body reverse out s : Str) :
    Function.update (store n v body reverse out) (source n 1) s=store n v body s out := by
  funext r
  rcases r with ((((p|j|u)|a)|u|w)|t)
  · rfl
  · exact j.elim0
  · cases u; rfl
  · fin_cases a <;> rfl
  · cases u; rfl
  · rfl
  · rfl
lemma update_param (n : ℕ) (v : Environment) (body reverse out : Str) (p : Param) (a : ℕ) :
    Function.update (store n v body reverse out) (param n p) (unary a)=
      store n (Function.update v p a) body reverse out := by
  funext r
  rcases r with ((((q|j|u)|a)|u|w)|t)
  · by_cases h : q=p <;> simp_all [store,param]
  · exact j.elim0
  · cases u; rfl
  · rfl
  · cases u; rfl
  · rfl
  · rfl

lemma read_param (n : ℕ) (v : Environment) (tail reverse out : Str) (p : Param) (a : ℕ)
    (q : Option Bool) (hp : v p=0) :
    (readField (source n 0) (param n p)).Exec (q,store n v (encNat a++tail) reverse out)
      (none,store n (Function.update v p a) tail reverse out) (2*a+3) := by
  have h := readField_exec (source n 0) (param n p) (by simp) a tail
    (store n v (encNat a++tail) reverse out) q rfl
  change (readField (source n 0) (param n p)).Exec _
    (none,Function.update (Function.update (store n v (encNat a++tail) reverse out) (source n 0) tail)
      (param n p) (unary a++unary (v p))) _ at h
  rw [hp,show unary 0=[] from rfl,List.append_nil,update_source,update_param] at h
  exact h

def metadata (P : CyclicRaw.Meta) (body : Str) : Str :=
  encNat P.k++encNat P.c++encNat P.ell++encNat P.m++encNat P.a++encNat P.out++encNat P.hh++body
def sum (P : CyclicRaw.Meta) : ℕ := P.k+P.c+P.ell+P.m+P.a+P.out+P.hh
abbrev parse (n : ℕ) : Code (Registers n) := seq (readField (source n 0) (param n .index)) (seq (readField (source n 0) (param n .clock)) (seq (readField (source n 0) (param n .ell)) (seq (readField (source n 0) (param n .proof)) (seq (readField (source n 0) (param n .ancilla)) (seq (readField (source n 0) (param n .output)) (seq (readField (source n 0) (param n .hadamards)) (load none)))))))

lemma parse_exec (n : ℕ) (P : CyclicRaw.Meta) (body : Str) :
    (parse n).Exec (none,store n (fun _=>0) (metadata P body) [] [])
      (none,store n P.env body [] []) (2*sum P+22) := by
  let v0 : Environment := fun _=>0
  let v1 : Environment := Function.update v0 .index P.k
  let v2 : Environment := Function.update v1 .clock P.c
  let v3 : Environment := Function.update v2 .ell P.ell
  let v4 : Environment := Function.update v3 .proof P.m
  let v5 : Environment := Function.update v4 .ancilla P.a
  let v6 : Environment := Function.update v5 .output P.out
  let v7 : Environment := Function.update v6 .hadamards P.hh
  have h0 := read_param n v0 (encNat P.c++(encNat P.ell++(encNat P.m++(encNat P.a++(encNat P.out++(encNat P.hh++(body))))))) [] [] .index P.k none (by simp [v0])
  have h1 := read_param n v1 (encNat P.ell++(encNat P.m++(encNat P.a++(encNat P.out++(encNat P.hh++(body)))))) [] [] .clock P.c none (by simp [v1,v0])
  have h2 := read_param n v2 (encNat P.m++(encNat P.a++(encNat P.out++(encNat P.hh++(body))))) [] [] .ell P.ell none (by simp [v2,v1,v0])
  have h3 := read_param n v3 (encNat P.a++(encNat P.out++(encNat P.hh++(body)))) [] [] .proof P.m none (by simp [v3,v2,v1,v0])
  have h4 := read_param n v4 (encNat P.out++(encNat P.hh++(body))) [] [] .ancilla P.a none (by simp [v4,v3,v2,v1,v0])
  have h5 := read_param n v5 (encNat P.hh++(body)) [] [] .output P.out none (by simp [v5,v4,v3,v2,v1,v0])
  have h6 := read_param n v6 (body) [] [] .hadamards P.hh none (by simp [v6,v5,v4,v3,v2,v1,v0])
  have hv : v7=P.env := by
    funext p
    cases p <;> simp [v7,v6,v5,v4,v3,v2,v1,v0,CyclicRaw.Meta.env]
  have h7 := load_exec none (none,store n v7 body [] [])
  have hh := (seq_exec _ _ h0 (seq_exec _ _ h1 (seq_exec _ _ h2 (seq_exec _ _ h3 (seq_exec _ _ h4 (seq_exec _ _ h5 (seq_exec _ _ h6 h7)))))))
  rw [hv] at hh
  simp only [Prod.snd] at hh
  simp only [metadata,List.append_assoc]
  convert hh using 1 <;> unfold sum <;> ring

abbrev bufferLayout (n : ℕ) : Fin 4 ↪ Registers n where
  toFun j := if j=0 then source n 0 else if j=1 then extra n 0 else if j=2 then extra n 1 else source n 1
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all [source,extra]
abbrev prepare (n : ℕ) : Code (Registers n) := prepareBuffers (bufferLayout n)
lemma prepare_exec (n : ℕ) (P : CyclicRaw.Meta) (src : List RawEncoding.Instruction)
    (hv : Context.SourceValid src) :
    (prepare n).Exec (none,store n P.env (src.flatMap RawEncoding.Instruction.encode) [] [])
      (none,store n P.env (src.flatMap RawEncoding.Instruction.encode)
        (src.reverse.flatMap RawEncoding.Instruction.encode) [])
      (6*(src.flatMap RawEncoding.Instruction.encode).length+3*src.length+2) := by
  have h := prepareBuffers_exec (bufferLayout n) src hv
    (store n P.env (src.flatMap RawEncoding.Instruction.encode) [] []) none rfl rfl rfl rfl
  rw [show bufferLayout n 3=source n 1 from rfl,update_reverse] at h
  exact h

abbrev setup (n : ℕ) : Code (Registers n) := seq (parse n) (prepare n)
lemma setup_exec (n : ℕ) (P : CyclicRaw.Meta) (src : List RawEncoding.Instruction)
    (hv : Context.SourceValid src) :
    (setup n).Exec (none,store n (fun _=>0) (metadata P (src.flatMap RawEncoding.Instruction.encode)) [] [])
      (none,store n P.env (src.flatMap RawEncoding.Instruction.encode)
        (src.reverse.flatMap RawEncoding.Instruction.encode) [])
      (2*sum P+6*(src.flatMap RawEncoding.Instruction.encode).length+3*src.length+24) := by
  have h := seq_exec _ _ (parse_exec n P _) (prepare_exec n P src hv)
  convert h using 1 <;> ring

end QMAPerfectCompleteness.Main.CircuitRecipe.Serializer


