-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RecipeSerializerTM
-- name    : QMAPerfectCompleteness_Proof_RecipeSerializerTM
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:41:48.823121+00:00
-- url     : https://prove2.me/theorems/9c4e38f6-d7be-42c1-8379-fe4d48f7c4af
-- title:
--   Finite serialization of the cyclic verifier
-- statement:
--   Defines the finite machine that prepares metadata, runs a recipe writer, clears its input registers and transfers the reversed accumulated output into ordinary byte order. It produces the writer’s literal or provisional verifier bytes with clean workspace; a separate recount pass repairs the gate-count header.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RecipeSerializerTM.lean, retained declaration span lines 14–180.

/- Generated from Solutions.RecipeSerializerTM by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_ClearStacksTM
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
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeSerializerSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeVerifierContext
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeWriterContext
import Definitions.Def_QMAPerfectCompleteness_Proof_RecountGatesCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_RecountGatesTM
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
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 2048
open Turing StateTransition
namespace QMAPerfectCompleteness.Main.CircuitRecipe.Serializer
open QAlgorithms.Complexity (Str encNat)
open QMAPerfectCompleteness.Uniformity
open StructuredStack StructuredStack.Code

abbrev writerEmbedding (n : ℕ) : WriterStacks (ReadOnly 0) n ↪ Registers n :=
  ⟨Sum.inl,Sum.inl_injective⟩
abbrev address (n : ℕ) : Registers n := .inl (.inl (.inl (.inr (.inr ()))))
def inputKeys (n : ℕ) : List (Registers n) :=
  [param n .index,param n .clock,param n .ell,param n .proof,param n .ancilla,param n .output,
    param n .hadamards,address n,source n 0,source n 1]
lemma inputKeys_length (n : ℕ) : (inputKeys n).length=10 := rfl

def ready (n : ℕ) (P : CyclicRaw.Meta) (src : List RawEncoding.Instruction) : Registers n→Str :=
  store n P.env (src.flatMap RawEncoding.Instruction.encode) (src.reverse.flatMap RawEncoding.Instruction.encode) []

def written (n : ℕ) (P : CyclicRaw.Meta) (src : List RawEncoding.Instruction) (bits : Str) : Registers n→Str :=
  Function.update (ready n P src) (output n) bits.reverse

lemma ready_input (n : ℕ) (P : CyclicRaw.Meta) (src : List RawEncoding.Instruction) (ro : ReadOnly 0) :
    ready n P src (.inl (.inl ro))=(Context.ofMeta P src).encode ro := by
  rcases ro with ((p|j|u)|r)
  · rfl
  · exact j.elim0
  · cases u; rfl
  · fin_cases r <;> rfl

lemma writer_exec {g : Context 0→Str} (W : RecipeWriter 0 g) (P : CyclicRaw.Meta)
    (src : List RawEncoding.Instruction) (B : ℕ) (hv : (Context.ofMeta P src).Valid B) :
    (W.code.embed (writerEmbedding W.slots)).Exec (none,ready W.slots P src)
      (none,written W.slots P src (g (Context.ofMeta P src))) (W.time.eval B) := by
  have h := W.run (Context.ofMeta P src) B hv ((ready W.slots P src) ∘ writerEmbedding W.slots) none
    (fun ro=>ready_input _ _ _ ro) (fun _=>rfl)
  have hout : ((ready W.slots P src) ∘ writerEmbedding W.slots) writerOutput=[] := rfl
  rw [hout,List.append_nil] at h
  have hh := embed_exec_update (writerEmbedding W.slots) W.code (ready W.slots P src) none none
    writerOutput ((g (Context.ofMeta P src)).reverse) (W.time.eval B) h
  exact hh

lemma erased_written (n : ℕ) (P : CyclicRaw.Meta) (src : List RawEncoding.Instruction) (bits : Str) :
    erased (written n P src bits) (inputKeys n)=Function.update (fun _=>[]) (output n) bits.reverse := by
  funext r
  rcases r with ((((p|j|u)|a)|u|w)|t)
  · cases p <;> simp [erased,written,ready,store,inputKeys,param,output,source,address]
  · exact j.elim0
  · cases u; simp [erased,written,ready,store,inputKeys,param,output,source,address]
  · fin_cases a <;> simp [erased,written,ready,store,inputKeys,param,output,source,address]
  · cases u; simp [erased,written,ready,store,inputKeys,param,output,source,address]
  · simp [erased,written,ready,store,inputKeys,param,output,source,address]
  · simp [erased,written,ready,store,inputKeys,param,output,source,address]

lemma reversed_source_length (src : List RawEncoding.Instruction) :
    (src.reverse.flatMap RawEncoding.Instruction.encode).length=(src.flatMap RawEncoding.Instruction.encode).length := by
  simp [List.length_flatMap,List.map_reverse]

lemma clear_time_bound (n : ℕ) (P : CyclicRaw.Meta) (src : List RawEncoding.Instruction)
    (bits : Str) (B : ℕ) (hv : (Context.ofMeta P src).Valid B) :
    clearListTime (written n P src bits) (inputKeys n)≤20*B+11 := by
  have hf : ∀k∈inputKeys n,(written n P src bits k).length≤B := by
    intro k hk
    simp only [inputKeys,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [written,ready,store,output,param,source,address,unary,reversed_source_length,-List.length_flatMap]
    · exact hv.1 (.inl .index)
    · exact hv.1 (.inl .clock)
    · exact hv.1 (.inl .ell)
    · exact hv.1 (.inl .proof)
    · exact hv.1 (.inl .ancilla)
    · exact hv.1 (.inl .output)
    · exact hv.1 (.inl .hadamards)
    · exact hv.2.2.1
    · exact hv.2.2.1
  have hb : ((inputKeys n).map (fun k=>(written n P src bits k).length)).sum≤
      ((inputKeys n).map (fun _=>B)).sum := by
    apply List.sum_le_sum
    exact hf
  have hconst : ((inputKeys n).map (fun _=>B)).sum=(inputKeys n).length*B := by simp
  rw [hconst] at hb
  unfold clearListTime
  rw [inputKeys_length] at hb ⊢
  omega

lemma sum_bound (P : CyclicRaw.Meta) (src : List RawEncoding.Instruction) (B : ℕ)
    (hv : (Context.ofMeta P src).Valid B) : sum P≤7*B := by
  have h0:=hv.1 (.inl .index); have h1:=hv.1 (.inl .clock)
  have h2:=hv.1 (.inl .ell); have h3:=hv.1 (.inl .proof)
  have h4:=hv.1 (.inl .ancilla); have h5:=hv.1 (.inl .output)
  have h6:=hv.1 (.inl .hadamards)
  change P.k≤B at h0; change P.c≤B at h1; change P.ell≤B at h2
  change P.m≤B at h3; change P.a≤B at h4; change P.out≤B at h5; change P.hh≤B at h6
  unfold sum
  omega

lemma raw_gates_length_le (src : List RawEncoding.Instruction) :
    src.length≤(src.flatMap RawEncoding.Instruction.encode).length := by
  induction src with
  | nil=>simp
  | cons i src ih=>
    have hi : 1 ≤ i.encode.length := by
      simp only [RawEncoding.Instruction.encode,List.length_append,Encoding.encNat_length]
      omega
    simpa only [List.length_cons,List.flatMap_cons,List.length_append,Nat.add_comm] using Nat.add_le_add hi ih

noncomputable def program {g : Context 0→Str} (W : RecipeWriter 0 g) : Code (Registers W.slots) :=
  seq (setup W.slots) (seq (W.code.embed (writerEmbedding W.slots))
    (seq (clearList (inputKeys W.slots)) (transfer (output W.slots) (extra W.slots 0))))
noncomputable def machine {g : Context 0→Str} (W : RecipeWriter 0 g) :=
  Code.toMachine (program W) (source W.slots 0) (extra W.slots 0)
noncomputable def timePolynomial {g : Context 0→Str} (W : RecipeWriter 0 g) : Polynomial ℕ :=
  W.time+2*W.size+50*(Polynomial.X+1)

lemma full_exec {g : Context 0→Str} (W : RecipeWriter 0 g) (P : CyclicRaw.Meta)
    (src : List RawEncoding.Instruction) (B : ℕ) (hv : (Context.ofMeta P src).Valid B) :
    (program W).Exec
      (none,Function.update (fun _=>[]) (source W.slots 0) (metadata P (src.flatMap RawEncoding.Instruction.encode)))
      (none,Function.update (fun _=>[]) (extra W.slots 0) (g (Context.ofMeta P src)))
      ((timePolynomial W).eval B) := by
  have h0:=setup_exec W.slots P src hv.2.2.2
  have h1:=writer_exec W P src B hv
  have h2:=clearList_exec (inputKeys W.slots) (written W.slots P src (g (Context.ofMeta P src))) none
  rw [erased_written] at h2
  have h3:=transfer_exec (output W.slots) (extra W.slots 0) (by simp [output,extra])
    (g (Context.ofMeta P src)).reverse
    (Function.update (fun _=>[]) (output W.slots) (g (Context.ofMeta P src)).reverse) none (by simp)
  have he : Function.update
      (Function.update (Function.update (fun _ : Registers W.slots=>[]) (output W.slots) (g (Context.ofMeta P src)).reverse)
        (output W.slots) []) (extra W.slots 0)
        (((g (Context.ofMeta P src)).reverse).reverse++
          Function.update (fun _ : Registers W.slots=>[]) (output W.slots) (g (Context.ofMeta P src)).reverse (extra W.slots 0))=
      Function.update (fun _=>[]) (extra W.slots 0) (g (Context.ofMeta P src)) := by
    simp [Function.update_idem,output,extra,Function.update_eq_self]
  rw [he] at h3
  have hh:=seq_exec _ _ h0 (seq_exec _ _ h1 (seq_exec _ _ h2 h3))
  have hi : store W.slots (fun _=>0) (metadata P (src.flatMap RawEncoding.Instruction.encode)) [] []=
      Function.update (fun _=>[]) (source W.slots 0) (metadata P (src.flatMap RawEncoding.Instruction.encode)) := by
    funext r
    rcases r with ((((p|j|u)|a)|u|w)|t)
    · rfl
    · exact j.elim0
    · cases u; rfl
    · fin_cases a <;> rfl
    · cases u; rfl
    · rfl
    · rfl
  rw [hi] at hh
  apply exec_mono _ hh
  have hs:=sum_bound P src B hv
  have hg:=raw_gates_length_le src
  have hb:=hv.2.2.1
  have hc:=clear_time_bound W.slots P src (g (Context.ofMeta P src)) B hv
  have hw:=W.length_bound (Context.ofMeta P src) B hv
  simp only [List.length_reverse,timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  change (src.flatMap RawEncoding.Instruction.encode).length≤B at hb
  omega

lemma metadata_ofVerifier (V : Verifier gatesG2) :
    metadata (CyclicRaw.params V) ((RawEncoding.eraseVerifier V).gates.flatMap RawEncoding.Instruction.encode)=
      CyclicMetadataTM.metadataCode V := by
  simp only [CyclicRaw.params,CyclicRaw.ofRaw_erase]
  simp [metadata,CyclicMetadataTM.metadataCode,
    CyclicMetadataTM.clockCode,CyclicMetadataTM.code,RawEncoding.eraseVerifier,List.flatMap_map,
    Function.comp_def,List.append_assoc]

/-- Actual finite-machine serialization, with every non-output stack cleared. -/
noncomputable def outputs_verifier {g : Context 0→Str} (W : RecipeWriter 0 g) (V : Verifier gatesG2) :
    TM2OutputsInTime (machine W) (CyclicMetadataTM.metadataCode V) (some (g (Context.ofVerifier V)))
      ((timePolynomial W).eval (CyclicMetadataTM.metadataCode V).length) := by
  have h:=full_exec W (CyclicRaw.params V) (RawEncoding.eraseVerifier V).gates
    (CyclicMetadataTM.metadataCode V).length (Context.ofVerifier_valid V)
  rw [metadata_ofVerifier] at h
  exact Code.outputs (program W) (source W.slots 0) (extra W.slots 0) _ _ _ h

end QMAPerfectCompleteness.Main.CircuitRecipe.Serializer


