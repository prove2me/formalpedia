-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CyclicIndexMetadataTM
-- name    : QMAPerfectCompleteness_Proof_CyclicIndexMetadataTM
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:04:14.014843+00:00
-- url     : https://prove2.me/theorems/874c2ea1-9720-4b57-ba77-6f83bf97ea5f
-- title:
--   Arithmetic for the index-register width
-- statement:
--   Defines the shared unary registers and arithmetic program computing the required even index width from the paired-Hadamard count and cycle length. Preserved-source multiplication and even rounding leave the original metadata available for serialization.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CyclicIndexMetadataTM.lean, retained declaration span lines 13–159.

/- Generated from Solutions.CyclicIndexMetadataTM by authoritative Stage-2 skeleton subtraction.
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



/-! A concrete shared-stack cyclic metadata machine: k,c,ell,m,a,out,HH and retained source body. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.CyclicIndexMetadataTM
open QAlgorithms.Complexity (Str encNat)
open StructuredStack StructuredStack.Code

inductive Reg where
  | input | field : Fin 6 → Reg
  | index | iterator | scratch | output
  deriving DecidableEq, Fintype

abbrev Values := Fin 6 → ℕ

def bank (v : Values) (k i t : ℕ) (input output : Str) : Reg → Str
  | .input => input
  | .field j => unary (v j)
  | .index => unary k
  | .iterator => unary i
  | .scratch => unary t
  | .output => output

lemma update_input (v : Values) (k i t : ℕ) (input output s : Str) :
    Function.update (bank v k i t input output) .input s = bank v k i t s output := by
  funext r; cases r <;> rfl
lemma update_output (v : Values) (k i t : ℕ) (input output s : Str) :
    Function.update (bank v k i t input output) .output s = bank v k i t input s := by
  funext r; cases r <;> rfl
lemma update_index (v : Values) (k i t n : ℕ) (input output : Str) :
    Function.update (bank v k i t input output) .index (unary n) = bank v n i t input output := by
  funext r; cases r <;> rfl
lemma update_iterator (v : Values) (k i t n : ℕ) (input output : Str) :
    Function.update (bank v k i t input output) .iterator (unary n) = bank v k n t input output := by
  funext r; cases r <;> rfl

lemma update_field (v : Values) (k i t n : ℕ) (input output : Str) (j : Fin 6) :
    Function.update (bank v k i t input output) (.field j) (unary n) =
      bank (Function.update v j n) k i t input output := by
  funext r
  cases r with
  | field l => by_cases h : l=j <;> simp_all [bank,Function.update_apply]
  | input => rfl
  | index => rfl
  | iterator => rfl
  | scratch => rfl
  | output => rfl

lemma unary_append (a b : ℕ) : unary a++unary b=unary (a+b) := by simp only [unary,List.replicate_add]
lemma unary_reverse (a : ℕ) : (unary a).reverse=unary a := by simp [unary]
lemma unary_succ (a : ℕ) : true::unary a=unary (a+1) := by simp [unary,List.replicate_succ]

lemma readField_state (v : Values) (k i t : ℕ) (output tail : Str) (j : Fin 6) (n : ℕ)
    (q : Option Bool) (hj : v j=0) :
    (Code.readField Reg.input (.field j)).Exec (q,bank v k i t (encNat n++tail) output)
      (none,bank (Function.update v j n) k i t tail output) (2*n+3) := by
  have h := readField_exec Reg.input (.field j) (by simp) n tail
    (bank v k i t (encNat n++tail) output) q rfl
  change (Code.readField Reg.input (.field j)).Exec _
    (none,Function.update (Function.update (bank v k i t (encNat n++tail) output) .input tail)
      (.field j) (unary n++unary (v j))) _ at h
  rw [hj,show unary 0=[] from rfl,List.append_nil,update_input,update_field] at h
  exact h

lemma emitField_state (v : Values) (k i t : ℕ) (input output : Str) (j : Fin 6) (q : Option Bool) :
    (Code.emitField (.field j) Reg.output).Exec (q,bank v k i t input output)
      (none,bank (Function.update v j 0) k i t input (encNat (v j)++output)) (2*v j+2) := by
  have h := emitField_exec (.field j) Reg.output (by simp) (v j)
    (bank v k i t input output) q rfl
  rw [show ([] : Str)=unary 0 from rfl,update_field,update_output] at h
  exact h

lemma emitIndex_state (v : Values) (k i t : ℕ) (input output : Str) (q : Option Bool) :
    (Code.emitField Reg.index Reg.output).Exec (q,bank v k i t input output)
      (none,bank v 0 i t input (encNat k++output)) (2*k+2) := by
  have h := emitField_exec Reg.index Reg.output (by decide) k
    (bank v k i t input output) q rfl
  rw [show ([] : Str)=unary 0 from rfl,update_index,update_output] at h
  exact h

lemma copyHH_state (v : Values) (k i : ℕ) (input output : Str) (q : Option Bool) :
    (Code.copy (.field 5) Reg.iterator Reg.scratch).Exec (q,bank v k i 0 input output)
      (none,bank v k (v 5+i) 0 input output) (4*v 5+2) := by
  have h := copy_exec (.field 5) Reg.iterator Reg.scratch (by decide) (by decide) (by decide)
    (unary (v 5)) (bank v k i 0 input output) q rfl rfl
  rw [unary_reverse] at h
  change (Code.copy (.field 5) Reg.iterator Reg.scratch).Exec _
    (none,Function.update (bank v k i 0 input output) .iterator (unary (v 5)++unary i)) _ at h
  rw [unary_append,update_iterator] at h
  simpa only [unary,List.length_replicate] using h

lemma initIndex_state (v : Values) (input output : Str) (q : Option Bool) :
    (Code.constant Reg.index 4).Exec (q,bank v 0 0 0 input output)
      (q,bank v 4 0 0 input output) 1 := by
  have h := constant_exec Reg.index 4 q (bank v 0 0 0 input output)
  change (Code.constant Reg.index 4).Exec _
    (q,Function.update (bank v 0 0 0 input output) .index (unary 4)) _ at h
  rw [update_index] at h
  exact h

lemma pushIterator_state (v : Values) (k i : ℕ) (input output : Str) (q : Option Bool) :
    (Code.push Reg.iterator true).Exec (q,bank v k i 0 input output)
      (q,bank v k (i+1) 0 input output) 1 := by
  have h := push_exec Reg.iterator true (q,bank v k i 0 input output)
  change (Code.push Reg.iterator true).Exec _
    (q,Function.update (bank v k i 0 input output) .iterator (true::unary i)) _ at h
  rw [unary_succ,update_iterator] at h
  exact h

lemma multiply_state (v : Values) (k i : ℕ) (input output : Str) (q : Option Bool) :
    (Code.multiplyAdd Reg.iterator (.field 1) Reg.index Reg.scratch).Exec (q,bank v k i 0 input output)
      (none,bank v (i*v 1+k) 0 0 input output) (i*(4*v 1+4)+1) := by
  have h := multiplyAdd_exec Reg.iterator (.field 1) Reg.index Reg.scratch
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    i (v 1) (bank v k i 0 input output) q rfl rfl rfl
  change (Code.multiplyAdd Reg.iterator (.field 1) Reg.index Reg.scratch).Exec _
    (none,Function.update (Function.update (bank v k i 0 input output) .iterator (unary 0))
      .index (unary (i*v 1)++unary k)) _ at h
  rw [unary_append,update_iterator,update_index] at h
  exact h

lemma round_state (v : Values) (k : ℕ) (input output : Str) (q : Option Bool) :
    (Code.roundEven Reg.index Reg.scratch).Exec (q,bank v k 0 0 input output)
      (none,bank v (k+k%2) 0 0 input output) (4*k+7) := by
  have h := roundEven_exec Reg.index Reg.scratch (by decide) k (bank v k 0 0 input output) q rfl rfl
  rw [update_index] at h
  exact h

abbrev arithmetic : Code Reg := seq (constant .index 4)
  (seq (copy (.field 5) .iterator .scratch)
    (seq (copy (.field 5) .iterator .scratch)
      (seq (push .iterator true)
        (seq (multiplyAdd .iterator (.field 1) .index .scratch) (roundEven .index .scratch)))))

def rawIndex (v : Values) : ℕ := (2*v 5+1)*v 1+4
def index (v : Values) : ℕ := rawIndex v+rawIndex v%2
def arithmeticTime (v : Values) : ℕ := 8*v 5+14+(2*v 5+1)*(4*v 1+4)+4*rawIndex v

lemma arithmetic_exec (v : Values) (input output : Str) (q : Option Bool) :
    arithmetic.Exec (q,bank v 0 0 0 input output) (none,bank v (index v) 0 0 input output) (arithmeticTime v) := by
  have h1 := initIndex_state v input output q
  have h2 : (copy (.field 5) Reg.iterator Reg.scratch).Exec (q,bank v 4 0 0 input output)
      (none,bank v 4 (v 5) 0 input output) (4*v 5+2) := by
    simpa only [Nat.add_zero] using copyHH_state v 4 0 input output q
  have h3 : (copy (.field 5) Reg.iterator Reg.scratch).Exec (none,bank v 4 (v 5) 0 input output)
      (none,bank v 4 (2*v 5) 0 input output) (4*v 5+2) := by
    simpa only [Nat.two_mul] using copyHH_state v 4 (v 5) input output none
  have h4 := pushIterator_state v 4 (2*v 5) input output none
  have h5 := multiply_state v 4 (2*v 5+1) input output none
  have h6 := round_state v (rawIndex v) input output none
  have hh := seq_exec _ _ h1 (seq_exec _ _ h2 (seq_exec _ _ h3 (seq_exec _ _ h4 (seq_exec _ _ h5 h6))))
  change arithmetic.Exec _ (none,bank v (index v) 0 0 input output) _ at hh
  convert hh using 1 <;> unfold arithmeticTime rawIndex <;> ring

end QMAPerfectCompleteness.Uniformity.CyclicIndexMetadataTM


