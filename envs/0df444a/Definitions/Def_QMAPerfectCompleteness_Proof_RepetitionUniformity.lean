-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionUniformity
-- name    : QMAPerfectCompleteness_Proof_RepetitionUniformity
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:01:27.021197+00:00
-- url     : https://prove2.me/theorems/bdb31a06-caa7-49be-a635-ce0cc2d918d4
-- title:
--   Timed continuation after duplicating verifier code
-- statement:
--   Defines the continuation on a duplicated source-code stream for positive fixed-count repetition. Its finite-machine output witness consumes the repeated packets and produces the exact executable repetition encoding within an explicit quadratic polynomial in stream length. The repetition-count dependence is carried by the polynomial’s fixed coefficient.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RepetitionUniformity.lean, lines 13–53.

/- Generated from Solutions.RepetitionUniformity by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCompilerBounds
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCompilerInterface
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCompilerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Actual TM2 polynomial-time uniformity of fixed positive-count G₂ repetition. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
open Turing StateTransition
namespace QMAPerfectCompleteness.Main.Repetition.CompilerTM
open QAlgorithms.Complexity (Str encNat)
open Uniformity

/-- Total continuation on the duplicated source stream. Only the first validated packet is
needed to specify its output; the checked machine consumes exactly all n packets. -/
def duplicatedCompile (n : ℕ) (s : Str) : Str :=
  match RawEncoding.parseCircuit RawEncoding.g2Table s with
  | none => Encoding.rejectFallback.encode
  | some (V,_) => (Encoding.rawRepeat n V).encode

lemma duplicatedCompile_replicate (n : ℕ) (hn : 0<n) (V : Verifier gatesG2) :
    duplicatedCompile n (List.replicate n V.encode).flatten = Encoding.executableCompile n V.encode := by
  have he : (List.replicate n V.encode).flatten = V.encode++(List.replicate (n-1) V.encode).flatten := by
    conv_lhs => rw [show n=(n-1)+1 by omega,List.replicate_succ,List.flatten_cons]
  rw [he]
  simp only [duplicatedCompile,RawEncoding.parseCircuit_encode RawEncoding.g2Table RawEncoding.g2Table_correct,
    Encoding.rawRepeat_erase,RawEncoding.eraseVerifier_encode,Encoding.executableCompile_encode]

noncomputable def timePolynomial (n : ℕ) : Polynomial ℕ :=
  Polynomial.C (1000000*(n+1)^4)*(Polynomial.X+1)^2

noncomputable def outputs_verifier (n : ℕ) (hn : 0<n) (V : Verifier gatesG2) :
    TM2OutputsInTime (machine n) (List.replicate n V.encode).flatten
      (some (duplicatedCompile n (List.replicate n V.encode).flatten))
      ((timePolynomial n).eval (List.replicate n V.encode).flatten.length) where
  steps := fullTime n V.proofQubits V.ancillaQubits V.output.val (V.gates.map instrRecipe)
  evals_in_steps := by
    rw [duplicatedCompile_replicate n hn,Encoding.executableCompile_encode,
      ← targetCode_verifier V n,← sourceCode_verifier V]
    exact full_run n hn _ _ _ _
  steps_le_m := by
    have hr := source_resources_le V
    have ha : ∀ r ∈ V.gates.map instrRecipe, ∀ i, r.2 i ≤ V.encode.length := by
      intro r hm i
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hm
      exact (instrRecipe_address_le g i).trans (by omega)
    have h := fullTime_bound n V.proofQubits V.ancillaQubits V.output.val V.encode.length
      (V.gates.map instrRecipe) hr.1 (by simpa using hr.2) ha
    have he : (List.replicate n V.encode).flatten.length = n*V.encode.length := by simp
    have hl : V.encode.length ≤ (List.replicate n V.encode).flatten.length := by rw [he]; nlinarith
    have hp := Nat.mul_le_mul_left (1000000*(n+1)^4) (Nat.pow_le_pow_left (by omega :
      V.encode.length+1 ≤ (List.replicate n V.encode).flatten.length+1) 2)
    simpa only [timePolynomial,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using h.trans hp







end QMAPerfectCompleteness.Main.Repetition.CompilerTM


