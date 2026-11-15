-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
-- name    : QMAPerfectCompleteness_Proof_RepetitionEncoding
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:52:46.79773+00:00
-- url     : https://prove2.me/theorems/76c37a6e-4137-43af-8633-3351cf916366
-- title:
--   Raw and serialized fixed-count repetition compiler
-- statement:
--   Defines numerical address remapping and the executable raw repetition circuit with n copies and a prefix-AND output chain. Its erasure identity matches the semantic gate-list construction, and its total serialized compiler returns that verifier on valid input codes. An always-rejecting valid verifier provides the malformed-input fallback.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RepetitionEncoding.lean, lines 220–300.

/- Generated from Solutions.RepetitionEncoding by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



/-! A total string-level repetition compiler and checked code-size bounds.
Runtime claims require an explicit TM2 witness and are not inferred from output size. -/
namespace QMAPerfectCompleteness.Main.Repetition.Encoding
open QAlgorithms.Complexity (Str)























end QMAPerfectCompleteness.Main.Repetition.Encoding

/-! Concrete TM2 primitive for fixed-symbol expansion. It supports copying/scaling unary code
fields while preserving their delimiters; its runtime proof is independent of output-size bounds. -/
open Turing StateTransition
namespace QMAPerfectCompleteness.Main.Repetition.Encoding.TM
open QMAPerfectCompleteness.Uniformity

























end QMAPerfectCompleteness.Main.Repetition.Encoding.TM

namespace QMAPerfectCompleteness.Main.Repetition.Encoding

/-- Raw address arithmetic corresponding to copyEmbedding. No gate matrix is inspected. -/
def remapWire (m a n j w : ℕ) : ℕ :=
  if w < m then w + m*j else n*m + (w-m) + a*j

def remapInstruction (m a n j : ℕ) (i : RawEncoding.Instruction) : RawEncoding.Instruction :=
  {i with wires := i.wires.map (remapWire m a n j)}

/-- Fully executable natural-number/list syntax for the repeated verifier. -/
def rawRepeat (n : ℕ) (V : RawEncoding.Circuit) : RawEncoding.Circuit where
  proofQubits := n * V.proofQubits
  ancillaQubits := n * V.ancillaQubits + (n+1)
  output := n * V.proofQubits + n * V.ancillaQubits + n
  gates := (List.finRange n).flatMap (fun j =>
      V.gates.map (remapInstruction V.proofQubits V.ancillaQubits n j.val)) ++
    [⟨0,[n * V.proofQubits + n * V.ancillaQubits]⟩] ++
    (List.finRange n).map (fun j => ⟨2,
      [n * V.proofQubits + n * V.ancillaQubits + j.val,
       remapWire V.proofQubits V.ancillaQubits n j.val V.output,
       n * V.proofQubits + n * V.ancillaQubits + (j.val+1)]⟩)

lemma copyEmbedding_val (V : Verifier gatesG2) (n : ℕ) (j : Fin n)
    (w : Fin (V.proofQubits+V.ancillaQubits)) :
    (Circuit.copyEmbedding V n j w).val =
      remapWire V.proofQubits V.ancillaQubits n j.val w.val := by
  refine Fin.addCases (fun p => ?_) (fun a => ?_) w
  · rw [CircuitProof.copyEmbedding_proof]
    simp only [Fin.val_castAdd, remapWire, if_pos p.isLt]
    rfl
  · rw [CircuitProof.copyEmbedding_ancilla]
    simp only [Fin.val_natAdd, Fin.val_castAdd, Circuit.proofCount, remapWire]
    rw [if_neg (by omega)]
    simp only [Nat.add_sub_cancel_left]
    change n*V.proofQubits + (a.val + V.ancillaQubits*j.val) =
      n*V.proofQubits + a.val + V.ancillaQubits*j.val
    omega

lemma erase_mapped_instruction (V : Verifier gatesG2) (n : ℕ) (j : Fin n)
    (i : Instr gatesG2 (V.proofQubits+V.ancillaQubits)) :
    RawEncoding.eraseInstr (i.mapWires (Circuit.copyEmbedding V n j)) =
      remapInstruction V.proofQubits V.ancillaQubits n j.val (RawEncoding.eraseInstr i) := by
  simp only [RawEncoding.eraseInstr, remapInstruction, Instr.mapWires, List.map_ofFn]
  congr 2
  funext a
  exact copyEmbedding_val V n j (i.targets a)

lemma erase_initializeFlag (V : Verifier gatesG2) (n : ℕ) :
    RawEncoding.eraseInstr (Circuit.initializeFlag V n) =
      ⟨0,[n*V.proofQubits + n*V.ancillaQubits]⟩ := by
  change (⟨0,[((Circuit.flagWire V n 0).val)]⟩ : RawEncoding.Instruction) = _
  simp [Circuit.flagWire, Circuit.proofCount]

lemma erase_andStep (V : Verifier gatesG2) (n : ℕ) (j : Fin n) :
    RawEncoding.eraseInstr (Circuit.andStep V n j) =
      ⟨2,[n*V.proofQubits+n*V.ancillaQubits+j.val,
        remapWire V.proofQubits V.ancillaQubits n j.val V.output.val,
        n*V.proofQubits+n*V.ancillaQubits+(j.val+1)]⟩ := by
  change (⟨2,[(Circuit.flagWire V n j.castSucc).val,
    (Circuit.copyEmbedding V n j V.output).val,(Circuit.flagWire V n j.succ).val]⟩ :
      RawEncoding.Instruction) = _
  rw [copyEmbedding_val]
  simp [Circuit.flagWire, Circuit.proofCount, Nat.add_assoc]

/-- The executable raw compiler is exactly the proved semantic circuit transformation. -/
theorem rawRepeat_erase (V : Verifier gatesG2) (n : ℕ) :
    rawRepeat n (RawEncoding.eraseVerifier V) = RawEncoding.eraseVerifier (Circuit.verifier V n) := by
  simp only [rawRepeat, RawEncoding.eraseVerifier, Circuit.verifier]
  congr 1
  · simp [Circuit.flagWire, Circuit.proofCount, Nat.add_assoc]
  · simp [Circuit.parallelGates, List.map_flatMap, List.map_map, erase_mapped_instruction,
      erase_initializeFlag, erase_andStep, Function.comp_def]

/-- A valid, always-rejecting fallback for malformed input codes. -/
def rejectFallback : RawEncoding.Circuit := ⟨0,1,0,[]⟩

def executableCompile (n : ℕ) : QAlgorithms.Complexity.Str → QAlgorithms.Complexity.Str :=
  RawEncoding.compile RawEncoding.g2Table (rawRepeat n) rejectFallback

@[simp] theorem executableCompile_encode (V : Verifier gatesG2) (n : ℕ) :
    executableCompile n V.encode = (Circuit.verifier V n).encode := by
  exact RawEncoding.compile_encode RawEncoding.g2Table RawEncoding.g2Table_correct
    (rawRepeat n) rejectFallback (fun V => Circuit.verifier V n) (fun V => rawRepeat_erase V n) V

end QMAPerfectCompleteness.Main.Repetition.Encoding

namespace QMAPerfectCompleteness.Main.Repetition.Encoding.TM
open QAlgorithms.Complexity (encNat)







end QMAPerfectCompleteness.Main.Repetition.Encoding.TM


