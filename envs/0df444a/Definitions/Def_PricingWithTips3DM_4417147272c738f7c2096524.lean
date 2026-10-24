-- Prove2me | Definitions.Def_PricingWithTips3DM_4417147272c738f7c2096524
-- name    : PricingWithTips3DM_4417147272c738f7c2096524
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:29:27.327995+00:00
-- url     : https://prove2.me/theorems/b8d2f34d-13ce-4d23-aebb-60778ae42743
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.Verification
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_3e5e8df74ad0aba26b3400f6
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Finite certificate semantics for general circuits

Boolean assignments are encoded as lists of the two constant symbols.  The
executable verifier rejects malformed circuits, malformed assignments, and
wrong assignment lengths before evaluating the decoded circuit.
-/

namespace CLRS.Chapter34

/-! ## Canonical Boolean certificates -/

/-- Recognize the two circuit symbols allowed in an assignment certificate. -/
def isAssignmentSymbol : CircuitSym → Bool
  | .constFalseMark | .constTrueMark => true
  | _ => false

/-- Interpret an assignment symbol as a Boolean value. -/
def assignmentSymbolValue : CircuitSym → Bool
  | .constTrueMark => true
  | _ => false

/-- Read an assignment certificate, defaulting to false beyond its end. -/
def assignmentInputs (certificate : List CircuitSym) (i : Nat) : Bool :=
  if hi : i < certificate.length then
    assignmentSymbolValue certificate[i]
  else false

/-- Encode a finite Boolean assignment as its canonical symbol list. -/
def encodeAssignment {n : Nat} (assignment : Fin n → Bool) : List CircuitSym :=
  List.ofFn fun i =>
    if assignment i then .constTrueMark else .constFalseMark

@[simp] theorem encodeAssignment_length {n : Nat}
    (assignment : Fin n → Bool) :
    (encodeAssignment assignment).length = n := by
  simp [encodeAssignment]

@[simp] theorem encodeAssignment_all {n : Nat}
    (assignment : Fin n → Bool) :
    (encodeAssignment assignment).all isAssignmentSymbol = true := by
  rw [List.all_eq_true]
  simp only [encodeAssignment, List.forall_mem_ofFn_iff]
  intro i
  cases assignment i <;> simp [isAssignmentSymbol]

@[simp] theorem assignmentInputs_encodeAssignment_of_lt {n : Nat}
    (assignment : Fin n → Bool) (i : Nat) (hi : i < n) :
    assignmentInputs (encodeAssignment assignment) i =
      assignment ⟨i, hi⟩ := by
  cases hvalue : assignment ⟨i, hi⟩ <;>
    simp [assignmentInputs, encodeAssignment, hi, hvalue,
      assignmentSymbolValue]

theorem assignmentInputs_encodeAssignment {n : Nat}
    (assignment : Fin n → Bool) :
    assignmentInputs (encodeAssignment assignment) =
      fun i => if hi : i < n then assignment ⟨i, hi⟩ else false := by
  funext i
  by_cases hi : i < n
  · simp [hi]
  · simp [assignmentInputs, encodeAssignment, hi]

/-! ## Executable verifier -/

/-- Check a finite assignment certificate against an encoded general circuit. -/
def generalCircuitVerifier (certificate input : List CircuitSym) : Bool :=
  match decodeCircuit input with
  | none => false
  | some c =>
      decide c.WellFormed &&
        decide (certificate.length = c.inputCount) &&
          certificate.all isAssignmentSymbol &&
            c.eval (assignmentInputs certificate)

/-- Exact acceptance semantics of the executable certificate checker. -/
theorem generalCircuitVerifier_accepts_iff
    (certificate input : List CircuitSym) :
    generalCircuitVerifier certificate input = true ↔
      ∃ c, decodeCircuit input = some c ∧
        c.WellFormed ∧
        certificate.length = c.inputCount ∧
        certificate.all isAssignmentSymbol = true ∧
        c.eval (assignmentInputs certificate) = true := by
  cases hdecode : decodeCircuit input with
  | none => simp [generalCircuitVerifier, hdecode]
  | some c => simp [generalCircuitVerifier, hdecode, and_assoc]

/-- Membership in {lit}`GeneralCircuitSAT` is exactly bounded acceptance by the
finite certificate checker. -/
theorem mem_generalCircuitSAT_iff_exists_certificate
    (input : List CircuitSym) :
    input ∈ GeneralCircuitSAT ↔
      ∃ certificate : List CircuitSym,
        certificate.length ≤ input.length ∧
          generalCircuitVerifier certificate input = true := by
  constructor
  · rintro ⟨c, hdecode, hwf, assignment, heval⟩
    refine ⟨encodeAssignment assignment, ?_, ?_⟩
    · rw [encodeAssignment_length]
      exact Nat.le_of_lt
        (inputCount_lt_length_of_decodeCircuit_eq_some hdecode)
    · apply (generalCircuitVerifier_accepts_iff _ _).2
      refine ⟨c, hdecode, hwf, encodeAssignment_length assignment,
        encodeAssignment_all assignment, ?_⟩
      rw [assignmentInputs_encodeAssignment]
      exact heval
  · rintro ⟨certificate, _, haccept⟩
    rcases (generalCircuitVerifier_accepts_iff certificate input).1 haccept with
      ⟨c, hdecode, hwf, hlength, _, heval⟩
    refine ⟨c, hdecode, hwf, ?_⟩
    let assignment : Fin c.inputCount → Bool :=
      fun i => assignmentInputs certificate i.val
    refine ⟨assignment, ?_⟩
    have hinputs :
        (fun i => if hi : i < c.inputCount then
          assignment ⟨i, hi⟩ else false) = assignmentInputs certificate := by
      funext i
      by_cases hi : i < c.inputCount
      · simp [hi, assignment]
      · have hcertificate : ¬i < certificate.length := by
          simpa [hlength] using hi
        simp [hi, assignmentInputs, hcertificate]
    rw [hinputs]
    exact heval

end CLRS.Chapter34


