-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
-- name    : QMAPerfectCompleteness_Proof_BlockEncoding
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:47:05.096793+00:00
-- url     : https://prove2.me/theorems/4122db37-4fdf-40f3-80df-865b8db7ee04
-- title:
--   Compressed transition and closing blocks
-- statement:
--   Defines the history-space blocks obtained from the transition and closing gadgets by fixing verifier ancillas to zero and selecting incoming flag one and outgoing flag zero. Self-adjointness and reversed-circuit identities for the dyadic gate set support the later identification of these compressions with the cyclic transition and closing terms.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BlockEncoding.lean, lines 23–402.

/- Generated from Solutions.BlockEncoding by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates



/-! Algebraic ingredients of Lemma 3.6. All results in this file are proved from definitions;
no import of the open `exact_block_encoding` statement is used. -/

open Matrix
open scoped Kronecker

namespace QMAPerfectCompleteness.Main.BlockProof

variable {G : GateSet} (V : Verifier G)





/-- The basis state used to insert the history and a prescribed flag value. -/
def bodyInitial (f : Bool) (x : History V) : V.Body := (x.1, V.initialState x.2, f)









































/-- The two transition blocks on the history register, with all verifier ancillas fixed. -/
noncomputable def forwardBlock : Matrix (History V) (History V) ℂ :=
  fun y x => V.gadgetT (bodyInitial V false y) (bodyInitial V true x)

noncomputable def closingBlock (z : V.Proof) : Matrix (History V) (History V) ℂ :=
  fun y x => V.gadgetR z (bodyInitial V false y) (bodyInitial V true x)











/-- Every reversible involution is a self-adjoint permutation matrix. -/
theorem classicalMatrix_selfAdjoint {n : ℕ} (σ : Basis n → Basis n)
    (hσ : Function.Involutive σ) : (classicalMatrix σ)ᴴ = classicalMatrix σ := by
  classical
  ext y x
  have hiff : x = σ y ↔ y = σ x := by
    constructor
    · intro h
      rw [h, hσ]
    · intro h
      rw [h, hσ]
  simp [classicalMatrix, Matrix.conjTranspose_apply, hiff]

/-- All four gates in G₂ are their own adjoints, as used in Lemma 3.6. -/
theorem g2_gate_selfAdjoint (j : Fin gatesG2.length) :
    (gatesG2.get j).matrixᴴ = (gatesG2.get j).matrix := by
  fin_cases j
  · apply classicalMatrix_selfAdjoint
    intro x
    funext i
    fin_cases i
    simp
  · apply classicalMatrix_selfAdjoint
    intro x
    funext i
    fin_cases i <;> simp
  · apply classicalMatrix_selfAdjoint
    intro x
    funext i
    fin_cases i <;> simp
  · change hadamardTwoMatrixᴴ = hadamardTwoMatrix
    ext y x
    simp only [Matrix.conjTranspose_apply, hadamardTwoMatrix, Matrix.of_apply]
    simp only [Bool.and_comm]
    split_ifs <;> norm_num <;> simp_all [Bool.and_comm]

/-- Placing a self-adjoint gate on arbitrary distinct wires preserves self-adjointness. -/
theorem instr_selfAdjoint {n : ℕ} (i : Instr G n)
    (hgate : (G.get i.gate).matrixᴴ = (G.get i.gate).matrix) : i.matrixᴴ = i.matrix := by
  classical
  ext y x
  have hs := congrArg (fun M => M (y ∘ i.targets) (x ∘ i.targets)) hgate
  change (starRingEnd ℂ) (if (∀ w, (∀ a, i.targets a ≠ w) → x w = y w) then
      (G.get i.gate).matrix (x ∘ i.targets) (y ∘ i.targets) else 0) =
    if (∀ w, (∀ a, i.targets a ≠ w) → y w = x w) then
      (G.get i.gate).matrix (y ∘ i.targets) (x ∘ i.targets) else 0
  by_cases hxy : ∀ w, (∀ a, i.targets a ≠ w) → y w = x w
  · have hyx : ∀ w, (∀ a, i.targets a ≠ w) → x w = y w := by
      intro w hw
      exact (hxy w hw).symm
    rw [if_pos hyx, if_pos hxy]
    exact hs
  · have hyx : ¬ (∀ w, (∀ a, i.targets a ≠ w) → x w = y w) := by
      intro h
      apply hxy
      intro w hw
      exact (h w hw).symm
    rw [if_neg hyx, if_neg hxy]
    simp

/-- Executing appended gate lists executes the first list before the second. -/
theorem circuitMatrix_append {n : ℕ} (gs hs : List (Instr G n)) :
    circuitMatrix (gs ++ hs) = circuitMatrix hs * circuitMatrix gs := by
  induction gs with
  | nil => simp [circuitMatrix]
  | cons g gs ih => simp [circuitMatrix, ih, Matrix.mul_assoc]

/-- G₂ circuits implement their exact adjoints by reversing the gate list. -/
theorem circuitMatrix_reverse_g2 {n : ℕ} (gs : List (Instr gatesG2 n)) :
    circuitMatrix gs.reverse = (circuitMatrix gs)ᴴ := by
  induction gs with
  | nil => simp [circuitMatrix]
  | cons g gs ih =>
    rw [List.reverse_cons, circuitMatrix_append, ih]
    simp [circuitMatrix, Matrix.conjTranspose_mul,
      instr_selfAdjoint g (g2_gate_selfAdjoint g.gate)]



end QMAPerfectCompleteness.Main.BlockProof


