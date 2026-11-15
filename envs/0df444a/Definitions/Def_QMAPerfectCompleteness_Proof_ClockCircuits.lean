-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
-- name    : QMAPerfectCompleteness_Proof_ClockCircuits
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:52:50.089193+00:00
-- url     : https://prove2.me/theorems/7342d61a-bb72-4f2b-bc8a-ae4841ca4230
-- title:
--   Clean controlled cyclic clock increment
-- statement:
--   Defines literal reversible circuits for incrementing a little-endian binary clock modulo its register size, controlled by an additional bit. Prefix conjunction flags implement the carries, and the action is specified to preserve wires outside the clock and reusable workspace.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, Sections 3.2–3.3, the binary clock and index-register operations. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/ClockCircuits.lean, retained declaration span lines 12–186.

/- Generated from Solutions.ClockCircuits by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets



/-! Controlled cyclic increment of a little-endian binary clock, using reusable clean flags. -/

open Matrix
namespace QMAPerfectCompleteness.Main.ClockCircuits
open ReversibleGadgets ControlCircuits ComparisonCircuits

variable {r n : ℕ} (L : AndLayout (r+1) n)

/-- Restricting a layout preserves the prefix conjunction. -/
theorem prefixAnd_prefixLayout {k : ℕ} (A : AndLayout k n) (t : ℕ) (ht : t ≤ k)
    (x : Basis n) (u : ℕ) (hu : u ≤ t) :
    prefixAnd (prefixLayout A t ht) x u hu = prefixAnd A x u (hu.trans ht) := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [prefixAnd, prefixAnd, ih (by omega)]
    rfl



/-- Step t flips clock bit t, controlled on enable and all t lower bits. -/
noncomputable def incrementStepGates (t : ℕ) (ht : t < r) : List (Instr gatesG2 n) :=
  multiControlledX (prefixLayout L (t+1) (by omega))
    (L.controls ⟨t+1, by omega⟩) (fun j => L.disjoint _ _)

theorem incrementStep_controls (t : ℕ) (ht : t < r) :
    ∀ j, L.controls (⟨t+1, by omega⟩ : Fin (r+1)) ≠
      (prefixLayout L (t+1) (by omega)).controls j := by
  intro j h
  have he := congrArg (fun i : Fin (r+1) => i.val) (L.controls.injective h)
  change t+1 = j.val at he
  have := j.isLt
  omega

theorem incrementStepGates_matrix (t : ℕ) (ht : t < r) (y x : Basis n)
    (hclean : ∀ j, x (L.flags j) = false) :
    circuitMatrix (incrementStepGates L t ht) y x =
      if y = Function.update x (L.controls ⟨t+1, by omega⟩)
        (xor (x (L.controls ⟨t+1, by omega⟩)) (prefixAnd L x (t+1) (by omega)))
      then 1 else 0 := by
  have h := multiControlledX_matrix (prefixLayout L (t+1) (by omega))
    (L.controls ⟨t+1, by omega⟩) (incrementStep_controls L t ht)
    (fun j => L.disjoint _ _) y x (fun j => hclean _)
  simpa only [incrementStepGates, prefixAnd_prefixLayout] using h



/-- Process clock targets from high to low, so every carry reads the original lower bits. -/
noncomputable def incrementPrefixGates : (t : ℕ) → t ≤ r → List (Instr gatesG2 n)
  | 0, _ => []
  | t+1, ht => incrementStepGates L t (by omega) ++ incrementPrefixGates t (by omega)

def incrementPrefixAction : (t : ℕ) → t ≤ r → Basis n → Basis n
  | 0, _, x => x
  | t+1, ht, x => incrementPrefixAction t (by omega)
      (Function.update x (L.controls ⟨t+1, by omega⟩)
        (xor (x (L.controls ⟨t+1, by omega⟩)) (prefixAnd L x (t+1) (by omega))))



theorem incrementPrefixGates_matrix (t : ℕ) (ht : t ≤ r) (y x : Basis n)
    (hclean : ∀ j, x (L.flags j) = false) :
    circuitMatrix (incrementPrefixGates L t ht) y x =
      if y = incrementPrefixAction L t ht x then 1 else 0 := by
  induction t generalizing y x with
  | zero => change (if y = x then (1 : ℂ) else 0) = if y = x then 1 else 0; rfl
  | succ t ih =>
    rw [incrementPrefixGates, BlockProof.circuitMatrix_append, Matrix.mul_apply]
    simp_rw [incrementStepGates_matrix L t (by omega) _ x hclean]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hcn : ∀ j, (Function.update x (L.controls ⟨t+1, by omega⟩)
        (xor (x (L.controls ⟨t+1, by omega⟩)) (prefixAnd L x (t+1) (by omega)))) (L.flags j) = false := by
      intro j
      rw [Function.update_of_ne (L.disjoint _ _).symm]
      exact hclean j
    exact ih (by omega) y _ hcn



theorem incrementPrefix_outside (t : ℕ) (ht : t ≤ r) (x : Basis n) (w : Fin n)
    (hw : ∀ i, w ≠ L.controls i) : incrementPrefixAction L t ht x w = x w := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    rw [incrementPrefixAction, ih (by omega)]
    exact Function.update_of_ne (hw _) _ _

noncomputable def controlledIncrementGates : List (Instr gatesG2 n) := incrementPrefixGates L r le_rfl

def controlledIncrementAction : Basis n → Basis n := incrementPrefixAction L r le_rfl



theorem controlledIncrementGates_matrix (y x : Basis n) (hclean : ∀ j, x (L.flags j) = false) :
    circuitMatrix (controlledIncrementGates L) y x =
      if y = controlledIncrementAction L x then 1 else 0 :=
  incrementPrefixGates_matrix L r le_rfl y x hclean





theorem controlledIncrementAction_outside (x : Basis n) (w : Fin n)
    (hw : ∀ i, w ≠ L.controls i) : controlledIncrementAction L x w = x w :=
  incrementPrefix_outside L r le_rfl x w hw

/-- Fixed-width binary positional value is injective on bit strings. -/
theorem littleValue_injective {k : ℕ} : Function.Injective (@littleValue k) := by
  intro x y h
  have hp : prefixValue (fun j => x j.rev) k le_rfl = prefixValue (fun j => y j.rev) k le_rfl := by
    rw [prefixValue_reverse x, prefixValue_reverse y]
    exact h
  have hall := (prefixValue_eq_iff (fun j => x j.rev) (fun j => y j.rev) k le_rfl).mp hp
  funext j
  simpa using hall j.rev j.rev.isLt

/-- The positional encoding decodes back to its original little-endian bits. -/
theorem littleValue_decode {k : ℕ} (x : Fin k → Bool) (j : Fin k) :
    (littleValue x).testBit j = x j := by
  have hval : littleValue (fun i : Fin k => (littleValue x).testBit i) = littleValue x := by
    rw [littleValue_testBit, Nat.mod_eq_of_lt (littleValue_lt_two_pow x)]
  exact congrFun (littleValue_injective hval) j

/-- The r actual clock wires, excluding the enable wire, as a bounded binary word. -/
def clockWord (x : Basis n) : BitVec r :=
  BitVec.ofNatLT (littleValue (fun j : Fin r => x (L.controls j.succ))) (littleValue_lt_two_pow _)

















end QMAPerfectCompleteness.Main.ClockCircuits


