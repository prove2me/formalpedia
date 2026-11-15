-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
-- name    : QMAPerfectCompleteness_Proof_EqualityCircuits
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:50:35.157021+00:00
-- url     : https://prove2.me/theorems/ed77a76c-4ee9-4821-9976-28ba89039b83
-- title:
--   Clean tests for fixed bit patterns
-- statement:
--   Defines circuits that normalize a chosen control pattern, compute a conjunction and perform a controlled flip before undoing the normalization. Their matrix and basis-action interfaces implement fixed-pattern equality with restored temporary flags.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/EqualityCircuits.lean, retained declaration span lines 11–197.

/- Generated from Solutions.EqualityCircuits by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets



/-! Actual clean circuits testing a fixed bit pattern, with linear gate count. -/

open Matrix
namespace QMAPerfectCompleteness.Main.EqualityCircuits
open ReversibleGadgets ControlCircuits

variable {r n : ℕ} (L : AndLayout r n)

/-- A pattern bit is matched by leaving true controls alone and negating false controls. -/
def matchBit (a p : Bool) : Bool := if p then a else !a

@[simp] theorem matchBit_eq_true (a p : Bool) : matchBit a p = true ↔ a = p := by
  cases a <;> cases p <;> decide

/-- Normalize the first t controls to positive controls. -/
noncomputable def normalizePrefixGates (p : Fin r → Bool) : (t : ℕ) → t ≤ r → List (Instr gatesG2 n)
  | 0, _ => []
  | t+1, ht => normalizePrefixGates p t (by omega) ++
      (if p ⟨t, by omega⟩ then [] else [xAt (L.controls ⟨t, by omega⟩)])

def normalizePrefixAction (p : Fin r → Bool) : (t : ℕ) → t ≤ r → Basis n → Basis n
  | 0, _, x => x
  | t+1, ht, x => if p ⟨t, by omega⟩ then normalizePrefixAction p t (by omega) x
      else xAction (L.controls ⟨t, by omega⟩) (normalizePrefixAction p t (by omega) x)

theorem normalizePrefixGates_matrix (p : Fin r → Bool) (t : ℕ) (ht : t ≤ r) :
    circuitMatrix (normalizePrefixGates L p t ht) = classicalMatrix (normalizePrefixAction L p t ht) := by
  induction t with
  | zero => ext y x; change (if y = x then (1 : ℂ) else 0) = if y = x then 1 else 0; rfl
  | succ t ih =>
    rw [normalizePrefixGates, BlockProof.circuitMatrix_append, ih (by omega)]
    cases hp : p ⟨t, by omega⟩ <;>
      simp [hp, normalizePrefixAction, circuitMatrix, xAt_matrix, classicalMatrix_mul, Function.comp_def]



theorem normalizePrefix_outside (p : Fin r → Bool) (t : ℕ) (ht : t ≤ r)
    (x : Basis n) (w : Fin n) (hw : ∀ j, w ≠ L.controls j) :
    normalizePrefixAction L p t ht x w = x w := by
  induction t with
  | zero => rfl
  | succ t ih =>
    let u : Fin r := ⟨t, by omega⟩
    change (if p u then normalizePrefixAction L p t (by omega) x else
      xAction (L.controls u) (normalizePrefixAction L p t (by omega) x)) w = x w
    cases hp : p u
    · simp only [hp, Bool.false_eq_true, if_false, xAction, Function.update_of_ne (hw u)]
      exact ih (by omega)
    · simp only [hp, if_true]
      exact ih (by omega)

theorem normalizePrefix_control (p : Fin r → Bool) (t : ℕ) (ht : t ≤ r)
    (x : Basis n) (j : Fin r) :
    normalizePrefixAction L p t ht x (L.controls j) =
      if (j : ℕ) < t then matchBit (x (L.controls j)) (p j) else x (L.controls j) := by
  induction t generalizing j with
  | zero => simp [normalizePrefixAction]
  | succ t ih =>
    let u : Fin r := ⟨t, by omega⟩
    have hprev := ih (by omega) j
    change (if p u then normalizePrefixAction L p t (by omega) x else
      xAction (L.controls u) (normalizePrefixAction L p t (by omega) x)) (L.controls j) = _
    by_cases hj : j = u
    · subst j
      have hpu : normalizePrefixAction L p t (by omega) x (L.controls u) = x (L.controls u) := by
        rw [ih (by omega) u]
        simp [u]
      cases hp : p u <;> simp [hp, xAction, hpu, matchBit, u]
    · have hne : (j : ℕ) ≠ t := by
        intro h
        apply hj
        exact Fin.ext h
      have hlt : (j : ℕ) < t ↔ (j : ℕ) < t+1 := by omega
      cases hp : p u <;>
        simp only [hp, Bool.false_eq_true, if_false, if_true, xAction,
          Function.update_of_ne (L.controls.injective.ne hj)]
      all_goals rw [hprev]; simp only [hlt]

noncomputable def normalizeGates (p : Fin r → Bool) : List (Instr gatesG2 n) :=
  normalizePrefixGates L p r le_rfl

def normalizeAction (p : Fin r → Bool) : Basis n → Basis n := normalizePrefixAction L p r le_rfl

theorem normalizeGates_matrix (p : Fin r → Bool) :
    circuitMatrix (normalizeGates L p) = classicalMatrix (normalizeAction L p) :=
  normalizePrefixGates_matrix L p r le_rfl



theorem normalize_control (p : Fin r → Bool) (x : Basis n) (j : Fin r) :
    normalizeAction L p x (L.controls j) = matchBit (x (L.controls j)) (p j) := by
  rw [normalizeAction, normalizePrefix_control]
  simp [j.isLt]

theorem normalize_outside (p : Fin r → Bool) (x : Basis n) (w : Fin n)
    (hw : ∀ j, w ≠ L.controls j) : normalizeAction L p x w = x w :=
  normalizePrefix_outside L p r le_rfl x w hw

theorem xAction_update_other (v w : Fin n) (hne : w ≠ v) (x : Basis n) (b : Bool) :
    xAction v (Function.update x w b) = Function.update (xAction v x) w b := by
  simp only [xAction, Function.update_of_ne hne.symm]
  exact Function.update_comm hne _ _ _

theorem normalizePrefix_update_other (p : Fin r → Bool) (t : ℕ) (ht : t ≤ r)
    (x : Basis n) (w : Fin n) (b : Bool) (hw : ∀ j, w ≠ L.controls j) :
    normalizePrefixAction L p t ht (Function.update x w b) =
      Function.update (normalizePrefixAction L p t ht x) w b := by
  induction t with
  | zero => rfl
  | succ t ih =>
    let u : Fin r := ⟨t, by omega⟩
    change (if p u then normalizePrefixAction L p t (by omega) (Function.update x w b) else
      xAction (L.controls u) (normalizePrefixAction L p t (by omega) (Function.update x w b))) =
      Function.update (if p u then normalizePrefixAction L p t (by omega) x else
        xAction (L.controls u) (normalizePrefixAction L p t (by omega) x)) w b
    cases hp : p u <;> simp only [hp, Bool.false_eq_true, if_false, if_true]
    · rw [ih (by omega), xAction_update_other _ _ (hw u)]
    · exact ih (by omega)

theorem normalize_update_other (p : Fin r → Bool) (x : Basis n) (w : Fin n) (b : Bool)
    (hw : ∀ j, w ≠ L.controls j) :
    normalizeAction L p (Function.update x w b) = Function.update (normalizeAction L p x) w b :=
  normalizePrefix_update_other L p r le_rfl x w b hw

theorem normalize_injective (p : Fin r → Bool) : Function.Injective (normalizeAction L p) :=
  classicalCircuit_injective (normalizeGates L p) (normalizeAction L p) (normalizeGates_matrix L p)

/-- The normalized all-ones condition is exactly equality with the prescribed control pattern. -/
theorem normalized_conjunction (p : Fin r → Bool) (x : Basis n) :
    prefixAnd L (normalizeAction L p x) r le_rfl = decide (∀ j, x (L.controls j) = p j) := by
  have hiff : prefixAnd L (normalizeAction L p x) r le_rfl = true ↔
      ∀ j, x (L.controls j) = p j := by
    rw [prefixAnd_eq_true]
    simp only [normalize_control, matchBit_eq_true]
    constructor
    · intro h j
      exact h j j.isLt
    · intro h j _
      exact h j
  cases hb : prefixAnd L (normalizeAction L p x) r le_rfl
  · have hnot : ¬ (∀ j, x (L.controls j) = p j) := by
      intro h
      have := hiff.mpr h
      simp [hb] at this
    simp [hnot]
  · have hall := hiff.mp hb
    simp [hall]

/-- A concrete pattern-equality controlled X, including uncomputation of negative controls. -/
noncomputable def patternControlledX (p : Fin r → Bool) (target : Fin n)
    (hf : ∀ j, target ≠ L.flags j) : List (Instr gatesG2 n) :=
  computeUseUncompute (normalizeGates L p) (multiControlledX L target hf)



/-- A deterministic computation before and after an arbitrary middle operation selects its
matrix entries, allowing the clean-workspace hypothesis on the actual middle input. -/
theorem classical_sandwich_general (f : Basis n → Basis n)
    (M : Matrix (Basis n) (Basis n) ℂ) (y x : Basis n) :
    ((classicalMatrix f)ᴴ * M * classicalMatrix f) y x = M (f y) (f x) := by
  classical
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, classicalMatrix, ite_mul, mul_ite]

/-- Exact bit-pattern equality with clean scratch, preserving every nontarget bit. -/
theorem patternControlledX_matrix (p : Fin r → Bool) (target : Fin n)
    (hc : ∀ j, target ≠ L.controls j) (hf : ∀ j, target ≠ L.flags j)
    (y x : Basis n) (hclean : ∀ j, x (L.flags j) = false) :
    circuitMatrix (patternControlledX L p target hf) y x =
      if y = Function.update x target (xor (x target) (decide (∀ j, x (L.controls j) = p j)))
      then 1 else 0 := by
  rw [patternControlledX, computeUseUncompute_matrix, normalizeGates_matrix,
    classical_sandwich_general]
  have hcn : ∀ j, normalizeAction L p x (L.flags j) = false := by
    intro j
    rw [normalize_outside L p x _ (fun k => (L.disjoint k j).symm)]
    exact hclean j
  rw [multiControlledX_matrix L target hc hf _ _ hcn, normalized_conjunction]
  have hcov : Function.update (normalizeAction L p x) target
      (xor (normalizeAction L p x target) (decide (∀ j, x (L.controls j) = p j))) =
      normalizeAction L p
        (Function.update x target (xor (x target) (decide (∀ j, x (L.controls j) = p j)))) := by
    rw [normalize_update_other L p x target _ hc, normalize_outside L p x target hc]
  rw [hcov]
  simp only [(normalize_injective L p).eq_iff]

end QMAPerfectCompleteness.Main.EqualityCircuits


