-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
-- name    : QMAPerfectCompleteness_Proof_VariableComparison
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:01:02.339272+00:00
-- url     : https://prove2.me/theorems/eb457294-691a-4715-9b4c-0939298b43a2
-- title:
--   Reversible comparison of variable binary words
-- statement:
--   Defines a linear ripple-borrow comparison circuit for two variable binary registers. Prefix-value and borrow-state identities connect its gate action with the integer comparison while identifying the preserved input and spectator wires.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/VariableComparison.lean, retained declaration span lines 10–288.

/- Generated from Solutions.VariableComparison by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets



/-! Reversible variable-register comparison by a linear ripple-borrow computation. -/
open Matrix
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.VariableComparison
open BooleanCircuits ComparisonCircuits ReversibleGadgets

/-- Borrow from the low bits of a-b: generate when !a∧b, propagate when a=b. -/
def borrowBit (a b c : Bool) : Bool := xor ((!a) && b) ((!(xor a b)) && c)

/-- Local wires are a,b,previous borrow,next borrow,one temporary. The temporary is restored. -/
def borrowCommands {n : ℕ} (e : Fin 5 ↪ Fin n) : List (Command n) :=
  [.copy (e 0) (e 4) (e.injective.ne (by decide)),
   .copy (e 1) (e 4) (e.injective.ne (by decide)),
   .flip (e 4), .flip (e 0),
   .conj (e 0) (e 1) (e 3) (e.injective.ne (by decide)) (e.injective.ne (by decide)),
   .flip (e 0),
   .conj (e 4) (e 2) (e 3) (e.injective.ne (by decide)) (e.injective.ne (by decide)),
   .flip (e 4),
   .copy (e 1) (e 4) (e.injective.ne (by decide)),
   .copy (e 0) (e 4) (e.injective.ne (by decide))]



set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem borrowCommands_eval {n : ℕ} (e : Fin 5 ↪ Fin n) (x : Basis n)
    (h3 : x (e 3) = false) (h4 : x (e 4) = false) :
    eval (borrowCommands e) x =
      Function.update x (e 3) (borrowBit (x (e 0)) (x (e 1)) (x (e 2))) := by
  funext w
  by_cases h0 : w=e 0
  · subst w
    cases ha : x (e 0) <;> cases hb : x (e 1) <;> cases hc : x (e 2) <;>
      simp [borrowCommands,eval,evalCommand,Function.update_apply,e.injective.eq_iff,ha,hb,hc,h3,h4,borrowBit]
  · by_cases h1 : w=e 1
    · subst w
      cases ha : x (e 0) <;> cases hb : x (e 1) <;> cases hc : x (e 2) <;>
        simp [borrowCommands,eval,evalCommand,Function.update_apply,e.injective.eq_iff,ha,hb,hc,h3,h4,borrowBit]
    · by_cases h3' : w=e 3
      · subst w
        cases ha : x (e 0) <;> cases hb : x (e 1) <;> cases hc : x (e 2) <;>
          simp [borrowCommands,eval,evalCommand,Function.update_apply,e.injective.eq_iff,ha,hb,hc,h3,h4,borrowBit]
      · by_cases h4' : w=e 4
        · subst w
          cases ha : x (e 0) <;> cases hb : x (e 1) <;> cases hc : x (e 2) <;>
            simp [borrowCommands,eval,evalCommand,Function.update_apply,e.injective.eq_iff,ha,hb,hc,h3,h4,borrowBit]
        · simp [borrowCommands,eval,evalCommand,Function.update_apply,h0,h1,h3',h4']

/-- The borrow recurrence is exactly comparison of growing little-endian prefixes. -/
theorem borrow_numeric_step (m a b : ℕ) (ha : a < m) (hb : b < m) (u v : Bool) :
    borrowBit u v (decide (a < b)) =
      decide (a + (if u then m else 0) < b + (if v then m else 0)) := by
  cases u <;> cases v <;> simp [borrowBit] <;> omega

/-- The source words, borrow chain and one reused temporary occupy 3r+2 selected wires. -/
def leftWire {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (i : Fin r) : Fin n :=
  e ⟨i,by have := i.isLt; omega⟩
def rightWire {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (i : Fin r) : Fin n :=
  e ⟨r+i,by have := i.isLt; omega⟩
def carryWire {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (i : Fin (r+1)) : Fin n :=
  e ⟨2*r+i,by have := i.isLt; omega⟩
def tempWire {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) : Fin n := e ⟨3*r+1,by omega⟩

set_option maxRecDepth 10000 in
def stepEmbedding {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (i : Fin r) : Fin 5 ↪ Fin n :=
  (⟨fun j => ⟨(![i.val,r+i.val,2*r+i.val,2*r+i.val+1,3*r+1] : Fin 5 → ℕ) j,
      by have := i.isLt; fin_cases j <;> simp <;> omega⟩,
    by intro j k h
       have hv := congrArg Fin.val h
       have hi := i.isLt
       change (![i.val,r+i.val,2*r+i.val,2*r+i.val+1,3*r+1] : Fin 5 → ℕ) j =
         (![i.val,r+i.val,2*r+i.val,2*r+i.val+1,3*r+1] : Fin 5 → ℕ) k at hv
       fin_cases j <;> fin_cases k <;> first | rfl | (norm_num at hv <;> omega)⟩ : Fin 5 ↪ Fin (3*r+2)).trans e

def borrowPrefix {r : ℕ} (a b : Fin r → Bool) : (t : ℕ) → t ≤ r → Bool
  | 0,_ => false
  | t+1,ht => borrowBit (a ⟨t,by omega⟩) (b ⟨t,by omega⟩) (borrowPrefix a b t (by omega))

def lowValue {r : ℕ} (a : Fin r → Bool) (t : ℕ) (ht : t ≤ r) : ℕ :=
  littleValue (fun j : Fin t => a ⟨j,Nat.lt_of_lt_of_le j.isLt ht⟩)

lemma lowValue_step {r : ℕ} (a : Fin r → Bool) (t : ℕ) (ht : t+1 ≤ r) :
    lowValue a (t+1) ht = lowValue a t (by omega) +
      if a ⟨t,by omega⟩ then 2^t else 0 := by
  unfold lowValue littleValue
  rw [Fin.sum_univ_castSucc]
  rfl

lemma borrowPrefix_correct {r : ℕ} (a b : Fin r → Bool) (t : ℕ) (ht : t ≤ r) :
    borrowPrefix a b t ht = decide (lowValue a t ht < lowValue b t ht) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [borrowPrefix,ih (by omega),lowValue_step,lowValue_step]
    exact borrow_numeric_step (2^t) _ _ (littleValue_lt_two_pow _) (littleValue_lt_two_pow _) _ _

noncomputable def borrowChain {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) :
    (t : ℕ) → t ≤ r → List (Command n)
  | 0,_ => []
  | t+1,ht => borrowChain e t (by omega) ++ borrowCommands (stepEmbedding e ⟨t,by omega⟩)

def chainState {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (x : Basis n) :
    (t : ℕ) → t ≤ r → Basis n
  | 0,_ => x
  | t+1,ht => Function.update (chainState e x t (by omega)) (carryWire e ⟨t+1,by omega⟩)
      (borrowPrefix (x ∘ leftWire e) (x ∘ rightWire e) (t+1) ht)

lemma carryWire_injective {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) : Function.Injective (carryWire e) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val (e.injective h)
  change 2*r+i.val = 2*r+j.val at hv
  omega

lemma left_ne_carry {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (i : Fin r) (j : Fin (r+1)) :
    leftWire e i ≠ carryWire e j := by
  intro h
  have hv := congrArg Fin.val (e.injective h)
  have := i.isLt
  change i.val = 2*r+j.val at hv
  omega
lemma right_ne_carry {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (i : Fin r) (j : Fin (r+1)) :
    rightWire e i ≠ carryWire e j := by
  intro h
  have hv := congrArg Fin.val (e.injective h)
  have := i.isLt
  change r+i.val = 2*r+j.val at hv
  omega
lemma temp_ne_carry {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (j : Fin (r+1)) :
    tempWire e ≠ carryWire e j := by
  intro h
  have hv := congrArg Fin.val (e.injective h)
  have := j.isLt
  change 3*r+1 = 2*r+j.val at hv
  omega

lemma chainState_outside {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (x : Basis n)
    (t : ℕ) (ht : t ≤ r) (w : Fin n) (hw : ∀ j, w ≠ carryWire e j) : chainState e x t ht w = x w := by
  induction t with
  | zero => rfl
  | succ t ih => rw [chainState,Function.update_of_ne (hw _),ih (by omega)]

lemma chainState_carry {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (x : Basis n)
    (t : ℕ) (ht : t ≤ r) (j : Fin (r+1)) :
    chainState e x t ht (carryWire e j) =
      if 0<j.val ∧ j.val≤t then
        borrowPrefix (x ∘ leftWire e) (x ∘ rightWire e) j.val (by have := j.isLt; omega)
      else x (carryWire e j) := by
  induction t with
  | zero => rw [chainState,if_neg (by omega)]
  | succ t ih =>
    by_cases hj : j = (⟨t+1,by omega⟩ : Fin (r+1))
    · subst j
      simp [chainState]
    · rw [chainState,Function.update_of_ne ((carryWire_injective e).ne hj),ih (by omega)]
      have hjv : j.val ≠ t+1 := by intro h; exact hj (Fin.ext h)
      have heq : (0<j.val ∧ j.val≤t) ↔ (0<j.val ∧ j.val≤t+1) := by omega
      simp only [heq]

lemma eval_append {n : ℕ} (p q : List (Command n)) (x : Basis n) :
    eval (p++q) x = eval q (eval p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons c cs ih => exact ih (evalCommand c x)

theorem borrowChain_eval {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (x : Basis n)
    (hx : ∀ j, x (carryWire e j) = false) (hp : x (tempWire e) = false)
    (t : ℕ) (ht : t ≤ r) : eval (borrowChain e t ht) x = chainState e x t ht := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [borrowChain,eval_append,ih (by omega)]
    have hnext : chainState e x t (by omega) (carryWire e ⟨t+1,by omega⟩) = false := by
      rw [chainState_carry]
      simp [hx]
    have htemp : chainState e x t (by omega) (tempWire e) = false :=
      (chainState_outside e x t (by omega) _ (temp_ne_carry e)).trans hp
    rw [borrowCommands_eval _ _ hnext htemp]
    have hl := chainState_outside e x t (by omega) (leftWire e ⟨t,by omega⟩)
      (left_ne_carry e _)
    have hr := chainState_outside e x t (by omega) (rightWire e ⟨t,by omega⟩)
      (right_ne_carry e _)
    have hc : chainState e x t (by omega) (carryWire e ⟨t,by omega⟩) =
        borrowPrefix (x ∘ leftWire e) (x ∘ rightWire e) t (by omega) := by
      rw [chainState_carry]
      by_cases hz : t=0
      · subst t
        simp [borrowPrefix,hx]
      · simp [hz,Nat.pos_of_ne_zero hz]
    change Function.update (chainState e x t (by omega)) (carryWire e ⟨t+1,by omega⟩)
      (borrowBit (chainState e x t (by omega) (leftWire e ⟨t,by omega⟩))
        (chainState e x t (by omega) (rightWire e ⟨t,by omega⟩))
        (chainState e x t (by omega) (carryWire e ⟨t,by omega⟩))) = _
    rw [hl,hr,hc]
    rfl

/-- The last carry of the actual linear-size program is exactly variable-register less-than. -/
theorem borrowChain_result {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (x : Basis n)
    (hx : ∀ j, x (carryWire e j) = false) (hp : x (tempWire e) = false) :
    eval (borrowChain e r le_rfl) x (carryWire e (Fin.last r)) =
      decide (littleValue (x ∘ leftWire e) < littleValue (x ∘ rightWire e)) := by
  rw [borrowChain_eval e x hx hp,chainState_carry]
  by_cases hz : r=0
  · subst r
    simp [hx,littleValue]
  · simp only [Fin.val_last,Nat.pos_of_ne_zero hz,le_refl,and_self,if_true]
    exact borrowPrefix_correct _ _ _ _



/-- Updating an unrelated wire commutes with the entire borrow computation. -/
lemma chainState_update {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (x : Basis n)
    (w : Fin n) (b : Bool) (hw : ∀ j, w ≠ e j) (t : ℕ) (ht : t ≤ r) :
    chainState e (Function.update x w b) t ht = Function.update (chainState e x t ht) w b := by
  have hl : (Function.update x w b) ∘ leftWire e = x ∘ leftWire e := by
    funext j
    exact Function.update_of_ne (hw _).symm _ _
  have hr : (Function.update x w b) ∘ rightWire e = x ∘ rightWire e := by
    funext j
    exact Function.update_of_ne (hw _).symm _ _
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [chainState,chainState,ih (by omega),hl,hr]
    exact Function.update_comm (hw _) _ _ _

lemma classical_conjugate_column {n : ℕ} (f g : Basis n → Basis n) (y x : Basis n) :
    ((classicalMatrix f)ᴴ * classicalMatrix g * classicalMatrix f) y x =
      if f y = g (f x) then (1 : ℂ) else 0 := by
  rw [Matrix.mul_assoc,classicalMatrix_mul]
  simp [Matrix.mul_apply,classicalMatrix,Matrix.conjTranspose_apply,ite_mul,eq_comm]

/-- A clean variable comparator: XOR [A<B] into an external target and restore all work. -/
noncomputable def comparatorGates {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n)
    (target : Fin n) (hout : ∀ j, target ≠ e j) : List (Instr gatesG2 n) :=
  computeUseUncompute (compile (borrowChain e r le_rfl))
    [cnotAt (BooleanCircuits.pair (carryWire e (Fin.last r)) target (hout _).symm)]



/-- Exact full-register clean-workspace semantics of the linear-size comparator. -/
theorem comparatorGates_matrix {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n)
    (target : Fin n) (hout : ∀ j, target ≠ e j) (y x : Basis n)
    (hx : ∀ j, x (carryWire e j) = false) (hp : x (tempWire e) = false) :
    circuitMatrix (comparatorGates e target hout) y x =
      if y = Function.update x target (xor (x target)
        (decide (littleValue (x ∘ leftWire e) < littleValue (x ∘ rightWire e)))) then 1 else 0 := by
  let f := eval (borrowChain e r le_rfl)
  let bit := decide (littleValue (x ∘ leftWire e) < littleValue (x ∘ rightWire e))
  let b := xor (x target) bit
  have hf : Function.Injective f := classicalCircuit_injective (compile (borrowChain e r le_rfl)) f (compile_matrix _)
  have ht : f x target = x target := by
    change eval (borrowChain e r le_rfl) x target = _
    rw [borrowChain_eval e x hx hp]
    exact chainState_outside e x r le_rfl target (fun j => hout _)
  have hc : f x (carryWire e (Fin.last r)) = bit := borrowChain_result e x hx hp
  have hx' : ∀ j, (Function.update x target b) (carryWire e j) = false := by
    intro j
    have hj : carryWire e j ≠ target := (hout _).symm
    rw [Function.update_of_ne hj]
    exact hx j
  have hp' : (Function.update x target b) (tempWire e) = false := by
    have hj : tempWire e ≠ target := (hout _).symm
    rw [Function.update_of_ne hj]
    exact hp
  have hcomm : f (Function.update x target b) = Function.update (f x) target b := by
    change eval (borrowChain e r le_rfl) (Function.update x target b) =
      Function.update (eval (borrowChain e r le_rfl) x) target b
    rw [borrowChain_eval e _ hx' hp',chainState_update e x target b hout,borrowChain_eval e x hx hp]
  rw [comparatorGates,computeUseUncompute_matrix,compile_matrix]
  simp only [circuitMatrix,Matrix.one_mul,copy_matrix]
  rw [classical_conjugate_column]
  change (if f y = Function.update (f x) target
    (xor (f x target) (f x (carryWire e (Fin.last r)))) then (1 : ℂ) else 0) = _
  rw [ht,hc,← hcomm]
  simp only [hf.eq_iff]
  rfl

end QMAPerfectCompleteness.Main.VariableComparison


