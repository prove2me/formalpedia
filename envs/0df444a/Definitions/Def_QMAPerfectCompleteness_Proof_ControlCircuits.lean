-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
-- name    : QMAPerfectCompleteness_Proof_ControlCircuits
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:49:08.107652+00:00
-- url     : https://prove2.me/theorems/ca8ffaa0-e054-46f8-a4d5-f4ef9293aae5
-- title:
--   Prefix conjunctions and controlled flips
-- statement:
--   Defines disjoint control and flag layouts, prefix-AND computations, and many-controlled bit flips assembled from literal reversible gates. Compute-use-uncompute programs expose the intended basis action while restoring the conjunction workspace.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/ControlCircuits.lean, retained declaration span lines 9–273.

/- Generated from Solutions.ControlCircuits by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets



/-! Concrete prefix-AND and many-control circuits for the block compiler. -/

open Matrix
namespace QMAPerfectCompleteness.Main.ControlCircuits
open ReversibleGadgets

/-- Distinct input controls and a disjoint chain of r+1 prefix flags. -/
structure AndLayout (r n : ℕ) where
  controls : Fin r ↪ Fin n
  flags : Fin (r+1) ↪ Fin n
  disjoint : ∀ i j, controls i ≠ flags j

variable {r n : ℕ} (L : AndLayout r n)

/-- One Toffoli computes the next prefix conjunction into an initially-zero flag. -/
def andTargets (j : Fin r) : Fin 3 ↪ Fin n :=
  ⟨![L.flags j.castSucc, L.controls j, L.flags j.succ], by
    intro a b hab
    have hprev := L.disjoint j j.castSucc
    have hnext := L.disjoint j j.succ
    have hflags : L.flags j.castSucc ≠ L.flags j.succ := by
      intro h
      have hv := congrArg Fin.val (L.flags.injective h)
      simp at hv
    fin_cases a <;> fin_cases b <;> simp_all⟩

def andStep (j : Fin r) : Instr gatesG2 n := toffoliAt (andTargets L j)

/-- The first t prefix steps, in increasing control order. -/
noncomputable def prefixGates : (t : ℕ) → t ≤ r → List (Instr gatesG2 n)
  | 0, _ => []
  | t+1, ht => prefixGates t (by omega) ++ [andStep L ⟨t, by omega⟩]

/-- The explicit classical basis action of the same steps. -/
def prefixAction : (t : ℕ) → t ≤ r → Basis n → Basis n
  | 0, _, x => x
  | t+1, ht, x => toffoliAction (andTargets L ⟨t, by omega⟩)
      (prefixAction t (by omega) x)



theorem prefixGates_matrix (t : ℕ) (ht : t ≤ r) :
    circuitMatrix (prefixGates L t ht) = classicalMatrix (prefixAction L t ht) := by
  induction t with
  | zero =>
    ext y x
    change (if y = x then (1 : ℂ) else 0) = if y = x then 1 else 0
    rfl
  | succ t ih =>
    rw [prefixGates, BlockProof.circuitMatrix_append, ih]
    simp only [circuitMatrix, Matrix.one_mul, andStep, toffoliAt_matrix, classicalMatrix_mul]
    rfl

/-- Prefix conjunction of the first t controls. -/
def prefixAnd (x : Basis n) : (t : ℕ) → t ≤ r → Bool
  | 0, _ => true
  | t+1, ht => prefixAnd x t (by omega) && x (L.controls ⟨t, by omega⟩)

/-- No prefix step changes a control bit. -/
theorem prefixAction_control (t : ℕ) (ht : t ≤ r) (x : Basis n) (j : Fin r) :
    prefixAction L t ht x (L.controls j) = x (L.controls j) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change Function.update _ (L.flags (⟨t, by omega⟩ : Fin r).succ) _ (L.controls j) = _
    rw [Function.update_of_ne (L.disjoint j _)]
    exact ih (by omega)

/-- Nor do they change any bit outside the flag chain. -/
theorem prefixAction_outside (t : ℕ) (ht : t ≤ r) (x : Basis n) (w : Fin n)
    (hw : ∀ j, w ≠ L.flags j) : prefixAction L t ht x w = x w := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change Function.update _ (L.flags (⟨t, by omega⟩ : Fin r).succ) _ w = _
    rw [Function.update_of_ne (hw _)]
    exact ih (by omega)

/-- Exact flag values after t steps, assuming all flags initially zero and the seed set to one. -/
theorem prefixAction_flags (t : ℕ) (ht : t ≤ r) (x : Basis n)
    (hclean : ∀ j, x (L.flags j) = false) (j : Fin (r+1)) :
    prefixAction L t ht (Function.update x (L.flags 0) true) (L.flags j) =
      if (j : ℕ) ≤ t then prefixAnd L x j (Nat.le_of_lt_succ j.isLt) else false := by
  induction t generalizing j with
  | zero =>
    by_cases hj : j = 0
    · subst j
      simp [prefixAction, prefixAnd]
    · have hjval : ¬ (j : ℕ) ≤ 0 := by intro h; apply hj; exact Fin.ext (by simpa using h)
      simp [prefixAction, Function.update_of_ne (L.flags.injective.ne hj), hjval, hclean j]
  | succ t ih =>
    let u : Fin r := ⟨t, by omega⟩
    have hnew : prefixAction L t (by omega) (Function.update x (L.flags 0) true)
        (L.flags u.succ) = false := by
      rw [ih (by omega) u.succ]
      simp [u]
    have hprev : prefixAction L t (by omega) (Function.update x (L.flags 0) true)
        (L.flags u.castSucc) = prefixAnd L x t (by omega) := by
      rw [ih (by omega) u.castSucc]
      simp [u]
    have hcontrol : prefixAction L t (by omega) (Function.update x (L.flags 0) true)
        (L.controls u) = x (L.controls u) := by
      rw [prefixAction_control]
      exact Function.update_of_ne (L.disjoint u 0) _ _
    let s : Basis n := prefixAction L t (by omega) (Function.update x (L.flags 0) true)
    change Function.update s (L.flags u.succ)
      (xor (s (L.flags u.succ)) (s (L.flags u.castSucc) && s (L.controls u))) (L.flags j) = _
    have hsnew : s (L.flags u.succ) = false := hnew
    have hsprev : s (L.flags u.castSucc) = prefixAnd L x t (by omega) := hprev
    have hscontrol : s (L.controls u) = x (L.controls u) := hcontrol
    rw [hsnew, hsprev, hscontrol]
    by_cases hj : j = u.succ
    · subst j
      simp [prefixAnd, u]
    · rw [Function.update_of_ne (L.flags.injective.ne hj)]
      have hsj : s (L.flags j) =
          if (j : ℕ) ≤ t then prefixAnd L x j (Nat.le_of_lt_succ j.isLt) else false :=
        ih (by omega) j
      rw [hsj]
      have hle : (j : ℕ) ≤ t ↔ (j : ℕ) ≤ t+1 := by
        have hne : (j : ℕ) ≠ t+1 := by
          intro h
          apply hj
          exact Fin.ext h
        omega
      simp only [hle]

/-- Initialize the seed, then run every prefix-AND step. -/
noncomputable def andGates : List (Instr gatesG2 n) :=
  [xAt (L.flags 0)] ++ prefixGates L r le_rfl

def andAction (x : Basis n) : Basis n := prefixAction L r le_rfl (xAction (L.flags 0) x)



theorem andGates_matrix : circuitMatrix (andGates L) = classicalMatrix (andAction L) := by
  rw [andGates, BlockProof.circuitMatrix_append, prefixGates_matrix]
  simp only [circuitMatrix, Matrix.one_mul, xAt_matrix, classicalMatrix_mul]
  rfl

/-- The final flag contains exactly the conjunction of every input control. -/
theorem andAction_last (x : Basis n) (hclean : ∀ j, x (L.flags j) = false) :
    andAction L x (L.flags (Fin.last r)) = prefixAnd L x r le_rfl := by
  unfold andAction
  have hx : xAction (L.flags 0) x = Function.update x (L.flags 0) true := by
    simp [xAction, hclean 0]
  rw [hx, prefixAction_flags L r le_rfl x hclean (Fin.last r)]
  simp

/-- Prefix conjunction equals true precisely when all earlier controls are true. -/
theorem prefixAnd_eq_true (x : Basis n) (t : ℕ) (ht : t ≤ r) :
    prefixAnd L x t ht = true ↔ ∀ j : Fin r, (j : ℕ) < t → x (L.controls j) = true := by
  induction t with
  | zero => simp [prefixAnd]
  | succ t ih =>
    rw [prefixAnd, Bool.and_eq_true, ih (by omega)]
    constructor
    · rintro ⟨hp, hn⟩ j hj
      by_cases hlt : (j : ℕ) < t
      · exact hp j hlt
      · have heq : j = (⟨t, by omega⟩ : Fin r) := by
          apply Fin.ext
          change j.val = t
          omega
        simpa only [heq] using hn
    · intro h
      exact ⟨fun j hj => h j (by omega), h ⟨t, by omega⟩ (by simp)⟩

/-- A Toffoli commutes with an update to a distinct, unaccessed wire. -/
theorem toffoliAction_update_other (e : Fin 3 ↪ Fin n) (x : Basis n) (w : Fin n) (b : Bool)
    (hw : ∀ j, w ≠ e j) :
    toffoliAction e (Function.update x w b) = Function.update (toffoliAction e x) w b := by
  simp only [toffoliAction, Function.update_of_ne (hw 0).symm,
    Function.update_of_ne (hw 1).symm, Function.update_of_ne (hw 2).symm]
  exact Function.update_comm (hw 2) _ _ _

/-- The entire AND chain does not read or write a wire outside controls and flags. -/
theorem prefixAction_update_other (t : ℕ) (ht : t ≤ r) (x : Basis n) (w : Fin n) (b : Bool)
    (hc : ∀ j, w ≠ L.controls j) (hf : ∀ j, w ≠ L.flags j) :
    prefixAction L t ht (Function.update x w b) = Function.update (prefixAction L t ht x) w b := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change toffoliAction (andTargets L ⟨t, by omega⟩)
      (prefixAction L t (by omega) (Function.update x w b)) = _
    rw [ih (by omega)]
    apply toffoliAction_update_other
    intro j
    fin_cases j <;> simp [andTargets, hf, hc]

theorem andAction_outside (x : Basis n) (w : Fin n) (hw : ∀ j, w ≠ L.flags j) :
    andAction L x w = x w := by
  rw [andAction, prefixAction_outside L r le_rfl _ w hw]
  exact Function.update_of_ne (hw 0) _ _

theorem andAction_update_other (x : Basis n) (w : Fin n) (b : Bool)
    (hc : ∀ j, w ≠ L.controls j) (hf : ∀ j, w ≠ L.flags j) :
    andAction L (Function.update x w b) = Function.update (andAction L x) w b := by
  unfold andAction xAction
  rw [Function.update_of_ne (hf 0).symm, Function.update_comm (hf 0)]
  exact prefixAction_update_other L r le_rfl _ w b hc hf

/-- The basis action of an addressed CNOT. -/
def cnotAction (e : Fin 2 ↪ Fin n) (x : Basis n) : Basis n :=
  Function.update x (e 1) (xor (x (e 1)) (x (e 0)))

theorem cnotAt_matrix (e : Fin 2 ↪ Fin n) :
    (cnotAt e).matrix = classicalMatrix (cnotAction e) := by
  rw [instr_classical (cnotAt e) _ rfl]
  congr 1
  funext x
  change placePermutation e (fun a : Basis 2 => ![a 0, xor (a 1) (a 0)]) x = cnotAction e x
  apply (CircuitProof.splitTargets e).injective
  simp only [placePermutation, Equiv.apply_symm_apply]
  apply Prod.ext
  · funext j
    fin_cases j <;> simp [CircuitProof.splitTargets_fst, cnotAction,
      Function.update_of_ne (e.injective.ne (by decide : (0 : Fin 2) ≠ 1))]
  · funext w
    have hw : (w : Fin n) ≠ e 1 := by intro h; exact w.2 ⟨1,h.symm⟩
    change x (w : Fin n) = Function.update x (e 1) _ (w : Fin n)
    rw [Function.update_of_ne hw]

/-- The use step reads the final prefix flag and flips an external target. -/
def useTargets (target : Fin n) (h : ∀ j, target ≠ L.flags j) : Fin 2 ↪ Fin n :=
  ⟨![L.flags (Fin.last r), target], by
    intro a b hab
    have hne : L.flags (Fin.last r) ≠ target := (h _).symm
    fin_cases a <;> fin_cases b <;> simp_all⟩

/-- A genuine many-controlled X circuit, with r+1 clean scratch flags. -/
noncomputable def multiControlledX (target : Fin n) (h : ∀ j, target ≠ L.flags j) :
    List (Instr gatesG2 n) :=
  computeUseUncompute (andGates L) [cnotAt (useTargets L target h)]



/-- The matrix of a reversible computation, classical use step, and its adjoint. -/
theorem classical_sandwich_apply (f g : Basis n → Basis n) (y x : Basis n) :
    ((classicalMatrix f)ᴴ * classicalMatrix g * classicalMatrix f) y x =
      if f y = g (f x) then 1 else 0 := by
  classical
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, classicalMatrix,
    ite_mul, mul_ite, eq_comm]

/-- Exact many-controlled X semantics. All controls, every clean scratch flag, and every other
wire are restored; only the external target is toggled by the conjunction of all r controls. -/
theorem multiControlledX_matrix (target : Fin n) (hc : ∀ j, target ≠ L.controls j)
    (hf : ∀ j, target ≠ L.flags j) (y x : Basis n)
    (hclean : ∀ j, x (L.flags j) = false) :
    circuitMatrix (multiControlledX L target hf) y x =
      if y = Function.update x target (xor (x target) (prefixAnd L x r le_rfl)) then 1 else 0 := by
  rw [multiControlledX, computeUseUncompute_matrix, andGates_matrix]
  simp only [circuitMatrix, Matrix.one_mul, cnotAt_matrix]
  rw [classical_sandwich_apply]
  have hcomm : cnotAction (useTargets L target hf) (andAction L x) =
      andAction L (Function.update x target (xor (x target) (prefixAnd L x r le_rfl))) := by
    rw [andAction_update_other L x target _ hc hf]
    change Function.update (andAction L x) target
      (xor (andAction L x target) (andAction L x (L.flags (Fin.last r)))) =
      Function.update (andAction L x) target (xor (x target) (prefixAnd L x r le_rfl))
    rw [andAction_last L x hclean, andAction_outside L x target hf]
  rw [hcomm]
  have hinj := classicalCircuit_injective (andGates L) (andAction L) (andGates_matrix L)
  simp only [hinj.eq_iff]









end QMAPerfectCompleteness.Main.ControlCircuits


