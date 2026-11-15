-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
-- name    : QMAPerfectCompleteness_Proof_BooleanCircuits
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:48:52.485068+00:00
-- url     : https://prove2.me/theorems/5a989587-a452-4177-88e8-606ca0693003
-- title:
--   Reversible Boolean commands and dyadic gate compilation
-- statement:
--   Defines Boolean commands that negate a target bit or XOR a source bit or a conjunction into a distinct target. Their compilation uses NOT, CNOT and Toffoli gates; coincident conjunction inputs are correctly compiled as a CNOT. The circuit matrix is exactly the deterministic basis action of the command sequence.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BooleanCircuits.lean, lines 10–77.

/- Generated from Solutions.BooleanCircuits by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets



/-! A literal reversible compiler for Boolean straight-line computations. Every command XORs
its value into a distinct destination; destinations may be reused or reversed. Coincident
AND inputs are compiled to CNOT, so no unjustified distinct-control assumption is needed. -/
open Matrix
namespace QMAPerfectCompleteness.Main.BooleanCircuits
open ReversibleGadgets

inductive Command (n : ℕ) where
  | flip (target : Fin n)
  | copy (source target : Fin n) (hne : source ≠ target)
  | conj (left right target : Fin n) (hl : left ≠ target) (hr : right ≠ target)

def pair {n : ℕ} (a b : Fin n) (h : a ≠ b) : Fin 2 ↪ Fin n :=
  ⟨![a,b],by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all⟩
def triple {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Fin 3 ↪ Fin n :=
  ⟨![a,b,c],by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_two]⟩

noncomputable def compileCommand {n : ℕ} : Command n → Instr gatesG2 n
  | .flip t => xAt t
  | .copy s t h => cnotAt (pair s t h)
  | .conj a b t ha hb => if h : a=b then cnotAt (pair a t ha)
      else toffoliAt (triple a b t h ha hb)

def evalCommand {n : ℕ} : Command n → Basis n → Basis n
  | .flip t,x => Function.update x t (!x t)
  | .copy s t _,x => Function.update x t (xor (x t) (x s))
  | .conj a b t _ _,x => Function.update x t (xor (x t) (x a && x b))

lemma copy_matrix {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (cnotAt (pair a b hab)).matrix =
      classicalMatrix (fun x => Function.update x b (xor (x b) (x a))) := by
  let σ : Basis 2 → Basis 2 := fun u => Function.update u 1 (xor (u 1) (u 0))
  have hg : gateCNOT.matrix = classicalMatrix σ := by
    change classicalMatrix (fun u : Basis 2 => ![u 0,xor (u 1) (u 0)]) = classicalMatrix σ
    congr 1
    funext u i
    fin_cases i <;> simp [σ]
  rw [instr_classical (cnotAt (pair a b hab)) σ hg]
  congr 1
  funext x
  exact place_update (pair a b hab) 1 (fun u => xor (u 1) (u 0)) x

theorem compileCommand_matrix {n : ℕ} (c : Command n) :
    (compileCommand c).matrix = classicalMatrix (evalCommand c) := by
  cases c with
  | flip t => exact xAt_matrix t
  | copy s t h => exact copy_matrix s t h
  | conj a b t ha hb =>
    by_cases h : a=b
    · subst b
      simp only [compileCommand,dif_pos rfl,evalCommand]
      change (cnotAt (pair a t ha)).matrix = classicalMatrix
        (fun x => Function.update x t (xor (x t) (x a && x a)))
      simp only [Bool.and_self]
      exact copy_matrix a t ha
    · simp only [compileCommand,dif_neg h,toffoliAt_matrix]
      rfl

noncomputable def compile {n : ℕ} (p : List (Command n)) : List (Instr gatesG2 n) :=
  p.map compileCommand

def eval {n : ℕ} : List (Command n) → Basis n → Basis n
  | [],x => x
  | c::cs,x => eval cs (evalCommand c x)

/-- Exact basis action of an arbitrary Boolean straight-line program, on every input column. -/
theorem compile_matrix {n : ℕ} (p : List (Command n)) : circuitMatrix (compile p) = classicalMatrix (eval p) := by
  induction p with
  | nil =>
    ext y x
    rfl
  | cons c cs ih =>
    change circuitMatrix (compile cs) * (compileCommand c).matrix = _
    rw [ih,compileCommand_matrix,classicalMatrix_mul]
    rfl













end QMAPerfectCompleteness.Main.BooleanCircuits


