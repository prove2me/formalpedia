-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_TuringSimulation
-- name    : OAI_NumberTheory_SingleFold_TuringSimulation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:45:21.887815+00:00
-- url     : https://prove2.me/theorems/26cff1e6-ef96-4ebb-b89c-5d93c9bd5556
-- title:
--   Simulating Mathlib's stack machines for partial recursive functions
-- statement:
--   Consider the stack machine of $\texttt{Turing.PartrecToTM2}$, with stacks $\mathrm{main},\mathrm{rev},\mathrm{aux},\mathrm{stack}$, four stack symbols and a local store.
--
--   1. **Packing stacks.** Symbols get digits $1,2,3,4$, and a stack $s_0s_1\dots$ (top first) is the number
--   $$
--   \mathrm{pack}(s::l)=5\,\mathrm{pack}(l)+\mathrm{digit}(s),\qquad\mathrm{pack}([])=0 .
--   $$
--   2. **The macro program.** Its registers are the four stacks and $n$ input registers. Its labels are statements of the stack machine with a store value, restore labels, and input-loading labels $\mathrm{start},\mathrm{divide},\mathrm{bit},\mathrm{pushBit},\mathrm{reverse},\mathrm{pushRev}$. A push is a multiply-add, a pop or peek is a division by $5$ (a peek pushes the digit back), and load, branch and goto only change the label. The loading phase writes each natural-number input in binary onto the main stack via the reverse stack.
--   3. **Encodings.** A stack-machine configuration plus input values maps to a macro configuration with packed stacks; the initial configuration has given main and reverse stacks.
--   4. **Restriction.** A macro program can be relabelled, and restricted to a set of labels closed under its transitions, retracting all other labels to a fixed one.
--
--   This yields a macro program whose halting on input $x$ matches halting of the stack machine on the encoded input.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/TuringSimulation.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/TuringSimulation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SingleFold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterMachine
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterBounds
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterCompilation
import Definitions.Def_OAI_NumberTheory_SingleFold_MacroMachine

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace SingleFold.TM2Macro

section
open Turing Turing.PartrecToTM2 StateTransition Relation
open Macro (mod5)
abbrev Symbol := Γ'
abbrev Store := Option Symbol
abbrev Stack := K'
instance : Fintype K' where
  elems := {.main,.rev,.aux,.stack}
  complete k := by cases k <;> simp
abbrev Stmt (Λ : Type) := TM2.Stmt (fun _ : Stack=>Symbol) Λ Store
abbrev Reg (n : ℕ) := Stack ⊕ Fin n
inductive Label (n : ℕ) (Λ : Type)
  | code (q : Stmt Λ) (v : Store)
  | restore (k : Stack) (d : Fin 5) (q : Stmt Λ) (v : Store)
  | start (i : Fin (n+1))
  | divide (i : Fin n)
  | bit (i : Fin n)
  | pushBit (i : Fin n) (d : Fin 5)
  | reverse (i : Fin n)
  | pushRev (i : Fin n) (d : Fin 5)

def digit : Symbol → Fin 5
  | .consₗ=>1 | .cons=>2 | .bit0=>3 | .bit1=>4
def symbol (d : Fin 5) : Store :=
  if d.val=1 then some .consₗ else if d.val=2 then some .cons else if d.val=3 then some .bit0 else if d.val=4 then some .bit1 else none
@[simp] lemma symbol_zero : symbol 0=none := rfl
@[simp] lemma symbol_digit (s : Symbol) : symbol (digit s)=some s := by cases s <;> rfl
def pack : List Symbol → ℕ
  | []=>0
  | s::l=>5*pack l+(digit s).val
@[simp] lemma pack_nil : pack []=0 := rfl
@[simp] lemma pack_cons (s : Symbol) (l : List Symbol) : pack (s::l)=5*pack l+(digit s).val := rfl
variable {n : ℕ} {Λ : Type}
def program (M : Λ → Stmt Λ) (initial : Λ) : Label n Λ → Macro.Instr (Label n Λ) (Reg n)
  | .code q v => match q with
    | .push k f q => .muladd (.inl k) (digit (f v)) (.code q v)
    | .peek k f q => .div (.inl k) false (fun d=>.restore k d q (f v (symbol d)))
    | .pop k f q => .div (.inl k) false (fun d=>.code q (f v (symbol d)))
    | .load f q => .goto (.code q (f v))
    | .branch f q r => .goto (.code (if f v then q else r) v)
    | .goto f => .goto (.code (M (f v)) v)
    | .halt => .halt
  | .restore k d q v => if d.val=0 then .goto (.code q v) else .muladd (.inl k) d (.code q v)
  | .start i => if hi : i.val=0 then .goto (.code (M initial) none)
      else .muladd (.inl .main) (digit .cons) (.divide ⟨i.val-1,by omega⟩)
  | .divide i => .test (.inr i) (.reverse i) (.bit i)
  | .bit i => .div (.inr i) true (fun d=>.pushBit i d)
  | .pushBit i d => .muladd (.inl .rev) (digit (if d.val=0 then .bit0 else .bit1)) (.divide i)
  | .reverse i => .div (.inl .rev) false (fun d=>if d.val=0 then .start i.castSucc else .pushRev i d)
  | .pushRev i d => .muladd (.inl .main) d (.reverse i)

def values (S : Stack → List Symbol) (x : Fin n → ℕ) : Reg n → ℕ := Sum.elim (fun k=>pack (S k)) x
def encode (M : Λ → Stmt Λ) (c : TM2.Cfg (fun _ : Stack=>Symbol) Λ Store) (x : Fin n → ℕ) : Macro.Cfg (Label n Λ) (Reg n) :=
  ⟨c.l.map (fun l=>.code (M l) c.var),values c.stk x⟩
def codeCfg (q : Stmt Λ) (v : Store) (S : Stack → List Symbol) (x : Fin n → ℕ) : Macro.Cfg (Label n Λ) (Reg n) :=
  ⟨some (.code q v),values S x⟩
@[simp] lemma values_inl (S : Stack → List Symbol) (x : Fin n → ℕ) (k : Stack) : values S x (.inl k)=pack (S k) := rfl
@[simp] lemma values_inr (S : Stack → List Symbol) (x : Fin n → ℕ) (i : Fin n) : values S x (.inr i)=x i := rfl
end

section
open Turing Turing.PartrecToTM2 StateTransition Relation
open Turing Turing.PartrecToTM2 StateTransition Relation
open Macro (mod5)
variable {n : ℕ} {Λ : Type}
def initValues (L R : List Symbol) (x : Fin n → ℕ) : Reg n → ℕ := values (K'.elim L R [] []) x
def initCfg (q : Label n Λ) (L R : List Symbol) (x : Fin n → ℕ) : Macro.Cfg (Label n Λ) (Reg n) :=
  ⟨some q,initValues L R x⟩
@[simp] lemma initValues_main (L R : List Symbol) (x : Fin n → ℕ) : initValues L R x (.inl .main)=pack L := rfl
@[simp] lemma initValues_rev (L R : List Symbol) (x : Fin n → ℕ) : initValues L R x (.inl .rev)=pack R := rfl
@[simp] lemma initValues_input (L R : List Symbol) (x : Fin n → ℕ) (i : Fin n) : initValues L R x (.inr i)=x i := rfl
variable (M : Λ → Stmt Λ) (initial : Λ)
local notation "F" => Macro.step (program M initial)
end

open Turing Turing.PartrecToTM2 StateTransition Relation
variable {n : ℕ} {Λ : Type}
def inputPrefix (x : Fin n → ℕ) (k : ℕ) (hk : k≤n) : List ℕ :=
  List.ofFn (fun j : Fin k=>x ⟨j.val,lt_of_lt_of_le j.isLt hk⟩)
def clearPrefix (x : Fin n → ℕ) (k : ℕ) : Fin n → ℕ := fun j=>if j.val<k then 0 else x j
variable (M : Λ → Stmt Λ) (initial : Λ)
local notation "F" => Macro.step (program M initial)
end SingleFold.TM2Macro

namespace SingleFold.Macro
open StateTransition Relation
open scoped Classical
variable {Q Q' J : Type} [DecidableEq J]
def Instr.map (f : Q → Q') : Instr Q J → Instr Q' J
  | .halt=>.halt | .goto q=>.goto (f q) | .inc j q=>.inc j (f q)
  | .test j q r=>.test j (f q) (f r) | .muladd j d q=>.muladd j d (f q)
  | .div j b q=>.div j b (f ∘ q)
def Instr.Within (p : Q → Prop) : Instr Q J → Prop
  | .halt=>True | .goto q=>p q | .inc _ q=>p q
  | .test _ q r=>p q ∧ p r | .muladd _ _ q=>p q | .div _ _ q=>∀ d,p (q d)
def Cfg.map (f : Q → Q') (c : Cfg Q J) : Cfg Q' J := ⟨c.label.map f,c.value⟩
def retract (p : Q → Prop) (q₀ : {q // p q}) (q : Q) : {q // p q} :=
  if h : p q then ⟨q,h⟩ else q₀
def restrict (M : Q → Instr Q J) (p : Q → Prop) (q₀ : {q // p q}) : {q // p q} → Instr {q // p q} J :=
  fun q=>Instr.map (retract p q₀) (M q.val)
end SingleFold.Macro

end

end OAI


