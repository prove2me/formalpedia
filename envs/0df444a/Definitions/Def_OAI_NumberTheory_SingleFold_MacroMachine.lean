-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_MacroMachine
-- name    : OAI_NumberTheory_SingleFold_MacroMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:41:46.860424+00:00
-- url     : https://prove2.me/theorems/4071b208-4178-4b38-aca6-2e7338706f6c
-- title:
--   Macro counter machines with base-5 arithmetic and their compilation
-- statement:
--   1. **Macro instructions.** Over states $Q$ and registers $J$: halt; goto $p$; increment $v_j$; test whether $v_j=0$ (without changing it); multiply-add $v_j\mapsto5v_j+e$ for a digit $e<5$; and divide $v_j$ by the radix $\rho\in\{2,5\}$, replacing $v_j$ by $\lfloor v_j/\rho\rfloor$ and branching on the remainder $v_j\bmod\rho$. A configuration has an optional label ($\mathrm{none}$ meaning halted) and register values; one step executes the labelled instruction.
--   2. **Compilation.** A macro program becomes an ordinary counter machine (increment / test-and-decrement) on registers $J\sqcup\{\text{scratch},\text{zero}\}$. Its states are the original labels plus auxiliary states:
--   $$
--   \mathrm{grow}(q,i),\ \mathrm{copy}(q,r),\ \mathrm{copyInc}(q,r),\ \mathrm{add}(q,i),\ \mathrm{quotient}(q,r),\ \mathrm{carry}(q),\ \mathrm{restore}(q).
--   $$
--      Multiplication by $5$ moves the register into scratch five units per unit and copies it back. Division repeatedly subtracts the radix, counting the quotient in scratch. A zero test is a test-and-decrement followed by a restoring increment.
--   3. A macro configuration is encoded by its label (or the halt state) with scratch and the zero register set to $0$.
--
--   Base-$5$ registers can hold whole stacks of symbols, so this layer lets counter machines simulate stack machines.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/MacroMachine.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/MacroMachine.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Counter
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
def step (M : Machine Q J) (c : Cfg Q J) : Option (Cfg Q J) :=
  match M.instr c.state with | .halt=>none | _=>some (next M c)
end SingleFold.Counter

namespace SingleFold.Macro

section
open Counter StateTransition Relation
inductive Instr (Q J : Type)
  | halt
  | goto (p : Q)
  | inc (j : J) (p : Q)
  | test (j : J) (pz pp : Q)
  | muladd (j : J) (e : Fin 5) (p : Q)
  | div (j : J) (binary : Bool) (p : Fin 5 → Q)

def radix (binary : Bool) : ℕ := if binary then 2 else 5
structure Cfg (Q J : Type) where
  label : Option Q
  value : J → ℕ
variable {Q J : Type}
def next [DecidableEq J] (M : Q → Instr Q J) (q : Q) (v : J → ℕ) : Cfg Q J :=
  match M q with
  | .halt => ⟨none,v⟩
  | .goto p => ⟨some p,v⟩
  | .inc j p => ⟨some p,Function.update v j (v j+1)⟩
  | .test j pz pp => ⟨some (if v j=0 then pz else pp),v⟩
  | .muladd j e p => ⟨some p,Function.update v j (5*v j+e)⟩
  | .div j b p => ⟨some (p ⟨v j%radix b,by have h := Nat.mod_lt (v j) (show 0 < radix b by cases b <;> decide); cases b <;> simp_all [radix]; omega⟩),Function.update v j (v j/radix b)⟩
def step [DecidableEq J] (M : Q → Instr Q J) (c : Cfg Q J) : Option (Cfg Q J) :=
  c.label.map (fun q=>next M q c.value)

inductive State (Q : Type)
  | main (q : Q)
  | grow (q : Q) (i : Fin 5)
  | copy (q : Q) (r : Fin 5)
  | copyInc (q : Q) (r : Fin 5)
  | add (q : Q) (i : Fin 5)
  | quotient (q : Q) (r : Fin 5)
  | carry (q : Q)
  | restore (q : Q)
  | halt
  deriving DecidableEq, Fintype
abbrev Reg (J : Type) := J ⊕ Bool
def scratch : Reg J := .inr false
def zeroReg : Reg J := .inr true

def succ5 (i : Fin 5) : Fin 5 := ⟨(i.val+1)%5,Nat.mod_lt _ (by omega)⟩
def go (s : State Q) : Counter.Instr (State Q) (Reg J) := .test zeroReg s s

def finish (M : Q → Instr Q J) (q : Q) (r : Fin 5) : State Q :=
  match M q with
  | .muladd _ _ _ => .add q 0
  | .div _ _ p => .main (p r)
  | _ => .halt

def compileInstr (M : Q → Instr Q J) : State Q → Counter.Instr (State Q) (Reg J)
  | .main q => match M q with
    | .halt => go .halt
    | .goto p => go (.main p)
    | .inc j p => .inc (.inl j) (.main p)
    | .test j pz _ => .test (.inl j) (.main pz) (.restore q)
    | .muladd j _ _ => .test (.inl j) (.copy q 0) (.grow q 0)
    | .div _ _ _ => go (.quotient q 0)
  | .grow q i => .inc scratch (if i.val=4 then .main q else .grow q (succ5 i))
  | .copy q r => .test scratch (finish M q r) (.copyInc q r)
  | .copyInc q r => match M q with
    | .muladd j _ _ | .div j _ _ => .inc (.inl j) (.copy q r)
    | _ => go .halt
  | .add q i => match M q with
    | .muladd j e p => if i.val<e.val then .inc (.inl j) (.add q (succ5 i)) else go (.main p)
    | _ => go .halt
  | .quotient q r => match M q with
    | .div j b _ => .test (.inl j) (.copy q r)
        (if r.val+1=radix b then .carry q else .quotient q (succ5 r))
    | _ => go .halt
  | .carry q => .inc scratch (.quotient q 0)
  | .restore q => match M q with
    | .test j _ p => .inc (.inl j) (.main p)
    | _ => go .halt
  | .halt => .halt

def compile (M : Q → Instr Q J) (start : Q) : Counter.Machine (State Q) (Reg J) where
  instr := compileInstr M
  start := .main start
  halt := .halt
  halt_iff q := by
    cases q with
    | main q => cases h : M q <;> simp [compileInstr, h, go]
    | grow q i => simp [compileInstr]
    | copy q r => simp [compileInstr]
    | copyInc q r => cases h : M q <;> simp [compileInstr, h, go]
    | add q i => cases h : M q <;> simp [compileInstr, h, go]; split <;> simp
    | quotient q r => cases h : M q <;> simp [compileInstr, h, go]
    | carry q => simp [compileInstr]
    | restore q => cases h : M q <;> simp [compileInstr, h, go]
    | halt => simp [compileInstr]

variable [DecidableEq J]
def cfg (s : State Q) (v : J → ℕ) (a : ℕ) : Counter.Cfg (State Q) (Reg J) :=
  ⟨s,Sum.elim v (fun b=>if b then 0 else a)⟩
def encode (c : Cfg Q J) : Counter.Cfg (State Q) (Reg J) :=
  cfg (c.label.elim .halt State.main) c.value 0
variable [DecidableEq Q]

end

section
open Counter StateTransition Relation
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
variable (M : Q → Instr Q J) (start : Q)
local notation "F" => Counter.step (compile M start)
end

open Counter StateTransition Relation
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
lemma radix_pos (b : Bool) : 0 < radix b := by cases b <;> decide
lemma radix_le (b : Bool) : radix b ≤ 5 := by cases b <;> decide
def mod5 (b : Bool) (n : ℕ) : Fin 5 := ⟨n%radix b,(Nat.mod_lt _ (radix_pos b)).trans_le (radix_le b)⟩
@[simp] lemma mod5_val (b : Bool) (n : ℕ) : (mod5 b n).val=n%radix b := rfl
variable (M : Q → Instr Q J) (start : Q)
local notation "F" => Counter.step (compile M start)
end SingleFold.Macro

namespace SingleFold.Counter
open StateTransition Relation
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
end SingleFold.Counter

end OAI


