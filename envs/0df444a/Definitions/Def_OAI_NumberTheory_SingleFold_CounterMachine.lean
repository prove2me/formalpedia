-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_CounterMachine
-- name    : OAI_NumberTheory_SingleFold_CounterMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:34:14.711488+00:00
-- url     : https://prove2.me/theorems/2e3de401-bd87-4550-b547-6efada7655e6
-- title:
--   Counter machines and their arithmetized halting witnesses
-- statement:
--   A counter machine has finitely many states $Q$, counters $J$, a start state and a halting state. Each state carries one instruction: halt; increment counter $j$ and go to $p$; or test counter $j$, going to $p_0$ if it is $0$ and otherwise decrementing it and going to $p_d$.
--
--   1. **Runs.** A configuration is a state and a vector of counter values. One step executes the instruction of the current state (halt leaves the configuration unchanged), and $\mathrm{run}(d,t)$ is the configuration after $t$ steps from the start state with input $d$. The machine halts at time $T$ if $T$ is the first time it is in the halting state.
--   2. **Witnesses.** A witness consists of numbers $w,B,b,k,H,\mathrm{last},\mathrm{mask}$ and, per state or counter, packed indicator sequences (state occupancy, zero branch, decrement branch, complement) and packed counter values with final values and remainders. An extra clock counter is included. Let $C(d)=1+|Q|+\sum_jd_j$.
--   3. **The system.** It requires $B=2^w=4b$, $2C(d)<B$, $k>0$, $H=B^k=B\cdot\mathrm{last}$ and $(B-1)\mathrm{mask}=H-1$. The state indicators partition $\mathrm{mask}$, and the branch indicators split the states. The state sequence satisfies the transition law
--   $$
--   \mathrm{state}_q=[q=\text{start}]+B\cdot\mathrm{incoming}_q ,
--   $$
--      each counter is updated by its increments and decrements, the zero tests are digit dominations, and the clock and scale bounds hold.
--
--   A solution of the system is a base-$B$ packing of a halting run. Each condition is a polynomial equation or a binary domination.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/CounterMachine.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/CounterMachine.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Counter

section
inductive Instr (Q J : Type)
  | halt
  | inc (j : J) (p : Q)
  | test (j : J) (pzero pdec : Q)
  deriving DecidableEq

structure Machine (Q J : Type) where
  instr : Q → Instr Q J
  start : Q
  halt : Q
  halt_iff : ∀q,instr q=Instr.halt ↔ q=halt

structure Cfg (Q J : Type) where
  state : Q
  value : J → ℕ

variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
def next (M : Machine Q J) (c : Cfg Q J) : Cfg Q J :=
  match M.instr c.state with
  | .halt => c
  | .inc j p => ⟨p,Function.update c.value j (c.value j+1)⟩
  | .test j p0 pd => if c.value j=0 then ⟨p0,c.value⟩ else ⟨pd,Function.update c.value j (c.value j-1)⟩
def run (M : Machine Q J) (d : J → ℕ) (t : ℕ) : Cfg Q J := (next M)^[t] ⟨M.start,d⟩
omit [DecidableEq Q] in
@[simp] lemma run_zero (M : Machine Q J) (d : J → ℕ) : run M d 0=⟨M.start,d⟩ := rfl
def HaltsAt (M : Machine Q J) (d : J → ℕ) (T : ℕ) : Prop :=
  (run M d T).state=M.halt ∧ ∀t < T,(run M d t).state≠M.halt
def Halts (M : Machine Q J) (d : J → ℕ) : Prop := ∃T,HaltsAt M d T
def dest (M : Machine Q J) (q : Q) (b : Bool) : Option Q :=
  match M.instr q,b with
  | .inc _ p,false => some p
  | .test _ p0 _,false => some p0
  | .test _ _ pd,true => some pd
  | _,_ => none

structure Witness (Q J : Type) where
  w : ℕ
  B : ℕ
  b : ℕ
  k : ℕ
  H : ℕ
  last : ℕ
  mask : ℕ
  state : Q → ℕ
  zeroBranch : Q → ℕ
  decBranch : Q → ℕ
  complement : Q → ℕ
  counter : Option J → ℕ
  final : Option J → ℕ
  rem : Option J → ℕ

variable [Fintype Q] [Fintype J]
def baseC (Q : Type) [Fintype Q] (d : J → ℕ) : ℕ := 1+Fintype.card Q+∑j,d j

def arc (M : Machine Q J) (v : Witness Q J) (q : Q) (b : Bool) : ℕ :=
  match M.instr q,b with
  | .inc _ _,false => v.state q
  | .test _ _ _,false => v.zeroBranch q
  | .test _ _ _,true => v.decBranch q
  | _,_ => 0

def incoming (M : Machine Q J) (v : Witness Q J) (p : Q) : ℕ :=
  ∑q,∑b : Bool,if dest M q b=some p then arc M v q b else 0

def increments (M : Machine Q J) (v : Witness Q J) (j : J) : ℕ :=
  ∑q, match M.instr q with | .inc i _ => if i=j then v.state q else 0 | _ => 0

def decrements (M : Machine Q J) (v : Witness Q J) (j : J) : ℕ :=
  ∑q, match M.instr q with | .test i _ _ => if i=j then v.decBranch q else 0 | _ => 0

def Bits (x y : ℕ) : Prop := ∀i, x/2^i%2 ≤ y/2^i%2

structure System (M : Machine Q J) (d : J → ℕ) (v : Witness Q J) : Prop where
  power : v.B=2^v.w
  base : v.B=4*v.b
  bound : 2*baseC Q d < v.B
  length : 0 < v.k
  full : v.H=v.B^v.k
  last : v.B*v.last=v.H
  mask : (v.B-1)*v.mask=v.H-1
  state_bits : ∀q,Bits (v.state q) v.mask
  partition : (∑q,v.state q)=v.mask
  branch : ∀q,match M.instr q with
    | .test _ _ _ => Bits (v.zeroBranch q) (v.state q) ∧ Bits (v.decBranch q) (v.state q) ∧
        v.zeroBranch q+v.decBranch q=v.state q ∧ v.zeroBranch q+v.complement q=v.mask
    | _ => v.zeroBranch q=0 ∧ v.decBranch q=0 ∧ v.complement q=0
  transition : ∀q,v.state q=(if q=M.start then 1 else 0)+v.B*incoming M v q
  counter : ∀j,Bits (v.counter j) ((2*v.b-1)*v.mask) ∧ v.counter j=v.final j*v.last+v.rem j ∧ v.rem j < v.last
  update : ∀j,v.counter (some j)+v.B*decrements M v j=d j+v.B*(v.rem (some j)+increments M v j)
  zero_test : ∀q,match M.instr q with | .test j _ _ => Bits (v.counter (some j)) ((v.B-1)*v.complement q) | _ => True
  clock : v.counter none+v.B*v.last=baseC Q d+v.B*(v.rem none+v.mask)
  scale_lower : v.b ≤ v.final none
  scale_upper : 2*v.final none < v.B
end

open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
namespace System

section
variable (h : System M d v)
include h
end

section
variable (h : System M d v)
include h
end

variable (h : System M d v)
include h
def selected (P : Q → Bool → Prop) [DecidableRel P] : ℕ := ∑q,∑b : Bool,if P q b then arc M v q b else 0
end System
end SingleFold.Counter

end OAI


