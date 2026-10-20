-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_CounterBounds
-- name    : OAI_NumberTheory_SingleFold_CounterBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:35:25.182881+00:00
-- url     : https://prove2.me/theorems/0c418f1b-cf8f-4a17-b75c-e12154d4f3eb
-- title:
--   Indicators of a configuration and the packed trace of a run
-- statement:
--   A counter machine has finitely many states $Q$, counters $J$, a start state and a halting state. Each state carries one instruction: halt; increment counter $j$ and go to $p$; or test counter $j$, going to $p_0$ if it is $0$ and otherwise decrementing it and going to $p_d$. For a configuration $c$:
--
--   1. $\mathrm{stateAt}(c,q)=[q=c.\mathrm{state}]$. At a test state, $\mathrm{zeroAt}$ and $\mathrm{decAt}$ indicate the zero branch and the decrement branch taken. $\mathrm{arcAt}$ selects the indicator of the outgoing arc, and $\mathrm{incomingAt}(p)$ sums the arcs entering $p$.
--   2. $\mathrm{incAt}(j)$ and $\mathrm{subAt}(j)$ indicate an increment and a decrement of counter $j$.
--   3. The value of a counter at time $t$ is its value in $\mathrm{run}(d,t)$, and the clock has value $C(d)+t$.
--   4. The trace of length $T$ in base $B$ is the witness whose entries are
--   $$
--   \mathrm{pack}_B\bigl(T+1,\ t\mapsto\text{indicator or value at time }t\bigr),
--   $$
--      with $H=B^{T+1}$, $\mathrm{last}=B^T$ and $\mathrm{mask}=\sum_{t\le T}B^t$.
--
--   The trace is the canonical witness of a halting run. It is used to show that the counter system is complete.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/CounterBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/CounterBounds.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Packed
end SingleFold.Packed

namespace SingleFold.Counter
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
def stateAt (c : Cfg Q J) (q : Q) : ℕ := if q=c.state then 1 else 0
def zeroAt (M : Machine Q J) (c : Cfg Q J) (q : Q) : ℕ :=
  match M.instr q with
  | .test j _ _ => if q=c.state ∧ c.value j=0 then 1 else 0
  | _ => 0
def decAt (M : Machine Q J) (c : Cfg Q J) (q : Q) : ℕ :=
  match M.instr q with
  | .test j _ _ => if q=c.state ∧ c.value j≠0 then 1 else 0
  | _ => 0
def arcAt (M : Machine Q J) (c : Cfg Q J) (q : Q) (b : Bool) : ℕ :=
  match M.instr q,b with
  | .inc _ _,false => stateAt c q
  | .test _ _ _,false => zeroAt M c q
  | .test _ _ _,true => decAt M c q
  | _,_ => 0
variable [Fintype Q]
def incomingAt (M : Machine Q J) (c : Cfg Q J) (p : Q) : ℕ :=
  ∑q,∑b : Bool,if dest M q b=some p then arcAt M c q b else 0
def incAt (M : Machine Q J) (c : Cfg Q J) (j : J) : ℕ :=
  ∑q,match M.instr q with | .inc i _=>if i=j then stateAt c q else 0 | _=>0
def subAt (M : Machine Q J) (c : Cfg Q J) (j : J) : ℕ :=
  ∑q,match M.instr q with | .test i _ _=>if i=j then decAt M c q else 0 | _=>0
end SingleFold.Counter

namespace SingleFold.Packed
end SingleFold.Packed
namespace SingleFold.Counter
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
def valueAt (M : Machine Q J) (d : J → ℕ) (j : Option J) (t : ℕ) : ℕ :=
  match j with | none=>baseC Q d+t | some i=>(run M d t).value i

def trace (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) : Witness Q J where
  w:=w
  B:=B
  b:=b
  k:=T+1
  H:=B^(T+1)
  last:=B^T
  mask:=ones B (T+1)
  state:=fun q=>pack B (T+1) (fun t=>stateAt (run M d t) q)
  zeroBranch:=fun q=>pack B (T+1) (fun t=>zeroAt M (run M d t) q)
  decBranch:=fun q=>pack B (T+1) (fun t=>decAt M (run M d t) q)
  complement:=fun q=> match M.instr q with
    | .test _ _ _ => pack B (T+1) (fun t=>1-zeroAt M (run M d t) q)
    | _=>0
  counter:=fun j=>pack B (T+1) (valueAt M d j)
  final:=fun j=>valueAt M d j T
  rem:=fun j=>pack B T (valueAt M d j)
end SingleFold.Counter

namespace SingleFold.Packed
end SingleFold.Packed

namespace SingleFold.Counter
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
end SingleFold.Counter

end OAI


