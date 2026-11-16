-- Prove2me | Definitions.Def_DecrAlmostLinearSSSP_Decremental_Supplement_Execution
-- name    : DecrAlmostLinearSSSP_Decremental_Supplement_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:14:28.275205+00:00
-- url     : https://prove2.me/theorems/12a12487-bb9c-4c44-848c-b2eceb13e394
-- title:
--   Online incremental calls with charged scalar execution
-- statement:
--   A program is a finite list of the published scalar arithmetic-machine instructions, with initialization, update and query entry points. Its memory starts at zero except for the initial graph input tape. Initialization receives $n,m,s,W,\epsilon$ and the initial edge list. Each later insertion supplies only its identifier, endpoints, weight and, for the black-box reduction, the current report batch. The total eventual edge count and future edge data are absent from the input tape.
--
--   Writing $c_t$ for the completed machine after $t$ insertions, the execution relation requires
--
--   $$
--   c_0=\operatorname{execute}(p,\operatorname{init}(E_0)),\qquad
--   c_{t+1}=\operatorname{execute}(p,\operatorname{insert}(c_t,e_{t+1},B_{t+1})),
--   $$
--
--   with successful termination of every call. The equalities abbreviate finite iteration of the actual instruction transition, not an assumed algorithm evaluation. Each instruction increases the machine work counter by one. The budget also charges 32 units per call or initially delivered edge and per delivered report; these conservative interface charges are representation choices, absorbed into the uniform operation constant. Report computation itself is external only in the standalone reduction.
--
--   Input tape cells occupy a separate strided bank from persistent work cells and the explicit output array. Call-entry registers are fresh scratch registers with fixed headers, so persistent data lives in memory. This protocol permits arbitrary prefixes without exposing future updates and supplies a shared notion of charged maintenance work.
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), pp.1, 18, 21, 31–36, unit-cost arithmetic and completed-batch query convention

import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Supplement_Input
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Machine

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental.Supplement

/-- A report is a vertex identifier and its new finite oracle estimate. -/
abbrev Report (i : Instance) := Fin i.n × ℝ

/-- Input cells are n+2+2j; other cells are preserved work memory. Two output ports are n,n+1.
The environment supplies a finite input tape. Every delivered scalar is also charged below. -/
def inputAddress (n a : ℕ) : Bool := decide (n + 2 ≤ a ∧ (a - (n + 2)) % 2 = 0)

def replaceTape (n : ℕ) (old tape : ℕ → ℕ) : ℕ → ℕ :=
  fun a => if inputAddress n a then tape ((a - (n + 2)) / 2) else old a

def replaceRealTape (n : ℕ) (old tape : ℕ → ℝ) : ℕ → ℝ :=
  fun a => if inputAddress n a then tape ((a - (n + 2)) / 2) else old a

/-- The two output ports are scratch cells, reset at every public entry point. -/
def clearPorts (i : Instance) (c : Machine) : Machine :=
  {c with natMem := Function.update (Function.update c.natMem i.n 0) (i.n + 1) 0}

/-- n,m,initial-count,s occupy natural registers 0..3; accuracy,W occupy real 0..1.
Initial edge j supplies its identifier, tail and head in natural input cells 3j..3j+2,
and its real weight in real input cell j. No k or future edge data is supplied. -/
def start (p : Program) (i : Instance) : Machine where
  pc := p.initPC
  realReg := fun r => if r = 0 then i.accuracy else if r = 1 then i.W else 0
  natReg := fun r => if r = 0 then i.n else if r = 1 then i.size
    else if r = 2 then i.initial.length else if r = 3 then i.source.val else 0
  realMem := replaceRealTape i.n (fun _ => 0) (fun j =>
    match i.initial[j]? with | none => 0 | some e => i.weight e)
  natMem := replaceTape i.n (fun _ => 0) (fun j =>
    match i.initial[j / 3]? with
    | none => 0
    | some e => if j % 3 = 0 then e.val else if j % 3 = 1 then (i.graph.tail e).val
      else (i.graph.head e).val)
  halted := false
  fault := false
  work := 0

/-- Only the current edge and one batch of current reports become available. The caller sets
registers 4..7 to id,tail,head,report-count and real register 2 to the edge weight. -/
def insertCall (p : Program) (i : Instance) (c : Machine) (e : Fin i.k)
    (reports : List (Report i)) : Machine :=
  {resume (clearPorts i c) p.update with
    natReg := fun r => if r = 0 then i.n else if r = 1 then i.size
      else if r = 2 then i.initial.length else if r = 3 then i.source.val
      else if r = 4 then e.val else if r = 5 then (i.graph.tail e).val
      else if r = 6 then (i.graph.head e).val else if r = 7 then reports.length else 0
    realReg := fun r => if r = 0 then i.accuracy else if r = 1 then i.W
      else if r = 2 then i.weight e else 0
    natMem := replaceTape i.n (clearPorts i c).natMem (fun j =>
      match reports[j]? with | none => 0 | some q => q.1.val)
    realMem := replaceRealTape i.n c.realMem (fun j =>
      match reports[j]? with | none => 0 | some q => q.2)}

/-- Exactly one initialization and one completed call per insertion. `batches j` is delivered
after the j-th insertion (numbering starts at one). No future batch is visible. -/
inductive Run (p : Program) (i : Instance) (batches : ℕ → List (Report i)) :
    List (Fin i.k) → List Machine → Prop
  | init {c : Machine} (h : Ends p (start p i) c) : Run p i batches [] [c]
  | next {es : List (Fin i.k)} {cs : List Machine} {c d : Machine}
      (h : Run p i batches es cs) (hlast : cs.getLast? = some c) (e : Fin i.k)
      (hd : Ends p (insertCall p i c e (batches (es.length + 1))) d) :
      Run p i batches (es ++ [e]) (cs ++ [d])

/-- Conservative constant charge for call setup and delivered input scalars, including reports.
All internal loads, stores, arithmetic and report processing are already counted by `step`. -/
def deliveryWork (i : Instance) (batches : ℕ → List (Report i)) (t : ℕ) : ℕ :=
  32 * (1 + i.initial.length + t +
    ((List.range t).map (fun j => (batches (j + 1)).length)).sum)

def WithinBudget (i : Instance) (batches : ℕ → List (Report i))
    (es : List (Fin i.k)) (cs : List Machine) (budget : ℝ) : Prop :=
  ∀ c, cs.getLast? = some c → ((c.work + deliveryWork i batches es.length : ℕ) : ℝ) ≤ budget

end DecrAlmostLinearSSSP.Decremental.Supplement


