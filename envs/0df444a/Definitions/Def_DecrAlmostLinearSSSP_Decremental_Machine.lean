-- Prove2me | Definitions.Def_DecrAlmostLinearSSSP_Decremental_Machine
-- name    : DecrAlmostLinearSSSP_Decremental_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:49:46.249206+00:00
-- url     : https://prove2.me/theorems/34d81719-6c4e-46ed-8c1c-7b277b1f0464
-- title:
--   Finite deterministic arithmetic RAM, online calls and charged work
-- statement:
--   A deterministic program is finite scalar code acting on real and natural registers and two memory banks. Instructions charge one unit for rational constants, casts, arithmetic, logarithms, integer indexing arithmetic, indirect scalar loads and stores, comparisons, branches and halting. Natural registers supply addresses; real-to-integer conversion and arbitrary mathematical function evaluation are absent. A configuration records the program counter, registers, memory, fault and halt flags, and accumulated work.
--
--   The initial input supplies only the graph, source, weight and size bounds and accuracy. Each subsequent call supplies only the currently deleted identifier. A successful call is a finite sequence of actual instruction transitions ending without fault. The output uses one infinity flag and one real memory cell per vertex. The predicate for maintaining distances concludes simultaneous accuracy, exact reachability, termination at every completed prefix and read-only constant-work queries. For overhead $a(m)>0$,
--
--   $$\frac{\log a(m)}{\log\max(2,m)}\longrightarrow0,$$
--
--   and the total maintenance bound is $Cma(m)\epsilon^{-1}\max(1,\log_2W)$, or $Cma(m)\epsilon^{-1}$ in the polynomial-weight case. All request setup, initialization, output writes and query instructions are charged; the standard initial input tape is supplied before execution.
--
--   This provides operational meaning to the complexity clauses, without assuming an accurate answer array or a cost certificate. **Formalization Note** Logarithm is an explicitly named scalar primitive needed for the paper's parameter formulas; ceilings are implemented through comparisons rather than a rounding primitive. The unnamed model of Theorem 1.1 is read consistently with the unit-cost arithmetic model explicitly named in Lemma 4.1.
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), p. 3, Theorem 1.1; p. 4, Preliminaries; p. 18, Lemma 4.1 (computational-model reading); pinned PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf

import Mathlib
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Graph

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental

/-- Scalar arithmetic RAM. A finite code contains only rational real constants. Natural
registers are for addresses and indices; no real-to-integer or arbitrary-function primitive. -/
inductive Instruction
  | rational (d : ℕ) (q : ℚ)
  | natural (d a : ℕ)
  | cast (d a : ℕ)
  | add (d a b : ℕ)
  | sub (d a b : ℕ)
  | mul (d a b : ℕ)
  | div (d a b : ℕ)
  | log (d a : ℕ)
  | nadd (d a b : ℕ)
  | nsub (d a b : ℕ)
  | load (d a : ℕ)
  | store (a d : ℕ)
  | loadN (d a : ℕ)
  | storeN (a d : ℕ)
  | jump (pc : ℕ)
  | less (a b pc : ℕ)
  | lessN (a b pc : ℕ)
  | halt

structure Machine where
  pc : ℕ
  realReg : ℕ → ℝ
  natReg : ℕ → ℕ
  realMem : ℕ → ℝ
  natMem : ℕ → ℕ
  halted : Bool
  fault : Bool
  work : ℕ

structure Program where
  code : List Instruction
  initPC : ℕ
  update : ℕ
  query : ℕ

noncomputable def step (p : Program) (c : Machine) : Machine := by
  classical
  exact if c.halted then c else
    let d := {c with pc := c.pc + 1, work := c.work + 1}
    match p.code[c.pc]? with
    | none => {d with halted := true, fault := true}
    | some ins => match ins with
      | .rational a q => {d with realReg := Function.update c.realReg a (q : ℝ)}
      | .natural a b => {d with natReg := Function.update c.natReg a b}
      | .cast a b => {d with realReg := Function.update c.realReg a (c.natReg b : ℝ)}
      | .add a b e => {d with realReg := Function.update c.realReg a (c.realReg b + c.realReg e)}
      | .sub a b e => {d with realReg := Function.update c.realReg a (c.realReg b - c.realReg e)}
      | .mul a b e => {d with realReg := Function.update c.realReg a (c.realReg b * c.realReg e)}
      | .div a b e => {d with realReg := Function.update c.realReg a (c.realReg b / c.realReg e)}
      | .log a b => {d with realReg := Function.update c.realReg a (Real.log (c.realReg b))}
      | .nadd a b e => {d with natReg := Function.update c.natReg a (c.natReg b + c.natReg e)}
      | .nsub a b e => {d with natReg := Function.update c.natReg a (c.natReg b - c.natReg e)}
      | .load a b => {d with realReg := Function.update c.realReg a (c.realMem (c.natReg b))}
      | .store a b => {d with realMem := Function.update c.realMem (c.natReg a) (c.realReg b)}
      | .loadN a b => {d with natReg := Function.update c.natReg a (c.natMem (c.natReg b))}
      | .storeN a b => {d with natMem := Function.update c.natMem (c.natReg a) (c.natReg b)}
      | .jump t => {d with pc := t}
      | .less a b t => if c.realReg a < c.realReg b then {d with pc := t} else d
      | .lessN a b t => if c.natReg a < c.natReg b then {d with pc := t} else d
      | .halt => {d with halted := true}

noncomputable def execute (p : Program) (c : Machine) (t : ℕ) : Machine := (step p)^[t] c

def resume (c : Machine) (entry : ℕ) : Machine :=
  {c with pc := entry, halted := false, fault := false}

def Ends (p : Program) (c d : Machine) : Prop :=
  ∃ t, execute p c t = d ∧ d.halted = true ∧ d.fault = false

/-- Input layout: n,k,m,W,s in natural registers 0..4; accuracy in real register 0.
Input edge e occupies memory 3e,3e+1,3e+2 (tail,head,weight). Output cell v is
natural flag v (1 means infinity) and real value v, in disjoint memory banks.
Input edges are in natural memory after n; their initialization is the standard free input tape. -/
def initialMachine (p : Program) (i : Input) : Machine where
  pc := p.initPC
  realReg := fun j => if j = 0 then i.accuracy else 0
  natReg := fun j => if j = 0 then i.n else if j = 1 then i.k else if j = 2 then i.size
    else if j = 3 then i.W else if j = 4 then i.source.val else 0
  realMem := fun _ => 0
  natMem := fun j => if h : i.n ≤ j ∧ (j - i.n) / 3 < i.k then
    let e : Fin i.k := ⟨(j - i.n) / 3, h.2⟩
    if (j - i.n) % 3 = 0 then (i.graph.tail e).val
    else if (j - i.n) % 3 = 1 then (i.graph.head e).val else i.weight e
    else 0
  halted := false
  fault := false
  work := 0

/-- Only the current deletion identifier is supplied, never future updates. -/
def deletionMachine (p : Program) (c : Machine) (e : ℕ) : Machine :=
  {resume c p.update with natReg := Function.update c.natReg 5 e}

noncomputable def stored (c : Machine) (v : ℕ) : ℝ≥0∞ :=
  if c.natMem v = 1 then ⊤ else ENNReal.ofReal (c.realMem v)

/-- One call for initialization, then one call per deletion. `Ends` counts actual instructions. -/
inductive OnlineRun (p : Program) (i : Input) : List (Fin i.k) → List Machine → Prop
  | init {c : Machine} (h : Ends p (initialMachine p i) c) : OnlineRun p i [] [c]
  | next {ds : List (Fin i.k)} {cs : List Machine} {c d : Machine}
      (h : OnlineRun p i ds cs) (hlast : cs.getLast? = some c) (e : Fin i.k)
      (hd : Ends p (deletionMachine p c e.val) d) : OnlineRun p i (ds ++ [e]) (cs ++ [d])

noncomputable def logarithm2 (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- All sizes use max(2,m); convergence excludes finite-size logarithm defaults. -/
def Subpolynomial (a : ℕ → ℝ) : Prop :=
  (∀ m, 0 < a m) ∧ Filter.Tendsto (fun m => Real.log (a m) / Real.log (max 2 m : ℕ))
    Filter.atTop (nhds 0)

/-- Uniform correctness, termination and charged maintenance work for a whole legal stream.
All completed prefixes, including initialization, have simultaneous accuracy and exact infinity. -/
def Maintains (p : Program) (C : ℝ) (a : ℕ → ℝ) (queryBound : ℕ) (logWeights : Bool) (i : Input) : Prop :=
  ∀ ds : List (Fin i.k), Legal ds → ∃ cs : List Machine,
    OnlineRun p i ds cs ∧ cs.length = ds.length + 1 ∧
    (∀ j (c : Machine), cs[j]? = some c →
      stored c i.source.val = 0 ∧
      (∀ v : Fin i.n, c.natMem v.val ≤ 1 ∧ (c.natMem v.val = 0 → 0 ≤ c.realMem v.val)) ∧
      ∀ v : Fin i.n, i.dist (ds.take j) v ≤ stored c v.val ∧
        stored c v.val ≤ ENNReal.ofReal (1 + i.accuracy) * i.dist (ds.take j) v ∧
        (stored c v.val = ⊤ ↔ ¬ Reachable i.graph (live (ds.take j)) i.source v)) ∧
    (∀ c, cs.getLast? = some c → ((c.work + 6 * ds.length : ℕ) : ℝ) ≤
      C * i.size * a i.size / i.accuracy *
        (if logWeights then max 1 (logarithm2 i.W) else 1)) ∧
    (∀ c ∈ cs, ∀ v : Fin i.n,
      ∃ d, Ends p {resume c p.query with natReg := Function.update c.natReg 5 v.val} d ∧
        d.work + 6 ≤ c.work + queryBound ∧
        d.natReg 6 = c.natMem v.val ∧ d.realReg 1 = c.realMem v.val ∧
        d.realMem = c.realMem ∧ d.natMem = c.natMem)

end DecrAlmostLinearSSSP.Decremental


