-- Prove2me | Definitions.Def_EnvyFreeCake104_Divide_Query
-- name    : EnvyFreeCake104_Divide_Query
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:00:35.853087+00:00
-- url     : https://prove2.me/theorems/7432eb6a-c780-4a84-ab6d-8070f5e0cae9
-- title:
--   Robertson–Webb oracle programs, choice oracles, recorded values and prefix cuts
-- statement:
--   A **protocol** is a program that interacts with the valuations only through the two **Robertson–Webb queries**: $\mathrm{Eval}_i([a,b))$ returns $V_i([a,b))$, and $\mathrm{Cut}_i(x,w)$ returns the smallest $x'\in[x,1]$ with $V_i([x,x'])=w$. A program may also **fail**, or make a **free choice** among finitely many options. Running a program answers every query truthfully and resolves every free choice by a **choice oracle**: an arbitrary function of the transcript so far. The **number of queries** of a run is the number of Eval and Cut events in its transcript.
--
--   The program keeps the paper's **recorded values** in its own state: a finite set of points containing $0$ and $1$ and every Cut point returned so far, and, for each agent and each cell $[c,c^+)$ between consecutive points, a recorded value. The records are **valid** for a set $N$ of agents when the points lie in $[0,1]$ and every recorded value of an agent of $N$ is her true value of the cell; a piece is **aligned** when all its endpoints are recorded points. Initially the only cell is $[0,1]$, which every agent values at $1$; this costs no query.
--
--   A **prefix cut** on a piece $P$ for agent $i$ and value $w$ returns the end position of the *smallest* prefix of $P$ worth exactly $w$ to $i$. It locates, by recorded values, the interval and then the cell where that prefix ends; asks one $\mathrm{Cut}_i$ query inside that cell; and, if the returned point is new, asks one $\mathrm{Eval}_j$ query per participating agent $j$ for one part of the split cell, the other part following by subtraction. So a prefix cut costs at most $n+1$ queries. A zero value removes nothing and asks nothing. A counter in the state counts prefix cuts.
--
--   This is the query model in which the paper's bounds are stated.
--
--   **Formalization Note** Programs form a free monad with constructors for the two queries, a choice among $m+1$ options and failure; protocols are state transformers over it, with the record table as state. The Cut answer is defined as an infimum; on every query the protocols issue under valid records the set is nonempty and closed, so the infimum is the minimum.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.1, 4, §1 (Robertson–Webb model), §1.3 (Recorded values; prefix cuts)

import Definitions.Def_EnvyFreeCake104_Divide_Model

set_option autoImplicit false

namespace EnvyFreeCake104.Divide

open scoped Classical

/-! # The Robertson–Webb query model with recorded values

Source: p.1 (Eval and Cut queries) and §1.3, p.4 ("Recorded values").

A protocol is a program over an oracle interface with exactly two queries, `eval i a b` and
`cut i x w`, plus a nondeterministic `choose` among finitely many options and `fail`. A program
never receives the valuations: it learns about them only through the answers. Running a
program interprets `eval` and `cut` with the true Eval and Cut answers, and `choose` with an
arbitrary *choice oracle*; the number of queries of a run is the number of `eval` and `cut`
events in its transcript. -/

/-- Programs over the Robertson–Webb oracle, returning a value of type `α`. -/
inductive Prog (ι : Type) (α : Type) : Type where
  /-- Stop with a result. -/
  | ret (x : α) : Prog ι α
  /-- Stop without a result (an impossible step was reached). -/
  | fail : Prog ι α
  /-- `Eval_i([a,b))`, continuing with its answer. -/
  | eval (i : ι) (a b : ℝ) (k : ℝ → Prog ι α) : Prog ι α
  /-- `Cut_i(x, w)`, continuing with its answer. -/
  | cut (i : ι) (x w : ℝ) (k : ℝ → Prog ι α) : Prog ι α
  /-- A free choice among `m + 1` options, resolved by the choice oracle. -/
  | choose (m : ℕ) (k : Fin (m + 1) → Prog ι α) : Prog ι α

namespace Prog

variable {ι : Type}

/-- Sequential composition. -/
def bind {α β : Type} : Prog ι α → (α → Prog ι β) → Prog ι β
  | ret x, f => f x
  | fail, _ => fail
  | eval i a b k, f => eval i a b (fun r => bind (k r) f)
  | cut i x w k, f => cut i x w (fun r => bind (k r) f)
  | choose m k, f => choose m (fun c => bind (k c) f)

instance : Monad (Prog ι) where
  pure := ret
  bind := bind

end Prog

/-- One event of a run's transcript: an Eval query, a Cut query (with its answer), or a
resolved choice. -/
inductive Event (ι : Type) : Type where
  | eval (i : ι) (a b answer : ℝ) : Event ι
  | cut (i : ι) (x w answer : ℝ) : Event ι
  | choice (m : ℕ) (c : ℕ) : Event ι

/-- `true` exactly for the two Robertson–Webb queries. -/
def Event.isQuery {ι : Type} : Event ι → Bool
  | .eval .. => true
  | .cut .. => true
  | .choice .. => false

/-- A choice oracle: given the transcript so far, resolves a choice among `m + 1` options.
Theorems quantify over **every** choice oracle, so they hold for every resolution of the
protocol's free choices, which may depend adaptively on everything seen so far. -/
def ChoiceOracle (ι : Type) : Type := List (Event ι) → (m : ℕ) → Fin (m + 1)

/-- The answer to `Eval_i([a,b))`: `V_i([a,b))` (p.1). -/
noncomputable def evalAnswer {ι : Type} (V : ι → Valuation) (i : ι) (a b : ℝ) : ℝ :=
  (V i).value (Set.Ico a b)

/-- The answer to `Cut_i(x, w)`: the smallest `x' ∈ [x,1]` with `V_i([x,x']) = w` (p.1). On a
valid query (`x ∈ [0,1]`, `0 ≤ w ≤ V_i([x,1])`) this minimum exists. -/
noncomputable def cutAnswer {ι : Type} (V : ι → Valuation) (i : ι) (x w : ℝ) : ℝ :=
  sInf {y : ℝ | y ∈ Set.Icc x 1 ∧ (V i).value (Set.Icc x y) = w}

/-- Running a program against the true valuations `V` and a choice oracle `o`, appending to
the transcript `tr`. Returns `none` iff the program reaches `fail`. -/
noncomputable def Prog.run {ι α : Type} (V : ι → Valuation) (o : ChoiceOracle ι) :
    Prog ι α → List (Event ι) → Option (α × List (Event ι))
  | .ret x, tr => some (x, tr)
  | .fail, _ => none
  | .eval i a b k, tr =>
      Prog.run V o (k (evalAnswer V i a b)) (tr ++ [Event.eval i a b (evalAnswer V i a b)])
  | .cut i x w k, tr =>
      Prog.run V o (k (cutAnswer V i x w)) (tr ++ [Event.cut i x w (cutAnswer V i x w)])
  | .choose m k, tr =>
      Prog.run V o (k (o tr m)) (tr ++ [Event.choice m (o tr m)])

/-- The number of Robertson–Webb queries (Eval and Cut) in a transcript. -/
def queryCount {ι : Type} (tr : List (Event ι)) : ℕ := tr.countP Event.isQuery

/-! ## Recorded values (§1.3) -/

/-- The protocol's own bookkeeping state. `pts` holds `0`, `1` and every Cut point returned
so far; the cells are the intervals between consecutive points. `val i c` is agent `i`'s
recorded value of the cell starting at the point `c`. `prefixCuts` counts prefix cuts. -/
structure Rec (ι : Type) where
  pts : Finset ℝ
  val : ι → ℝ → ℝ
  prefixCuts : ℕ

variable {ι : Type}

/-- The point of `pts` following `c` (or `c` itself if there is none). -/
noncomputable def Rec.nextPt (s : Rec ι) (c : ℝ) : ℝ :=
  if h : (s.pts.filter (fun d => c < d)).Nonempty then (s.pts.filter (fun d => c < d)).min' h
  else c

/-- Recorded value of an interval: the sum of the recorded values of the cells it contains. -/
noncomputable def Rec.intervalVal (s : Rec ι) (i : ι) (I : Interval) : ℝ :=
  ∑ c ∈ s.pts.filter (fun c => I.a ≤ c ∧ c < I.b), s.val i c

/-- Recorded value of a piece (a sum of recorded cell values; costs no query, §1.3). -/
noncomputable def Rec.pieceVal (s : Rec ι) (i : ι) (P : Piece) : ℝ :=
  (P.map (s.intervalVal i)).sum

/-- The §1.3 invariant for the participating agents `N`: `0, 1 ∈ pts ⊆ [0,1]`, and every
participating agent's recorded value of every cell `[c, c⁺)` is her true value. -/
def Rec.Valid (V : ι → Valuation) (N : Finset ι) (s : Rec ι) : Prop :=
  (0 : ℝ) ∈ s.pts ∧ (1 : ℝ) ∈ s.pts ∧ (∀ c ∈ s.pts, 0 ≤ c ∧ c ≤ 1) ∧
    ∀ i ∈ N, ∀ c ∈ s.pts, c < 1 → s.val i c = (V i).value (Set.Ico c (s.nextPt c))

/-- §1.3: "every piece our protocols handle is a union of intervals in the partition
determined by 0, 1, and all previously returned Cut points": every endpoint is recorded. -/
def Rec.Aligned (s : Rec ι) (P : Piece) : Prop :=
  ∀ I ∈ P, I.a ∈ s.pts ∧ I.b ∈ s.pts

/-- The initial records of the top-level call: the single cell `[0,1]`, which every agent
values at `1` (normalization), recorded at no query cost (§1.3). -/
noncomputable def initRec (ι : Type) : Rec ι where
  pts := {0, 1}
  val := fun _ c => if c = 0 then 1 else 0
  prefixCuts := 0

/-! ## Protocol monad and primitive operations -/

/-- Protocols: programs with the record table as their own state. -/
abbrev Proto (ι : Type) (α : Type) : Type := StateT (Rec ι) (Prog ι) α

/-- Issue `Eval_i([a,b))`. -/
def evalQ (i : ι) (a b : ℝ) : Proto ι ℝ := StateT.lift (Prog.eval i a b Prog.ret)

/-- Issue `Cut_i(x, w)`. -/
def cutQ (i : ι) (x w : ℝ) : Proto ι ℝ := StateT.lift (Prog.cut i x w Prog.ret)

/-- Abort. -/
def failP {α : Type} : Proto ι α := StateT.lift Prog.fail

/-- A free choice of one element of a list, resolved by the choice oracle; fails if the list
is empty (no admissible option). -/
def chooseP {β : Type} : List β → Proto ι β
  | [] => failP
  | b :: bs => StateT.lift (Prog.choose bs.length (fun c => Prog.ret ((b :: bs).get c)))

/-- Running a protocol from the record state `s` with an empty transcript: the result, the
final record state and the transcript. -/
noncomputable def exec {α : Type} (V : ι → Valuation) (o : ChoiceOracle ι) (m : Proto ι α)
    (s : Rec ι) : Option (α × Rec ι × List (Event ι)) :=
  match Prog.run V o (m.run s) [] with
  | some ((x, s'), tr) => some (x, s', tr)
  | none => none

/-! ## Prefix cuts compiled into oracle calls (§1.3) -/

/-- First interval (0-based index `k`) whose recorded value brings the cumulative value to at
least `w`, with the remaining value `w - (value of intervals 0..k-1)`. -/
noncomputable def findInterval (s : Rec ι) (i : ι) : List Interval → ℕ → ℝ → Option (ℕ × ℝ)
  | [], _, _ => none
  | I :: rest, k, w =>
      if w ≤ s.intervalVal i I then some (k, w) else findInterval s i rest (k + 1) (w - s.intervalVal i I)

/-- First cell (by its starting point, cells in left-to-right order) whose recorded value
brings the cumulative value to at least `w`, with the remaining value. -/
noncomputable def findCell (s : Rec ι) (i : ι) : List ℝ → ℝ → Option (ℝ × ℝ)
  | [], _ => none
  | c :: rest, w => if w ≤ s.val i c then some (c, w) else findCell s i rest (w - s.val i c)

/-- Record a new cut point `y` strictly inside the cell `[c, c⁺)`: one Eval query per
participating agent gives the value of `[c, y)`, and subtraction gives that of `[y, c⁺)`. -/
noncomputable def splitCell (N : Finset ι) (c y : ℝ) : Proto ι Unit := do
  for j in N.toList do
    let r ← evalQ j c y
    modify fun s => { s with
      val := fun j' x => if j' = j then (if x = c then r else if x = y then s.val j c - r
        else s.val j x) else s.val j' x }
  modify fun s => { s with pts := insert y s.pts }

/-- A prefix cut on the piece `P` for agent `i` and value `w` (§1.3): finds the **smallest**
prefix of `P` worth exactly `w` to `i` and returns its end position. The interval and the cell
containing the end are located with recorded values; then one Cut query inside that cell finds
the end point, and, if it is a new point, one Eval query per participating agent records the
split. A zero value removes nothing and issues no query. Fails only if `w` exceeds the
recorded value of `P`. A returned position past the last interval (only for `P = []`) denotes
the whole piece as prefix and the empty suffix. -/
noncomputable def prefixCut (N : Finset ι) (i : ι) (P : Piece) (w : ℝ) : Proto ι Pos := do
  modify fun s => { s with prefixCuts := s.prefixCuts + 1 }
  let s ← get
  match findInterval s i P 0 w with
  | none =>
    -- only reachable for the empty list: a zero-value cut of `[]` removes nothing
    if w ≤ 0 then return (P.length, 0) else failP
  | some (k, w') =>
    let I := P.getD k default
    if w' ≤ 0 then
      return (k, I.a)
    else
      let cells := (s.pts.filter (fun c => I.a ≤ c ∧ c < I.b)).sort (· ≤ ·)
      match findCell s i cells w' with
      | none => failP
      | some (c, w'') =>
        let y ← cutQ i c w''
        if c < y ∧ y < s.nextPt c then splitCell N c y
        return (k, y)

end EnvyFreeCake104.Divide


