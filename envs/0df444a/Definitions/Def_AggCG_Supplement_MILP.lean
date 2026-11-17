-- Prove2me | Definitions.Def_AggCG_Supplement_MILP
-- name    : AggCG_Supplement_MILP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:22:02.826716+00:00
-- url     : https://prove2.me/theorems/488cd59e-9795-4f6e-beba-449048aec152
-- title:
--   Mixed-binary programs and exact branch-and-bound runs
-- statement:
--   A mixed-binary linear program consists of a maximized linear objective, equality and inequality rows, variable boxes, and binary-variable flags. A branch-and-bound run performs exact LP relaxation checks, creates both children, and prunes infeasible, integral, or incumbent-dominated nodes.
--
--   The run records open, processed, and expanded nodes, the incumbent, and the number of generated nodes, including the root.
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), §E.3, pp.29–30, PDF pp.30–31; §H.1–H.2, pp.45–46, PDF pp.46–47

import Mathlib

namespace AggCG.Supplement

/-- A mixed binary linear program `max objᵀx` over variables `V` (Sharma, *Computational Complexity of
Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027
submission (manuscript sha256 f7ea0248…), §E.3, p.29, PDF p.30; §H.1, p.45, PDF p.46): linear rows
`aᵀx ≤ b` or `aᵀx = b`, a box `lo ≤ x ≤ hi`, and a flag for the binary (integer-constrained) variables.

**Formalization Note** Data are real, so the perturbed programs of Theorem E.6 are programs of this kind;
every integer-constrained variable of the paper's programs is binary with box `[0, 1]`. -/
structure MILP (V : Type) where
  /-- Objective coefficients (maximized). -/
  obj : V → ℝ
  /-- Rows `(a, isEquality, b)`. -/
  rows : List ((V → ℝ) × Bool × ℝ)
  /-- Lower bounds. -/
  lo : V → ℝ
  /-- Upper bounds. -/
  hi : V → ℝ
  /-- Binary (integer-constrained) variables. -/
  isBin : V → Bool

/-- A B&B node: the list of branching decisions from the root, `(v, false)` for the child `x_v ≤ 0`
and `(v, true)` for the child `x_v ≥ 1`. -/
abbrev BBNode (V : Type) := List (V × Bool)

namespace MILP

variable {V : Type} [Fintype V]

/-- Objective value. -/
def value (Q : MILP V) (x : V → ℝ) : ℝ := ∑ v, Q.obj v * x v

/-- The LP relaxation region of a node: box, rows and branching bounds. -/
def region (Q : MILP V) (ν : BBNode V) : Set (V → ℝ) :=
  {x | (∀ v, Q.lo v ≤ x v ∧ x v ≤ Q.hi v) ∧
    (∀ r ∈ Q.rows, if r.2.1 then ∑ v, r.1 v * x v = r.2.2 else ∑ v, r.1 v * x v ≤ r.2.2) ∧
    ∀ d ∈ ν, if d.2 then 1 ≤ x d.1 else x d.1 ≤ 0}

/-- The LP upper bound of a node (a maximum on every nonempty region used: the boxes are bounded). -/
noncomputable def lpBound (Q : MILP V) (ν : BBNode V) : ℝ := sSup (Q.value '' Q.region ν)

/-- `x` is an optimal solution of the node LP. -/
def IsLPOpt (Q : MILP V) (ν : BBNode V) (x : V → ℝ) : Prop :=
  x ∈ Q.region ν ∧ ∀ x' ∈ Q.region ν, Q.value x' ≤ Q.value x

/-- Every binary variable takes an integer value (`0` or `1`). -/
def Integral (Q : MILP V) (x : V → ℝ) : Prop := ∀ v, Q.isBin v = true → x v = 0 ∨ x v = 1

end MILP

/-- The state of an LP-based B&B search: open (generated, unprocessed) nodes, processed nodes in
processing order, the nodes branched on, the incumbent value, and the number of generated nodes. -/
structure BBState (V : Type) where
  /-- Open nodes. -/
  openNodes : List (BBNode V)
  /-- Processed nodes, in order. -/
  processed : List (BBNode V)
  /-- Nodes that were branched on, in order. -/
  expanded : List (BBNode V)
  /-- Incumbent value, if any. -/
  inc : Option ℝ
  /-- Number of generated nodes, the root included. -/
  gen : ℕ

/-- The initial state: only the root is open and generated, no incumbent (§E.3: "It begins without an
incumbent"). -/
def BBState.init (V : Type) : BBState V := ⟨[[]], [], [], none, 1⟩

/-- One step of exact LP-based B&B with no presolve, cuts or primal heuristic (§E.3, p.30; §H.1, p.45):
the node `ν` chosen by the node-selection relation `Sel` is removed from the open list and processed. It
is pruned if its LP is infeasible or its LP bound is no greater than the incumbent; if a chosen LP optimum
is integral it becomes the incumbent; otherwise a branching variable allowed by `Br` at that LP optimum is
chosen and both children are created.

**Formalization Note** The choice of the LP optimum and, where `Br` allows several, of the branching
variable is left free: the theorems quantify over every complete run. -/
inductive BBStep {V : Type} [Fintype V] [DecidableEq V] (Q : MILP V) (Sel : BBState V → BBNode V → Prop)
    (Br : BBNode V → (V → ℝ) → V → Prop) : BBState V → BBState V → Prop
  | infeasible (s : BBState V) (ν : BBNode V) :
      ν ∈ s.openNodes → Sel s ν → Q.region ν = ∅ →
      BBStep Q Sel Br s ⟨s.openNodes.erase ν, s.processed ++ [ν], s.expanded, s.inc, s.gen⟩
  | bound (s : BBState V) (ν : BBNode V) (z : ℝ) :
      ν ∈ s.openNodes → Sel s ν → (Q.region ν).Nonempty → s.inc = some z → Q.lpBound ν ≤ z →
      BBStep Q Sel Br s ⟨s.openNodes.erase ν, s.processed ++ [ν], s.expanded, s.inc, s.gen⟩
  | integral (s : BBState V) (ν : BBNode V) (x : V → ℝ) :
      ν ∈ s.openNodes → Sel s ν → (∀ z, s.inc = some z → z < Q.lpBound ν) →
      Q.IsLPOpt ν x → Q.Integral x →
      BBStep Q Sel Br s ⟨s.openNodes.erase ν, s.processed ++ [ν], s.expanded, some (Q.lpBound ν), s.gen⟩
  | branch (s : BBState V) (ν : BBNode V) (x : V → ℝ) (w : V) :
      ν ∈ s.openNodes → Sel s ν → (∀ z, s.inc = some z → z < Q.lpBound ν) →
      Q.IsLPOpt ν x → ¬ Q.Integral x → Br ν x w →
      BBStep Q Sel Br s ⟨s.openNodes.erase ν ++ [ν ++ [(w, false)], ν ++ [(w, true)]],
        s.processed ++ [ν], s.expanded ++ [ν], s.inc, s.gen + 2⟩

/-- A complete run: a chain of steps from the initial state ending with no open node. -/
def BBComplete {V : Type} [Fintype V] [DecidableEq V] (Q : MILP V) (Sel : BBState V → BBNode V → Prop)
    (Br : BBNode V → (V → ℝ) → V → Prop) (ρ : List (BBState V)) : Prop :=
  ρ.head? = some (BBState.init V) ∧ List.IsChain (BBStep Q Sel Br) ρ ∧
    ∃ s, ρ.getLast? = some s ∧ s.openNodes = []

/-- The tree size of the search: the number of generated nodes at the end of a complete run (the least
such number, should runs differ). -/
noncomputable def bbTreeSize {V : Type} [Fintype V] [DecidableEq V] (Q : MILP V) (Sel : BBState V → BBNode V → Prop)
    (Br : BBNode V → (V → ℝ) → V → Prop) : ℕ :=
  sInf {g | ∃ ρ s, BBComplete Q Sel Br ρ ∧ ρ.getLast? = some s ∧ s.gen = g}

section Controller

variable {V : Type} {T : ℕ}

/-- The continuing-spine node of stage `j`: the selectors `x_0, …, x_{j−1}` fixed to zero (§H.1, Lemma
H.1: "At the node x_1 = ⋯ = x_{j−1} = 0"). -/
def spineNode (xv : Fin (T + 1) → V) (j : ℕ) : BBNode V :=
  ((List.finRange (T + 1)).take j).map fun i => (xv i, false)

/-- The trap child `H_j` of the spine node of stage `j`: `x_j` fixed to one. -/
def trapNode (xv : Fin (T + 1) → V) (j : ℕ) : BBNode V :=
  spineNode xv j ++ (if h : j < T + 1 then [(xv ⟨j, h⟩, true)] else [])

/-- `ν` is a descendant of the trap `H_j`: further decisions on parity (`y`) variables only. -/
def IsTrapDesc (xv : Fin (T + 1) → V) (isY : V → Prop) (ν : BBNode V) : Prop :=
  ∃ j < T + 1, ∃ l : BBNode V, l ≠ [] ∧ (∀ d ∈ l, isY d.1) ∧ ν = trapNode xv j ++ l

open Classical in
/-- The current stage: the number of spine nodes already processed. -/
noncomputable def ctrlStage (xv : Fin (T + 1) → V) (s : BBState V) : ℕ :=
  ((List.range (T + 2)).filter fun j => spineNode xv j ∈ s.processed).length

open Classical in
/-- The recorded decision of stage `i`: whether the trap `H_i` was processed before its continuation
(the spine node of stage `i + 1`). -/
noncomputable def ctrlBit (xv : Fin (T + 1) → V) (s : BBState V) (i : ℕ) : Bool :=
  decide (s.processed.idxOf (trapNode xv i) < s.processed.idxOf (spineNode xv (i + 1)))

/-- The midpoint `m_j = (L + R)/2` of the dyadic interval after the recorded decisions of the stages
before `j`. -/
noncomputable def ctrlMid (xv : Fin (T + 1) → V) (s : BBState V) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, (if ctrlBit xv s i then (1 : ℝ) else 0) / 2 ^ (i + 1) + 1 / 2 ^ (j + 1)

open Classical in
/-- The two fixed node-scoring rules `(s₀, s₁)` of the Appendix H controller (§H.2, p.46; §H.3, p.46–47),
at the current stage `j = ctrlStage − 1`: the current trap `H_j` gets `(0, 1)` and its continuation
`(m_j, m_j)` for `j < T`; trap descendants get `2` until exhausted; at the final stage `j = T` the probe
trap gets `1` if the clause read from the block sizes is false on the recorded word and `−1` otherwise,
and its continuation `0`; previously deferred traps and every other node get `−3`. The predicate
`probeFalse` is the final rule's clause test on the recorded bits.

**Formalization Note** The paper fixes the values `0, 1, m_j, 2, −3` and only the order of the two
final-stage priorities ("higher priority than its continuation if and only if C(b) is false"); the values
`1`, `−1`, `0` realize that order between the deferred-trap value `−3` and the trap-descendant value `2`. -/
noncomputable def ctrlScores (xv : Fin (T + 1) → V) (isY : V → Prop)
    (probeFalse : (ℕ → Bool) → Prop) (s : BBState V) (ν : BBNode V) : ℝ × ℝ :=
  let c := ctrlStage xv s
  let j := c - 1
  if IsTrapDesc xv isY ν then (2, 2)
  else if 1 ≤ c ∧ j < T ∧ ν = trapNode xv j then (0, 1)
  else if 1 ≤ c ∧ j < T ∧ ν = spineNode xv (j + 1) then (ctrlMid xv s j, ctrlMid xv s j)
  else if 1 ≤ c ∧ j = T ∧ ν = trapNode xv T then
    (if probeFalse (ctrlBit xv s) then (1, 1) else (-1, -1))
  else if 1 ≤ c ∧ j = T ∧ ν = spineNode xv (T + 1) then (0, 0)
  else (-3, -3)

/-- The mixed score `s_θ = (1 − θ)s₀ + θ s₁`. -/
noncomputable def ctrlScore (xv : Fin (T + 1) → V) (isY : V → Prop)
    (probeFalse : (ℕ → Bool) → Prop) (θ : ℝ) (s : BBState V) (ν : BBNode V) : ℝ :=
  (1 - θ) * (ctrlScores xv isY probeFalse s ν).1 + θ * (ctrlScores xv isY probeFalse s ν).2

/-- Node selection of the controller: an open node of largest mixed score, ties resolved toward the
continuing node (§H.2: "Ties are resolved toward the continuing node"). -/
def ctrlSel (xv : Fin (T + 1) → V) (isY : V → Prop) (probeFalse : (ℕ → Bool) → Prop) (θ : ℝ)
    (s : BBState V) (ν : BBNode V) : Prop :=
  ν ∈ s.openNodes ∧ (∀ ν' ∈ s.openNodes, ctrlScore xv isY probeFalse θ s ν' ≤
      ctrlScore xv isY probeFalse θ s ν) ∧
    ∀ ν' ∈ s.openNodes, ν' = spineNode xv (ctrlStage xv s) →
      ctrlScore xv isY probeFalse θ s ν' = ctrlScore xv isY probeFalse θ s ν → ν = ν'

/-- The variable-branching rule (§E.3, p.30; §H.2, p.46): the least-indexed fractional selector if one
exists, and otherwise any fractional parity variable. -/
def ctrlBranch (xv : Fin (T + 1) → V) (isY : V → Prop) (_ν : BBNode V) (x : V → ℝ) (w : V) : Prop :=
  (∃ j : Fin (T + 1), w = xv j ∧ x (xv j) ≠ 0 ∧ x (xv j) ≠ 1 ∧
      ∀ i : Fin (T + 1), i < j → x (xv i) = 0 ∨ x (xv i) = 1) ∨
    ((∀ i : Fin (T + 1), x (xv i) = 0 ∨ x (xv i) = 1) ∧ isY w ∧ x w ≠ 0 ∧ x w ≠ 1)

end Controller

/-- The dyadic interval `[L, R]` of the controller before stage `j`, started at `[0, 1]` and moved to its
right half when `θ > m_j` and to its left half otherwise (§H.2, p.46). -/
noncomputable def dyadicLR (θ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 1)
  | j + 1 =>
    let LR := dyadicLR θ j
    let m := (LR.1 + LR.2) / 2
    if m < θ then (m, LR.2) else (LR.1, m)

/-- The induced binary word `b = B(θ)` of the dyadic controller: `b_j = 1` iff `θ > m_j = (L + R)/2`
(§H.2, p.46: "If θ > m_j, the trap is processed first"; ties go to the continuation). -/
noncomputable def dyadicWord (θ : ℝ) (j : ℕ) : Bool :=
  decide (((dyadicLR θ j).1 + (dyadicLR θ j).2) / 2 < θ)

/-- `h(k) = 2(C(k + 1, (k + 1)/2) − 1)`, i.e. `h(2r + 1) = 2(C(2r + 2, r + 1) − 1)`, the number of nodes
strictly below an odd parity trap of size `k` (eq. (13), p.45; Theorem E.6, p.29). -/
def trapCount (k : ℕ) : ℕ := 2 * ((k + 1).choose ((k + 1) / 2) - 1)

end AggCG.Supplement


