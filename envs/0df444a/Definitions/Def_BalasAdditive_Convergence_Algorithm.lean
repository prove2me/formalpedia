-- Prove2me | Definitions.Def_BalasAdditive_Convergence_Algorithm
-- name    : BalasAdditive_Convergence_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:17:36.09998+00:00
-- url     : https://prove2.me/theorems/c72325d2-0891-4ef4-b9b2-bd9c168a5d9a
-- title:
--   Balas's additive algorithm, solutions, cancellations, ceiling, and transitions
-- statement:
--   The **additive algorithm** starts with $J_0=\varnothing$ and generates a sequence $J_0,\ldots,J_s$ of binary assignments. The slacks and costs are computed from $J_p$. The **ceiling** $z^{*(s)}$ is the least cost of a feasible generated assignment, with value $+\infty$ if none has been generated.
--
--   $$z^{*(s)}=\min\{z(J_p):0\le p\le s,\ J_p\text{ feasible}\},\qquad \min\varnothing=+\infty.$$
--
--   Each generated solution retains the improving set $N_p$ formed when it was obtained. The record also retains the cancellations $C_k^s$ at that time; a separate running record holds every cancellation made so far, so during iteration $s+1$ it is $C_p^{s+1}$ as accumulated up to the current point. The sets $C^s,D_s,E_s,N_s,D_k^s,N_k^s$ implement equations (13)–(18); in particular $N_k^s=N_k-(C_k^s\cup D_k^s)$ uses the snapshot $C_k^s$ of (18). The values $v_j^p$ implement (11)–(12).
--
--   At a new solution, the transition relation applies steps 1–4: a feasible solution causes the older ceiling cancellations; an empty improving set or a failed row test starts the old-solution scan; strict row tests choose a maximum-$v$ index; equality rows form $F$, which is either added if its cost stays below the ceiling or cancelled. Step 5 scans earlier strict subsets in decreasing index order. Steps 6–7 repeat the row and ceiling tests on the first remaining improving set, adding a new assignment or cancelling that set and continuing below its index. Step 8 appends the assignment produced by a chosen index.
--
--   A value-maximizing index is chosen with minimum $c_j$ among tied maximizers. If a tie remains, every tied choice is an allowed transition. A state stops exactly when step 5 has no eligible earlier set left. Reachability means that the state follows finitely many of these transitions from the initial state; a generated solution $u^k$ ($k\le s$) is **abandoned** (p. 529) when the algorithm is instructed to stop, or to check some $N_p^s$ with $p<k$; in a step-5 scan this means that every earlier index still to be selected lies below $k$.
--
--   **Formalization Note** The paper's $N=\{1,\ldots,n\}$ and $M=\{1,\ldots,m\}$ use zero-based `Fin n` and `Fin m`. The ceiling is `WithTop ℝ`, and all comparisons to it are additive, so $+\infty$ retains its intended meaning. A generated assignment is a finite set rather than a separate $(x,y)$ pair, since equations (5)–(6) determine both vectors from it. The transition relation records the paper's nondeterministic final tie break.
-- source:
--   Balas, An additive algorithm for solving linear programs with zero-one variables, Oper. Res. 13 (1965), pp. 523–528, Eqs. (9)–(33), Steps 1–8 and Fig. 2, DOI 10.1287/opre.13.4.517

import Mathlib
import Definitions.Def_BalasAdditive_Convergence_Problem

set_option autoImplicit false

namespace BalasAdditive.Convergence

open Classical
noncomputable section

/-- One generated solution, its fixed improving set, and the cancellations recorded when it was obtained. -/
structure Record (n : ℕ) where
  J : Finset (Fin n)
  N : Finset (Fin n)
  snapshot : List (Finset (Fin n))

/-- The program is either inspecting a newly generated solution, scanning older solutions
below a bound, or has reached one of the stopping situations. -/
inductive Phase where
  | start
  | scan (bound : ℕ)
  | stopped
  deriving DecidableEq

/-- The generated records, the cancellation records (`cancelled[p]` is every `j` whose value
`v_j^p` has been cancelled so far, over all iterations), and the program point. -/
structure State (n : ℕ) where
  history : List (Record n)
  cancelled : List (Finset (Fin n))
  phase : Phase

/-- The generated set `J_p`; the default is used only for ill-formed, unreachable states. -/
def State.J {n : ℕ} (σ : State n) (p : ℕ) : Finset (Fin n) :=
  ((σ.history[p]?).map Record.J).getD ∅

/-- The improving set formed when `J_p` was first generated. -/
def State.N {n : ℕ} (σ : State n) (p : ℕ) : Finset (Fin n) :=
  ((σ.history[p]?).map Record.N).getD ∅

/-- The stored snapshot `C_p^s`, where `s` is the current iteration. -/
def State.snapshotC {n : ℕ} (σ : State n) (p : ℕ) : Finset (Fin n) :=
  (((σ.history[σ.history.length - 1]?).map Record.snapshot).getD [])[p]?.getD ∅

/-- All cancellations of values `v_j^p` made so far: during iteration `s + 1` this is the
paper's `C_p^{s+1}` as accumulated up to the current point. -/
def State.currentC {n : ℕ} (σ : State n) (p : ℕ) : Finset (Fin n) :=
  (σ.cancelled[p]?).getD ∅

/-- The current generated solution. -/
def State.latest {n : ℕ} (σ : State n) : Finset (Fin n) :=
  σ.J (σ.history.length - 1)

/-- The ceiling is the minimum cost of generated feasible solutions, or `⊤` if there are none. -/
def ceilingFrom {n m : ℕ} (P : Problem n m) (xs : List (Finset (Fin n))) : WithTop ℝ :=
  xs.foldl (fun z J => if P.lp.Feasible J then min z (↑(P.lp.cost J) : WithTop ℝ) else z) ⊤

def ceiling {n m : ℕ} (P : Problem n m) (σ : State n) : WithTop ℝ :=
  ceilingFrom P (σ.history.map Record.J)

/-- Union of cancellations inherited from strictly smaller generated assignments. -/
def inheritedC {n : ℕ} (h : List (Record n)) (cs : List (Finset (Fin n)))
    (J : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.range h.length).biUnion fun p =>
    if ((h[p]?).map Record.J).getD ∅ ⊂ J then (cs[p]?).getD ∅ else ∅

/-- The set `C^s` of (13) at the moment the current solution was obtained. -/
def State.C {n : ℕ} (σ : State n) : Finset (Fin n) :=
  inheritedC σ.history
    (((σ.history[σ.history.length - 1]?).map Record.snapshot).getD []) σ.latest

/-- Equation (16), formed once, at the moment a new solution is generated. -/
def newN {n m : ℕ} (P : Problem n m) (h : List (Record n))
    (cs : List (Finset (Fin n))) (J : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun j =>
    j ∉ inheritedC h cs J ∧
    ¬ (ceilingFrom P (h.map Record.J ++ [J]) ≤
      (↑(P.lp.cost J + P.lp.c j) : WithTop ℝ)) ∧
    ¬ (∀ i : Fin m, P.lp.slack J i < 0 → 0 ≤ P.lp.A i j)

/-- The initialization (19), including the improving set formed for `J₀ = ∅`. -/
def init {n m : ℕ} (P : Problem n m) : State n :=
  { history := [{ J := ∅, N := newN P [] [] ∅, snapshot := [∅] }]
    cancelled := [∅]
    phase := .start }

/-- Add a cancellation to one generated solution's current record. -/
def cancelAt {n : ℕ} (cs : List (Finset (Fin n))) (p : ℕ)
    (X : Finset (Fin n)) : List (Finset (Fin n)) :=
  cs.set p ((cs[p]?).getD ∅ ∪ X)

/-- The old-solution ceiling cancellation set (17), using the snapshot `C_k^s`. -/
def oldD {n m : ℕ} (P : Problem n m) (σ : State n) (k : ℕ) : Finset (Fin n) :=
  (σ.N k).filter fun j => j ∉ σ.snapshotC k ∧
    ceiling P σ ≤ (↑(P.lp.cost (σ.J k) + P.lp.c j) : WithTop ℝ)

/-- The improving indices left after iteration `s`, equation (18):
`N_k^s = N_k − (C_k^s ∪ D_k^s)`, with the snapshot `C_k^s`. -/
def oldRemaining {n m : ℕ} (P : Problem n m) (σ : State n) (k : ℕ) : Finset (Fin n) :=
  σ.N k \ (σ.snapshotC k ∪ oldD P σ k)

/-- Step 1a cancels `D_k^s` for every earlier generated solution. -/
def cancelOldD {n m : ℕ} (P : Problem n m) (σ : State n) : List (Finset (Fin n)) :=
  (Finset.range (σ.history.length - 1)).toList.foldl
    (fun cs k => cancelAt cs k (oldD P σ k)) σ.cancelled

/-- Append a new solution, snapshot all current cancellations, and form its fixed `N`. -/
def appendSolution {n m : ℕ} (P : Problem n m) (σ : State n)
    (p : ℕ) (X Y : Finset (Fin n)) : State n :=
  let cs := cancelAt σ.cancelled p Y
  let J := σ.J p ∪ X
  let r : Record n := { J := J, N := newN P σ.history cs J, snapshot := cs ++ [∅] }
  { history := σ.history ++ [r], cancelled := cs ++ [∅], phase := .start }

/-- Sum of the negative entries of a row across a candidate improving set, (22)/(27). -/
def negativeSum {n m : ℕ} (P : Problem n m) (X : Finset (Fin n)) (i : Fin m) : ℝ :=
  ∑ j ∈ X, min (P.lp.A i j) 0

def relationsHold {n m : ℕ} (P : Problem n m) (J X : Finset (Fin n)) : Prop :=
  ∀ i : Fin m, P.lp.slack J i < 0 → negativeSum P X i ≤ P.lp.slack J i

def relationsStrict {n m : ℕ} (P : Problem n m) (J X : Finset (Fin n)) : Prop :=
  ∀ i : Fin m, P.lp.slack J i < 0 → negativeSum P X i < P.lp.slack J i

/-- The set `F` from the equality rows of (22) or (27). -/
def equalityF {n m : ℕ} (P : Problem n m) (J X : Finset (Fin n)) : Finset (Fin n) :=
  X.filter fun j => ∃ i : Fin m,
    P.lp.slack J i < 0 ∧ negativeSum P X i = P.lp.slack J i ∧ P.lp.A i j < 0

/-- The value `v_j^p` of (11)–(12)/(28). -/
def choiceValue {n m : ℕ} (P : Problem n m) (J : Finset (Fin n)) (j : Fin n) : ℝ :=
  ∑ i : Fin m, min (P.lp.slack J i - P.lp.A i j) 0

/-- The maximum-value choice with minimum-cost tie break; any remaining tie is allowed. -/
def Chosen {n m : ℕ} (P : Problem n m) (J X : Finset (Fin n)) (j : Fin n) : Prop :=
  j ∈ X ∧
  (∀ q ∈ X, choiceValue P J q ≤ choiceValue P J j) ∧
  (∀ q ∈ X, choiceValue P J q = choiceValue P J j → P.lp.c j ≤ P.lp.c q)

/-- A still viable old solution in the descending scan of step 5. -/
def Candidate {n m : ℕ} (P : Problem n m) (σ : State n)
    (bound k : ℕ) : Prop :=
  k < bound ∧ σ.J k ⊂ σ.latest ∧ (oldRemaining P σ k).Nonempty

/-- The next index inspected is the largest eligible `k` below the scan bound. -/
def Selected {n m : ℕ} (P : Problem n m) (σ : State n)
    (bound k : ℕ) : Prop :=
  Candidate P σ bound k ∧ ∀ q, Candidate P σ bound q → q ≤ k

/-- The additive form of the strict ceiling tests (24) and (29). -/
def belowCeiling {n m : ℕ} (P : Problem n m) (σ : State n)
    (J X : Finset (Fin n)) : Prop :=
  (↑(P.lp.cost J + ∑ j ∈ X, P.lp.c j) : WithTop ℝ) < ceiling P σ

def beginScan {n : ℕ} (σ : State n) (cs : List (Finset (Fin n)))
    (bound : ℕ) : State n :=
  { σ with cancelled := cs, phase := .scan bound }

def stop {n : ℕ} (σ : State n) : State n :=
  { σ with phase := .stopped }

/-- The transitions of the original algorithm, grouped by the numbered situations in
pp. 525–528. Each choice in 3b/6b is nondeterministic among the printed ties. -/
inductive Step {n m : ℕ} (P : Problem n m) : State n → State n → Prop where
  | one_a (σ : State n) (hphase : σ.phase = .start)
      (hfeas : P.lp.Feasible σ.latest) :
      Step P σ (beginScan σ (cancelOldD P σ) (σ.history.length - 1))
  | two_a (σ : State n) (hphase : σ.phase = .start)
      (hbad : ¬ P.lp.Feasible σ.latest)
      (hempty : σ.N (σ.history.length - 1) = ∅) :
      Step P σ (beginScan σ σ.cancelled (σ.history.length - 1))
  | three_a (σ : State n) (hphase : σ.phase = .start)
      (hbad : ¬ P.lp.Feasible σ.latest)
      (hnonempty : (σ.N (σ.history.length - 1)).Nonempty)
      (hfail : ¬ relationsHold P σ.latest (σ.N (σ.history.length - 1))) :
      Step P σ (beginScan σ σ.cancelled (σ.history.length - 1))
  | three_b (σ : State n) (j : Fin n) (hphase : σ.phase = .start)
      (hbad : ¬ P.lp.Feasible σ.latest)
      (hnonempty : (σ.N (σ.history.length - 1)).Nonempty)
      (hstrict : relationsStrict P σ.latest (σ.N (σ.history.length - 1)))
      (hchoice : Chosen P σ.latest (σ.N (σ.history.length - 1)) j) :
      Step P σ (appendSolution P σ (σ.history.length - 1) {j} {j})
  | four_a (σ : State n) (hphase : σ.phase = .start)
      (hbad : ¬ P.lp.Feasible σ.latest)
      (hnonempty : (σ.N (σ.history.length - 1)).Nonempty)
      (hhold : relationsHold P σ.latest (σ.N (σ.history.length - 1)))
      (hnonstrict : ¬ relationsStrict P σ.latest (σ.N (σ.history.length - 1)))
      (hcost : belowCeiling P σ σ.latest
        (equalityF P σ.latest (σ.N (σ.history.length - 1)))) :
      Step P σ (appendSolution P σ (σ.history.length - 1)
        (equalityF P σ.latest (σ.N (σ.history.length - 1)))
        (equalityF P σ.latest (σ.N (σ.history.length - 1))))
  | four_b (σ : State n) (hphase : σ.phase = .start)
      (hbad : ¬ P.lp.Feasible σ.latest)
      (hnonempty : (σ.N (σ.history.length - 1)).Nonempty)
      (hhold : relationsHold P σ.latest (σ.N (σ.history.length - 1)))
      (hnonstrict : ¬ relationsStrict P σ.latest (σ.N (σ.history.length - 1)))
      (hcost : ¬ belowCeiling P σ σ.latest
        (equalityF P σ.latest (σ.N (σ.history.length - 1)))) :
      Step P σ (beginScan σ
        (cancelAt σ.cancelled (σ.history.length - 1) (σ.N (σ.history.length - 1)))
        (σ.history.length - 1))
  | five_a (σ : State n) (bound : ℕ) (hphase : σ.phase = .scan bound)
      (hnone : ¬ ∃ k, Candidate P σ bound k) :
      Step P σ (stop σ)
  | six_a (σ : State n) (bound k : ℕ) (hphase : σ.phase = .scan bound)
      (hselect : Selected P σ bound k)
      (hfail : ¬ relationsHold P (σ.J k) (oldRemaining P σ k)) :
      Step P σ (beginScan σ (cancelAt σ.cancelled k (oldRemaining P σ k)) k)
  | six_b (σ : State n) (bound k : ℕ) (j : Fin n)
      (hphase : σ.phase = .scan bound) (hselect : Selected P σ bound k)
      (hstrict : relationsStrict P (σ.J k) (oldRemaining P σ k))
      (hchoice : Chosen P (σ.J k) (oldRemaining P σ k) j) :
      Step P σ (appendSolution P σ k {j} {j})
  | seven_a (σ : State n) (bound k : ℕ)
      (hphase : σ.phase = .scan bound) (hselect : Selected P σ bound k)
      (hhold : relationsHold P (σ.J k) (oldRemaining P σ k))
      (hnonstrict : ¬ relationsStrict P (σ.J k) (oldRemaining P σ k))
      (hcost : belowCeiling P σ (σ.J k)
        (equalityF P (σ.J k) (oldRemaining P σ k))) :
      Step P σ (appendSolution P σ k
        (equalityF P (σ.J k) (oldRemaining P σ k))
        (equalityF P (σ.J k) (oldRemaining P σ k)))
  | seven_b (σ : State n) (bound k : ℕ)
      (hphase : σ.phase = .scan bound) (hselect : Selected P σ bound k)
      (hhold : relationsHold P (σ.J k) (oldRemaining P σ k))
      (hnonstrict : ¬ relationsStrict P (σ.J k) (oldRemaining P σ k))
      (hcost : ¬ belowCeiling P σ (σ.J k)
        (equalityF P (σ.J k) (oldRemaining P σ k))) :
      Step P σ (beginScan σ (cancelAt σ.cancelled k (oldRemaining P σ k)) k)

/-- Only states generated by the algorithm are within the scope of its theorems. -/
def Reachable {n m : ℕ} (P : Problem n m) (σ : State n) : Prop :=
  Relation.ReflTransGen (Step P) (init P) σ

/-- The generated solution `u^k` (`k ≤ s`) is abandoned (p. 529) when the algorithm is
instructed to stop, or to check some `N_p^s` with `p < k`. In a step-5 scan below `bound`,
the check runs down from `bound − 1` to the selected candidate, so `u^k` is abandoned
exactly when every remaining candidate lies below `k` (with no candidate the algorithm
is about to stop). -/
def Abandoned {n m : ℕ} (P : Problem n m) (σ : State n) (k : ℕ) : Prop :=
  k < σ.history.length ∧
    (σ.phase = .stopped ∨
      ∃ bound, σ.phase = .scan bound ∧ ∀ p, Candidate P σ bound p → p < k)

end
end BalasAdditive.Convergence


