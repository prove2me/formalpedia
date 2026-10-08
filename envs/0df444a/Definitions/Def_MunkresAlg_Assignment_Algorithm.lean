-- Prove2me | Definitions.Def_MunkresAlg_Assignment_Algorithm
-- name    : MunkresAlg_Assignment_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:09:21.017142+00:00
-- url     : https://prove2.me/theorems/c443ceac-10b6-4c89-bc6e-b9de43c67c00
-- title:
--   §1, pp. 33–34 — Munkres' assignment algorithm as a nondeterministic transition system: Preliminaries, Steps 1–3
-- statement:
--   This module encodes the assignment algorithm of §1 of Munkres' paper (pp. 33–34) as a transition system on states, with every choice the paper leaves free kept free.
--
--   A **state** consists of the current real $n\times n$ matrix, a set of **starred zeros** ($0^*$), a set of **primed zeros** ($0'$), a set of **covered rows**, a set of **covered columns**, and a **phase**: Step 1, Step 2 (remembering the primed zero $Z_0$ just found), Step 3, or done. A position $(i,j)$ is **non-covered** if neither row $i$ nor column $j$ is covered.
--
--   **Preliminaries** (p. 33). From the input matrix $A$, subtract from each row its smallest element and then from each column of the result its smallest entry; call the result $A_1$. Then consider the positions in some order, in turn: a zero of $A_1$ is starred if there is no starred zero in its row and none in its column. Cover every column containing a starred zero. A **start state** for $A$ is the state so obtained, for any order of the zeros, with no primes and no covered rows, followed by the test below.
--
--   **Test** (end of Step 2, p. 34). If all columns are covered the algorithm stops (phase done); otherwise it goes to Step 1.
--
--   The **moves** are:
--
--   1. *Step 1, no star in the row.* Choose any non-covered zero $p$ whose row contains no starred zero; prime it and go to Step 2 with $Z_0=p$.
--   2. *Step 1, a star in the row.* Choose any non-covered zero $p$ whose row contains a starred zero $Z$; prime $p$, cover the row of $p$, and uncover the column of $Z$.
--   3. *Step 1, all zeros covered.* If there is no non-covered zero, go to Step 3.
--   4. *Step 2.* Let $Z_0,Z_1,\dots,Z_{2k}$ be a sequence starting at $Z_0$ in which each $Z_{2i+1}$ is a starred zero in the column of $Z_{2i}$, each $Z_{2i+2}$ is a primed zero in the row of $Z_{2i+1}$, and the last element $Z_{2k}$ has no starred zero in its column. Unstar each starred zero of the sequence and star each primed zero of the sequence; erase all primes, uncover every row, cover every column containing a starred zero, and apply the test.
--   5. *Step 3.* Let $h$ be the smallest non-covered element of the matrix. Add $h$ to each covered row, subtract $h$ from each uncovered column, and return to Step 1 without altering any stars, primes or covered lines.
--
--   A state is **reachable** from $A$ if some run of moves leads to it from some start state for $A$. A **Step 1 move** is a move made from a state in phase Step 1.
--
--   This module is the object of every result of the mission: the paper's correctness proof consists of claims about reachable states and runs of this system.
--
--   **Formalization Note** The moves form an inductive relation `Step`, not a function: which non-covered zero is primed, and the order in which the Preliminaries consider the zeros, are arbitrary, as on the page. Step 2's sequence and Step 3's $h$ are described relationally (no existence is built in); that they exist, and that $h>0$, are theorems of the mission. The test "if all columns are covered" is also applied when leaving the Preliminaries, where the page goes to Step 1 unconditionally; without it a run whose Preliminaries already star $n$ zeros would reach Step 3 with no non-covered element and be stuck. The row reduction uses `Finset.inf'` with the index in scope as nonemptiness witness, so it is defined for every $n$, including $n=0$.
-- source:
--   Munkres, Algorithms for the assignment and transportation problems, J. SIAM 5 (1957), pp. 33–34, §1 (Preliminaries, Steps 1–3)

import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic

namespace MunkresAlg.Assignment

open Classical

/-- The control point of the algorithm of §1 (pp. 33–34). `step2 z₀` remembers the primed zero
`Z₀` just found by Step 1 in a row containing no starred zero. -/
inductive Phase (n : ℕ) where
  | step1
  | step2 (z₀ : Fin n × Fin n)
  | step3
  | done
  deriving DecidableEq

/-- A state of the algorithm: the current matrix, the starred zeros, the primed zeros, the
covered rows and covered columns, and the phase. -/
structure State (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  starred : Finset (Fin n × Fin n)
  primed : Finset (Fin n × Fin n)
  rowCov : Finset (Fin n)
  colCov : Finset (Fin n)
  phase : Phase n

/-- Preliminaries, p. 33: subtract from each element of each row the smallest element of
that row. -/
def rowReduce {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A i j - Finset.univ.inf' ⟨j, Finset.mem_univ j⟩ (A i)

/-- Preliminaries, p. 33: subtract from each column its smallest entry. -/
def colReduce {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => B i j - Finset.univ.inf' ⟨i, Finset.mem_univ i⟩ (fun i' => B i' j)

/-- The matrix produced by the Preliminaries: rows reduced first, then columns. -/
def prelimMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  colReduce (rowReduce A)

/-- Preliminaries, p. 33: the greedy starring, considering the positions of the list `L` in
turn. A position `z` is starred when it is a zero of `B` and there is no starred zero in its
row and none in its column. -/
noncomputable def greedyStar {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (L : List (Fin n × Fin n)) : Finset (Fin n × Fin n) :=
  L.foldl (fun S z => if B z.1 z.2 = 0 ∧ ∀ q ∈ S, q.1 ≠ z.1 ∧ q.2 ≠ z.2 then insert z S else S) ∅

/-- The columns containing a position of `S`. -/
def colsOf {n : ℕ} (S : Finset (Fin n × Fin n)) : Finset (Fin n) :=
  S.image Prod.snd

/-- The test at the end of Step 2 (p. 34): if all columns are covered the algorithm stops
(`done`), otherwise it goes to Step 1. It is also applied when leaving the Preliminaries. -/
def enterStep1 {n : ℕ} (s : State n) : State n :=
  if s.colCov = Finset.univ then { s with phase := Phase.done } else { s with phase := Phase.step1 }

/-- `s` is a state in which the algorithm may begin Step 1 (or stop) after the Preliminaries
applied to `A`, for some order `L` in which the zeros are considered. -/
def IsStart {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n) : Prop :=
  ∃ L : List (Fin n × Fin n), L.Nodup ∧ (∀ i j, prelimMatrix A i j = 0 → (i, j) ∈ L) ∧
    s = enterStep1
      { A := prelimMatrix A
        starred := greedyStar (prelimMatrix A) L
        primed := ∅
        rowCov := ∅
        colCov := colsOf (greedyStar (prelimMatrix A) L)
        phase := Phase.step1 }

/-- A position is non-covered if neither its row nor its column is covered. -/
def NonCovered {n : ℕ} (s : State n) (p : Fin n × Fin n) : Prop :=
  p.1 ∉ s.rowCov ∧ p.2 ∉ s.colCov

/-- Step 2, p. 34: `zs = [Z₀, Z₁, …, Z₂ₖ]` is a sequence of alternating starred and primed zeros
starting at `z₀`: each `Z₂ᵢ₊₁` is a starred zero in the column of `Z₂ᵢ`, each `Z₂ᵢ₊₂` is a
primed zero in the row of `Z₂ᵢ₊₁`, the sequence has odd length, and its last element has no
starred zero in its column. -/
def IsStep2Seq {n : ℕ} (s : State n) (z₀ : Fin n × Fin n) (zs : List (Fin n × Fin n)) : Prop :=
  zs.head? = some z₀ ∧ zs.length % 2 = 1 ∧
  (∀ i (h : 2 * i + 1 < zs.length),
      zs[2 * i + 1] ∈ s.starred ∧ zs[2 * i + 1].2 = zs[2 * i].2) ∧
  (∀ i (h : 2 * i + 2 < zs.length),
      zs[2 * i + 2] ∈ s.primed ∧ zs[2 * i + 2].1 = zs[2 * i + 1].1) ∧
  (∀ z ∈ zs.getLast?, ∀ q ∈ s.starred, q.2 ≠ z.2)

/-- The marks after Step 2's exchange (p. 34): each starred zero of the sequence is unstarred and
each primed zero of the sequence is starred; all primes are erased, every row is uncovered, and
every column containing a starred zero is covered. -/
def augmentState {n : ℕ} (s : State n) (zs : List (Fin n × Fin n)) : State n :=
  let S' := (s.starred \ zs.toFinset) ∪ (s.primed ∩ zs.toFinset)
  { s with starred := S', primed := ∅, rowCov := ∅, colCov := colsOf S' }

/-- One move of the algorithm of §1, pp. 33–34. The choices left free by the paper (which
non-covered zero to prime) are nondeterministic. -/
inductive Step {n : ℕ} : State n → State n → Prop
  /-- Step 1, a non-covered zero with no starred zero in its row: prime it, go to Step 2. -/
  | prime_go2 (s : State n) (p : Fin n × Fin n)
      (hphase : s.phase = Phase.step1) (hzero : s.A p.1 p.2 = 0) (hnc : NonCovered s p)
      (hnostar : ∀ q ∈ s.starred, q.1 ≠ p.1) :
      Step s { s with primed := insert p s.primed, phase := Phase.step2 p }
  /-- Step 1, a non-covered zero with a starred zero `z` in its row: prime it, cover this row
  and uncover the column of `z`. -/
  | prime_cover (s : State n) (p z : Fin n × Fin n)
      (hphase : s.phase = Phase.step1) (hzero : s.A p.1 p.2 = 0) (hnc : NonCovered s p)
      (hz : z ∈ s.starred) (hrow : z.1 = p.1) :
      Step s { s with primed := insert p s.primed, rowCov := insert p.1 s.rowCov,
                      colCov := s.colCov.erase z.2 }
  /-- Step 1, all zeros covered: go to Step 3. -/
  | to_step3 (s : State n) (hphase : s.phase = Phase.step1)
      (hnone : ∀ p : Fin n × Fin n, NonCovered s p → s.A p.1 p.2 ≠ 0) :
      Step s { s with phase := Phase.step3 }
  /-- Step 2: exchange stars and primes along the sequence, reset the marks, and stop or
  return to Step 1. -/
  | augment (s : State n) (z₀ : Fin n × Fin n) (zs : List (Fin n × Fin n))
      (hphase : s.phase = Phase.step2 z₀) (hseq : IsStep2Seq s z₀ zs) :
      Step s (enterStep1 (augmentState s zs))
  /-- Step 3: with `h` the smallest non-covered element, add `h` to each covered row and
  subtract `h` from each uncovered column; return to Step 1 with all marks unchanged. -/
  | reduce (s : State n) (h : ℝ) (hphase : s.phase = Phase.step3)
      (hmin : ∃ p, NonCovered s p ∧ s.A p.1 p.2 = h)
      (hle : ∀ q, NonCovered s q → h ≤ s.A q.1 q.2) :
      Step s { s with
        A := fun i j => s.A i j + (if i ∈ s.rowCov then h else 0) - (if j ∈ s.colCov then 0 else h)
        phase := Phase.step1 }

/-- A move made inside Step 1 (from a state in phase `step1`). -/
def Step1Move {n : ℕ} (u v : State n) : Prop :=
  Step u v ∧ u.phase = Phase.step1

/-- `s` is reachable by some run of the algorithm on the input matrix `A`. -/
def Reachable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n) : Prop :=
  ∃ s₀, IsStart A s₀ ∧ Relation.ReflTransGen Step s₀ s

end MunkresAlg.Assignment


