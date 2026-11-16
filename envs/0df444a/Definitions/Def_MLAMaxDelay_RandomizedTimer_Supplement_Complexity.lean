-- Prove2me | Definitions.Def_MLAMaxDelay_RandomizedTimer_Supplement_Complexity
-- name    : MLAMaxDelay_RandomizedTimer_Supplement_Complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:50:22.637872+00:00
-- url     : https://prove2.me/theorems/1ef32127-2110-42f9-945c-c35b669ecb57
-- title:
--   Step-counted Algorithm 1 in the unit-cost arithmetic model
-- statement:
--   The proof of Theorem 3.3 analyses Algorithm 1 in the **unit-cost arithmetic model**. This definition writes Algorithm 1 (p. 5, lines 1–19) as an explicit program on the published tick-counting monad `Timed`, whose value is the program's result and whose cost is the number of unit steps executed.
--
--   1. One tick is charged for each real arithmetic operation, each comparison, and each read, write, insertion or membership test of a finite structure (a list entry, a marked-vertex set).
--   2. A loop over a list charges every iteration: the cost of its body plus one tick.
--   3. Line 1 reads the $N$ request occurrences, sorts them by arrival time by a charged insertion sort, and identifies the distinct arrival times $a_1<\dots<a_n$ and the request lists $R_i$ by one charged scan.
--   4. For each endpoint $j$, lines 7–11 scan $p=j,j-1,\dots,1$, adding the root paths of the requests of $R_p$ to a marked rooted union $U$: each path is walked toward the root one vertex at a time until it meets $U$, and each newly marked vertex adds its parent-edge weight, so $w(U)=C(p,j)$.
--   5. Line 12 tests the $j$ predecessors with recurrence (1), keeping the first strict minimiser, and stores $F(j)$ and $p^*_j$.
--   6. Lines 14–18 backtrack from $j=n$, prepending $(a_j,U(R[p,j]))$; the footprint of the recovered interval is rebuilt by charged root-path walks.
--
--   The returned value is $(F(n),S)$, or $(0,\emptyset)$ when there are no requests.
--
--   **Formalization Note** No cost is a closed-form formula: every tick comes from a primitive inside the program's own loops. Root-path walks use the fuel $|V|$, which bounds the length of every root path.
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 5, Algorithm 1; p. 7, proof of Theorem 3.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Offline
import Definitions.Def_MITMSynthesis_Timed

namespace MLAMaxDelay.RandomizedTimer.Supplement

open MITMSynthesis

/-! Theorem 3.3, p. 7: the unit-cost arithmetic model of its proof, on the published
tick-counting monad `Timed`. One tick is charged for every real arithmetic operation, every
comparison, and every read, write, insertion or membership test of a finite structure. Loops
charge every iteration (one tick per iteration plus the body). No cost is a closed-form formula:
every tick comes from a primitive inside the program's own loops. -/

/-- One unit-cost primitive step returning `a`. -/
def op {α : Type} (a : α) : Timed α := ⟨a, 1⟩

/-- A sequential loop over a list: every iteration charges its body plus one loop tick. -/
def foldC {α β : Type} (f : β → α → Timed β) : List α → β → Timed β
  | [], b => pure b
  | a :: as, b => do
      let b' ← f b a
      let _ ← op ()
      foldC f as b'

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Insertion of a request label into a list sorted by arrival time; one comparison and one
list write per visited position. -/
noncomputable def insertByArrivalC (I : Input V) (r : ℕ) : List ℕ → Timed (List ℕ)
  | [] => op [r]
  | s :: rest => by
      classical
      exact do
        let le ← op (decide (I.arrival r ≤ I.arrival s))
        if le then op (r :: s :: rest) else do
          let tl ← insertByArrivalC I r rest
          op (s :: tl)

/-- Line 1, first half: read the request occurrences (one tick each) and sort them by
arrival time with charged comparisons. -/
noncomputable def sortRequestsC (I : Input V) : Timed (List ℕ) :=
  foldC (fun acc r => do
      let r' ← op r
      insertByArrivalC I r' acc)
    (I.requests.sort (· ≤ ·)) []

/-- A charged list reversal. -/
def reverseC {α : Type} (l : List α) : Timed (List α) :=
  foldC (fun acc x => op (x :: acc)) l []

/-- Line 1, second half: identify the distinct arrival times `a₁ < ⋯ < aₙ` and the request
lists `Rᵢ` by one charged scan of the sorted list. Entry `i` (zero-based) is `(aᵢ₊₁, Rᵢ₊₁)`. -/
noncomputable def groupEpochsC (I : Input V) (sorted : List ℕ) : Timed (List (ℝ × List ℕ)) := by
  classical
  exact do
    let rev ← foldC (fun (acc : List (ℝ × List ℕ)) r =>
        match acc with
        | [] => do
            let a ← op (I.arrival r)
            op [(a, [r])]
        | (a, rs) :: rest => do
            let ar ← op (I.arrival r)
            let same ← op (decide (ar = a))
            if same then op ((a, r :: rs) :: rest)
            else op ((ar, [r]) :: (a, rs) :: rest))
      sorted []
    reverseC rev

/-- Lines 9 and 17: walk the root path of `v` toward the root until it meets the marked
rooted union `U`, marking each new vertex and adding its parent-edge weight. One membership
test per visited vertex, one insertion and one addition per newly marked vertex. The fuel
`Fintype.card V` bounds the length of every root path. -/
noncomputable def markPathC (T : WeightedTree V) : ℕ → V → Finset V × ℝ → Timed (Finset V × ℝ)
  | 0, _, s => pure s
  | fuel + 1, v, (U, w) => do
      let mem ← op (decide (v ∈ U))
      if mem then pure (U, w) else do
        let U' ← op (insert v U)
        let wv ← op (T.weight v)
        let w' ← op (w + wv)
        markPathC T fuel (T.parent v) (U', w')

/-- Add the root paths of all requests of one epoch list to the marked union. -/
noncomputable def addEpochC (T : WeightedTree V) (I : Input V) (rs : List ℕ)
    (st : Finset V × ℝ) : Timed (Finset V × ℝ) :=
  foldC (fun st r => do
      let v ← op (I.location r)
      markPathC T (Fintype.card V) v st)
    rs st

/-- Lines 7–11 for the (one-based) endpoint `j`: scan `p = j, j-1, …, 1` maintaining the
rooted union `U(R[p,j])` and record `C(p,j) = w(U)`. The result lists `C(p,j)` for zero-based
`p = 0, …, j-1` (that is, source `p = 1, …, j`). -/
noncomputable def intervalCostsC (T : WeightedTree V) (I : Input V)
    (groups : List (ℝ × List ℕ)) (j : ℕ) : Timed (List ℝ) := do
  let st ← foldC (fun (st : Finset V × ℝ × List ℝ) p => do
      let g ← op ((groups[p]?.getD (0, [])).2)
      let uw ← addEpochC T I g (st.1, st.2.1)
      let cs ← op (uw.2 :: st.2.2)
      pure (uw.1, uw.2, cs))
    (List.range j).reverse ({T.root}, 0, [])
  pure st.2.2

/-- Line 12 for the endpoint `j`: test the `j` predecessors in increasing order with recurrence
(1), keeping the first strict minimizer. Returns `(F(j), p*_j)` with the zero-based predecessor
(the source's `p*_j - 1`). -/
noncomputable def bestC (groups : List (ℝ × List ℕ)) (F : List ℝ) (Cs : List ℝ) (j : ℕ) :
    Timed (ℝ × ℕ) := by
  classical
  exact do
    let aj ← op ((groups[j - 1]?.getD (0, [])).1)
    let cand : ℕ → Timed ℝ := fun p => do
      let fp ← op (F[p]?.getD 0)
      let cp ← op (Cs[p]?.getD 0)
      let ap ← op ((groups[p]?.getD (0, [])).1)
      let s1 ← op (fp + cp)
      let s2 ← op (s1 + aj)
      op (s2 - ap)
    let c0 ← cand 0
    foldC (fun (best : ℝ × ℕ) p => do
        let c ← cand p
        let lt ← op (decide (c < best.1))
        if lt then pure (c, p) else pure best)
      (List.range j) (c0, 0)

/-- Lines 5–13: fill the table `F(0), …, F(n)` and the minimizing predecessors. -/
noncomputable def fillTableC (T : WeightedTree V) (I : Input V) (groups : List (ℝ × List ℕ)) :
    Timed (List ℝ × List ℕ) :=
  foldC (fun (tab : List ℝ × List ℕ) j => do
      let Cs ← intervalCostsC T I groups j
      let fp ← bestC groups tab.1 Cs j
      let F' ← op (tab.1 ++ [fp.1])
      let P' ← op (tab.2 ++ [fp.2])
      pure (F', P'))
    (List.range' 1 groups.length) ([0], [0])

/-- Lines 14–18: backtrack from `j = n`, prepending `(aⱼ, U(R[p,j]))`; the rooted footprint of
the recovered interval is rebuilt by charged root-path walks. The fuel bounds the number of
backtracking steps. -/
noncomputable def backtrackC (T : WeightedTree V) (I : Input V) (groups : List (ℝ × List ℕ))
    (pred : List ℕ) : ℕ → ℕ → Schedule V → Timed (Schedule V)
  | 0, _, S => pure S
  | fuel + 1, j, S => by
      classical
      exact do
        let pos ← op (decide (1 ≤ j))
        if pos then do
          let p ← op (pred[j]?.getD 0)
          let a ← op ((groups[j - 1]?.getD (0, [])).1)
          let uw ← foldC (fun st q => do
              let g ← op ((groups[q]?.getD (0, [])).2)
              addEpochC T I g st)
            (List.range' p (j - p)) ({T.root}, 0)
          let S' ← op ((a, uw.1) :: S)
          backtrackC T I groups pred fuel p S'
        else pure S

/-- Algorithm 1, p. 5, lines 1–19, as an explicit step-counted program. Its value is the pair
returned on line 3 or line 19; its cost is the number of unit-cost steps executed. -/
noncomputable def offlineProgram (T : WeightedTree V) (I : Input V) :
    Timed (ℝ × Schedule V) := by
  classical
  exact do
  let sorted ← sortRequestsC I
  let groups ← groupEpochsC I sorted
  let empty ← op (decide (groups = []))
  if empty then op (0, []) else do
    let tab ← fillTableC T I groups
    let n ← op groups.length
    let S ← backtrackC T I groups tab.2 (n + 1) n []
    let Fn ← op (tab.1[n]?.getD 0)
    op (Fn, S)

end MLAMaxDelay.RandomizedTimer.Supplement


