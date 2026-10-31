-- Prove2me | Definitions.Def_ChenPairedDomination_Interval_MPDI
-- name    : ChenPairedDomination_Interval_MPDI
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-31T01:25:52.648651+00:00
-- url     : https://prove2.me/theorems/c7fe2be4-90b0-4494-a6c6-aebc1f1748b3
-- title:
--   Concrete MPDI execution with an operation counter
-- statement:
--   The implementation first scans each adjacency row to fill an array F with the least earlier neighbor, using the vertex itself as fallback. It initializes dominated and selected bit arrays to false and processes vertices in reverse order. A dominated vertex is skipped. Otherwise, writing k = F(i), if k differs from i and j = F(k) differs from k, it selects k and j and marks their closed neighborhoods. If k differs from i but F(k) = k, it selects i and k and marks only the closed neighborhood of k. Otherwise it selects i and index 1 (the paper’s u_2), and marks only i. A final scan materializes the selected vertices as a list; resultSet is its mathematical interpretation on Fin n.
--
--   The fixed unit-cost RAM counter includes allocation and initialization of the three arrays, F preprocessing, index reads and writes, comparisons, loop control and output collection. Every neighbor-list cons visited is charged, including repeated visits to already marked vertices. The code documents the exact primitive count for each block. Functional arrays express mutable indexed RAM tables; Lean allocation, proof checking and counter bookkeeping are outside this abstract graph-algorithm cost model. No general finite-set union or search is treated as a constant-time algorithm primitive. For valid inputs n is at least 2; the raw execution remains total outside that domain without asserting correctness there.
-- source:
--   Chen, Lu and Zeng, arXiv:0802.2742v1 (2008), https://arxiv.org/abs/0802.2742v1, §3, Algorithm MPDI, pp. 12–13; Theorem 10, p. 13

import Definitions.Def_ChenPairedDomination_Interval_AdjacencyList

namespace ChenPairedDomination.Interval

/-- State of MPDI in an indexed unit-cost RAM model. Arrays denote mutable indexed tables.
The counter charges reads/writes, comparisons, control and index arithmetic; it does not
model Lean allocation, proof checking, or the bookkeeping of the counter itself. -/
structure MPDIState where
  dominated : Array Bool
  selected : Array Bool
  cost : ℕ
  deriving Repr

/-- One earlier-neighbor scan. Each cons step charges cursor test/read/advance (3),
the earlier-index comparison (1), and, when earlier, a minimum comparison (1)
and a replacement assignment if necessary (1). The terminal test costs 1. -/
def scanFirst (i : ℕ) : List ℕ → ℕ → ℕ × ℕ
  | [], best => (best, 1)
  | k :: ks, best =>
    let next := if k < i then min best k else best
    let charge := if k < i then (if k < best then 6 else 5) else 4
    let r := scanFirst i ks next
    (r.1, charge + r.2)

/-- Fill entries 0 through r-1. Per vertex: loop test/increment (2), row read (1),
initial best assignment (1), father-table write (1). Terminal test costs 1. -/
def prepareAux (rows : Array (List ℕ)) : ℕ → Array ℕ → Array ℕ × ℕ
  | 0, father => (father, 1)
  | r + 1, father =>
    let prev := prepareAux rows r father
    let found := scanFirst r rows[r]! r
    (prev.1.set! r found.1, prev.2 + found.2 + 5)

/-- Father preprocessing includes allocation and initialization of all n cells. -/
def prepare (n : ℕ) (rows : Array (List ℕ)) : Array ℕ × ℕ :=
  let p := prepareAux rows n (Array.replicate n 0)
  (p.1, n + 1 + p.2)

/-- Mark every listed neighbor; repeated visits remain charged. Each cons costs
cursor test/read/advance (3) and one label write (1); final test costs 1. -/
def markNeighbors : List ℕ → MPDIState → MPDIState
  | [], s => { s with cost := s.cost + 1 }
  | v :: vs, s => markNeighbors vs
      { s with dominated := s.dominated.set! v true, cost := s.cost + 4 }

/-- A closed-neighborhood update charges its own label write and adjacency row read. -/
def markClosed (rows : Array (List ℕ)) (v : ℕ) (s : MPDIState) : MPDIState :=
  markNeighbors rows[v]! { s with dominated := s.dominated.set! v true, cost := s.cost + 2 }

/-- Two selected-bit writes: set insertion does not perform a linear membership search. -/
def selectPair (v w : ℕ) (s : MPDIState) : MPDIState :=
  { s with selected := (s.selected.set! v true).set! w true, cost := s.cost + 2 }

/-- Exactly the three printed branches. The second branch marks only N[F(i)];
the last branch selects index 1 (u_2) and marks only i. -/
def mpdiStep (rows : Array (List ℕ)) (father : Array ℕ) (i : ℕ)
    (s : MPDIState) : MPDIState :=
  let s := { s with cost := s.cost + 2 } -- D read and branch test
  if s.dominated[i]! then s else
    let k := father[i]!
    let s := { s with cost := s.cost + 2 } -- F read and k != i comparison
    if k != i then
      let j := father[k]!
      let s := { s with cost := s.cost + 2 } -- F read and j != k comparison
      if j != k then
        markClosed rows j (markClosed rows k (selectPair k j s))
      else
        markClosed rows k (selectPair i k s)
    else
      let s := selectPair i 1 s
      { s with dominated := s.dominated.set! i true, cost := s.cost + 1 }

/-- Reverse loop n-1,...,0. Each iteration charges loop test and decrement;
the terminal test is charged as well. -/
def mpdiLoop (rows : Array (List ℕ)) (father : Array ℕ) : ℕ → MPDIState → MPDIState
  | 0, s => { s with cost := s.cost + 1 }
  | r + 1, s => mpdiLoop rows father r
      (mpdiStep rows father r { s with cost := s.cost + 2 })

/-- Output scan, n-1,...,0, consing selected vertices. Each iteration charges
loop test/decrement (2), selected-bit read/test (2), and a cons write when selected (1).
The terminal test costs 1. -/
def collectSelected (selected : Array Bool) : ℕ → List ℕ → List ℕ × ℕ
  | 0, acc => (acc, 1)
  | r + 1, acc =>
    let chosen := selected[r]!
    let out := collectSelected selected r (if chosen then r :: acc else acc)
    (out.1, out.2 + if chosen then 5 else 4)

structure MPDIResult where
  output : List ℕ
  cost : ℕ
  deriving Repr

/-- The complete execution: F preprocessing, two zero bit arrays, reverse loop,
and materialized output. The two array allocations and n writes each cost 2n+2. -/
def runMPDI (n : ℕ) (rows : Array (List ℕ)) : MPDIResult :=
  let p := prepare n rows
  let s := mpdiLoop rows p.1 n
    ⟨Array.replicate n false, Array.replicate n false, p.2 + 2 * n + 2⟩
  let out := collectSelected s.selected n []
  ⟨out.1, s.cost + out.2 + 1⟩ -- final return

/-- Mathematical decoding of the already materialized result, not an extra algorithm step. -/
def resultSet (n : ℕ) (r : MPDIResult) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v.val ∈ r.output)

end ChenPairedDomination.Interval


