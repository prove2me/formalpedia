-- Prove2me | Definitions.Def_NearLinearRSP_TwoResources_Supplement_Outer
-- name    : NearLinearRSP_TwoResources_Supplement_Outer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:20:58.464983+00:00
-- url     : https://prove2.me/theorems/4091da02-13c6-42a1-91d9-9a902a24ca38
-- title:
--   Zero-resource branches, geometric guesses and all-target answer selection
-- statement:
--   Let $a$ and $b$ be the smallest and largest original positive objective lengths. For $\delta=\varepsilon/4$, the positive guesses are
--   $$
--   L_j=a(1+\delta)^j,
--   $$
--   through the first guess at least $nb$. If there are no positive lengths, there are no positive guesses. Zero-budget resource edges are removed first. When positive-budget resources remain, the first call uses their clocks on the zero-length subgraph, retaining a zero-increment objective clock with threshold one. Further calls use the positive guesses on the full filtered graph. When no positive budgets remain, ordinary deterministic Dijkstra on the filtered graph supplies exact objective distances and parent paths.
--
--   The source answer is always distance zero with path $[s]$. Every other target selects the first accepted call, with the zero-length call first. A selected zero-length call reports distance zero; a positive call reports $(1+\delta)L_j$. The same call's deterministic retrieval supplies its path. If there is no accepted call, the answer is absent. No exact infeasibility test is built into that convention.
--
--   All loops are finite definitions; success is not assumed. The logarithm in the semantic recursion fuel for the guess list is not an instruction or advice supplied to the program: an implementation must reach the stopping threshold by charged multiplication and comparison. In particular, multiple positive budgets on the zero-length subgraph still use the multidimensional computation.
-- source:
--   Vikrant Ashvinkumar, STOC 2027 submission #289 (October 2026), p.3 zero-weight convention; outer framework pp.4,6,9; retrieval pp.10–12; k-resource extension Appendix B p.14

import Definitions.Def_NearLinearRSP_TwoResources_Supplement_Retrieval

set_option autoImplicit false

namespace NearLinearRSP.TwoResources.Supplement

structure ShortestCell where
  distance : Option ℝ
  parent : Option ℕ

structure ShortestState where
  cells : ℕ → ShortestCell
  queue : List ℕ

/-- None is infinity; no real supremum or default-zero optimum is used. -/
noncomputable def distanceLess (x y : Option ℝ) : Bool :=
  match x, y with
  | none, _ => false
  | some _, none => true
  | some a, some b => decide (a < b)

noncomputable def relaxShortest {k : ℕ} (I : MultiInstance k) (u : ℕ)
    (S : ShortestState) (e : ℕ × ℕ) : ShortestState :=
  if e.1 = u ∧ e.2 ∈ S.queue then
    match (S.cells u).distance with
    | none => S
    | some d =>
      let b := d + (I.length e.1 e.2 : ℝ)
      if distanceLess (some b) (S.cells e.2).distance then
        { S with cells := Function.update S.cells e.2 ⟨some b, some u⟩ }
      else S
  else S

noncomputable def popShortest {k : ℕ} (I : MultiInstance k) (S : ShortestState) : ShortestState :=
  match S.queue with
  | [] => S
  | v :: _ =>
    let u := S.queue.foldl (fun x y =>
      if distanceLess (S.cells y).distance (S.cells x).distance then y else x) v
    (usableEdges I).foldl (relaxShortest I u) { S with queue := S.queue.erase u }

/-- Ordinary Dijkstra is used only after every constrained budget is zero. -/
noncomputable def shortestTree {k : ℕ} (I : MultiInstance k) : ℕ → ShortestCell :=
  ((List.range (incidentVertices I).length).foldl (fun S _ => popShortest I S)
    ⟨(fun v => ⟨if v = I.source then some 0 else none, none⟩), incidentVertices I⟩).cells

def followParents (s : ℕ) (T : ℕ → ShortestCell) : ℕ → ℕ → Option (List ℕ)
  | 0, _ => none
  | fuel + 1, v =>
    if v = s then some [s] else
      match (T v).parent with
      | none => none
      | some u => (followParents s T fuel u).map (fun P => P ++ [v])

noncomputable def shortestPath {k : ℕ} (I : MultiInstance k) (t : ℕ) : Option (List ℕ) :=
  if ((shortestTree I t).distance).isSome then
    followParents I.source (shortestTree I) ((incidentVertices I).length + 1) t
  else none

/-- Stop through the first geometric threshold at least n*b. The logarithm below
only supplies semantic recursion fuel, not a machine primitive or input advice. -/
noncomputable def guessesAux (δ cap : ℝ) : ℕ → ℝ → List ℝ
  | 0, _ => []
  | fuel + 1, L => L :: (if cap ≤ L then [] else guessesAux δ cap fuel (L * (1 + δ)))

noncomputable def positiveGuesses {k : ℕ} (I : MultiInstance k) (ε : ℝ) : List ℝ :=
  if (positiveLengths (lengthInstance I)).isEmpty ∨ ε ≤ 0 then [] else
    let a := firstPositiveLength (lengthInstance I)
    let cap := (I.graph.n : ℝ) * largestLength (lengthInstance I)
    guessesAux (ε / 4) cap
      (Nat.ceil (Real.log (cap / a) / Real.log (1 + ε / 4)) + 2) a

/-- The zero-objective call retains a zero-increment objective clock at threshold 1.
Its other clocks are the positive-budget constraints, so this is genuinely multi-resource. -/
noncomputable def outerCalls {k : ℕ} (I : MultiInstance k) (ε : ℝ) : List (ClockCall k) :=
  if hasPositiveBudget I then
    ⟨I, ε / 4, 1, true⟩ :: (positiveGuesses I ε).map (fun L => ⟨I, ε / 4, L, false⟩)
  else []

inductive OutputBranch where
  | absent
  | source
  | ordinary
  | table (callIndex : ℕ)
  deriving DecidableEq

noncomputable def selectedBranch {k : ℕ} (I : MultiInstance k) (ε : ℝ) (t : ℕ) : OutputBranch :=
  if t = I.source then .source else
  if hasPositiveBudget I then
    match ((List.range (outerCalls I ε).length).find? (fun r =>
      match (outerCalls I ε)[r]? with
      | none => false
      | some A => accepts A t)) with
    | none => .absent
    | some r => .table r
  else if ((shortestTree I t).distance).isSome then .ordinary else .absent

noncomputable def selectedDistance {k : ℕ} (I : MultiInstance k) (ε : ℝ) (t : ℕ) : Option ℝ :=
  match selectedBranch I ε t with
  | .absent => none
  | .source => some 0
  | .ordinary => (shortestTree I t).distance
  | .table r => ((outerCalls I ε)[r]?).map (fun A => if A.zeroOnly then 0 else (1 + ε / 4) * A.L)

noncomputable def selectedPath {k : ℕ} (I : MultiInstance k) (ε : ℝ) (t : ℕ) : Option (List ℕ) :=
  match selectedBranch I ε t with
  | .absent => none
  | .source => some [I.source]
  | .ordinary => shortestPath I t
  | .table r => ((outerCalls I ε)[r]?).bind (fun A => retrieve A t)

end NearLinearRSP.TwoResources.Supplement


