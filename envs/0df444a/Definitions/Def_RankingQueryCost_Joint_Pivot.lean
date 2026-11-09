-- Prove2me | Definitions.Def_RankingQueryCost_Joint_Pivot
-- name    : RankingQueryCost_Joint_Pivot
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:26:05.894603+00:00
-- url     : https://prove2.me/theorems/61bd56b0-6262-43a2-bf94-52c5fe78b187
-- title:
--   Fresh uniform pivot executions on the shared ledger
-- statement:
--   Each pivot is the least-priority member of its current block under a fresh independent uniform permutation. Its full internal star is read through the shared ledger, giving observed losers and winners. The width-limited execution stops blocks of size at most $b$; the truncated execution processes breadth-first levels $0,\ldots,L-1$, where $L=\lceil\log_{3/2}n\rceil$. Terminal blocks are completed by public labels.
--
--   $$f_b(m)=\begin{cases}0&m\le b,\\m[1+\log_2(m/b)]&m>b.\end{cases}$$
--
--   The result records all logical requests separately from the physical ledger. A legal earlier cached state is defined by actual reachability under a causal earlier protocol, with no accuracy hypothesis. The finite priority seed is fresh after that state is fixed.
--
--   **Formalization Note** At most $n$ nontrivial pivots can occur, so $n$ independent permutation rows suffice. This represents ideal uniform pivots exactly; bounded-bit implementations and their failure allowances belong to the upper theorems.
--
--   Comparison stars are traversed in the explicit public lexicographic pair order `pairList n`; no classically chosen list order is required by a finite implementation.
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), §3.3, pp. 9–12, PDF pp. 10–13; §6.1, pp. 28–29, PDF pp. 29–30; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Interaction
import Definitions.Def_RankingQueryCost_Joint_Reference

set_option autoImplicit false

noncomputable section

namespace RankingQueryCost.Joint

attribute [local instance] Classical.propDecidable

/-- Fresh independent uniform permutations are a finite representation of fresh uniform
pivots: the least-priority member of any current block is uniform in that block. -/
abbrev PivotSeed (n : ℕ) := Fin n → Rank n

abbrev PivotSlots (n : ℕ) := List (Finset (Fin n) × ℕ)

structure PivotState (n : ℕ) where
  slots : PivotSlots n
  interaction : InteractionState n
  requests : List (Pair n)

def pivotStart {n : ℕ} (S : InteractionState n) : PivotState n := ⟨[(Finset.univ, 0)], S, []⟩

/-- A public processing order chooses among the presently live block indices. -/
abbrev BlockSelector (n : ℕ) := PublicHistory n → PivotSlots n → ℕ

def liveBlocks {n : ℕ} (b L : ℕ) (slots : PivotSlots n) : List ℕ :=
  (List.range slots.length).filter fun j =>
    match slots[j]? with
    | none => false
    | some Ud => decide (b < Ud.1.card ∧ Ud.2 < L)

def breadthFirst {n : ℕ} : BlockSelector n := fun _ slots =>
  ((List.range slots.length).mergeSort fun i j =>
    decide (((slots[i]?).map Prod.snd).getD 0 ≤ ((slots[j]?).map Prod.snd).getD 0)).headD 0

/-- In the breadth-first execution the live candidate with least depth is selected. -/
def pivotStep {n : ℕ} (b L : ℕ) (select : BlockSelector n) (bfs : Bool)
    (W : ComparisonWorld n) (h : ℕ) (seed : PivotSeed n) (j : ℕ)
    (P : PivotState n) : PivotState n :=
  let candidates := liveBlocks b L P.slots
  if candidates.isEmpty then P else
  let candidates := if bfs then candidates.mergeSort (fun i j =>
    decide (((P.slots[i]?).map Prod.snd).getD 0 ≤ ((P.slots[j]?).map Prod.snd).getD 0)) else candidates
  let index := if bfs then candidates.headD 0 else
    (candidates[select P.interaction.history P.slots % candidates.length]?).getD 0
  let Ud := (P.slots[index]?).getD (∅, 0)
  let priority := if hj : j < n then seed ⟨j, hj⟩ else Equiv.refl (Fin n)
  match (Ud.1.toList.mergeSort fun i j => decide (priority i ≤ priority j)).head? with
  | none => P
  | some pivot =>
    let star := (pairList n).filter fun e => decide (
      (e.1.1 = pivot ∨ e.1.2 = pivot) ∧ e.1.1 ∈ Ud.1 ∧ e.1.2 ∈ Ud.1)
    let S := star.foldl (fun S e => (readIdentity h W S [] e).2) P.interaction
    let left := Ud.1.filter fun i => RecordedForward S.ledger i pivot
    let right := Ud.1.filter fun i => RecordedForward S.ledger pivot i
    let children := [(left, Ud.2 + 1), ({pivot}, Ud.2 + 1), (right, Ud.2 + 1)]
      |>.filter fun child => decide (0 < child.1.card)
    ⟨P.slots.take index ++ children ++ P.slots.drop (index + 1), S, P.requests ++ star⟩

def pivotExecution {n : ℕ} (b L : ℕ) (select : BlockSelector n) (bfs : Bool)
    (W : ComparisonWorld n) (h : ℕ) (S : InteractionState n) (seed : PivotSeed n) : PivotState n :=
  (List.range n).foldl (fun P j => pivotStep b L select bfs W h seed j P) (pivotStart S)

def pivotOutput {n : ℕ} (P : PivotState n) : Fin n → ℝ :=
  let L := P.slots.flatMap fun Ud => Ud.1.sort (· ≤ ·)
  fun i => (L.idxOf i : ℝ)

def kendallCount {n : ℕ} (r : Rank n) (π : Fin n → ℝ) : ℕ :=
  ((Finset.univ : Finset (Pair n)).filter fun e =>
    ((r e.1.1 < r e.1.2 ∧ π e.1.2 < π e.1.1) ∨
     (r e.1.2 < r e.1.1 ∧ π e.1.1 < π e.1.2))).card

def pivotDepth (n : ℕ) : ℕ := ⌈Real.logb (3 / 2 : ℝ) n⌉₊

def queryPotential (b m : ℕ) : ℝ :=
  if m ≤ b then 0 else (m : ℝ) * (1 + Real.logb 2 ((m : ℝ) / b))

/-- A legal earlier cached state is reachable by an earlier causal protocol in this world.
This is operational reachability, not an accuracy premise or an unverified invariant. The fresh
pivot seed in subsequent theorems is independent of all randomness used to reach this state. -/
def LegalCachedState {n : ℕ} (a h : ℕ) (W : ComparisonWorld n) (S : InteractionState n) : Prop :=
  LegalWorld a W ∧ ∃ (A : QueryPolicy n) (ω : PrivateTape) (t : ℕ),
    executionState (executionPrefix A W h ω t) = S

end RankingQueryCost.Joint


