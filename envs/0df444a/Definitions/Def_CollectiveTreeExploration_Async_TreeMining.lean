-- Prove2me | Definitions.Def_CollectiveTreeExploration_Async_TreeMining
-- name    : CollectiveTreeExploration_Async_TreeMining
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:09:08.391368+00:00
-- url     : https://prove2.me/theorems/04498e10-7ece-447b-b4cc-24b66d347d7a
-- title:
--   The continuous tree-mining game, its plays and cumulative cost
-- statement:
--   This file defines the **continuous tree-mining game** (CTM) of §2.2.
--
--   **State.** A weighted tree $T(t)$, controlled by the adversary, and an integral configuration $x(t)$ of $k$ miners, controlled by the player. Initially the tree is the root alone, carrying all $k$ miners.
--
--   **Adversary's events.**
--   1. *Elongation* of a non-root leaf $l$ at unit rate during an arbitrary real duration $\tau\ge0$, allowed only while $x_l\ge2$.
--   2. *Fork* of a leaf $l$ with $x_l\ge3$ into $m\in\{2,\dots,x_l-1\}$ new children.
--   3. *Deletion* of a non-root leaf $l$, provided another leaf survives.
--
--   **Player.** A deterministic strategy may depend on the past events and the current state. During an elongation of $l$ it follows a trajectory $s\mapsto x(s)$ of integral configurations fixed when the elongation starts, so it cannot depend on how long the elongation will last; at a fork it chooses the common length $\delta\in(0,1]$ of the new edges and a list of actual transfers; at a deletion it chooses a list of transfers ending at a configuration on the surviving leaves. A response that is not an integral configuration of the current tree (or a fork length outside $(0,1]$) is illegal and costs $+\infty$.
--
--   **Costs.** During an elongation the player pays the service cost $\int_0^\tau x_l(s)\,ds$ plus the movement of the trajectory, defined as its total variation $\sup\sum_i\mathrm{OT}(x(s_i),x(s_{i+1}))$ over the partitions $0=s_0\le\dots\le s_n=\tau$ (each transport measured in the tree at time $s_i$), plus the initial jump. At a fork each successive transfer is charged in the new tree, including travel to the new children; at a deletion every evacuation and subsequent repair transfer is charged in the tree before deletion and suppression. Intermediate transfers conserve miners; the final configuration must occupy every live leaf. The sum does not cancel retracing. The **cumulative cost** of a play is the sum.
--
--   **Plays.** A play is a finite list of events, each allowed when it occurs. Every prefix of a play, in particular an elongation stopped earlier, is again a play, so a statement about all plays is a statement at all times. A strategy is **well formed** when every reachable response is legal, finite-prefix costs are finite, and its elongation plans are measurable integral configurations for all nonnegative elapsed times. After growth blocks a plan can be held fixed. This is a conclusion to establish for a constructed strategy, not an assumption of its type. It also checks a plan that blocks growth immediately. A strategy **maintains cumulative cost at most $F(D)$** when it is well formed and every depth-bounded play has cumulative cost at most $F(D)$. Zero-duration events record immediate blocking redistributions and their cost; they add no positive-length game instances.
--
--   **Formalization Note** Fresh vertices created by a fork receive the next unused labels. The service cost is a lower Lebesgue integral and the variation a supremum, both in $[0,\infty]$.
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; §2.2, p.6 (the game); §2.1, p.5 (cumulative cost)

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_WeightedTree

namespace CollectiveTreeExploration.Async

open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open Classical

/-! Continuous tree-mining, §2.2, p.6. Events have arbitrary real durations. A response
contains actual transfers, rather than only the final displacement. Invalid responses cost
infinity; `WellFormedCTM` also checks trajectories before an elongation can be blocked.
No performance condition is part of the strategy type. -/

inductive Event where
  | elong (l : ℕ) (τ : ℝ)
  | fork (l m : ℕ)
  | del (l : ℕ)

structure GState where
  tree : WTree
  x : ℕ → ℕ

def initState (k : ℕ) : GState where
  tree := { V := {0}, root := 0, par := fun _ => 0, len := fun _ => 0 }
  x := fun v => if v = 0 then k else 0

/-- The plan is a function of elapsed time, not the future duration. Discrete responses
list all successive configurations after transfers, excluding the starting configuration.
The last entry is the final configuration; an empty list means no transfer. -/
structure CTMStrategy (k : ℕ) where
  elongPlan : List Event → GState → ℕ → ℝ → ℕ → ℕ
  forkMove : List Event → GState → ℕ → ℕ → ℝ × List (ℕ → ℕ)
  delMove : List Event → GState → ℕ → List (ℕ → ℕ)

namespace WTree
variable (T : WTree)

def elongAt (l : ℕ) (s : ℝ) : WTree := T.setLen l (T.len l + s)

/-- Weighted total variation, with the metric at the left endpoint of each partition
interval. The supremum over refinements charges every jump at its actual time. On a
smooth fractional trajectory this is the integral of the instantaneous movement norm.
The extended supremum also records infinite movement. -/
def variation (l : ℕ) (τ : ℝ) (z : ℝ → ℕ → ℝ) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (s : Fin (n + 1) → ℝ) (_ : Monotone s ∧ s 0 = 0 ∧ s (Fin.last n) = τ),
    ∑ i : Fin n, ENNReal.ofReal
      ((T.elongAt l (s i.castSucc)).OT (z (s i.castSucc)) (z (s i.succ)))

/-- Service and redistribution, including endpoint jumps. The nonnegative integral
retains infinity; it is not a Bochner integral with a zero default. -/
def elongCost (l : ℕ) (τ : ℝ) (z : ℝ → ℕ → ℝ) : ℝ≥0∞ :=
  (∫⁻ s in Set.Icc 0 τ, ENNReal.ofReal (z s l)) + T.variation l τ z

/-- Intermediate configurations during an instantaneous transport may occupy internal
vertices. They conserve miners and are supported on the current finite vertex set. -/
def IsTransportConfig (k : ℕ) (x : ℕ → ℕ) : Prop :=
  (∀ v, v ∉ T.V → x v = 0) ∧ ∑ v ∈ T.V, x v = k

/-- Every transfer is charged; backtracking or subsequent repairs are not cancelled. -/
def transferCost : (ℕ → ℕ) → List (ℕ → ℕ) → ℝ≥0∞
  | _, [] => 0
  | x, z :: zs => ENNReal.ofReal (T.OT (toReal x) (toReal z)) + transferCost z zs
end WTree

/-- Final configuration of a recorded transfer sequence. -/
def responseEnd (x : ℕ → ℕ) (zs : List (ℕ → ℕ)) : ℕ → ℕ := zs.getLast?.getD x

def ElongAllowed (st : GState) (l : ℕ) : Prop :=
  l ∈ st.tree.leaves ∧ l ≠ st.tree.root ∧ 2 ≤ st.x l

def ForkAllowed (st : GState) (l m : ℕ) : Prop :=
  l ∈ st.tree.leaves ∧ 3 ≤ st.x l ∧ 2 ≤ m ∧ m ≤ st.x l - 1

/-- Deleting the sole remaining leaf is inadmissible: evacuation needs a surviving leaf. -/
def DelAllowed (st : GState) (l : ℕ) : Prop :=
  l ∈ st.tree.leaves ∧ l ≠ st.tree.root ∧ ∃ ℓ ∈ st.tree.leaves, ℓ ≠ l

/-- Zero duration includes an immediate player redistribution when an attempted
elongation is blocked. A positive duration is legal only while the growing leaf has at
least two miners. On every accepted event an invalid player response has infinite cost. -/
def ctmStep {k : ℕ} (S : CTMStrategy k) (past : List Event) (st : GState) :
    Event → Option (GState × ℝ≥0∞)
  | .elong l τ =>
    let plan := S.elongPlan past st l
    if ElongAllowed st l ∧ 0 ≤ τ ∧ ∀ s ∈ Set.Ico 0 τ, 2 ≤ plan s l then
      let T := st.tree
      let cost : ℝ≥0∞ :=
        if (∀ s ∈ Set.Icc 0 τ, (T.elongAt l s).IsIntConfig k (plan s)) ∧
            (∀ v, Measurable (fun s : ℝ => plan s v)) then
          ENNReal.ofReal (T.OT (WTree.toReal st.x) (WTree.toReal (plan 0))) +
            T.elongCost l τ (fun s => WTree.toReal (plan s))
        else ⊤
      some (⟨T.elongAt l τ, plan τ⟩, cost)
    else none
  | .fork l m =>
    if ForkAllowed st l m then
      let (δ, zs) := S.forkMove past st l m
      let T' := st.tree.fork l m δ
      let x' := responseEnd st.x zs
      let cost : ℝ≥0∞ :=
        if 0 < δ ∧ δ ≤ 1 ∧ (∀ z ∈ zs, T'.IsTransportConfig k z) ∧ T'.IsIntConfig k x' then
          T'.transferCost st.x zs
        else ⊤
      some (⟨T', x'⟩, cost)
    else none
  | .del l =>
    if DelAllowed st l then
      let zs := S.delMove past st l
      let x' := responseEnd st.x zs
      let T' := st.tree.delete l
      let cost : ℝ≥0∞ :=
        if (∀ z ∈ zs, st.tree.IsTransportConfig k z) ∧ T'.IsIntConfig k x' then
          st.tree.transferCost st.x zs
        else ⊤
      some (⟨T', x'⟩, cost)
    else none

structure StepRecord where
  before : GState
  event : Event
  after : GState
  cost : ℝ≥0∞

def ctmRunFrom {k : ℕ} (S : CTMStrategy k) : List Event → List Event → GState →
    Option (List StepRecord)
  | _, [], _ => some []
  | past, e :: es, st =>
    match ctmStep S past st e with
    | none => none
    | some (st', c) => (ctmRunFrom S (past ++ [e]) es st').map (fun recs => ⟨st, e, st', c⟩ :: recs)

/-- Actual run from the root-only state. Quantifying every finite event list includes
every finite prefix and every interior time, by shortening its final elongation. -/
def ctmRun {k : ℕ} (S : CTMStrategy k) (es : List Event) : Option (List StepRecord) :=
  ctmRunFrom S [] es (initState k)

def playCost (recs : List StepRecord) : ℝ≥0∞ := (recs.map StepRecord.cost).sum

def finalState (k : ℕ) (recs : List StepRecord) : GState :=
  match recs.getLast? with
  | some r => r.after
  | none => initState k

/-- Operational well-definedness, without an invariant or competitive bound. At every
reachable history all responses are legal, and every attempted elongation has a measurable
integral trajectory, even if it immediately blocks growth. Values after growth has blocked
are a harmless total extension of a plan (one may hold the last configuration forever).
Thus an illegal plan cannot hide by making every positive duration inadmissible. -/
def WellFormedCTM {k : ℕ} (S : CTMStrategy k) : Prop :=
  ∀ (es : List Event) (recs : List StepRecord), ctmRun S es = some recs →
    playCost recs < ⊤ ∧
    (finalState k recs).tree.IsGameTree ∧
    (finalState k recs).tree.IsIntConfig k (finalState k recs).x ∧
    ∀ l, ElongAllowed (finalState k recs) l →
      (∀ s : ℝ, 0 ≤ s → ((finalState k recs).tree.elongAt l s).IsIntConfig k
        (S.elongPlan es (finalState k recs) l s)) ∧
      (∀ v, Measurable (fun s : ℝ => S.elongPlan es (finalState k recs) l s v))

/-- Uniform cost guarantee on every legal depth-bounded play, including legal responses
as a conclusion of the guarantee rather than a premise suppressing bad plays. -/
def MaintainsCost {k : ℕ} (S : CTMStrategy k) (F : ℝ → ℝ) : Prop :=
  WellFormedCTM S ∧
  ∀ (D : ℝ) (es : List Event) (recs : List StepRecord), ctmRun S es = some recs →
    (initState k).tree.DepthLE D → (∀ r ∈ recs, r.after.tree.DepthLE D) →
      playCost recs ≤ ENNReal.ofReal (F D) ∧ 0 ≤ F D

end
end CollectiveTreeExploration.Async


