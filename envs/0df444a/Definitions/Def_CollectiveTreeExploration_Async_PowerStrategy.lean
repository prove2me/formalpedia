-- Prove2me | Definitions.Def_CollectiveTreeExploration_Async_PowerStrategy
-- name    : CollectiveTreeExploration_Async_PowerStrategy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:16:35.101538+00:00
-- url     : https://prove2.me/theorems/0f620b6e-68cc-4a49-9906-c63966fcae61
-- title:
--   The CTM strategy tracking the minimizer of the power regularizer, and the cost of the fractional minimizer
-- statement:
--   This file defines the player's strategy of §3.1 and the cumulative cost $C_y$ of the fractional minimizer.
--
--   The player tracks $y(t)$, the fractional minimizer on the current tree $T(t)$, with the integral configuration $x(t)$, starting with all miners at the root, using three rules.
--
--   1. **Repair.** Whenever a leaf $\ell$ satisfies $x_\ell-y_\ell\ge\frac32$, let $v$ be the first ancestor of $\ell$ with $x_v-y_v<\frac32$; from $v$, descend through underloaded children ($x_u<y_u$) until a leaf $\ell'$ is reached, and move one miner from $\ell$ to $\ell'$. During an elongation this happens at the first time a leaf becomes overloaded, so the trajectory is piecewise constant and right-continuous.
--   2. **Fork.** When a leaf $\ell$ receives $m$ children, its $x_\ell$ miners are split as evenly as possible, in groups of $\lfloor x_\ell/m\rfloor$ and $\lceil x_\ell/m\rceil$. The fork length is half the supremum of the lengths $\delta\in(0,1]$ for which (I) holds for the split configuration and the minimizer of the forked tree with every child length in $(0,\delta]$ (and $1$ if there is none).
--   3. **Deletion.** At the deletion of $l$, its miners go to a surviving leaf below a sibling of $l$; then the configuration is repaired in the new tree. The evacuation and every individual repair are recorded and charged separately in the pre-deletion metric.
--
--   Ties are broken by the smallest label. The definitions do not assume that a repair terminates, that a descent succeeds or that a sibling leaf exists: a failure produces the all-zero configuration, which is illegal and costs $+\infty$ in the game.
--
--   **Cost of the fractional minimizer.** Along a play, $C_y$ adds: during an elongation of $l$, the service cost $\int y_l$ plus the movement (total variation) of $s\mapsto y(s)$; at a fork, $\mathrm{OT}(y(t^-),y(t^+))$ in the new tree; at a deletion, $\mathrm{OT}_d(y(t^-),y(t^+))$ in the tree before the deletion.
--
--   **Formalization Note** The source leaves the tie rules and the exact small fork length open; the choices above are one deterministic instance of the strategy.
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; §3.1, p.7 (player's strategy a)–c)); Appendix A, p.15 (fork length); §3.3–3.5, pp.9–13 (Ċ_y, Deletion Eq., Fork Eq.)

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_PowerRegularizer
import Definitions.Def_CollectiveTreeExploration_Async_TreeMining

namespace CollectiveTreeExploration.Async

open scoped BigOperators ENNReal

noncomputable section

open Classical

/-! # The CTM strategy of §3.1 (p.7) and the cumulative cost of the fractional minimizer

The player tracks the fractional minimizer `y(t) = fracMin (T(t)) k` with the integral
configuration `x(t)`:
* a) Repair: whenever a leaf `ℓ` has `x_ℓ - y_ℓ ≥ 3/2`, let `v` be the first ancestor of `ℓ` with
  `x_v - y_v < 3/2`, descend from `v` through underloaded children (`x_u < y_u`) to a leaf `ℓ'`, and
  move one miner from `ℓ` to `ℓ'`;
* b) Fork: split the miners of `ℓ` as evenly as possible (groups of `⌊x_ℓ/m⌋` and `⌈x_ℓ/m⌉`)
  among the `m` children; the fork length `δ ∈ (0, 1]` is chosen small enough to preserve (I);
* c) Deletion: send the miners of `l` to a surviving leaf below a sibling of `l`, remove the
  deleted edge, then repair.

Ties are broken by the smallest label. Nothing here assumes that a repair terminates or that a
descent succeeds: a failure produces the all-zero configuration, which is not an integral
configuration, so the game charges an infinite cost (Proposition 3.2 asserts that this never
happens). -/

namespace WTree

variable (T : WTree)

/-- The leaves violating the repair threshold: `x_ℓ - y_ℓ ≥ 3/2`. -/
def overloadedLeaves (y : ℕ → ℝ) (x : ℕ → ℕ) : Finset ℕ :=
  T.leaves.filter (fun ℓ => (3 / 2 : ℝ) ≤ (x ℓ : ℝ) - y ℓ)

/-- Descent from `v` through underloaded children (`x_u < y_u`, node masses), smallest label
first, until a leaf is reached; `none` if at some internal vertex no child is underloaded or the
fuel runs out. -/
def descend (y : ℕ → ℝ) (x : ℕ → ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, v =>
    if v ∈ T.leaves then some v else
      let U := (T.children v).filter (fun u => T.mass (WTree.toReal x) u < T.mass y u)
      if h : U.Nonempty then descend y x fuel (U.min' h) else none

/-- Move one miner from `a` to `b`. -/
def moveOne (x : ℕ → ℕ) (a b : ℕ) : ℕ → ℕ :=
  Function.update (Function.update x a (x a - 1)) b (Function.update x a (x a - 1) b + 1)

/-- One repair step (rule a) for the fractional configuration `y`: if no leaf is overloaded,
nothing changes; otherwise the overloaded leaf `ℓ` of smallest label sends one miner to the leaf
`ℓ'` reached by descending from the first ancestor `v` of `ℓ` with `x_v - y_v < 3/2`. -/
def repairStep (y : ℕ → ℝ) (x : ℕ → ℕ) : Option (ℕ → ℕ) :=
  if h : (T.overloadedLeaves y x).Nonempty then
    let ℓ := (T.overloadedLeaves y x).min' h
    if hv : ∃ n : ℕ, T.mass (WTree.toReal x) (T.par^[n] ℓ) - T.mass y (T.par^[n] ℓ) < 3 / 2 then
      let v := T.par^[Nat.find hv] ℓ
      match T.descend y x (T.V.card + 1) v with
      | some ℓ' => some (moveOne x ℓ ℓ')
      | none => none
    else none
  else some x

/-- The list of intermediate configurations after `n` repair steps. Failure is explicit. -/
def repairTrace (y : ℕ → ℝ) (x : ℕ → ℕ) : ℕ → Option (List (ℕ → ℕ))
  | 0 => some []
  | n + 1 => do
    let zs ← repairTrace y x n
    let z ← T.repairStep y (responseEnd x zs)
    pure (zs ++ [z])

/-- Actual successive repair transfers, stopped at the first stable configuration.
A failure or nontermination returns `[0]`, an illegal response, rather than assuming
termination or hiding intermediate movements. -/
def repairMoves (y : ℕ → ℝ) (x : ℕ → ℕ) : List (ℕ → ℕ) :=
  if h : ∃ n : ℕ, ∃ zs, T.repairTrace y x n = some zs ∧
      T.overloadedLeaves y (responseEnd x zs) = ∅ then
    (T.repairTrace y x (Nat.find h)).getD [fun _ => 0]
  else [fun _ => 0]

/-- Configuration obtained after the prescribed repair sequence. -/
def repairAll (y : ℕ → ℝ) (x : ℕ → ℕ) : ℕ → ℕ :=
  responseEnd x (T.repairMoves y x)

/-- Repair with respect to the fractional minimizer of `T`. -/
def repairMin (k : ℕ) (x : ℕ → ℕ) : ℕ → ℕ := T.repairAll (T.fracMin k) x

/-! ## Rule a) during an elongation -/

/-- The phases of the trajectory during an elongation of `l` started from configuration `x`:
phase `0` starts at time `0` with the repaired configuration; phase `j + 1` starts at the first
time after the start of phase `j` at which the configuration of phase `j` has an overloaded leaf,
with that configuration repaired. `none`: no further repair is ever needed. -/
def elongPhase (k : ℕ) (l : ℕ) (x : ℕ → ℕ) : ℕ → Option (ℝ × (ℕ → ℕ))
  | 0 => some (0, (T.elongAt l 0).repairMin k x)
  | j + 1 =>
    match elongPhase k l x j with
    | none => none
    | some (s, xj) =>
      if ∃ u : ℝ, s < u ∧ ((T.elongAt l u).overloadedLeaves ((T.elongAt l u).fracMin k) xj).Nonempty then
        let s' := sInf {u : ℝ | s < u ∧
          ((T.elongAt l u).overloadedLeaves ((T.elongAt l u).fracMin k) xj).Nonempty}
        some (s', (T.elongAt l s').repairMin k xj)
      else none

/-- Phase `j` is the one in force at time `s`: it has started by time `s` and the next phase (if
any) starts strictly after `s`. -/
def PhaseInForce (k : ℕ) (l : ℕ) (x : ℕ → ℕ) (s : ℝ) (j : ℕ) : Prop :=
  ∃ sj xj, T.elongPhase k l x j = some (sj, xj) ∧ sj ≤ s ∧
    ∀ s' x', T.elongPhase k l x (j + 1) = some (s', x') → s < s'

/-- The (right-continuous, piecewise constant) trajectory of rule a) during the elongation of `l`
from configuration `x`: the configuration of the phase in force at time `s` (all-zero, i.e.
illegal, if no phase is in force, e.g. after an accumulation of repair times). -/
def elongTrajectory (k : ℕ) (l : ℕ) (x : ℕ → ℕ) (s : ℝ) : ℕ → ℕ :=
  if h : ∃ j, T.PhaseInForce k l x s j then
    match T.elongPhase k l x (Nat.find h) with
    | some (_, xj) => xj
    | none => fun _ => 0
  else fun _ => 0

/-! ## Rule b) forks -/

/-- The even split of the `x_ℓ` miners of `ℓ` among its `m` new children `fresh + i`, `i < m`:
the first `x_ℓ mod m` children receive `⌈x_ℓ/m⌉` miners and the others `⌊x_ℓ/m⌋`. -/
def forkSplit (l m : ℕ) (x : ℕ → ℕ) : ℕ → ℕ := fun w =>
  if T.fresh ≤ w ∧ w < T.fresh + m then
    x l / m + (if w - T.fresh < x l % m then 1 else 0)
  else if w = l then 0 else x w

/-- The fork lengths `δ ∈ (0, 1]` such that (I) holds for the split configuration and the
fractional minimizer of the forked tree for every common child length in `(0, δ]` (so that
(I) holds throughout the interpolation of the fork). -/
def admissibleForkLengths (k : ℕ) (l m : ℕ) (x : ℕ → ℕ) : Set ℝ :=
  {δ | 0 < δ ∧ δ ≤ 1 ∧ ∀ s ∈ Set.Ioc (0 : ℝ) δ,
    (T.fork l m s).InvI (T.forkSplit l m x) ((T.fork l m s).fracMin k)}

/-- The fork length chosen by rule b): half the supremum of the admissible lengths (an
admissible length whenever one exists), and `1` if none exists. -/
def forkLength (k : ℕ) (l m : ℕ) (x : ℕ → ℕ) : ℝ :=
  if (T.admissibleForkLengths k l m x).Nonempty then sSup (T.admissibleForkLengths k l m x) / 2
  else 1

/-! ## Rule c) deletions -/

/-- The surviving leaves below a sibling of `l` (a sibling is another child of `p_l`). -/
def siblingLeaves (l : ℕ) : Finset ℕ :=
  T.leaves.filter (fun ℓ => ℓ ≠ l ∧ ∃ c ∈ T.children (T.par l), c ≠ l ∧ T.Desc ℓ c)

/-- Rule c), including every transfer: first evacuate to the smallest surviving
sibling leaf, then execute the actual repair sequence in the deleted/suppressed tree.
The entire list is charged in the pre-deletion metric. -/
def deletionMoves (k : ℕ) (l : ℕ) (x : ℕ → ℕ) : List (ℕ → ℕ) :=
  if h : (T.siblingLeaves l).Nonempty then
    let ℓ := (T.siblingLeaves l).min' h
    let evacuated := Function.update (Function.update x ℓ (x ℓ + x l)) l 0
    evacuated :: (T.delete l).repairMoves ((T.delete l).fracMin k) evacuated
  else [fun _ => 0]

end WTree

/-- The CTM strategy of §3.1 for `k` miners (it ignores the past events: it only uses the current
tree, its fractional minimizer and the current configuration). -/
def powerStrategy (k : ℕ) : CTMStrategy k where
  elongPlan _ st l := st.tree.elongTrajectory k l st.x
  forkMove _ st l m :=
    let δ := st.tree.forkLength k l m st.x
    (δ, [st.tree.forkSplit l m st.x])
  delMove _ st l := st.tree.deletionMoves k l st.x

/-! ## The cumulative cost `C_y` of the fractional minimizer along a play -/

/-- The movement cost of the fractional minimizer `y(t) = fracMin (T(t)) k` during one event:
* elongation of `l` for `τ`: service `∫ y_l` plus movement of `s ↦ y(s)` over `[0, τ]`;
* fork: `OT` in the new tree from `y(t⁻)` (whose mass at `l` now sits on an internal vertex) to
  `y(t⁺)`;
* deletion: `OT_d(y(t⁻), y(t⁺))` in the tree before the deletion. -/
def fracStepCost (k : ℕ) (r : StepRecord) : ℝ≥0∞ :=
  match r.event with
  | .elong l τ => r.before.tree.elongCost l τ (fun s => (r.before.tree.elongAt l s).fracMin k)
  | .fork _ _ => ENNReal.ofReal (r.after.tree.OT (r.before.tree.fracMin k) (r.after.tree.fracMin k))
  | .del _ => ENNReal.ofReal (r.before.tree.OT (r.before.tree.fracMin k) (r.after.tree.fracMin k))

/-- `C_y`: the cumulative movement cost of the fractional minimizer over a play. -/
def fracCost (k : ℕ) (recs : List StepRecord) : ℝ≥0∞ := (recs.map (fracStepCost k)).sum

end

end CollectiveTreeExploration.Async


