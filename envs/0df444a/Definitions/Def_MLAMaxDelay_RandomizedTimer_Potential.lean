-- Prove2me | Definitions.Def_MLAMaxDelay_RandomizedTimer_Potential
-- name    : MLAMaxDelay_RandomizedTimer_Potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:29:13.000171+00:00
-- url     : https://prove2.me/theorems/08b09363-33a3-4894-88e5-85eaa9b291b3
-- title:
--   Connected intervals, greedy partitions, and genuine potential limits
-- statement:
--   Write $h_\theta(i,j)=D(i,j)-(1-\theta)C(i,j)$. A connected interval is one for which every successive epoch satisfies the timer acceptance inequality. The greedy partition repeatedly selects the longest connected prefix. Weakly greedy partitions have connected blocks and weak boundary rejection, while actual greedy cuts require strict rejection. Consecutive coarsening means the larger blocks are unions of nonempty consecutive groups of smaller blocks.
--
--   On the positive-path reduction, the actual timer partition $P_\theta$ defines
--   $$Q(\theta)=\sum_{B\in P_\theta}\bigl(D(B)-(1-\theta)C(B)\bigr).$$
--   This does not define the actual execution cost. Interior breakpoint candidates are all positive-$C$ affine acceptance equalities in $(0,1)$; zero-$C$ tests have no parameter breakpoint. Left and right potential limits are expressed by their actual one-sided convergence, rather than values at the breakpoint or default-valued limit functions.
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 11–14, Section 4.2, equations (7)–(10), (19)–(21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Timer

namespace MLAMaxDelay.RandomizedTimer

open Filter
open scoped Topology

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def intervalH (T : WeightedTree V) (I : Input V) (θ : ℝ) (i j : ℕ) : ℝ :=
  intervalD T I i j - (1-θ) * intervalC T I i j

/-- Half-open [i,j) is connected precisely when each later epoch is accepted. -/
def Connected (T : WeightedTree V) (I : Input V) (θ : ℝ) (i j : ℕ) : Prop :=
  ∀ r ∈ Finset.Ioo i j, epochTime I r - epochTime I i ≤ intervalH T I θ i r

abbrev EpochBlock := ℕ × ℕ

/-- Ordered nonempty contiguous half-open blocks exactly cover [i,j). -/
def PartitionsInterval : ℕ → ℕ → List EpochBlock → Prop
  | i, j, [] => i = j
  | i, j, b :: rest => b.1 = i ∧ i < b.2 ∧ b.2 ≤ j ∧ PartitionsInterval b.2 j rest

/-- Weak cuts use ≥. Actual greedy rejection uses > and is kept separate. -/
def WeakCuts (T : WeightedTree V) (I : Input V) (θ : ℝ) : List EpochBlock → Prop
  | [] => True
  | [_] => True
  | b :: c :: rest =>
    intervalH T I θ b.1 b.2 ≤ epochTime I c.1 - epochTime I b.1 ∧
      WeakCuts T I θ (c :: rest)

def StrictCuts (T : WeightedTree V) (I : Input V) (θ : ℝ) : List EpochBlock → Prop
  | [] => True
  | [_] => True
  | b :: c :: rest =>
    intervalH T I θ b.1 b.2 < epochTime I c.1 - epochTime I b.1 ∧
      StrictCuts T I θ (c :: rest)

def WeaklyGreedy (T : WeightedTree V) (I : Input V) (θ : ℝ)
    (i j : ℕ) (P : List EpochBlock) : Prop :=
  PartitionsInterval i j P ∧ (∀ b ∈ P, Connected T I θ b.1 b.2) ∧ WeakCuts T I θ P

/-- Longest connected prefix; the finite fuel only bounds the number of
nonempty blocks and does not disclose an input length to the online timer. -/
noncomputable def greedyFrom (T : WeightedTree V) (I : Input V) (θ : ℝ)
    (j : ℕ) : ℕ → ℕ → List EpochBlock
  | 0, _ => []
  | fuel+1, i => by
    classical
    exact if i < j then
      let k := i + ((List.range (j-i)).takeWhile
        (fun q => decide (Connected T I θ i (i+q+1)))).length
      (i,k) :: greedyFrom T I θ j fuel k
    else []

noncomputable def greedyPartition (T : WeightedTree V) (I : Input V) (θ : ℝ) : List EpochBlock :=
  greedyFrom T I θ (epochs I).length (epochs I).length 0

/-- Each larger block consists of a nonempty contiguous sublist of smaller blocks. -/
def ConsecutiveCoarsening (Psmall Plarge : List EpochBlock) : Prop :=
  ∃ groups : List (List EpochBlock), groups.flatten = Psmall ∧ groups.length = Plarge.length ∧
    ∀ k : Fin groups.length,
      let G := groups[k]
      G ≠ [] ∧ PartitionsInterval ((Plarge[k.val]?.getD (0,0)).1)
        ((Plarge[k.val]?.getD (0,0)).2) G

/-- Q uses the actual timer blocks on the positive-path reduction. It is not a
redefinition of actual schedule cost. -/
noncomputable def potential (T : WeightedTree V) (I : Input V) (θ : ℝ) : ℝ :=
  let J := positiveInput T I
  ((timerBlocks T J θ).map (fun b =>
    optimumReal T (restrictInput J b.batch) - (1-θ) * kappa T J b.batch)).sum

/-- Every positive-C affine acceptance equality in the interior. Zero-C tests
have no parameter-dependent breakpoint; simultaneous equalities are retained. -/
def Breakpoint (T : WeightedTree V) (I : Input V) (z : ℝ) : Prop :=
  let J := positiveInput T I
  0 < z ∧ z < 1 ∧ ∃ i k : ℕ, i < k ∧ k < (epochs J).length ∧
    0 < intervalC T J i k ∧
    epochTime J k - epochTime J i = intervalH T J z i k

/-- Genuine one-sided limits, not endpoint values or default lim operations. -/
def HasLeftPotentialLimit (T : WeightedTree V) (I : Input V) (z q : ℝ) : Prop :=
  Tendsto (potential T I) (𝓝[<] z) (𝓝 q)

def HasRightPotentialLimit (T : WeightedTree V) (I : Input V) (z q : ℝ) : Prop :=
  Tendsto (potential T I) (𝓝[>] z) (𝓝 q)

end MLAMaxDelay.RandomizedTimer


