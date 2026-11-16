-- Prove2me | Definitions.Def_MLAMaxDelay_RandomizedTimer_Supplement_SubmodularTimer
-- name    : MLAMaxDelay_RandomizedTimer_Supplement_SubmodularTimer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:51:45.520361+00:00
-- url     : https://prove2.me/theorems/79ab6342-4aae-4b00-b611-bbf70d87e5c6
-- title:
--   Abstract OPT-Timer, θ-greedy partitions and the potential in a submodular model
-- statement:
--   In a submodular service-cost model (Definition 6.1), **OPT-Timer($\theta$)** is Algorithm 2 verbatim. A busy block starts when an epoch arrives while nothing is pending. While the block holds the revealed epochs $R[s,j]$, its deadline is
--
--   $$\tau=a_s+D(s,j)-(1-\theta)\,C(s,j),$$
--
--   where $D(s,j)$ is computed by the abstract dynamic program on the revealed block. The next epoch is accepted when it arrives no later than $\tau$ (arrival first, including equality); otherwise the block is served at $\tau$ by an attaining object and the next epoch starts a new block. Section 6 adds no zero-cost preprocessing. An online algorithm is a map from inputs to schedules whose services up to time $t$ depend only on the requests arrived by $t$.
--
--   For the analysis set $h_\theta(i,j)=D(i,j)-(1-\theta)C(i,j)$. An epoch interval beginning at $i$ is **θ-connected** when every later epoch $r$ in it satisfies $a_r-a_i\le h_\theta(i,r-1)$; the **θ-greedy partition** repeatedly takes the longest θ-connected prefix; a partition is **weakly θ-greedy** when its blocks are θ-connected and each nonfinal boundary $k$ of a block beginning at $i$ satisfies $a_k-a_i\ge h_\theta(i,k-1)$. With $P_\theta$ the partition produced by OPT-Timer($\theta$), the **potential** is $Q(\theta)=\sum_{B\in P_\theta}h_\theta(B)$. An interior **breakpoint** is a $z\in(0,1)$ at which $P_\theta$ is not locally constant. One-sided limits of $Q$ are genuine limits.
--
--   **Formalization Note** Epoch intervals are zero-based and half-open, and the abstract definitions mirror the published tree definitions of the base mission.
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), pp. 8, 11, 16, Algorithm 2, Section 4.2 and Section 6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Supplement_SubmodularModel

namespace MLAMaxDelay.RandomizedTimer.Supplement

open Filter
open scoped Topology

variable {U Obj : Type} [DecidableEq U]

/-- Equation (4) in the abstract model, p. 16: `τ = a_s + D(s,j) − (1−θ)C(s,j)`, where the
offline value of the revealed block is computed by the abstract dynamic program on that block
(no oracle for the true optimum). -/
noncomputable def smDeadline (M : SubmodularModel U Obj) (θ : ℝ) (B : Finset U) : ℝ :=
  smFirstArrival M B + (smOffline M B).value - (1 - θ) * M.κ B

structure SMTimerState (U : Type) where
  active : Option (Finset U)
  completed : List (Finset U × ℝ)

/-- One arrival transition of Algorithm 2: the complete epoch arriving at `a` is accepted when
`a ≤ τ` (arrival-first, including equality); otherwise the block is served at its deadline and
the epoch starts a new busy block. -/
noncomputable def smTimerStep (M : SubmodularModel U Obj) (I : Finset U) (θ : ℝ)
    (st : SMTimerState U) (a : ℝ) : SMTimerState U := by
  classical
  let R := I.filter (fun r => M.arrival r = a)
  exact match st.active with
  | none => ⟨some R, st.completed⟩
  | some B =>
    if a ≤ smDeadline M θ B then ⟨some (B ∪ R), st.completed⟩
    else ⟨some R, st.completed ++ [(B, smDeadline M θ B)]⟩

/-- The state after the first `k` epochs have been processed. -/
noncomputable def smTimerStateAfter (M : SubmodularModel U Obj) (I : Finset U) (θ : ℝ) (k : ℕ) :
    SMTimerState U :=
  ((smEpochs M I).take k).foldl (smTimerStep M I θ) ⟨none, []⟩

/-- The completed busy blocks with their service times; the last armed timer fires with no
end-of-input signal. -/
noncomputable def smTimerBlocks (M : SubmodularModel U Obj) (I : Finset U) (θ : ℝ) :
    List (Finset U × ℝ) :=
  let st := smTimerStateAfter M I θ (smEpochs M I).length
  match st.active with
  | none => st.completed
  | some B => st.completed ++ [(B, smDeadline M θ B)]

/-- Abstract OPT-Timer(θ), Algorithm 2 verbatim in the model of Definition 6.1 (Section 6 adds
no zero-cost preprocessing): each busy block is served at its deadline by an attaining object. -/
noncomputable def smOptTimer (M : SubmodularModel U Obj) (I : Finset U) (θ : ℝ) : SMSchedule Obj :=
  (smTimerBlocks M I θ).flatMap (fun b => attainingService M b.2 b.1)

/-- Revealed history at time `t`: the arrived occurrences. -/
noncomputable def smObserved (M : SubmodularModel U Obj) (I : Finset U) (t : ℝ) : Finset U := by
  classical
  exact I.filter (fun r => M.arrival r ≤ t)

noncomputable def smServiceHistory (S : SMSchedule Obj) (t : ℝ) : SMSchedule Obj := by
  classical
  exact S.filter (fun s => s.1 ≤ t)

/-- An online algorithm: services performed by time `t` depend only on what arrived by `t`. -/
def SMCausal (M : SubmodularModel U Obj) (A : Finset U → SMSchedule Obj) : Prop :=
  ∀ I J t, smObserved M I t = smObserved M J t →
    smServiceHistory (A I) t = smServiceHistory (A J) t

/-- `h_θ(i,j) = D(i,j) − (1−θ)C(i,j)` on half-open zero-based intervals. -/
noncomputable def smIntervalH (M : SubmodularModel U Obj) (I : Finset U) (θ : ℝ) (i j : ℕ) : ℝ :=
  smIntervalD M I i j - (1 - θ) * smIntervalC M I i j

/-- `[i,j)` is θ-connected when every later epoch `r` satisfies `a_r − a_i ≤ h_θ(i,r)`. -/
def SMConnected (M : SubmodularModel U Obj) (I : Finset U) (θ : ℝ) (i j : ℕ) : Prop :=
  ∀ r ∈ Finset.Ioo i j, smEpochTime M I r - smEpochTime M I i ≤ smIntervalH M I θ i r

def SMWeakCuts (M : SubmodularModel U Obj) (I : Finset U) (θ : ℝ) : List EpochBlock → Prop
  | [] => True
  | [_] => True
  | b :: c :: rest =>
    smIntervalH M I θ b.1 b.2 ≤ smEpochTime M I c.1 - smEpochTime M I b.1 ∧
      SMWeakCuts M I θ (c :: rest)

def SMWeaklyGreedy (M : SubmodularModel U Obj) (I : Finset U) (θ : ℝ)
    (i j : ℕ) (P : List EpochBlock) : Prop :=
  PartitionsInterval i j P ∧ (∀ b ∈ P, SMConnected M I θ b.1 b.2) ∧ SMWeakCuts M I θ P

/-- The θ-greedy partition: longest θ-connected prefix, repeated on the suffix. -/
noncomputable def smGreedyFrom (M : SubmodularModel U Obj) (I : Finset U) (θ : ℝ)
    (j : ℕ) : ℕ → ℕ → List EpochBlock
  | 0, _ => []
  | fuel + 1, i => by
    classical
    exact if i < j then
      let k := i + ((List.range (j - i)).takeWhile
        (fun q => decide (SMConnected M I θ i (i + q + 1)))).length
      (i, k) :: smGreedyFrom M I θ j fuel k
    else []

noncomputable def smGreedyPartition (M : SubmodularModel U Obj) (I : Finset U) (θ : ℝ) :
    List EpochBlock :=
  smGreedyFrom M I θ (smEpochs M I).length (smEpochs M I).length 0

/-- `Q(θ) = Σ_{B ∈ P_θ} (D(B) − (1−θ)C(B))` over the actual timer blocks. -/
noncomputable def smPotential (M : SubmodularModel U Obj) (I : Finset U) (θ : ℝ) : ℝ :=
  ((smTimerBlocks M I θ).map (fun b =>
    smOptimumReal M b.1 - (1 - θ) * M.κ b.1)).sum

/-- An interior breakpoint: a point of `(0,1)` at which the actual timer partition is not
locally constant (it changes in every neighbourhood). -/
def SMBreakpoint (M : SubmodularModel U Obj) (I : Finset U) (z : ℝ) : Prop :=
  0 < z ∧ z < 1 ∧ ∀ ε > 0, ∃ θ : ℝ, |θ - z| < ε ∧
    (smTimerBlocks M I θ).map Prod.fst ≠ (smTimerBlocks M I z).map Prod.fst

def SMHasLeftPotentialLimit (M : SubmodularModel U Obj) (I : Finset U) (z q : ℝ) : Prop :=
  Tendsto (smPotential M I) (𝓝[<] z) (𝓝 q)

def SMHasRightPotentialLimit (M : SubmodularModel U Obj) (I : Finset U) (z q : ℝ) : Prop :=
  Tendsto (smPotential M I) (𝓝[>] z) (𝓝 q)

end MLAMaxDelay.RandomizedTimer.Supplement


