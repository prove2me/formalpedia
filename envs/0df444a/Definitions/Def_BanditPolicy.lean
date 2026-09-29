-- Prove2me | Definitions.Def_BanditPolicy
-- name    : BanditPolicy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-17T20:09:50.385154+00:00
-- url     : https://prove2.me/theorems/cf0b6cda-7014-4926-858f-21803d1c81e3
-- statement:
--   A policy interacting with a $k$-armed bandit over $n$ rounds in the canonical bandit model (Section 4.6): at round $t$ the policy selects arm $A_t \in [k]$ as a (measurable, possibly randomized) function of the history $A_1, X_1, \dots, A_{t-1}, X_{t-1}$, and observes reward $X_t \sim P_{A_t}$. The interconnection of policy $\pi$ and environment $\nu$ induces the probability measure $\mathbb{P}_{\nu\pi}$ on the space of histories. Also includes the arm-pull counts
--
--   $$T_i(t) = \sum_{s\le t} \mathbb{1}\{A_s = i\}$$
--
--   and the per-arm empirical means $\hat\mu_i(t)$.
-- source:
--   L&S Section 4.6 (canonical bandit model), pp.63-66

import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Definitions.Def_StochasticBandit

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), §4.6:
the canonical bandit model.

A history of `n` completed rounds is a finite sequence of (arm, reward) pairs.
A policy is a family of Markov kernels, one per round, mapping the observed
history to a distribution over the next arm. The interconnection of a policy
`π` with an environment `ν` induces the canonical probability measure
`banditMeasure ν π n` on histories of length `n`:
round `t` samples `A_t ~ π(· | history)` then `X_t ~ P_{A_t}`, and appends
`(A_t, X_t)` to the history.

Also defines the arm pull counts `T_i` and per-arm empirical means `μ̂_i`
(L&S §4.5 / Ch 6-7), which are functions of the history.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- A history of `n` completed bandit rounds: the sequence
`(A_1, X_1), …, (A_n, X_n)` of (arm, reward) pairs (L&S §4.6). -/
abbrev BanditHistory (k n : ℕ) := Fin n → Fin k × ℝ

/-- A bandit policy (L&S §4.6): for each round, a Markov kernel from the
observed history to a distribution over the arm played next. -/
structure BanditPolicy (k : ℕ) where
  /-- The conditional distribution of the arm played in round `n + 1`
  given the history of the first `n` rounds. -/
  select : (n : ℕ) → Kernel (BanditHistory k n) (Fin k)
  /-- Each round's selection kernel is a Markov kernel. -/
  markov : ∀ n, IsMarkovKernel (select n)

attribute [instance] BanditPolicy.markov

/-- The reward kernel of an environment: arm `i` yields a reward drawn
from `ν.P i`. -/
noncomputable def banditRewardKernel {k : ℕ} (ν : StochasticBandit k) :
    Kernel (Fin k) ℝ :=
  Kernel.ofFunOfCountable ν.P

instance {k : ℕ} (ν : StochasticBandit k) : IsMarkovKernel (banditRewardKernel ν) :=
  ⟨fun i ↦ ν.prob i⟩

/-- One round of the canonical bandit model: given the history, sample the
arm `A ~ π.select n` and the reward `X ~ P_A`, returning the pair `(A, X)`. -/
noncomputable def banditStepKernel {k : ℕ} (ν : StochasticBandit k)
    (π : BanditPolicy k) (n : ℕ) :
    Kernel (BanditHistory k n) (Fin k × ℝ) :=
  (π.select n).compProd
    ((banditRewardKernel ν).comap Prod.snd measurable_snd)

instance banditStepKernel.instIsMarkovKernel {k : ℕ} (ν : StochasticBandit k)
    (π : BanditPolicy k) (n : ℕ) : IsMarkovKernel (banditStepKernel ν π n) := by
  rw [banditStepKernel]
  infer_instance

/-- Appending one round to a history is measurable. -/
lemma measurable_banditHistorySnoc {k n : ℕ} :
    Measurable (fun p : BanditHistory k n × (Fin k × ℝ) ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2) := by
  rw [measurable_pi_iff]
  intro t
  by_cases ht : (t : ℕ) < n
  · have : (fun p : BanditHistory k n × (Fin k × ℝ) ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2 t) =
        fun p ↦ p.1 (Fin.castLT t ht) := by
      funext p
      simp [Fin.snoc, ht]
    rw [this]
    exact (measurable_pi_apply _).comp measurable_fst
  · have : (fun p : BanditHistory k n × (Fin k × ℝ) ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2 t) =
        fun p ↦ p.2 := by
      funext p
      simp [Fin.snoc, ht]
    rw [this]
    exact measurable_snd

/-- The canonical bandit probability measure (L&S §4.6): the distribution
`ℙ_{νπ}` of the history after `n` rounds of the interconnection of policy `π`
and environment `ν`. -/
noncomputable def banditMeasure {k : ℕ} (ν : StochasticBandit k)
    (π : BanditPolicy k) : (n : ℕ) → Measure (BanditHistory k n)
  | 0 => Measure.dirac (fun t ↦ t.elim0)
  | n + 1 =>
      ((banditMeasure ν π n).compProd (banditStepKernel ν π n)).map
        (fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2)

instance banditMeasure.instIsProbabilityMeasure {k : ℕ} (ν : StochasticBandit k)
    (π : BanditPolicy k) (n : ℕ) : IsProbabilityMeasure (banditMeasure ν π n) := by
  induction n with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ n ih =>
      rw [banditMeasure]
      haveI := ih
      exact Measure.isProbabilityMeasure_map
        measurable_banditHistorySnoc.aemeasurable

/-- The number of times arm `i` was played in history `h`:
`T_i(n) = ∑_{t=1}^n 𝟙{A_t = i}` (L&S §4.5). -/
def armPullCount {k n : ℕ} (i : Fin k) (h : BanditHistory k n) : ℕ :=
  {t | (h t).1 = i}.toFinset.card

/-- The empirical mean `μ̂_i` of arm `i` in history `h`: the average of the
rewards observed in the rounds where arm `i` was played (L&S Ch 6-7);
junk value `0` if the arm was never played. -/
noncomputable def armEmpiricalMean {k n : ℕ} (i : Fin k) (h : BanditHistory k n) : ℝ :=
  (∑ t ∈ {t | (h t).1 = i}.toFinset, (h t).2) / armPullCount i h

end BanditAlgorithm


