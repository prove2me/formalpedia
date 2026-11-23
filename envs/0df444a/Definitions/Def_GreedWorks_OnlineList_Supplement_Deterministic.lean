-- Prove2me | Definitions.Def_GreedWorks_OnlineList_Supplement_Deterministic
-- name    : GreedWorks_OnlineList_Supplement_Deterministic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:53:49.063702+00:00
-- url     : https://prove2.me/theorems/ca0a3059-21b3-45e6-b205-4f124f882c5d
-- title:
--   Theorems 2 and 3, pp. 11, 13 — deterministic instances of the online-list and online-time models
-- statement:
--   The paper's model (§2, pp. 4–6) has a finite set $M$ of unrelated machines and jobs $j=1,\dots,n$; the processing time of job $j$ on machine $i$ is a random variable $P_{ij}$ with values in $\{0,1,2,\dots\}$, and $\mathbb E[P_{ij}]=\infty$ marks a pair $(i,j)$ on which job $j$ cannot run. Theorems 2 and 3 concern the **deterministic** problem, in which every processing time is a known number $p_{ij}$.
--
--   An instance is called **deterministic** if, for every pair $(i,j)$ on which job $j$ may run, there is a natural number $p_{ij}$ with
--
--   $$
--   P_{ij}=p_{ij}\quad\text{almost surely.}
--   $$
--
--   Pairs on which job $j$ cannot run (the page's $p_{ij}=\infty$) are not constrained. Two versions are defined: one for instances of the online-list model (jobs presented one by one, all available at time $0$), used by Theorem 2, and one for instances of the online-time model with release dates $r_j$, used by Theorem 3.
--
--   These predicates single out the deterministic special case of the stochastic model, so that the deterministic theorems are stated on the same instances, algorithms and comparator policies as the stochastic goal.
--
--   **Formalization Note** `IsDeterministic` applies to the published `GreedWorks.OnlineList.StochasticInstance` and `IsDeterministicTime` to the published `GreedWorks.OnlineTime.StochasticInstance`. The condition is almost-sure (the law of $P_{ij}$ is a point mass), which is the most general reading; on such an instance the mean $\mathbb E[P_{ij}]$ is $p_{ij}$. All other assumptions of the model (integer processing times with mean at least $1$ on eligible pairs, nonnegative weights, every job has an eligible machine) are fields of the published instance structures.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, p. 11, Theorem 2 and p. 13, Theorem 3 ("deterministic online scheduling problem"); model pp. 4–6, §2; p. 12, §6 (p_ij := E[P_ij])

import Mathlib
import Definitions.Def_GreedWorks_OnlineList_Model
import Definitions.Def_GreedWorks_OnlineTime_Model

namespace GreedWorks.OnlineList.Supplement

open MeasureTheory

/-- A deterministic online-list instance (Gupta–Moseley–Uetz–Xie, Theorem 2, p. 11): on every
eligible pair `(i, j)` the processing time `P_ij` is almost surely equal to a fixed natural number
`p_ij`, i.e. its law is a point mass.  Ineligible pairs are the page's `p_ij = ∞` and are not
constrained. -/
def IsDeterministic {M : Type*} [Fintype M] {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (I : GreedWorks.OnlineList.StochasticInstance M n Ω) : Prop :=
  ∀ i j, I.eligible i j → ∃ p : ℕ, ∀ᵐ ω ∂I.Pr, I.P i j ω = p

/-- A deterministic online-time instance (Theorem 3, p. 13): the same point-mass condition on
every eligible pair, for an instance with release dates. -/
def IsDeterministicTime {M : Type*} [Fintype M] {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (I : GreedWorks.OnlineTime.StochasticInstance M n Ω) : Prop :=
  ∀ i j, I.eligible i j → ∃ p : ℕ, ∀ᵐ ω ∂I.Pr, I.P i j ω = p

end GreedWorks.OnlineList.Supplement


