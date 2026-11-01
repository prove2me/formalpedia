-- Prove2me | Definitions.Def_GreedyReusableNet_History
-- name    : GreedyReusableNet_History
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:33:55.114349+00:00
-- url     : https://prove2.me/theorems/667c6afe-0ee6-43ea-9f2f-b4b5a4d98d2d
-- title:
--   Histories, counting vectors and available arms
-- statement:
--   A **history** records, for each past period, the action set taken, the set of activated bundles and the blocking times drawn for the activated arms. From a history $h$ of $t$ periods one reads:
--
--   1. the **counting vector** $n_t$: $n_{t,i}$ is the number of past periods in which arm $i$ belonged to an activated bundle (Algorithm 1, step 7);
--   2. the **available arms** at period $t$: arm $i$ is available unless some activation of $i$ at a period $k$ with blocking time $b$ has $t\in(k,k+b]$;
--   3. an action set $\mathcal A$ is **available** if $\mathcal A\in\mathscr A_t$ and every arm of every bundle of $\mathcal A$ is available.
--
--   Initially (empty history) all counts are $0$ and every arm is available. The history, together with the instance, is all the information an online policy may use.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.1, pp.8–11 (counting vector p.8; availability p.9; blocking p.11)

import Mathlib
import Definitions.Def_GreedyReusableNet_PeriodData

namespace GreedyReusableNet

/-- **The record of one period**: the action set taken, the activated bundles and the times
`b_{t,i}` drawn for the activated arms (Simchi-Levi, Zheng & Zhu, SSRN 3981123, Algorithm 1 steps 3–6, pp.8–9). The
entry of an arm that was not activated is recorded as `0` and never read. -/
abbrev Step (N : ℕ) := Finset (Finset (Fin N)) × Finset (Finset (Fin N)) × (Fin N → ℕ)

/-- **The history** of a policy: the records of the periods so far, oldest first; its length is
the current period (0-based). This is "all the information available by time t" (p.9) apart
from the instance itself, which a policy may know in full (p.15). -/
abbrev History (N : ℕ) := List (Step N)

/-- The arms of the activated bundles `S` ("each arm `i ∈ B` for some `B ∈ 𝒜^π_{t,act}`",
Algorithm 1 step 5, p.9). -/
def activatedArms {N : ℕ} (S : Finset (Finset (Fin N))) : Finset (Fin N) :=
  S.biUnion id

/-- The bundles activated in period `t` of the history `h` (`𝒜_{t,act}`; empty if `h` has no
period `t`). -/
def activatedAt {N : ℕ} (h : History N) (t : ℕ) : Finset (Finset (Fin N)) :=
  (h.getD t (∅, ∅, fun _ => 0)).2.1

/-- The action set taken in period `t` of the history `h` (`𝒜_t`; empty if `h` has no
period `t`). -/
def actionAt {N : ℕ} (h : History N) (t : ℕ) : Finset (Finset (Fin N)) :=
  (h.getD t (∅, ∅, fun _ => 0)).1

/-- **The counting vector** `n_t` (SSRN 3981123, §2.1, p.8): the number of periods of the history
in which arm `i` was activated; Algorithm 1 step 7 adds `1` for each arm of an activated bundle
(once per period). -/
def counts {N : ℕ} (h : History N) (i : Fin N) : ℕ :=
  (h.filter (fun st => decide (i ∈ activatedArms st.2.1))).length

/-- **The available arms at period `t`** (SSRN 3981123, §2.1, "Blocking Time", p.11): an arm
activated at period `k` with blocking time `b` is blocked during `(k, k + b]`, so arm `i` is
available at `t` when every activation `k` of `i` in the history has `k + b_{k,i} < t`.
Initially (empty history) every arm is available. -/
noncomputable def freeArms {N : ℕ} (h : History N) (t : ℕ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun i => ∀ (k : ℕ) (hk : k < h.length),
    i ∈ activatedArms (h[k]'hk).2.1 → k + (h[k]'hk).2.2 i < t)

/-- **An available action set** (SSRN 3981123, §2.1, p.9): `A ∈ 𝒜_t` and every arm of every
bundle of `A` lies in the set `free` of available arms ("An action set can be taken only if all
bundles included in `𝒜_t` are available"). -/
def IsAvailableSet {N : ℕ} (d : PeriodData N) (free : Finset (Fin N))
    (A : Finset (Finset (Fin N))) : Prop :=
  A ∈ d.actions ∧ ∀ B ∈ A, B ⊆ free

end GreedyReusableNet


