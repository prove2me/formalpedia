-- Prove2me | Definitions.Def_RecoveringBandits_OPT
-- name    : RecoveringBandits_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:54:17.180991+00:00
-- url     : https://prove2.me/theorems/746f64db-0dd6-41c8-93e1-f925b821788a
-- title:
--   The offline optimum $\mathrm{OPT}_R[K,T]$, problem (1)
-- statement:
--   A **feasible joint schedule** up to horizon $T$ with capacity $K$ assigns to every arm $i$ a set of pull times $S_i\subseteq\{1,\dots,T\}$ such that in every period $t$ at most $K$ arms are pulled. The **offline optimum** is
--
--   $$\mathrm{OPT}_R[K,T]=\max\ \sum_{i\in[N]}\sum_{j=1}^{J_i}R_i(s_{i,j}-s_{i,j-1})$$
--
--   over all feasible joint schedules, with $s_{i,0}=0$. It is the best total expected reward achievable when all recovery functions are known.
--
--   **Formalization Note** The feasible set is finite and contains the empty schedule, so the supremum is a maximum. The paper writes $J_i\in[T]$; here an arm may also never be pulled ($J_i=0$), so this maximum is at least the paper's.
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, §3.1, problem (1), pp.7–8

import Mathlib
import Definitions.Def_RecoveringBandits_schedReward

namespace RecoveringBandits

/-- **A feasible joint schedule** of the offline problem (1) (arXiv:2106.14813v2, §3.1, (1),
pp.7–8): every arm's pull times lie in `[1, T]` and in every period at most `K` arms are pulled
(`∑_i ∑_j 1{s_{i,j} = t} ≤ K` for all `t ∈ [T]`).

**Formalization Note.** Arm `i`'s schedule `0 = s_{i,0} < s_{i,1} < ⋯ < s_{i,J_i} ≤ T` is the
finite set `S i = {s_{i,1}, …, s_{i,J_i}}`. The paper writes `J_i ∈ [T]`; here `J_i = 0` (an arm
never pulled) is also allowed, so the feasible set contains the paper's and is never empty. -/
def IsFeasibleSchedule {N : ℕ} (K T : ℕ) (S : Fin N → Finset ℕ) : Prop :=
  (∀ i, S i ⊆ Finset.Icc 1 T) ∧
    ∀ t : ℕ, (Finset.univ.filter (fun i => t ∈ S i)).card ≤ K

/-- **The offline optimum `OPT_R[K, T]`** (arXiv:2106.14813v2, §3.1, (1), pp.7–8): the maximum,
over feasible joint schedules up to `T` with at most `K` pulls per period, of the total mean
reward `∑_i ∑_j R_i(s_{i,j} − s_{i,j−1})`.

**Formalization Note.** The feasible set is finite (every `S i ⊆ [1, T]`) and nonempty (all
`S i = ∅`), so this `sSup` is the maximum. `J_i = 0` is allowed (see `IsFeasibleSchedule`), which
can only increase the maximum relative to the paper's `J_i ∈ [T]`. -/
noncomputable def OPT {N : ℕ} (R : Fin N → ℕ → ℝ) (K T : ℕ) : ℝ :=
  sSup ((fun S : Fin N → Finset ℕ => ∑ i, schedReward (R i) (S i)) ''
    {S | IsFeasibleSchedule K T S})

end RecoveringBandits


