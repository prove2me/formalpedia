-- Prove2me | Definitions.Def_DelayedGamesMAO_Supplement_boldIndex
-- name    : DelayedGamesMAO_Supplement_boldIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:50:44.897042+00:00
-- url     : https://prove2.me/theorems/6e549974-0a6b-4612-b7f6-88bc9c7f8c63
-- title:
--   Smallest-idle-index rule $i_t$ of the refined BOLD reduction
-- statement:
--   The **refined BOLD reduction** runs independent copies $B_1,B_2,\dots$ of an undelayed online learner, indexed in order of creation, and assigns every round $t$ to one copy. Fix delays $(d_s)$, so that the feedback of round $s$ arrives at the end of round $s+d_s$, and let $P_t=\{s\in[t-1]: s+d_s\ge t\}$ be the rounds still pending at the start of round $t$. A copy $k$ is **busy** at round $t$ when it holds a pending round, that is, $k=i_s$ for some $s\in P_t$. The index of round $t$ is the smallest copy that is not busy:
--
--   $$
--   i_t=\min\{k\ge 1:\ k\ne i_s\ \text{for every } s\in P_t\}.
--   $$
--
--   This is Algorithm 2's rule: scan the existing copies $1,\dots,r$ in order and take the first idle one, creating copy $r+1$ only when all are busy. Preferring earlier copies is what distinguishes the refinement from the original BOLD reduction, which may use any idle copy.
--
--   **Formalization Note** The indices are defined by strong recursion on $t$ (since $P_t\subseteq[t-1]$) as the least natural number outside $\{0\}\cup\{i_s:s\in P_t\}$. They depend only on the delays, so two players facing the same delays compute the same indices.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §4, p.7 and App. B.1, Algorithm 2, p.33

import Mathlib
import Definitions.Def_DelayedGamesMAO_pending

set_option autoImplicit false

namespace DelayedGamesMAO.Supplement

/-- **Instance index of the refined BOLD reduction (smallest idle index)** `i_t`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §4, p.7 and App. B.1, Algorithm 2, p.33.

Instances `B_1, B_2, …` are indexed in order of creation. At the start of round `t`, instance
`k` is *busy* iff it holds a round whose feedback has not arrived, i.e. `k = i_s` for some
pending round `s ∈ P_t = {s ∈ [t − 1] : s + d_s ≥ t}` (feedback of `s` is fed back to `B_{i_s}`
at the end of round `s + d_s`, Algorithm 2 lines 9–11). Round `t` is assigned the least index
`k ≥ 1` that is not busy (Algorithm 2 lines 2–7: scan `k = 1, …, r`, and create instance
`r + 1` when all existing ones are busy; since busy indices lie in `[r]`, this is the least
non-busy index).

**Formalization Note.** Defined by strong recursion on `t` (`P_t ⊆ [t − 1]`) as the least
natural number outside `{0} ∪ {i_s : s ∈ P_t}`. It depends on the delays only, so two players
facing the same delays compute the same indices. Defined for every `t`; only `t ∈ [T]` is read. -/
def boldIndex (d : ℕ → ℕ) (t : ℕ) : ℕ :=
  Nat.find (Infinite.exists_notMem_finset
    (insert 0 ((DelayedGamesMAO.pending d t).attach.image (fun s => boldIndex d s.1))))
termination_by t
decreasing_by
  all_goals
    have h := s.2
    simp only [DelayedGamesMAO.pending, Finset.mem_filter, Finset.mem_Icc] at h
    omega

end DelayedGamesMAO.Supplement


