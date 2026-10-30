-- Prove2me | Definitions.Def_CloudAlloc_MWU_work
-- name    : CloudAlloc_MWU_work
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:36:21.089994+00:00
-- url     : https://prove2.me/theorems/ee42f976-e94c-477f-a4b4-628d1fcad861
-- title:
--   Work $w_t(i)=\min\{h_t(i),L_t(i)+Q_t(i)\}$
-- statement:
--   The work completed by user $i$ in step $t$ is
--
--   $$
--   w_t(i)=\min\{h_t(i),\ L_t(i)+Q_t(i)\}:
--   $$
--
--   the user processes as much of its queued and newly arrived work as its allocation allows.
--
--   **Formalization Note** Lean time $t$ is the paper's $t+1$. This is the model's definition; an active user whose queue plus new load is below its allocation does less work than its allocation.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, §1.1, p. 3 (definition of w_t(i))

import Mathlib
import Definitions.Def_CloudAlloc_MWU_queue

namespace CloudAlloc.MWU

/-- **The work `w_t(i)` done by user `i` in step `t`.**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency*, arXiv:1809.02688v3, §1.1, p. 3:
"The work completed by user i in step t is `wt(i) := min{ht(i), Lt(i) + Qt(i)}`."

`work h L t i = min{h_{t+1}(i), L_{t+1}(i) + Q_{t+1}(i)}`: in each step a user processes as much of
its queued plus newly arrived work as its allocation allows.

**Formalization Note.** Lean time `t` is the paper's time `t + 1`. This is the model's definition of
work; in particular an active user (non-empty queue) whose queue plus arriving load is below its
allocation does less work than its allocation (the remark "`h_t(i) = w_t(i)` for all active users"
on p. 8 is not built in). -/
noncomputable def work {N : ℕ} (h L : ℕ → Fin N → ℝ) (t : ℕ) (i : Fin N) : ℝ :=
  min (h t i) (L t i + queue h L t i)

end CloudAlloc.MWU


