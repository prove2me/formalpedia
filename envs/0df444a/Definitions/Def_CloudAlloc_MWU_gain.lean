-- Prove2me | Definitions.Def_CloudAlloc_MWU_gain
-- name    : CloudAlloc_MWU_gain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:37:56.786793+00:00
-- url     : https://prove2.me/theorems/8645a572-dc6e-4074-ac9b-ad4ed6b735e9
-- title:
--   Gain $g_t(i)$ of Algorithm 1
-- statement:
--   Fix SLAs $\beta(1),\dots,\beta(N)$ and $\lambda=\varepsilon^2/(8N)$. At step $t$ a user is **active** if its queue is non-empty, $Q_t(i)>0$. Let $A^1_t$ be the active users with $h_t(i)<\beta(i)$, $A^2_t$ the other active users, and $B_t$ the inactive users. The gain is
--
--   $$
--   g_t(i)=\begin{cases}1+\lambda, & i\in A^1_t,\\ 1, & i\in A^2_t,\\ 0, & i\in B_t.\end{cases}
--   $$
--
--   **Formalization Note** Lean time $t$ is the paper's $t+1$; the feedback is the queue at the start of the step. The comparison with $\beta(i)$ is strict, as printed.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, Algorithm 1, p. 9, lines 1, 4–5

import Mathlib
import Definitions.Def_CloudAlloc_MWU_queue

namespace CloudAlloc.MWU

/-- **The gain `g_t(i)` of Algorithm 1.**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency*, arXiv:1809.02688v3, Algorithm 1, p. 9, lines 4–5:
"Read active and inactive users `At` and `Bt`. `A¹t = {i ∈ At : ht(i) < β(i)}`, `A²t = At \ A¹t`.
Set gain function `gt(i) = 1 + λ` if `i ∈ A¹t`; `1` if `i ∈ A²t`; `0` if `i ∈ Bt`", with
"`λ = ε²/(8N)`" (line 1); active users are those with "`Qt(i) > 0`" (p. 3).

`gain N ε β h L t i` is `1 + ε²/(8N)` if user `i` has a non-empty queue and an allocation strictly
below its SLA `β(i)`, `1` if its queue is non-empty and its allocation is at least `β(i)`, and `0`
if its queue is empty.

**Formalization Note.** Lean time `t` is the paper's `t + 1`; the feedback read at step `t + 1` is the
queue at its start, `queue h L t` (= `Q_{t+1}`). "Active" is `0 < Q`, and `A¹` uses the strict
`h_t(i) < β(i)`, as printed. -/
noncomputable def gain (N : ℕ) (ε : ℝ) (β : Fin N → ℝ) (h L : ℕ → Fin N → ℝ) (t : ℕ) (i : Fin N) : ℝ :=
  if 0 < queue h L t i then (if h t i < β i then 1 + ε ^ 2 / (8 * N) else 1) else 0

end CloudAlloc.MWU


