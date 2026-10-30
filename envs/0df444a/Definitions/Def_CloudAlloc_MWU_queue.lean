-- Prove2me | Definitions.Def_CloudAlloc_MWU_queue
-- name    : CloudAlloc_MWU_queue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:35:49.873803+00:00
-- url     : https://prove2.me/theorems/c46913e5-b32e-4c33-af80-1e80ccbc28a6
-- title:
--   Queues $Q_t(i)$ of the allocation model
-- statement:
--   Allocations $h_t\in\mathbb R^N$ serve loads $L_t\in\mathbb R^N$ over discrete time. User $i$'s queue starts empty, $Q_1(i)=0$, and after step $t$ becomes
--
--   $$
--   Q_{t+1}(i)=\max\{0,\ L_t(i)+Q_t(i)-h_t(i)\}.
--   $$
--
--   This is the queue update of the model of §1.1; the queues are the feedback the allocator observes (empty or not).
--
--   **Formalization Note** Lean time $t$ is the paper's time $t+1$: `queue h L t` is $Q_{t+1}$, `h t` is $h_{t+1}$, `L t` is $L_{t+1}$. The model leaves $Q_1$ implicit; the LP (P_ε) of p. 11 fixes it to $0$.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, §1.1, p. 3 (queue update)

import Mathlib

namespace CloudAlloc.MWU

/-- **The queues `Q_t(i)` of the model.**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency*, arXiv:1809.02688v3, §1.1, p. 3:
"The queues at the end of the time step are updated accordingly,
`Qt+1(i) = max{0, Lt(i) + Qt(i) − ht(i)}`."

`queue h L t i` is the remaining work of user `i` at the start of step `t + 1` (the paper's
`Q_{t+1}(i)`) when the allocations `h` serve the loads `L`. The queues start empty and are
updated by `Q_{t+1}(i) = max{0, L_t(i) + Q_t(i) − h_t(i)}`.

**Formalization Note.** Lean time `t` is the paper's time `t + 1`: `h t` is `h_{t+1}`, `L t` is
`L_{t+1}` and `queue h L t` is `Q_{t+1}`. The initial queue `Q_1` is `0`: the model on p. 3 leaves
it implicit, and the LP constraint (1) of `(P_ε)` (p. 11), `Σ_{s≤t} w_s(i) ≤ Σ_{s≤t} L_s(i)`, fixes
it to `0`. Allocations and loads are arbitrary real sequences here; theorems state their own
hypotheses. -/
noncomputable def queue {N : ℕ} (h L : ℕ → Fin N → ℝ) : ℕ → Fin N → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun i => max 0 (L t i + queue h L t i - h t i)

end CloudAlloc.MWU


