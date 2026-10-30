-- Prove2me | Definitions.Def_CloudAlloc_MWU_userWork
-- name    : CloudAlloc_MWU_userWork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:37:32.366464+00:00
-- url     : https://prove2.me/theorems/6d1d11dd-147e-4acc-82a0-995ba648b9b1
-- title:
--   Cumulative work of one user $\sum_{\tau=1}^t w_\tau(i)$
-- statement:
--   The cumulative work of user $i$ up to time $t$ under allocations $h$ on loads $L$ is
--
--   $$
--   \sum_{\tau=1}^t w_\tau(i).
--   $$
--
--   This is the quantity compared in the SLA guarantees (Theorem 1, clause 2, and Theorem 4).
--
--   **Formalization Note** `Finset.range t` is the paper's $\tau=1,\dots,t$ (Lean time is shifted by one).
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, Theorem 1, p. 5; Theorem 4, p. 10

import Mathlib
import Definitions.Def_CloudAlloc_MWU_work

namespace CloudAlloc.MWU

/-- **Cumulative work of one user, `Σ_{τ=1}^t w_τ(i)`.**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency*, arXiv:1809.02688v3, Theorem 1, p. 5, and Theorem 4, p. 10: "`Σ_{τ=1}^t wτ(i)`".

`userWork h L i t` is the work done by user `i` in the first `t` steps when the allocations `h`
serve the loads `L`.

**Formalization Note.** Lean time `τ` is the paper's `τ + 1`, so `Finset.range t` is the paper's
`τ = 1, …, t`. -/
noncomputable def userWork {N : ℕ} (h L : ℕ → Fin N → ℝ) (i : Fin N) (t : ℕ) : ℝ :=
  ∑ τ ∈ Finset.range t, work h L τ i

end CloudAlloc.MWU


