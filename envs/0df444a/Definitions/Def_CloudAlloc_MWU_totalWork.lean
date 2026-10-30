-- Prove2me | Definitions.Def_CloudAlloc_MWU_totalWork
-- name    : CloudAlloc_MWU_totalWork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:36:55.710461+00:00
-- url     : https://prove2.me/theorems/188911fa-79a4-44f4-ac80-0d03f75c04b6
-- title:
--   Total work $\sum_{t=1}^T\sum_i w_t(i)$
-- statement:
--   The total work of an allocation sequence $h_1,\dots,h_T$ on loads $L_1,\dots,L_T$ is
--
--   $$
--   \mathrm{work}_{h_1,\dots,h_T}=\sum_{t=1}^T\sum_{i=1}^N w_t(i),
--   $$
--
--   where $w_t$ is the work of §1.1 computed with the queues of this allocation sequence. For Algorithm 1 this is $\mathrm{work}_{\mathrm{alg}}$ (or $\mathrm{work}_{\mathrm{alg},t}$ up to time $t$).
--
--   **Formalization Note** `Finset.range T` is the paper's $t=1,\dots,T$ (Lean time is shifted by one).
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, §1.2, p. 5 (work_{h*} − work_alg display); Theorem 3, p. 10 (work_{alg,t})

import Mathlib
import Definitions.Def_CloudAlloc_MWU_work

namespace CloudAlloc.MWU

/-- **Total work `work_{h_1,…,h_T} = Σ_{t=1}^T Σ_i w_t(i)`.**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency*, arXiv:1809.02688v3, §1.2, p. 5 (unnumbered display): "`work_{h∗1,...,h∗T} − work_alg = Σ_{t=1}^T Σ_i w∗t(i) − Σ_{t=1}^T Σ_i wt(i)`";
and Theorem 3, p. 10: "`work_{alg,t} = Σ_i Σ_{τ=1}^t wτ(i)`".

`totalWork h L T` is the total work done by all users in the first `T` steps when the allocations
`h` serve the loads `L`.

**Formalization Note.** Lean time `t` is the paper's `t + 1`, so `Finset.range T` is the paper's
`t = 1, …, T`. -/
noncomputable def totalWork {N : ℕ} (h L : ℕ → Fin N → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, ∑ i, work h L t i

end CloudAlloc.MWU


