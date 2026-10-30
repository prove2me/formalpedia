-- Prove2me | Definitions.Def_CloudAlloc_MWU_IsAlg1Run
-- name    : CloudAlloc_MWU_IsAlg1Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:38:33.564851+00:00
-- url     : https://prove2.me/theorems/0ef9cd9e-f484-4a0c-ac75-b8824630260e
-- title:
--   A run of Algorithm 1 (multiplicative weight update)
-- statement:
--   Given parameters $\varepsilon,\eta$, SLAs $\beta$ and loads $L_1,L_2,\dots$, a sequence of allocations $h_1,h_2,\dots$ is a **run of Algorithm 1** if $h_1\in\Delta_\varepsilon$ and for every $t$
--
--   $$
--   \widehat h_{t+1}(i)=h_t(i)\,e^{\eta g_t(i)},\qquad h_{t+1}=\pi_{\Delta_\varepsilon}(\widehat h_{t+1}),
--   $$
--
--   where the gains $g_t$ are computed from the run's own queues. The algorithm boosts active users, more so those below their SLA, and projects back onto the truncated simplex.
--
--   **Formalization Note** Lean time $t$ is the paper's $t+1$. The initial allocation is any point of $\Delta_\varepsilon$ ("$h_1$ any allocation over $\Delta_\varepsilon$"); given it, the run is unique. Parameter ranges are stated by the theorems.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, Algorithm 1, p. 9

import Mathlib
import Definitions.Def_CloudAlloc_MWU_IsKLProj
import Definitions.Def_CloudAlloc_MWU_gain

namespace CloudAlloc.MWU

/-- **A run of Algorithm 1 (Multiplicative Weight Update).**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency*, arXiv:1809.02688v3, Algorithm 1, p. 9:
"Input: Parameters `0 < ε ≤ 1/10, 0 < η < 1/3`. 1 Initialization: `h1` any allocation over `∆ε` and
`λ = ε²/(8N)`. 2 for `t = 1, . . . , T` do 3 Set allocation `ht`. … 6 Update allocation:
`ĥt+1(i) = ht(i)e^{ηgt(i)}`. `ht+1 = π∆ε(ĥt+1)`."

`IsAlg1Run N ε η β L h` says that the allocation sequence `h` is produced by Algorithm 1 with
parameters `ε, η`, SLAs `β` and loads `L`: the first allocation lies in `Δ_ε`, and each next
allocation is the KL projection onto `Δ_ε` of `ĥ_{t+1}(i) = h_t(i)·exp(η g_t(i))`.

**Formalization Note.** Lean time `t` is the paper's `t + 1` (`h 0` is `h_1`). The gain uses the
queues of the run itself, `queue h L`, so the feedback is the algorithm's own. The predicate fixes
`h_1` only up to membership in `Δ_ε` ("any allocation over `∆ε`"); given `h_1` the run is unique.
The parameter ranges are not part of the predicate; theorems state them. The run is defined on the
infinite horizon; the paper's horizon `T` enters only through the sums. -/
def IsAlg1Run (N : ℕ) (ε η : ℝ) (β : Fin N → ℝ) (L h : ℕ → Fin N → ℝ) : Prop :=
  h 0 ∈ truncSimplex N ε ∧
    ∀ t, IsKLProj N ε (fun i => h t i * Real.exp (η * gain N ε β h L t i)) (h (t + 1))

end CloudAlloc.MWU


