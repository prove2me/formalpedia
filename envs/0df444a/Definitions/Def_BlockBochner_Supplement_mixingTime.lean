-- Prove2me | Definitions.Def_BlockBochner_Supplement_mixingTime
-- name    : BlockBochner_Supplement_mixingTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:29:53.733195+00:00
-- url     : https://prove2.me/theorems/312656bf-d7da-4669-815e-1a8d4dfe3cd3
-- title:
--   Mixing time (worst-case start, threshold $1/4$)
-- statement:
--   For a Markov chain with transition kernel $P$ on a state space $S$ and stationary law $\mu$, the mixing time is
--   $$
--   t_{\mathrm{mix}}=\inf\Big\{t\in\mathbb Z_{\ge0}:\ \sup_{\sigma\in S}\big\|P^t(\sigma,\cdot)-\mu\big\|_{\mathrm{TV}}\le\tfrac14\Big\},
--   $$
--   where $P^t$ is the $t$-step kernel and $\|P-Q\|_{\mathrm{TV}}=\sup_A|P(A)-Q(A)|$ over measurable sets $A$.
--
--   **Formalization Note** Valued in $\mathbb N\cup\{\infty\}$: if no $t$ qualifies the value is $\infty$ (never mixes), not $0$. $P^t$ is the $t$-fold kernel composition ($P^0$ the identity kernel). The total variation distance is the published `totalVariationDistance`. The condition is imposed at every starting state $\sigma$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228 (sha256 e4bc2683…4a27706), Sec. 1.1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_ProbabilityTheory_chapter_08_def_8_5_F000

open MeasureTheory ProbabilityTheory

namespace BlockBochner.Supplement

/-- **Mixing time.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 1.1, p.2: the mixing time of a chain with
transition kernel `P` and stationary law `µ` is
```
inf { t ∈ ℤ_{≥0} : sup_{σ∈S} ‖P^t(σ, ·) − µ‖_TV ≤ 1/4 }.
```

**Formalization Note** `P^t` is the `t`-fold kernel composition (`Monoid (Kernel α α)`,
`P^0 = Kernel.id`). `‖·‖_TV` is the published `totalVariationDistance`
(`sup_A |P(A) − Q(A)|` over measurable `A`). The condition is required at **every** starting
configuration `σ` (worst-case start). The value is in `ℕ∞`, so an empty set gives `⊤`
(never mixes), not `0`. -/
noncomputable def mixingTime {S : Type*} [MeasurableSpace S] (P : Kernel S S) (μ : Measure S) :
    ℕ∞ :=
  ⨅ (t : ℕ) (_ : ∀ σ : S, totalVariationDistance ((P ^ t) σ) μ ≤ 1 / 4), (t : ℕ∞)

end BlockBochner.Supplement


