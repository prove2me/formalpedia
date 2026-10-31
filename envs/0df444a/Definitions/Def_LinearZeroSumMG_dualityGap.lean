-- Prove2me | Definitions.Def_LinearZeroSumMG_dualityGap
-- name    : LinearZeroSumMG_dualityGap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:53:43.073437+00:00
-- url     : https://prove2.me/theorems/4cd06cdd-6c79-415e-9387-23ddd5039a62
-- title:
--   The total duality gap $\mathrm{Gap}(K)$, (4)
-- statement:
--   Along a run of Algorithm 1 with initial states $x^k_1$ and marginal policies $\pi^k=\mathcal P_1\sigma^k$, $\nu^k=\mathcal P_2\sigma^k$, the **total duality gap** of the first $K$ episodes is
--   $$
--   \mathrm{Gap}(K)=\sum_{k=1}^K\Big[V^{*,\nu^k}_1(x^k_1)-V^{\pi^k,*}_1(x^k_1)\Big].
--   $$
--   Each summand is the sum of the two players' exploitabilities in episode $k$; it is nonnegative and vanishes exactly when $(\pi^k,\nu^k)$ is a Nash equilibrium at $x^k_1$. In the special case of an MDP it reduces to the regret.
--
--   **Formalization Note** $V^{*,\nu}$ and $V^{\pi,*}$ are the best-response values (suprema and infima over measurable Markov policies).
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, §3.1, (4), p.9; §3.3, p.12

import Mathlib
import Definitions.Def_LinearZeroSumMG_bestV1
import Definitions.Def_LinearZeroSumMG_omni

namespace LinearZeroSumMG

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A] {d : ℕ}

/-- **The total duality gap `Gap(K)`, (4).**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, §3.1, (4), p.9: "we aim to bound the
following total duality gap: `Gap(K) := ∑_{k=1}^K [V^{*,ν^k}_1(x^k_1) − V^{π^k,*}_1(x^k_1)]`", where (§3.3,
p.12) `π^k_h(x) := 𝒫₁σ^k_h(x)` and `ν^k_h(x) := 𝒫₂σ^k_h(x)` are the marginals of the joint policy
`σ^k_h` computed by Algorithm 1 in episode `k`.

`dualityGap G P K xs as bs` is this sum along the observed data: `x^k_1 = xs k 1`, with the
marginal policies `piK`, `nuK` of Algorithm 1 run on `xs`, `as`, `bs`.

**Formalization Note** `V^{*,ν}` and `V^{π,*}` are the best-response values `bestV1`, `bestV2`
(suprema and infima over measurable stochastic Markov policies). -/
noncomputable def dualityGap (G : MarkovGame S A) (P : OmniParams S A d) (K : ℕ)
    (xs : ℕ → ℕ → S) (as bs : ℕ → ℕ → A) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K,
    (bestV1 G (nuK G P xs as bs k) 1 (xs k 1) - bestV2 G (piK G P xs as bs k) 1 (xs k 1))

end LinearZeroSumMG


