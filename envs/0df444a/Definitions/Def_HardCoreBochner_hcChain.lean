-- Prove2me | Definitions.Def_HardCoreBochner_hcChain
-- name    : HardCoreBochner_hcChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:16.850436+00:00
-- url     : https://prove2.me/theorems/7fb4d440-1b0e-4a07-aaa5-ea3fa6e9a683
-- title:
--   Glauber dynamics $P_{GD}$ for the hard-core model and the law $\mu_{G,\lambda}$ on independent sets
-- statement:
--   Let $G=(V,E)$ be a finite graph and $\lambda>0$. The **hard-core model** is the distribution $\mu_{G,\lambda}(I)=\lambda^{|I|}/Z_G(\lambda)$ on the independent sets $I$ of $G$, with $Z_G(\lambda)=\sum_I\lambda^{|I|}$.
--
--   Its **Glauber dynamics** picks $v\in V$ uniformly at random and resamples the state of $v$ from $\mu$ conditioned on the rest. For independent sets $\sigma\ne\tau$,
--   $$P_{GD}(\sigma,\tau)=\begin{cases}\dfrac1{|V|}\,\dfrac{\mu(\tau)}{\mu(\sigma)+\mu(\tau)} & \text{if } \sigma\triangle\tau=\{v\} \text{ for some } v\in V,\\[4pt] 0&\text{otherwise,}\end{cases}$$
--   and the diagonal carries the remaining mass. This module records $P_{GD}$ as a matrix on the independent sets, together with $\mu_{G,\lambda}$ viewed as a distribution on them.
--
--   **Formalization Note** $P_{GD}$ is the published heat-bath matrix `MarkovMixing.glauber` for the published `MarkovMixing.hardcoreDist`, restricted to `MarkovMixing.IsHardcore G` by the published `MarkovMixing.subChain`.
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), §1, p.1 (hard-core model) and (1), p.2 (PDF pp.1–2)

import Definitions.Def_mm_coupling
import Definitions.Def_mm_mcmc

namespace HardCoreBochner

/-- The **Glauber dynamics for the hard-core model** `P_GD` on the independent sets of `G`.
Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), §1, (1), p.2: "In each step, the chain picks an element v ∈ V uniformly at random and resamples
its state (occupied or unoccupied) according to the measure µ conditioned on the current state of
all vertices in V \ {v}", with `P_GD(σ, τ) = (1/|V|) µ(τ)/(µ(σ) + µ(τ))` if `σ△τ = {v}`, and `0`
otherwise, for `σ ≠ τ`.

**Formalization Note** The published heat-bath matrix `MarkovMixing.glauber` for the published
hard-core law `MarkovMixing.hardcoreDist G λ` (`λ^{|σ|}/Z_G(λ)` on independent sets, `0` elsewhere),
restricted by the published `MarkovMixing.subChain` to the independent sets `MarkovMixing.IsHardcore G`.
Off the diagonal it is (1); the diagonal is the remaining mass. -/
noncomputable def hcChain {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (lam : ℝ) :
    Matrix {σ : V → Bool // MarkovMixing.IsHardcore G σ} {σ : V → Bool // MarkovMixing.IsHardcore G σ} ℝ :=
  MarkovMixing.subChain (MarkovMixing.glauber (MarkovMixing.hardcoreDist G lam))
    (MarkovMixing.IsHardcore G)

/-- The hard-core law `µ_{G,λ}` as a distribution on the independent sets of `G` (the state space of
`hcChain`). Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), §1, p.1. -/
noncomputable def hcLaw {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (lam : ℝ) : {σ : V → Bool // MarkovMixing.IsHardcore G σ} → ℝ :=
  fun σ => MarkovMixing.hardcoreDist G lam σ.1

end HardCoreBochner


