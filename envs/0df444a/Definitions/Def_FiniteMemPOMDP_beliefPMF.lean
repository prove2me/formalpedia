-- Prove2me | Definitions.Def_FiniteMemPOMDP_beliefPMF
-- name    : FiniteMemPOMDP_beliefPMF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:14.468643+00:00
-- url     : https://prove2.me/theorems/27ef7936-0f42-4b7f-b442-d4a03d3f19f5
-- title:
--   Beliefs $p\in\Delta(\mathcal K)$ and the Dirac belief $\delta_k$
-- statement:
--   A **belief** is a probability vector $p\in\Delta(\mathcal K)$, i.e. $p(k)\ge0$ and $\sum_k p(k)=1$; the initial state $K_1$ is drawn from the initial belief $p_1$. The paper identifies a state $k$ with the Dirac belief $\delta_k$ and writes $\mathbb P^k_\sigma$, $\gamma^k_\infty$ for $\mathbb P^{\delta_k}_\sigma$, $\gamma^{\delta_k}_\infty$.
--
--   `beliefPMF p` is the belief $p$ seen as a probability mass function on $\mathcal K$, and `pointBelief k` is $\delta_k$.
--
--   **Formalization Note** $\Delta(\mathcal K)$ is `stdSimplex ℝ K` throughout the mission.
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, §2.1, p.2

import Mathlib

namespace FiniteMemPOMDP

/-- **A belief `p ∈ ∆(K)` as a probability mass function.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, §2.1, p.2: "For a set C, denote ∆(C) the set
of probability measure distributions over C … Given p1 ∈ ∆(K), called initial belief".

Beliefs are elements of the standard simplex `stdSimplex ℝ K = {p : K → ℝ | p ≥ 0, ∑ p = 1}`.
`beliefPMF p` is the same distribution as a `PMF K`, with mass `p k` at `k`; it is used to draw
the initial state.

**Formalization Note** `∆(K)` is encoded as `stdSimplex ℝ K` throughout the mission (it carries
the topology and Borel σ-algebra needed for `∆(∆(K))`). -/
noncomputable def beliefPMF {K : Type} [Fintype K] (p : stdSimplex ℝ K) : PMF K :=
  PMF.ofFintype (fun k => ENNReal.ofReal (p.1 k)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => p.2.1 k), p.2.2, ENNReal.ofReal_one])

/-- **The Dirac belief `δ_k`.**
arXiv:1904.13360v2, §2.1, p.2: "For simplicity, identify K with the set of extremal points of
∆(K)." `pointBelief k` is the belief putting mass one on `k`; the paper writes `γ^k_∞`, `P^k_σ`
for `γ^{δ_k}_∞`, `P^{δ_k}_σ`. -/
def pointBelief {K : Type} [Fintype K] [DecidableEq K] (k : K) : stdSimplex ℝ K :=
  ⟨Pi.single k 1, single_mem_stdSimplex ℝ k⟩

end FiniteMemPOMDP


