-- Prove2me | Definitions.Def_FiniteMemPOMDP_vN
-- name    : FiniteMemPOMDP_vN
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:57.293183+00:00
-- url     : https://prove2.me/theorems/f0f4d8cd-05f3-42c8-b0bd-fcbafdb14465
-- title:
--   $n$-stage value $v_n(p)$
-- statement:
--   The **$n$-stage game** $\Gamma_n$ has payoff and value
--
--   $$\gamma^p_n(\sigma)=\frac1n\,\mathbb E^p_\sigma\Big(\sum_{m=1}^n G_m\Big),\qquad v_n(p)=\sup_{\sigma\in\Sigma}\gamma^p_n(\sigma).$$
--
--   A strategy $\sigma$ is **0-optimal** in $\Gamma_n(p)$ when $\gamma^p_n(\sigma)=v_n(p)$.
--
--   **Formalization Note** The supremum is over all pure strategies; the payoffs lie in $[0,1]$, so it is genuine. At $n=0$ both are $0$.
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Definition A.1, p.23

import Mathlib
import Definitions.Def_FiniteMemPOMDP_lawOfPlays
import Definitions.Def_FiniteMemPOMDP_avgReward

open MeasureTheory

namespace FiniteMemPOMDP

variable {K A S : Type} [Fintype K] [Fintype A] [Fintype S] [Nonempty A] [Nonempty S]

/-- The `n`-stage payoff `γ^p_n(σ) := n^{−1} E^p_σ (∑_{m=1}^n Gm)`. -/
noncomputable def gammaN (Γ : POMDP K A S) (n : ℕ) (p : stdSimplex ℝ K) (σ : List (A × S) → A) :
    ℝ :=
  ∫ ω, avgReward Γ n ω ∂(lawOfPlays Γ p σ)

/-- **The value `v_n` of the `n`-stage game.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Definition A.1, p.23: "Given a POMDP
Γ = (K, A, S, q, g), we denote Γn the n-stage game with a value defined by
vn(p) := sup_{σ∈Σ} γ^p_n(σ), where γ^p_n(σ) := n^{−1} E^p_σ (∑_{m=1}^n Gm)."

`vN Γ n p` is the supremum over all pure strategies of the expected average reward over the first
`n` stages, starting from the belief `p`.

**Formalization Note** The averages lie in `[0, 1]` and the index type of the `⨆` is nonempty, so
it is a genuine supremum. At `n = 0` both `γ_0` and `v_0` are `0` (Lean's `1/0 = 0`); the paper
only uses `n ≥ 1`. -/
noncomputable def vN (Γ : POMDP K A S) (n : ℕ) (p : stdSimplex ℝ K) : ℝ :=
  ⨆ σ : List (A × S) → A, gammaN Γ n p σ

end FiniteMemPOMDP


