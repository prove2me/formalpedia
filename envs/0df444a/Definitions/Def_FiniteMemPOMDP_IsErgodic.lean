-- Prove2me | Definitions.Def_FiniteMemPOMDP_IsErgodic
-- name    : FiniteMemPOMDP_IsErgodic
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:59.452281+00:00
-- url     : https://prove2.me/theorems/23ea0aad-5654-470d-bc8d-9f5a4c263b24
-- title:
--   Ergodic strategy for $p^*$
-- statement:
--   Let $p^*\in\Delta(\mathcal K)$. A strategy $\sigma$ is **ergodic for $p^*$** if for every $k\in\operatorname{supp}(p^*)$
--
--   $$\frac1n\sum_{m=1}^n G_m\xrightarrow[n\to\infty]{}\gamma^k_\infty(\sigma)\qquad\mathbb P^k_\sigma\text{-a.s.}$$
--
--   That is, started from each state in the support, the average rewards converge almost surely, and the limit is a constant depending only on the initial state.
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Definition 5.6, p.14

import Mathlib
import Definitions.Def_FiniteMemPOMDP_gammaInf

open MeasureTheory Filter Topology

namespace FiniteMemPOMDP

variable {K A S : Type} [Fintype K] [DecidableEq K] [Fintype A] [Fintype S] [Nonempty A]
  [Nonempty S]

/-- **Ergodic strategy.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Definition 5.6, p.14: "Let p∗ ∈ ∆(K). We say
that a strategy σ is ergodic for p∗ if the following holds for all k ∈ supp(p∗)
((1/n) ∑_{m=1}^n Gm) −→_{n→∞} γ^k_∞(σ)  P^k_σ − a.s."

`IsErgodic Γ p σ` says: for every state `k` with `p k > 0`, under the law of plays started from
the Dirac belief `δ_k`, the averages `(1/n) ∑_{m=1}^n G_m` converge almost surely to
`γ^k_∞(σ) = gammaInf Γ δ_k σ`. -/
def IsErgodic (Γ : POMDP K A S) (p : stdSimplex ℝ K) (σ : List (A × S) → A) : Prop :=
  ∀ k : K, 0 < p.1 k →
    ∀ᵐ ω ∂(lawOfPlays Γ (pointBelief k) σ),
      Tendsto (fun n => avgReward Γ n ω) atTop (𝓝 (gammaInf Γ (pointBelief k) σ))

end FiniteMemPOMDP


