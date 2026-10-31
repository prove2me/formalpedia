-- Prove2me | Definitions.Def_FiniteMemPOMDP_gammaInf
-- name    : FiniteMemPOMDP_gammaInf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:50.183291+00:00
-- url     : https://prove2.me/theorems/3ffb36a6-9d6d-48bb-afd7-54c058c8e691
-- title:
--   Long-run payoff $\gamma^{p_1}_\infty(\sigma)$
-- statement:
--   The **long-run payoff** of a strategy $\sigma$ from the initial belief $p_1$ is the expected liminf of the average rewards:
--
--   $$\gamma^{p_1}_\infty(\sigma)=\mathbb E^{p_1}_\sigma\Big(\liminf_{n\to+\infty}\frac1n\sum_{m=1}^n G_m\Big).$$
--
--   **Formalization Note** The averages lie in $[0,1]$, so the liminf is a genuine real liminf, the integrand is measurable and bounded, and the integral is the expectation (proved in the mission's verification file).
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, §2.1, p.2

import Mathlib
import Definitions.Def_FiniteMemPOMDP_lawOfPlays
import Definitions.Def_FiniteMemPOMDP_avgReward

open MeasureTheory Filter

namespace FiniteMemPOMDP

variable {K A S : Type} [Fintype K] [Fintype A] [Fintype S] [Nonempty A] [Nonempty S]

/-- **The long-run (liminf-average) payoff `γ^{p1}_∞(σ)`.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, §2.1, p.2:
"γ^{p1}_∞(σ) := E^{p1}_σ ( lim inf_{n→+∞} (1/n) ∑_{m=1}^n Gm )".

`gammaInf Γ p σ` is the expectation, under the law of plays `P^p_σ`, of
`liminf_{n→∞} (1/n) ∑_{m=1}^n G_m`.

**Formalization Note** The averages lie in `[0, 1]`, so the `liminf` is a genuine real liminf
(not a junk value), the integrand is measurable and bounded, and the Bochner integral is the
paper's expectation (checked in the mission's verification file). -/
noncomputable def gammaInf (Γ : POMDP K A S) (p : stdSimplex ℝ K) (σ : List (A × S) → A) : ℝ :=
  ∫ ω, liminf (fun n => avgReward Γ n ω) atTop ∂(lawOfPlays Γ p σ)

end FiniteMemPOMDP


