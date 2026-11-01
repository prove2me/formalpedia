-- Prove2me | Definitions.Def_CongestionTaxes_equilibriumCosts
-- name    : CongestionTaxes_equilibriumCosts
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:35:31.523219+00:00
-- url     : https://prove2.me/theorems/472f4f95-59e7-4962-85dc-8f96c6109c80
-- title:
--   Social costs of the equilibria of the taxed game
-- statement:
--   For an equilibrium class $K$, a congestion game $G$ and a parameter vector $(v_r)_r$, the set of **equilibrium social costs** consists of the (expected) social costs $\mathbb E[\mathrm{SC}]$ of all equilibria of class $K$ of the taxed game, whose players minimize the perceived costs $\bar C_i(a)=\sum_{r\in a_i}f_r(|a|_r,v_r)$, while the social cost is the untaxed $\mathrm{SC}(a)=\sum_i\sum_{r\in a_i}\ell_r(|a|_r)$ of (1):
--
--   1. pure: $\mathrm{SC}(a)$ for the pure Nash equilibria $a$;
--   2. mixed: $\mathbb E[\mathrm{SC}]$ for the mixed Nash equilibria (independent randomizations over each agent's strategies);
--   3. correlated: $\mathbb E_\sigma[\mathrm{SC}]$ for the correlated equilibria $\sigma$;
--   4. coarse correlated: $\mathbb E_\sigma[\mathrm{SC}]$ for the coarse correlated equilibria $\sigma$.
--
--   The highest element is $\mathrm{NeCost}(G,T)$ in the price of anarchy (3).
--
--   **Formalization Note** Pure and mixed Nash equilibria are the published `CongestionPoA.AsymSum.IsPureNash` and `CongestionPoA.Mixed.IsMixedNash` of the taxed game; coarse correlated ones the published `RobustPoA.Static.IsCCE`.
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, (1)–(3), p.4; footnote 3, p.4; Definition 4, p.18

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_CongestionPoA_Mixed_Model
import Definitions.Def_RobustPoA_Static_Distribution
import Definitions.Def_CongestionTaxes_taxedGame
import Definitions.Def_CongestionTaxes_perceivedCost
import Definitions.Def_CongestionTaxes_IsCorrelatedEq
import Definitions.Def_CongestionTaxes_EqClass

namespace CongestionTaxes

/-- The **(expected) social costs of the equilibria** of class `K` of the game `G` under the
taxation mechanism of Definition 4 with parameter vector `v` (Paccagnan, Gairing,
arXiv:2105.07480v2, (1)–(3), p.4, footnote 3, and Definition 4, p.18). Equilibria are those of the
taxed game, whose player costs are the perceived costs `C̄_i(a) = ∑_{r∈a_i} f_r(|a|_r, v_r)`; the
social cost is the untaxed `SC(a) = ∑_i ∑_{r∈a_i} ℓ_r(|a|_r)` of (1) (p.5: taxes "do not impact the
expression of the social cost"), in expectation for randomized equilibria.

1. `pure`: the social costs `SC(a)` of the pure Nash equilibria `a` of the taxed game.
2. `mixed`: the expected social costs `E[SC]` of the mixed Nash equilibria (independent lotteries
   over each agent's strategies) of the taxed game.
3. `correlated`: the expected social costs of the correlated equilibria of the taxed game.
4. `coarseCorrelated`: the expected social costs of its coarse correlated equilibria.

**Formalization Note** Pure equilibria use the published `CongestionPoA.AsymSum.IsPureNash` of the
taxed game (deviations over the agent's strategies), mixed ones the published
`CongestionPoA.Mixed.IsMixedNash`, whose `mixedSumCost` is `∑_i E[c_i] = E[SC]`; coarse correlated
ones the published `RobustPoA.Static.IsCCE` and correlated ones `IsCorrelatedEq`, over profiles
`∀ i, ↥(G.strategies i)`. -/
noncomputable def equilibriumCosts {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (K : EqClass) (G : CongestionPoA.AsymSum.CongestionGame ι E) (v : E → ℝ) :
    Set ℝ :=
  match K with
  | .pure => {c | ∃ a, CongestionPoA.AsymSum.IsPureNash (taxedGame G v) a ∧
      c = CongestionPoA.AsymSum.sumCost G a}
  | .mixed => {c | ∃ σ : (∀ i, ↥(G.strategies i) → ℝ),
      CongestionPoA.Mixed.IsMixedNash (taxedGame G v) σ ∧ c = CongestionPoA.Mixed.mixedSumCost G σ}
  | .correlated => {c | ∃ σ, IsCorrelatedEq (perceivedCost G v) σ ∧
      c = RobustPoA.Static.expect σ (fun s => CongestionPoA.AsymSum.sumCost G (fun j => (s j).1))}
  | .coarseCorrelated => {c | ∃ σ, RobustPoA.Static.IsCCE (perceivedCost G v) σ ∧
      c = RobustPoA.Static.expect σ (fun s => CongestionPoA.AsymSum.sumCost G (fun j => (s j).1))}

end CongestionTaxes


