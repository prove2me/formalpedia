-- Prove2me | Definitions.Def_CongestionTaxes_taxedGame
-- name    : CongestionTaxes_taxedGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:33:39.11918+00:00
-- url     : https://prove2.me/theorems/136d92bc-fe11-418f-a8e1-b43ec6e45776
-- title:
--   Congestion game under the taxes of Definition 4
-- statement:
--   Given a congestion game $G$ with agents $i$, strategy sets $\mathcal A_i\subseteq2^{\mathcal R}$ and resource costs $\ell_r$, and a parameter vector $(v_r)_r$, the **taxed game** has the same agents and strategies and the perceived resource costs $f_r(x,v_r)=\ell_r(x)+\tau_r(x,v_r)$. An agent's cost in it is
--
--   $$
--   \bar C_i(a)=\sum_{r\in a_i}f_r(|a|_r,v_r),
--   $$
--
--   where $|a|_r$ is the number of agents using $r$ in profile $a$. Equilibria under the taxes are equilibria of this game.
--
--   **Formalization Note** The game is the published `CongestionPoA.AsymSum.CongestionGame` with its latencies replaced; its player cost `CongestionPoA.AsymSum.cost` is $\bar C_i$.
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, display (2), p.4; Definition 4, p.18; p.19

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_CongestionTaxes_modifiedCost

namespace CongestionTaxes

/-- The **taxed congestion game** (Paccagnan, Gairing, arXiv:2105.07480v2, display (2), p.4, and
Definition 4, p.18): the game `G` with the same agents and strategies, in which every resource `r`
has the perceived cost `ℓ_r(x) + τ_r(x, v_r) = f_r(x, v_r)` of Definition 4 with parameter `v_r`.
A player's cost in this game is `C̄_i(a) = ∑_{r ∈ a_i} f_r(|a|_r, v_r)` (p.19).

**Formalization Note** The game is the published `CongestionPoA.AsymSum.CongestionGame`
(strategies `A_i ⊆ 2^𝓡` as a `Finset` of `Finset`s, latencies `𝓡 → ℕ → ℝ`); only the latencies
change. Its player cost `CongestionPoA.AsymSum.cost` is the perceived cost (2) of the taxed game. -/
noncomputable def taxedGame {ι E : Type*} (G : CongestionPoA.AsymSum.CongestionGame ι E)
    (v : E → ℝ) : CongestionPoA.AsymSum.CongestionGame ι E where
  strategies := G.strategies
  latency := fun r x => modifiedCost (G.latency r) x (v r)

end CongestionTaxes


