-- Prove2me | Definitions.Def_CongestionTaxes_poa
-- name    : CongestionTaxes_poa
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:30.067823+00:00
-- url     : https://prove2.me/theorems/21e02917-80ee-4ecc-8b24-e6bb11077985
-- title:
--   Price of anarchy of a taxation mechanism
-- statement:
--   Let $\mathcal L$ be a set of resource costs and $K$ an equilibrium class. A taxation mechanism of the form of Definition 4 is given by a **selection** $T$ assigning to each congestion game $G$ a parameter vector $T(G)=(v_r)_r$. Its **price of anarchy** is
--
--   $$
--   \mathrm{PoA}_K(T)=\sup_{G\in\mathcal G}\frac{\mathrm{NeCost}_K(G,T)}{\mathrm{MinCost}(G)},
--   $$
--
--   where $\mathcal G$ is the class of congestion games with costs in $\mathcal L$ and $\mathrm{NeCost}_K(G,T)$ is the highest (expected) social cost of an equilibrium of class $K$ of $G$ under the taxes with parameters $T(G)$.
--
--   **Formalization Note** Agents and resources are $\{0,\dots,N-1\}$ and $\{0,\dots,m-1\}$ for arbitrary $N,m$. The ratio is taken in $[0,\infty]$ with $c/0=\infty$ for $c>0$ and $0/0=0$; the supremum runs over games and equilibria jointly.
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, display (3), p.4; footnote 3, p.4; p.5

import Mathlib
import Definitions.Def_CongestionTaxes_minCost
import Definitions.Def_CongestionTaxes_equilibriumCosts
import Definitions.Def_CongestionTaxes_InClass

open scoped ENNReal

namespace CongestionTaxes

/-- The **price of anarchy** (3) of a taxation mechanism for the equilibrium class `K`
(Paccagnan, Gairing, arXiv:2105.07480v2, (3), p.4, and footnote 3):
`PoA(T) = sup_{G ∈ 𝒢} NeCost(G, T) / MinCost(G)`, where `𝒢` is the class of congestion games with
costs in `𝓛` (any number `N` of agents, any finite set of `m` resources) and `NeCost(G, T)` is the
highest (expected) social cost of an equilibrium of class `K` of `G` under the taxes `T`.

The mechanism of Definition 4 is determined by a parameter vector for each game, so the mechanism
`T` is a **selection**: `T N m G` is the parameter vector `(v_r)_{r}` used on the game `G`.

**Formalization Note** Agents are `Fin N` and resources `Fin m`. The ratio is taken in `ℝ≥0∞`
(`c/0 = ⊤` for `c > 0`, `0/0 = 0`) and the supremum is over games and equilibria jointly, which
equals the supremum over games of `NeCost/MinCost`. A game without equilibria of the class
contributes `0`; pure equilibria always exist (footnote 3). -/
noncomputable def poa (K : EqClass) (L : Set (ℕ → ℝ))
    (T : (N m : ℕ) → CongestionPoA.AsymSum.CongestionGame (Fin N) (Fin m) → Fin m → ℝ) : ℝ≥0∞ :=
  ⨆ (N : ℕ) (m : ℕ) (G : CongestionPoA.AsymSum.CongestionGame (Fin N) (Fin m))
    (_ : InClass L G) (c : ℝ) (_ : c ∈ equilibriumCosts K G (T N m G)),
      ENNReal.ofReal c / ENNReal.ofReal (minCost G)

end CongestionTaxes


