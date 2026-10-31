-- Prove2me | Definitions.Def_PlatformCournot_payoff
-- name    : PlatformCournot_payoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:24:10.335364+00:00
-- url     : https://prove2.me/theorems/b32d8aba-8e46-4f75-baa9-32dd179e5e95
-- title:
--   Payoff $\pi_i(q_i,q_{-i})$ of firm $i$, display (8)
-- statement:
--   The **payoff** (profit) of firm $i$ at the supply profile $q=(q_i,q_{-i})$ is its revenue minus its cost:
--
--   $$\pi_i(q_i,q_{-i})=\sum_{j=1}^m q_{ij}\,p_j(d_j)-C_i(s_i).$$
--
--   **Formalization Note** The payoff is a function of the whole profile $q$.
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, display (8), p.12

import Mathlib
import Definitions.Def_PlatformCournot_AffineDemand_price
import Definitions.Def_PlatformCournot_supply
import Definitions.Def_PlatformCournot_demand

namespace PlatformCournot

/-- **Payoff (profit) of firm `i`, display (8).**
Pang et al., arXiv:1903.04574v3, display (8), p.12:
"πi(qi,q−i) := Σ_{j=1}^m qij pj(dj) − Ci(si)".

**Formalization Note** The payoff is a function of the whole profile `q`; `(qᵢ, q₋ᵢ)` is `q`. -/
def payoff {n m : ℕ} (D : AffineDemand m) (C : Fin n → ℝ → ℝ) (q : Fin n → Fin m → ℝ)
    (i : Fin n) : ℝ :=
  (∑ j, q i j * D.price j (demand q j)) - C i (supply q i)

end PlatformCournot


