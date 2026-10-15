-- Prove2me | Definitions.Def_PoWMining_Investment_ClosedForm
-- name    : PoWMining_Investment_ClosedForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:55.327384+00:00
-- url     : https://prove2.me/theorems/61717887-dbdf-43b0-8b3e-12d3bb4c7ff5
-- title:
--   (B.3) — the closed forms g, f_i and the equilibrium profit π*_i of n active miners
-- statement:
--   Let $n$ miners be active with costs $c_1,\dots,c_n$, reward $R$ and capacity parameter $\gamma$, and let $c^{(n)}=c_1+\dots+c_n$. The aggregate hash rate (4.1), written $g$ in (B.3), is
--
--   $$
--   g=\begin{cases}\dfrac{\sqrt{(c^{(n)})^2+4(n-1)R\gamma}-c^{(n)}}{2\gamma}, & \gamma>0,\\[6pt] \dfrac{(n-1)R}{c^{(n)}}, & \gamma=0,\end{cases}
--   $$
--
--   and for an aggregate value $G$ the hash rate map of (B.3) is $f_i(G)=G\,(R-c_iG)/(R+\gamma G^2)$; the equilibrium hash rate of miner $i$ is $f_i=f_i(g)$. The equilibrium profit of miner $i$ is the payoff (3.4) (without fixed cost) at $h_i=f_i$, $H=g$:
--
--   $$
--   \pi^*_i=\frac{R}{g}f_i-c_if_i-\frac{\gamma}{2}f_i^2 .
--   $$
--
--   These closed forms are what Proposition B.1 differentiates: they are the equilibrium quantities of Proposition 4.1 for a fixed set of $n$ active miners.
--
--   **Formalization Note** The costs are a vector `c : Fin n → ℝ` of the active miners only; no sorting is assumed. Both branches of (4.1) are written out, since (B.3) itself prints only the $\gamma>0$ branch while Proposition B.1 is stated for $\gamma\ge0$.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 12, (4.1); pp. 39–40, (B.3); p. 43, proof of Proposition B.1

import Mathlib
import Definitions.Def_PoWMining_CostStatics_Setting

namespace PoWMining.Investment

/-- The cumulative cost `c^{(n)} = ∑_i c_i` of the `n` active miners' costs `c : Fin n → ℝ`. -/
def activeCumCost {n : ℕ} (c : Fin n → ℝ) : ℝ := ∑ i, c i

/-- The equilibrium profit `π*_i = R f_i / g - c_i f_i - (γ/2) f_i²` of active miner `i`, the
payoff (3.4) (without the fixed cost) at `h_i = f_i`, `H = g` (p. 43, proof of Proposition B.1). -/
noncomputable def profitH {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (i : Fin n) : ℝ :=
  R * PoWMining.CostStatics.fH c γ R (PoWMining.CostStatics.gH c γ R) i / PoWMining.CostStatics.gH c γ R - c i * PoWMining.CostStatics.fH c γ R (PoWMining.CostStatics.gH c γ R) i -
    γ / 2 * PoWMining.CostStatics.fH c γ R (PoWMining.CostStatics.gH c γ R) i ^ 2

end PoWMining.Investment


