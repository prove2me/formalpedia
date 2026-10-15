-- Prove2me | Definitions.Def_PoWMining_CapacityStatics_ClosedForms
-- name    : PoWMining_CapacityStatics_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:41.544463+00:00
-- url     : https://prove2.me/theorems/3261889e-2ac4-4218-8d89-aeb041cdd97e
-- title:
--   Standing assumptions of Proposition 4.8 (n ≥ 2, R > 0, γ > 0, sorted positive costs, all n miners active), over the closed forms g, fᵢ of (B.3) and (4.1)
-- statement:
--   Consider $n$ **active miners** of a proof-of-work cryptocurrency, with costs-per-hash $c_1,\dots,c_n$, a mining reward $R$ and a capacity parameter $\gamma$. The **cumulative cost** is $c^{(n)} = c_1+\dots+c_n$. The aggregate equilibrium hash rate is given by (4.1) and (B.3):
--   $$g = g(c_1,\dots,c_n,\gamma,R) = \begin{cases} \dfrac{\sqrt{(c^{(n)})^2 + 4(n-1)R\gamma} - c^{(n)}}{2\gamma}, & \gamma > 0,\\[1ex] \dfrac{(n-1)R}{c^{(n)}}, & \text{otherwise.}\end{cases}$$
--   For a free aggregate argument $G$, the map of (B.3) is
--   $$f_i(c,\gamma,R;G) = G\,\frac{R - c_iG}{R+\gamma G^2},$$
--   and the **equilibrium hash rate** of active miner $i$ is $h^*_i = f_i(c,\gamma,R;g)$, its **hash rate share** $h^*_i/H^*$ with $H^* = g$.
--
--   The **standing assumptions** of Proposition 4.8 are: $n \ge 2$; $R>0$; $\gamma>0$; $c_k>0$ for every $k$; the costs are sorted, $c_1\le c_2\le\dots\le c_n$; and all $n$ miners are active at the aggregate $g$, that is $R - c_k g > 0$ for every $k$.
--
--   These are the objects in which the paper states and proves the sensitivities of Proposition 4.8: at a state where small parameter changes leave the set of active miners unchanged, the equilibrium hash rates are the (B.3) maps of the active miners' costs.
--
--   **Formalization Note** Miners are indexed by `Fin n`, 0-based: Lean miner `i` is the paper's miner $i+1$. The $\gamma\le 0$ branch of `gH` is the $\gamma = 0$ case of (4.1); it is never used here, since every statement assumes $\gamma>0$ (the paper's (B.3) defines $g$ only for $\gamma>0$, and a derivative in $\gamma$ at $\gamma=0$ would be one-sided). Taking the active miners' costs as the data, rather than an equilibrium of the $N$-miner game, is the paper's own reading of "sensitivity" (pp. 15–16, (B.3)); that this $h^*_i$ is the equilibrium hash rate is Proposition 4.1, posed in mission 1 of this series. Activity $R - c_kg>0$ is exactly the condition that miner $k$ is active (proof of Proposition 4.4, p. 39).
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, pp. 12, 15–16, 39, (4.1), (B.3), cumulative cost c^(n)

import Mathlib
import Definitions.Def_PoWMining_CostStatics_Setting

namespace PoWMining.CapacityStatics

/-- Standing assumptions of Proposition 4.8 (pp. 10, 12, 15–16, 39): at least two active miners,
positive reward, positive capacity parameter `γ > 0` (the branch of (B.3)), positive costs sorted
increasingly, and every one of the `n` miners active at the aggregate `g`, i.e. `R − cₖ g > 0`. -/
structure Standing {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) : Prop where
  two_le : 2 ≤ n
  R_pos : 0 < R
  γ_pos : 0 < γ
  c_pos : ∀ k, 0 < c k
  c_mono : Monotone c
  active : ∀ k, 0 < R - c k * PoWMining.CostStatics.gH c γ R

end PoWMining.CapacityStatics


