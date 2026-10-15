-- Prove2me | Definitions.Def_PoWMining_Investment_MiningGame
-- name    : PoWMining_Investment_MiningGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:48.696843+00:00
-- url     : https://prove2.me/theorems/2476dd2c-e5ea-4cac-a882-740469244cab
-- title:
--   §3 — the mining stage for an arbitrary cost vector: payoff (3.4) without the fixed cost, equilibrium hash rate profile (Definition 3.2(i))
-- statement:
--   Fix $N$ miners, a vector of costs-per-hash $c=(c_1,\dots,c_N)$, a mining reward $R$ and a capacity parameter $\gamma$. Each miner $i$ chooses a hash rate $h_i\ge 0$; write $H=\sum_{j=1}^N h_j$ for the aggregate hash rate. Miner $i$'s mining-stage payoff is
--
--   $$
--   \pi_i(h)=\begin{cases}\dfrac{h_i}{H}\,R-c_ih_i-\dfrac{\gamma}{2}h_i^2, & H>0,\\[4pt] 0, & H=0,\end{cases}
--   $$
--
--   which is (3.4) without its fixed-cost term: given the investment profile, that term does not depend on the hash rates and plays no role in the mining stage.
--
--   A profile $h^*\in[0,\infty)^N$ is an **equilibrium hash rate profile** (Definition 3.2(i)) if, for every miner $i$ and every $x\ge 0$, replacing $h^*_i$ by $x$ does not raise $\pi_i$; equivalently $\pi_i(h^*)=\sup_{h_i\ge0}\pi_i(h_i,h^*_{-i})$, as in (3.5).
--
--   These objects describe the second stage of the investment game. No ordering of the costs is assumed, because investment can reorder them.
--
--   **Formalization Note** Miners are `Fin N`, so Lean miner `i` is the paper's miner $i+1$. The case $H=0$ is an explicit `if`; nothing relies on Lean's convention $x/0=0$. "$=\sup$" is rendered as "no deviation $x\ge0$ is profitable", which is equivalent and avoids `sSup`.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, pp. 10–11, (3.4), (3.5), Definition 3.2(i)

import Mathlib
import Definitions.Def_PoWMining_Equilibrium_Setting

namespace PoWMining.Investment

/-- Miner `i`'s mining-stage payoff (3.4) without the fixed-cost term (paper.md slip 1), for an
arbitrary (not necessarily sorted) cost-per-hash vector `c`, reward `R` and capacity parameter `γ`:
`(h_i / H) R - c_i h_i - (γ/2) h_i²` if `H > 0`, and `0` if `H = 0`. The case split is explicit;
nothing relies on Lean's `x / 0 = 0`. -/
noncomputable def payoff {N : ℕ} (c : Fin N → ℝ) (R γ : ℝ) (h : Fin N → ℝ) (i : Fin N) : ℝ :=
  if PoWMining.Equilibrium.aggH h = 0 then 0 else h i / PoWMining.Equilibrium.aggH h * R - c i * h i - γ / 2 * h i ^ 2

/-- Definition 3.2(i): `h` is an equilibrium hash rate profile of the mining stage with cost
vector `c`: every hash rate is nonnegative and no miner gains by deviating to any hash rate
`x ≥ 0` (this is "= sup over `h_i ≥ 0`" of (3.5), since `h_i` itself is a candidate). -/
def IsMiningEq {N : ℕ} (c : Fin N → ℝ) (R γ : ℝ) (h : Fin N → ℝ) : Prop :=
  (∀ i, 0 ≤ h i) ∧
    ∀ i, ∀ x : ℝ, 0 ≤ x → payoff c R γ (Function.update h i x) i ≤ payoff c R γ h i

end PoWMining.Investment


