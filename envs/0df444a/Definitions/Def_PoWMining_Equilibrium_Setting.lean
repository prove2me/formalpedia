-- Prove2me | Definitions.Def_PoWMining_Equilibrium_Setting
-- name    : PoWMining_Equilibrium_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:27.71489+00:00
-- url     : https://prove2.me/theorems/5d18fa9d-b47f-44f6-b300-06cf3da4c851
-- title:
--   §3–§4.2 — the mining game: payoff (3.4), equilibrium (Definition 3.2(i)), active set (3.3), cumulative cost $c^{(n)}$, (4.1), participation condition, marginal cost (4.3)
-- statement:
--   This file sets up one instance of the **mining stage** of the proof-of-work model of Capponi, Ólafsson and Alsabah, with the miners' cost-per-hash taken as exogenous.
--
--   There are $N$ miners. Miner $i$ has a cost-per-hash $c_i$; the miners share a capacity parameter $\gamma$ and compete for a total mining reward $R$. Throughout, the paper's miners are indexed $1,\dots,N$; in Lean miner $i$ is the element `i : Fin N` with $i = $ `i.val + 1`. The **standing assumptions** are
--   $$N\ge 2,\qquad R>0,\qquad \gamma\ge 0,\qquad c_i>0\ \text{for all } i,\qquad c_1\le c_2\le\cdots\le c_N,$$
--   the last being the paper's ordering of miners by increasing cost-per-hash.
--
--   A **hash rate profile** is a vector $h=(h_1,\dots,h_N)$; its **aggregate hash rate** is $H=\sum_{j=1}^N h_j$. The **objective** of miner $i$ is
--   $$\pi_i(h)=\begin{cases}\dfrac{h_i}{H}R-c_ih_i-\dfrac{\gamma}{2}h_i^2, & H>0,\\[4pt] 0, & H=0.\end{cases}$$
--   A profile $h^*$ is an **equilibrium hash rate profile** if $h^*_i\ge 0$ for every $i$ and, for every miner $i$ and every $x\ge 0$, replacing $h^*_i$ by $x$ (all other hash rates unchanged) does not increase $\pi_i$; that is, $\pi_i(h^*)=\sup_{h_i\ge 0}\pi_i(h_i;h^*_{-i})$.
--
--   The **active set** is $A=\{i: h_i>0\}$ and $|A|$ is the number of active miners. The **cumulative cost** of the first $k$ miners is $c^{(k)}=c_1+\cdots+c_k$. For $k\ge 2$ the closed form (4.1) with $n=k$ is
--   $$H_k=\begin{cases}\dfrac{\sqrt{(c^{(k)})^2+4(k-1)R\gamma}-c^{(k)}}{2\gamma}, & \gamma>0,\\[6pt] \dfrac{(k-1)R}{c^{(k)}}, & \gamma=0.\end{cases}$$
--   The **participation condition** for the paper's miner $k$ (with $1\le k\le N$) is
--   $$c_k<\frac{c^{(k)}+R\gamma/c_k}{k-1}.$$
--   Finally, the **marginal cost** of miner $i$ at $h$ is $MC_i=c_i+\gamma h_i$ (4.3), and the **mining profit** $\pi_i$ is the objective above.
--
--   These objects are shared by every statement of this mission: the existence and uniqueness of the equilibrium (Proposition 4.1), the first-order condition (4.2), the marginal-cost and profit orderings (Propositions 4.2–4.3), and the characterization of the number of active miners (Proposition 4.4).
--
--   **Formalization Note** The fixed entry cost $K$ of (3.4) is omitted: in the mining stage the investment profile is fixed, so that term does not depend on the miner's own hash rate and does not affect best responses. The equilibrium uses the published generic pure Nash definition for nonnegative real strategies, specialized to the mining payoff; it is never defined by a closed form. The case $H=0$ of the objective is an explicit `if`, not Lean's convention $x/0=0$. The participation condition `partCond P k` is a predicate on the natural number $k$ on the paper's domain $2\le k\le N$; outside it the predicate is false, and inside it asserts that miner $k$ satisfies the displayed inequality. `aggForm P k` selects its first branch when $\gamma>0$ and its second otherwise, which under the standing assumptions means $\gamma=0$.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, pp. 9–14: (3.3), (3.4) p. 10, Definition 3.2(i) and (3.5) p. 11, sorting and c^(n) p. 12, (4.1) p. 12, (4.3) p. 13, Proposition 4.4 inequality p. 14

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Nash

namespace PoWMining.Equilibrium

/-- Data of one instance of the mining stage (§3–§4.1): `N` miners with exogenous
cost-per-hash `c i`, total mining reward `R` and capacity parameter `γ`.
Lean miner `i : Fin N` is the paper's miner `i.val + 1`. -/
structure Params (N : ℕ) where
  c : Fin N → ℝ
  R : ℝ
  γ : ℝ

/-- Standing assumptions of §3–§4.1: at least two miners, `R > 0` (p. 10), `γ ≥ 0` (p. 10),
positive costs-per-hash (`c̃ᵢ > 0`, p. 9), and miners sorted by increasing cost-per-hash,
`cᵢ ≤ cᵢ₊₁` (p. 12). -/
def Params.Standing {N : ℕ} (P : Params N) : Prop :=
  2 ≤ N ∧ 0 < P.R ∧ 0 ≤ P.γ ∧ (∀ i, 0 < P.c i) ∧ Monotone P.c

/-- Aggregate hash rate `H = ∑ⱼ hⱼ`. -/
def aggH {N : ℕ} (h : Fin N → ℝ) : ℝ := ∑ j, h j

/-- Objective (3.4) of miner `i` in the mining stage, without the fixed-cost term (constant in
`h` once the investment profile is fixed):
`(hᵢ/H) R − cᵢ hᵢ − (γ/2) hᵢ²` if `H > 0`, and `0` if `H = 0`. -/
noncomputable def payoff {N : ℕ} (P : Params N) (h : Fin N → ℝ) (i : Fin N) : ℝ :=
  if aggH h = 0 then 0 else h i / aggH h * P.R - P.c i * h i - P.γ / 2 * h i ^ 2

/-- Equilibrium hash rate profile (Definition 3.2(i)): every hash rate is nonnegative and no
miner can increase its objective by any unilateral deviation to a hash rate `x ≥ 0`. -/
def IsMiningEq {N : ℕ} (P : Params N) (h : Fin N → ℝ) : Prop :=
  CachonCoord.Proportional.IsNash (fun i h' => payoff P h' i) h

/-- Set of active miners (3.3): the miners with strictly positive hash rate. -/
noncomputable def active {N : ℕ} (h : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => 0 < h i)

/-- Number of active miners `|A|`. -/
noncomputable def activeCount {N : ℕ} (h : Fin N → ℝ) : ℕ := (active h).card

/-- Cumulative cost `c⁽ᵏ⁾ = c₁ + ⋯ + cₖ` of the first `k` miners (p. 12); the Lean indices
`< k`. -/
def cumCost {N : ℕ} (P : Params N) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), P.c i

/-- Right-hand side of (4.1) with `n := k`:
`(√((c⁽ᵏ⁾)² + 4(k − 1)Rγ) − c⁽ᵏ⁾)/(2γ)` if `γ > 0`, and `(k − 1)R/c⁽ᵏ⁾` if `γ = 0`. -/
noncomputable def aggForm {N : ℕ} (P : Params N) (k : ℕ) : ℝ :=
  if 0 < P.γ then
    (Real.sqrt (cumCost P k ^ 2 + 4 * ((k : ℝ) - 1) * P.R * P.γ) - cumCost P k) / (2 * P.γ)
  else ((k : ℝ) - 1) * P.R / cumCost P k

/-- Participation condition of Proposition 4.4 for the paper's miner `k` (Lean index `k − 1`):
`c_k < (c⁽ᵏ⁾ + Rγ/c_k)/(k − 1)`, on its stated domain `2 ≤ k ≤ N`. -/
def partCond {N : ℕ} (P : Params N) (k : ℕ) : Prop :=
  2 ≤ k ∧ ∃ i : Fin N, i.val + 1 = k ∧
    P.c i < (cumCost P k + P.R * P.γ / P.c i) / ((k : ℝ) - 1)

/-- Marginal cost (4.3) of miner `i` at the profile `h`: `MCᵢ = cᵢ + γ hᵢ`. -/
def margCost {N : ℕ} (P : Params N) (h : Fin N → ℝ) (i : Fin N) : ℝ := P.c i + P.γ * h i

/-- Mining profit `πᵢ` of miner `i` at the profile `h` (the objective (3.4); at an equilibrium
profile it is the equilibrium profit `π*ᵢ` of Proposition 4.3). -/
noncomputable def profit {N : ℕ} (P : Params N) (h : Fin N → ℝ) (i : Fin N) : ℝ := payoff P h i

end PoWMining.Equilibrium


