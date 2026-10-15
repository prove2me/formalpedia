-- Prove2me | Definitions.Def_PoWMining_Investment_Model
-- name    : PoWMining_Investment_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:48.344009+00:00
-- url     : https://prove2.me/theorems/13530990-431a-43d2-8318-c1c08bcac222
-- title:
--   §3 and §5.1 — the hardware-investment game: costs (3.1)–(3.2), min{1/η,1}, the threshold profile (5.1), A(0), the investment payoff with fixed cost K, equilibrium investment (Definition 3.2(ii))
-- statement:
--   **Parameters.** There are $N$ miners with initial costs-per-hash $\tilde c_1\le\dots\le\tilde c_N$, the cost-per-hash $\tilde c_0$ of the newest hardware, an adjustment-cost parameter $\eta\ge0$, a mining reward $R>0$, a capacity parameter $\gamma\ge0$ and an entry fixed cost $K>0$. The **standing assumptions** are $N\ge2$, $R>0$, $\gamma\ge0$, $\eta\ge0$, $K>0$, the sorting $\tilde c_1\le\dots\le\tilde c_N$ (as in §4.1), and two additions: $\tilde c_0>0$ and $\tilde c_0<\tilde c_i$ for every $i$ (the paper states $\tilde c_0\le\min_i\tilde c_i$ and no sign of $\tilde c_0$).
--
--   **Costs after investment.** Miner $i$ replaces a fraction $\beta_i\in[0,1]$ of its hardware, which gives the cost-per-hash (3.1) with (3.2):
--
--   $$
--   c_i(\beta_i)=\tilde c_i-\beta_i(\tilde c_i-\tilde c_0)+\frac{\eta(\tilde c_i-\tilde c_0)}{2}\,\beta_i^2 .
--   $$
--
--   Write $\bar\beta=\min\{1/\eta,1\}$, read as $1$ when $\eta=0$. For $k\in\mathbb N$ the **threshold profile** $\beta^{(k)}$ has $\beta^{(k)}_j=\bar\beta$ for $j\le k$ and $\beta^{(k)}_j=0$ for $j>k$; this is (5.1) with $n=k$.
--
--   **Mining stage.** A **mining-equilibrium selection** is a map $h^*$ that assigns to every $\beta\in[0,1]^N$ an equilibrium hash rate profile $h^*(\beta)$ of the mining stage with costs $c_i(\beta_i)$ (Definition 3.2(i)). The sets of active miners (3.3) are $A(\beta)=\{i:h^*_i(\beta)>0\}$, and $A(0)$ is the set of miners active without investment.
--
--   **Investment stage.** Miner $i$'s objective at investment profile $\beta$ is (3.4) evaluated at $h^*(\beta)$, including the fixed cost:
--
--   $$
--   \Pi_i(\beta)=\begin{cases}\dfrac{h^*_i(\beta)}{H^*(\beta)}R-c_i(\beta_i)h^*_i(\beta)-\dfrac{\gamma}{2}h^*_i(\beta)^2-K\,\mathbf 1\{i\notin A(0),\ \beta_i>0\}, & H^*(\beta)>0,\\[4pt] 0, & H^*(\beta)=0.\end{cases}
--   $$
--
--   A profile $\beta^*\in[0,1]^N$ is an **equilibrium investment** (Definition 3.2(ii)) if no miner $i$ can raise $\Pi_i$ by changing $\beta^*_i$ to any $b\in[0,1]$, the mining stage being replayed at the new profile.
--
--   **Genericity of $K$.** $K$ is **generic** if, for every miner $i\notin A(0)$, its gross mining profit (the payoff above without the $K$ term) at the profile $\beta^{(i)}$ differs from $K$. This excludes finitely many values of $K$ once the other parameters are fixed.
--
--   **Participation inequality.** For a cost vector $c$ and $k\ge1$, write $c^{(k)}=c_1+\dots+c_k$. The participation inequality of Proposition 4.4 for the $k$-th miner is $c_k<\big(c^{(k)}+R\gamma/c_k\big)/(k-1)$.
--
--   These are the objects of the investment stage of the model; the corrected Proposition 5.1 and its milestones are stated in them.
--
--   **Formalization Note** Miners are `Fin N` (0-based): Lean miner `i` is the paper's miner $i+1$, so $\beta^{(k)}$ invests in Lean indices $0,\dots,k-1$ and the genericity condition for Lean miner `i` uses $\beta^{(i+1)}$. $\bar\beta$ is `if η ≤ 1 then 1 else 1/η`, never `min (1/η) 1`, since Lean's $1/0=0$. The selection $h^*$ is a hypothesis of each theorem, not a definition; Proposition 4.1 makes it unique. Its existence (Proposition 4.1) is not part of this definition. The fixed cost is subtracted exactly when $i\notin A(0)$ and $\beta_i>0$, inside the $H>0$ branch of (3.4), whether or not miner $i$ ends up active. The additions $\tilde c_0>0$ and $\tilde c_0<\tilde c_i$ and the genericity of $K$ are disclosed additions; each is needed for the corrected Proposition 5.1.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, pp. 9–12, (3.1)–(3.4), (3.6), Definition 3.2(ii); p. 14, Proposition 4.4; p. 21, (5.1) and β^(i)

import Mathlib
import Definitions.Def_PoWMining_Investment_MiningGame

namespace PoWMining.Investment

/-- Parameters of the two-stage investment-and-mining game (§3): initial costs-per-hash
`ct i` (`c̃_i`), the cost-per-hash `c0` (`c̃_0`) of the newest hardware, the adjustment-cost
parameter `η`, the mining reward `R`, the capacity parameter `γ` and the entry fixed cost `K`.
Miners are `Fin N`, 0-based: Lean miner `i` is the paper's miner `i + 1`. -/
structure InvParams (N : ℕ) where
  ct : Fin N → ℝ
  c0 : ℝ
  η : ℝ
  R : ℝ
  γ : ℝ
  K : ℝ

/-- Standing assumptions of §3 and §4.1. `two_le`, `R_pos`, `γ_nonneg`, `η_nonneg`, `K_pos` and
`sorted` (miners sorted by increasing initial cost, as in §4.1) are the paper's. Two are
**disclosed additions** (paper.md slip 11): `c0_pos` (`c̃_0 > 0`; the paper states no sign) and
`c0_lt` (`c̃_0 < c̃_i` for every `i`; the paper allows `c̃_0 ≤ min_i c̃_i`). -/
structure InvParams.Standing {N : ℕ} (P : InvParams N) : Prop where
  two_le : 2 ≤ N
  R_pos : 0 < P.R
  γ_nonneg : 0 ≤ P.γ
  η_nonneg : 0 ≤ P.η
  K_pos : 0 < P.K
  sorted : Monotone P.ct
  c0_pos : 0 < P.c0
  c0_lt : ∀ i, P.c0 < P.ct i

/-- (3.1) with (3.2): the cost-per-hash of miner `i` after investing `β i`,
`c_i(β_i) = c̃_i - β_i (c̃_i - c̃_0) + (η_i / 2) β_i²` with `η_i = η (c̃_i - c̃_0)`. -/
noncomputable def cost {N : ℕ} (P : InvParams N) (β : Fin N → ℝ) (i : Fin N) : ℝ :=
  P.ct i - β i * (P.ct i - P.c0) + P.η * (P.ct i - P.c0) / 2 * β i ^ 2

/-- `min{1/η, 1}`, written so that `η = 0` gives `1` (paper.md slip 10). -/
noncomputable def betaBar {N : ℕ} (P : InvParams N) : ℝ :=
  if P.η ≤ 1 then 1 else 1 / P.η

/-- The threshold profile (5.1) with `n = k` (also `β^{(k)}` of p. 21): the first `k` miners
(Lean indices `0, …, k-1`) invest `min{1/η, 1}`, the others invest `0`. -/
noncomputable def betaK {N : ℕ} (P : InvParams N) (k : ℕ) : Fin N → ℝ :=
  fun j => if j.val < k then betaBar P else 0

/-- `hstar` is a mining-equilibrium selection: for every investment profile `β ∈ [0,1]^N`,
`hstar β` is an equilibrium hash rate profile (Definition 3.2(i)) of the mining stage with the
costs `c_i(β_i)` of (3.1). The fixed cost `K` does not enter the mining stage (paper.md slip 1). -/
def IsSelection {N : ℕ} (P : InvParams N) (hstar : (Fin N → ℝ) → Fin N → ℝ) : Prop :=
  ∀ β : Fin N → ℝ, (∀ i, β i ∈ Set.Icc (0 : ℝ) 1) → IsMiningEq (cost P β) P.R P.γ (hstar β)

/-- `A(0)` of (3.3): the miners active in the mining equilibrium without investment. -/
noncomputable def A0 {N : ℕ} (hstar : (Fin N → ℝ) → Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => 0 < hstar 0 i)

/-- `A(β)` of (3.3): the miners active in the mining equilibrium at the investment profile `β`. -/
noncomputable def active {N : ℕ} (hstar : (Fin N → ℝ) → Fin N → ℝ) (β : Fin N → ℝ) :
    Finset (Fin N) :=
  Finset.univ.filter (fun i => 0 < hstar β i)

/-- Miner `i`'s objective (3.4) **with** the fixed-cost term, evaluated at the mining
equilibrium `hstar β`: the left side of (3.6). The fixed cost `K` is paid iff `i ∉ A(0)` and
`β_i > 0`, inside the `H > 0` branch of (3.4); when `H = 0` the objective is `0`. -/
noncomputable def invPayoff {N : ℕ} (P : InvParams N) (hstar : (Fin N → ℝ) → Fin N → ℝ)
    (β : Fin N → ℝ) (i : Fin N) : ℝ :=
  payoff (cost P β) P.R P.γ (hstar β) i -
    (if PoWMining.Equilibrium.aggH (hstar β) ≠ 0 ∧ i ∉ A0 hstar ∧ 0 < β i then P.K else 0)

/-- Definition 3.2(ii): `β` is an equilibrium investment: `β ∈ [0,1]^N` and no miner `i` gains by
deviating to any `b ∈ [0,1]`, the mining stage being replayed at the deviation
(`hstar (Function.update β i b)`). -/
def IsInvEq {N : ℕ} (P : InvParams N) (hstar : (Fin N → ℝ) → Fin N → ℝ) (β : Fin N → ℝ) :
    Prop :=
  (∀ i, β i ∈ Set.Icc (0 : ℝ) 1) ∧
    ∀ i, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      invPayoff P hstar (Function.update β i b) i ≤ invPayoff P hstar β i

/-- The knife-edge exclusion of paper.md slip 11 (a disclosed addition): for every miner `i`
outside `A(0)`, its gross mining profit at `β^{(i+1)}` (the first `i + 1` miners invest
`min{1/η, 1}`, Lean indices `0, …, i`) differs from the fixed cost `K`. This excludes finitely
many values of `K` for given other parameters. -/
def Generic {N : ℕ} (P : InvParams N) (hstar : (Fin N → ℝ) → Fin N → ℝ) : Prop :=
  ∀ i : Fin N, i ∉ A0 hstar →
    payoff (cost P (betaK P (i.val + 1))) P.R P.γ (hstar (betaK P (i.val + 1))) i ≠ P.K

/-- The cumulative cost `c^{(k)} = ∑_{i ≤ k} c_i` of the first `k` miners (Lean indices
`0, …, k-1`) for a cost vector `c`. -/
def cumCost {N : ℕ} (c : Fin N → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val < k), c j

/-- The participation inequality of Proposition 4.4 for the `k`-th miner `i` (Lean index
`k - 1`) of a cost vector `c`: `c_k < (c^{(k)} + Rγ/c_k)/(k - 1)`, in the printed division form. -/
def partCond {N : ℕ} (c : Fin N → ℝ) (R γ : ℝ) (k : ℕ) (i : Fin N) : Prop :=
  c i < (cumCost c k + R * γ / c i) / ((k : ℝ) - 1)

end PoWMining.Investment


