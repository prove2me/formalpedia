-- Prove2me | Definitions.Def_PriceQualityService_Oligopoly_Model
-- name    : PriceQualityService_Oligopoly_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:22.544229+00:00
-- url     : https://prove2.me/theorems/c6f94d79-7f41-4558-8398-3d75aeab4d81
-- title:
--   MNL price–quality–service model: firm payoffs (6), monopoly problem (4), the oligopoly game
-- statement:
--   There are $N$ products $\mathcal N = \{1, \dots, N\}$. Product $i$ has quality sensitivity $\alpha_i$, base service cost per unit time $a_i$, marginal effect $b_i$ of quality on the service cost, production-cost coefficient $c_i$ (cost $c_i q_i^2$) and service utility per unit time $s_i$. A decision consists of prices $p_i$, quality levels $q_i$ and service durations $t_i \in [t_s, t_l]$.
--
--   1. The **attraction** of product $i$ is $\exp(\alpha_i q_i - p_i + t_i s_i)$, and the **MNL choice probability** (2) is
--   $$
--   d_i(\mathbf p, \mathbf q, \mathbf t; \mathcal N) = \frac{\exp(\alpha_i q_i - p_i + t_i s_i)}{1 + \sum_{j \in \mathcal N} \exp(\alpha_j q_j - p_j + t_j s_j)},
--   $$
--   where the $1$ in the denominator is the outside (no-purchase) option.
--   2. The **markup** of product $i$ is $p_i - c_i q_i^2 - t_i(a_i - b_i q_i)$, and the payoff (6) of firm $i$, which sells product $i$ only, is $\Pi_i(\mathbf p, \mathbf q, \mathbf t; \mathcal N) = [p_i - c_i q_i^2 - t_i(a_i - b_i q_i)]\, d_i(\mathbf p, \mathbf q, \mathbf t; \mathcal N)$.
--   3. The monopolist's total profit (3) is $\Pi(\mathbf p, \mathbf q, \mathbf t; \mathcal N) = \sum_{i \in \mathcal N} \Pi_i(\mathbf p, \mathbf q, \mathbf t; \mathcal N)$, and $(\mathbf p, \mathbf q, \mathbf t)$ is a **monopoly optimum** (problem (4)) if $\mathbf t \in [t_s, t_l]^N$ and $\Pi(\mathbf p, \mathbf q, \mathbf t) \ge \Pi(\mathbf p', \mathbf q', \mathbf t')$ for all $\mathbf p', \mathbf q' \in \mathbb R^N$ and $\mathbf t' \in [t_s, t_l]^N$.
--   4. In the **oligopoly** of §2.4, firm $i$ chooses $(p_i, q_i, t_i) \in \mathbb R \times \mathbb R \times [t_s, t_l]$ and receives $\Pi_i$. An **oligopoly equilibrium** is a pure-strategy Nash equilibrium of this game.
--   5. A **price equilibrium** at fixed qualities $\mathbf q$ and durations $\mathbf t$ is a pure-strategy Nash equilibrium of the game in which firm $i$ chooses only $p_i \in \mathbb R$ and receives $\Pi_i$.
--   6. The **duration index** of product $i$ is $\varphi_i(t) = \dfrac{b_i^2 t^2}{4 c_i} + \Big(s_i - a_i + \dfrac{\alpha_i b_i}{2 c_i}\Big) t$, the $t$-dependent part of the exponent in (EC.3) and in Theorem 1(c).
--
--   These objects are the vocabulary of Theorem 2 and of its proof in the Online Supplement.
--
--   **Formalization Note** Products are indexed by `Fin N` (0-based). A strategy profile of the oligopoly is a map `x : Fin N → ℝ × ℝ × ℝ` with `x i = (p_i, q_i, t_i)`; `prices`, `qualities`, `durations` project it. Prices and qualities are unconstrained reals: the paper's normalization $q_i \in [0, a_i/b_i)$ (p. 8) is not imposed, as Theorem 1's quality formula and the proof ignore it. The MNL formula is taken as the definition; its derivation from Gumbel utilities is not formalized.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 7 eq. (2), p. 9 eqs. (3)–(4), p. 14 eq. (6); Online Supplement p. 2 (PDF p. 35), (EC.3)

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_PureGame
import Definitions.Def_PriceQualityService_Joint_Model

namespace PriceQualityService.Oligopoly

open Finset

/-- Payoff (6) of firm `i` in the oligopoly (p. 14): firm `i` sells only product `i`, and
`Π_i(p, q, t; 𝒩) = [p_i − c_i q_i² − t_i(a_i − b_i q_i)] · d_i(p, q, t; 𝒩)`
(market size normalized to one). -/
noncomputable def firmProfit {N : ℕ} (α a b c s p q t : Fin N → ℝ) (i : Fin N) : ℝ :=
  PriceQualityService.Joint.markup a b c p q t i * PriceQualityService.Joint.choiceProb α s p q t i

/-- Total profit (3) of a monopolist offering all products (p. 9):
`Π(p, q, t; 𝒩) = ∑_{i ∈ 𝒩} [p_i − c_i q_i² − t_i(a_i − b_i q_i)] · d_i(p, q, t; 𝒩)`. -/
noncomputable def totalProfit {N : ℕ} (α a b c s p q t : Fin N → ℝ) : ℝ :=
  ∑ i, firmProfit α a b c s p q t i

/-- `(p, q, t)` is an optimal solution of the monopolist's joint problem (4), p. 9: service
durations lie in `[t_s, t_l]` and the total profit (3) is at least that of every other
`(p', q', t')` with prices and qualities in `ℝ^N` and durations in `[t_s, t_l]^N`. -/
def IsMonopolyOptimum {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ) (p q t : Fin N → ℝ) : Prop :=
  (∀ i, t i ∈ Set.Icc ts tl) ∧
    ∀ p' q' t' : Fin N → ℝ, (∀ i, t' i ∈ Set.Icc ts tl) →
      totalProfit α a b c s p' q' t' ≤ totalProfit α a b c s p q t

/-- Prices of a strategy profile `x`, where `x i = (p_i, q_i, t_i)` is firm `i`'s strategy. -/
def prices {N : ℕ} (x : Fin N → ℝ × ℝ × ℝ) : Fin N → ℝ := fun i => (x i).1

/-- Quality levels of a strategy profile `x`, where `x i = (p_i, q_i, t_i)`. -/
def qualities {N : ℕ} (x : Fin N → ℝ × ℝ × ℝ) : Fin N → ℝ := fun i => (x i).2.1

/-- Service durations of a strategy profile `x`, where `x i = (p_i, q_i, t_i)`. -/
def durations {N : ℕ} (x : Fin N → ℝ × ℝ × ℝ) : Fin N → ℝ := fun i => (x i).2.2

/-- Pure-strategy Nash equilibrium of the joint price–quality–service competition of §2.4
(p. 14). Firm `i` chooses `(p_i, q_i, t_i) ∈ ℝ × ℝ × [t_s, t_l]` simultaneously with the other
firms, and its payoff is (6). A deviation of firm `i` changes its price, quality and duration
jointly, the other firms' strategies held fixed. -/
def IsOligopolyEquilibrium {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ)
    (x : Fin N → ℝ × ℝ × ℝ) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash (fun _ : Fin N => {y : ℝ × ℝ × ℝ | y.2.2 ∈ Set.Icc ts tl})
    (fun i x' => firmProfit α a b c s (prices x') (qualities x') (durations x') i) x

/-- Price equilibrium at fixed quality levels `q` and service durations `t` (the price
competition to which the proof of Theorem 2 reduces the joint game, Online Supplement p. 3):
firm `i` chooses only its price `p_i ∈ ℝ`, with payoff `Π_i(p, q, t; 𝒩)` of (6). -/
def IsPriceEquilibrium {N : ℕ} (α a b c s q t : Fin N → ℝ) (p : Fin N → ℝ) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash (fun _ : Fin N => (Set.univ : Set ℝ))
    (fun i p' => firmProfit α a b c s p' q t i) p

/-- Duration index of product `i`:
`b_i² t² / (4 c_i) + (s_i − a_i + α_i b_i / (2 c_i)) t`, the `t`-dependent part of the
exponent in (EC.3) (Online Supplement p. 2) and in Theorem 1(c) (p. 10). -/
noncomputable def durationIndex {N : ℕ} (α a b c s : Fin N → ℝ) (i : Fin N) (τ : ℝ) : ℝ :=
  b i ^ 2 * τ ^ 2 / (4 * c i) + (s i - a i + α i * b i / (2 * c i)) * τ

end PriceQualityService.Oligopoly


