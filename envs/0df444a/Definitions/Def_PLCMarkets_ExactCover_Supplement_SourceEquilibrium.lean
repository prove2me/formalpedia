-- Prove2me | Definitions.Def_PLCMarkets_ExactCover_Supplement_SourceEquilibrium
-- name    : PLCMarkets_ExactCover_Supplement_SourceEquilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:14:38.060548+00:00
-- url     : https://prove2.me/theorems/31f213a6-85f8-405f-ac49-77ec180a0fc1
-- title:
--   Optimal bundles, price equilibria and $\varepsilon$-approximate equilibria of Arrow–Debreu markets (§6, §7), and $\varepsilon$-approximate Fisher equilibria (§7)
-- statement:
--   Let $M$ be an Arrow–Debreu market with a finite set $B$ of agents and a finite set $G$ of divisible goods. Agent $i$ owns the endowment $w_{ij}\ge 0$ of good $j$ and has the additively separable utility $u_i(x)=\sum_{j\in G}f^i_j(x_j)$, where each $f^i_j$ is a nonnegative, nondecreasing, concave, piecewise-linear function with rational data. At prices $p=(p_j)_{j\in G}$, agent $i$'s income is $\sum_j p_jw_{ij}$ and the total supply of good $j$ is $\sum_i w_{ij}$.
--
--   1. A bundle $y\ge 0$ is an **optimal bundle** for agent $i$ at prices $p$ if $\sum_j p_jy_j\le\sum_jp_jw_{ij}$ and no bundle $z\ge0$ with $\sum_jp_jz_j\le\sum_jp_jw_{ij}$ gives $u_i(z)>u_i(y)$.
--   2. A vector $p$ is a **price equilibrium** if it lies in the unit simplex $S=\{p\ge0,\ \sum_jp_j=1\}$ and some allocation $x=(x_{ij})$ gives every agent an optimal bundle and clears the market:
--   $$\sum_{i\in B}x_{ij}=\sum_{i\in B}w_{ij}\qquad\text{for every good }j.$$
--   3. For $\varepsilon\ge0$, $p\in S$ is an **$\varepsilon$-approximate market equilibrium** if some allocation of optimal bundles satisfies $\big|\sum_ix_{ij}-\sum_iw_{ij}\big|\le\varepsilon\sum_iw_{ij}$ for every good $j$.
--
--   For a Fisher market with $n$ buyers of budgets $e(i)>0$ and one unit of every good, $p$ is an **$\varepsilon$-approximate equilibrium** if $p\ge0$, $\sum_jp_j=\sum_ie(i)$, and some allocation of budget-optimal bundles satisfies $\big|\sum_ix_{ij}-1\big|\le\varepsilon$ for every good $j$.
--
--   These are the solution concepts of Theorems 5.1, 6.1, 7.1 and 8.1.
--
--   **Formalization Note** The Arrow–Debreu market is the published `PLCMarkets.ExactCover.ADMarket`; its own `IsOptimalBundle` adds a cap on purchases beyond the listed segments of a flat utility, which the §6 definition does not have, so the optimality predicate here is the plain budget maximization of p. 10:10. The page states the Fisher notion for a market with $M=\sum_ie(i)$ units of each good, prices summing to $1$ and $|\sum_ix_{ij}-M|\le\varepsilon M$; measured in units of $M$ goods (the unit-supply normalization of §2, used by the published `PLCMarkets.Rationality.FisherMarket`), prices sum to $\sum_ie(i)$ and the error bound becomes $\varepsilon$.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:10 (§6, price equilibrium (a)–(b)); p. 10:16 (§7, ε-approximate market equilibrium); p. 10:17 (§7, ε-approximate equilibrium of a Fisher market); p. 10:6 (§2, unit supply)

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_ADMarket
import Definitions.Def_PLCMarkets_Rationality_FisherMarket

namespace PLCMarkets.ExactCover.Supplement

open PLCMarkets.ExactCover

section ArrowDebreu

variable {A G : Type} [Fintype A] [Fintype G]

/-- `y` is an optimal bundle for agent `i` at prices `p` in the sense of §6, p. 10:10 (a)
(Vazirani–Yannakakis 2011): `y ≥ 0`, `y` is affordable, `Σ_j p_j y_j ≤ Σ_j p_j w_ij`, and `y`
maximizes `u_i(y) = Σ_j f^i_j(y_j)` over all affordable bundles `z ≥ 0`.

Unlike the published `ADMarket.IsOptimalBundle` of the §8 mission, there is no restriction on
purchases of goods beyond the listed segments of a flat utility function. -/
def IsSrcOptimalBundle (M : ADMarket A G) (p : G → ℝ) (i : A) (y : G → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧ ∑ j, p j * y j ≤ M.income p i ∧
    ∀ z : G → ℝ, (∀ j, 0 ≤ z j) → ∑ j, p j * z j ≤ M.income p i →
      M.utility i z ≤ M.utility i y

/-- `p` is a price equilibrium of the Arrow–Debreu market `M` (§6, p. 10:10): `p` lies in the unit
simplex `S = {p ≥ 0, Σ_j p_j = 1}` and some allocation `x = (x_ij)` gives every agent an optimal
bundle (`IsSrcOptimalBundle`) and clears the market, `Σ_i x_ij = Σ_i w_ij` for every good `j`. -/
def IsSrcEquilibrium (M : ADMarket A G) (p : G → ℝ) : Prop :=
  ADMarket.InSimplex p ∧ ∃ x : A → G → ℝ, (∀ i, IsSrcOptimalBundle M p i (x i)) ∧
    ∀ j, ∑ i, x i j = M.supply j

/-- `p` is an `ε`-approximate market equilibrium of the Arrow–Debreu market `M` (§7, p. 10:16,
prices normalized to the unit simplex as in §6): some allocation gives every agent an optimal
bundle and `|Σ_i x_ij − Σ_i w_ij| ≤ ε · Σ_i w_ij` for every good `j`. -/
def IsSrcApproxEquilibrium (M : ADMarket A G) (ε : ℝ) (p : G → ℝ) : Prop :=
  ADMarket.InSimplex p ∧ ∃ x : A → G → ℝ, (∀ i, IsSrcOptimalBundle M p i (x i)) ∧
    ∀ j, |∑ i, x i j - M.supply j| ≤ ε * M.supply j

end ArrowDebreu

section Fisher

variable {n g : ℕ}

/-- `p` is an `ε`-approximate equilibrium of the (unit-supply) Fisher market `M` (§7, p. 10:17):
prices are nonnegative and sum to the total money `Σ_i e(i)`, and some allocation gives every
buyer an optimal bundle for her budget with `|Σ_i x_ij − 1| ≤ ε` for every good `j`.

The page states the notion for a market with `M = Σ_i e(i)` units of every good, with prices
summing to `1` and `|Σ_i x_ij − M| ≤ ε M`; measuring every good in units of `M`, which is the
paper's unit-supply normalization of §2, turns it into the statement above. -/
def IsFisherApproxEquilibrium (M : PLCMarkets.Rationality.FisherMarket n g) (ε : ℝ)
    (p : Fin g → ℝ) : Prop :=
  (∀ j, 0 ≤ p j) ∧ ∑ j, p j = ∑ i, (M.budget i : ℝ) ∧
    ∃ x : Fin n → Fin g → ℝ, (∀ i, M.IsOptimalBundle p i (x i)) ∧
      ∀ j, |∑ i, x i j - 1| ≤ ε

end Fisher

end PLCMarkets.ExactCover.Supplement


