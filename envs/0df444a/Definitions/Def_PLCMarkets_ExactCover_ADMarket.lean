-- Prove2me | Definitions.Def_PLCMarkets_ExactCover_ADMarket
-- name    : PLCMarkets_ExactCover_ADMarket
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T01:02:47.936619+00:00
-- url     : https://prove2.me/theorems/f55af4cb-3f4b-4998-9125-d17229165ff9
-- title:
--   Arrow–Debreu market with separable piecewise-linear concave utilities; exact and $\epsilon$-approximate equilibria (§6, §7)
-- statement:
--   An **Arrow–Debreu market** has a finite set $B$ of agents and a finite set $G$ of divisible goods. Agent $i$ owns an initial endowment $w_{ij}\ge 0$ of each good $j$, and has the additively separable utility $u_i(y)=\sum_{j\in G} f^i_j(y_j)$ for a bundle $y=(y_j)_{j\in G}$, where each $f^i_j$ is a piecewise-linear concave utility function. The total supply of good $j$ is $\sum_{i\in B} w_{ij}$.
--
--   Given prices $p=(p_j)_{j\in G}$, agent $i$'s **income** is $\sum_j p_j w_{ij}$. A bundle $y$ is an **optimal bundle** for agent $i$ at prices $p$ if
--
--   1. $y\ge 0$ and $\sum_j p_j y_j\le\sum_j p_j w_{ij}$;
--   2. $u_i(z)\le u_i(y)$ for every $z\ge 0$ with $\sum_j p_j z_j\le\sum_j p_j w_{ij}$;
--   3. agent $i$ buys a good only along the pieces of $f^i_j$ that carry utility: if $f^i_j$ is flat beyond its listed segments, then $y_j$ is at most their total length.
--
--   The price vector $p$ is a **price equilibrium** if it lies in the unit simplex, $p\ge 0$ and $\sum_j p_j=1$, and there is an allocation $x=(x_{ij})$ in which every agent receives an optimal bundle $x(i)$ and the market clears:
--
--   $$
--   \sum_{i\in B} x_{ij}=\sum_{i\in B} w_{ij}\qquad\text{for all } j\in G.
--   $$
--
--   For $\epsilon\ge 0$, $p$ is an **$\epsilon$-approximate market equilibrium** if it lies in the unit simplex and some allocation of optimal bundles clears the market approximately, in relative terms good by good:
--
--   $$
--   \Big|\sum_{i\in B} x_{ij}-\sum_{i\in B} w_{ij}\Big|\le\epsilon\sum_{i\in B} w_{ij}\qquad\text{for all } j\in G.
--   $$
--
--   These are the equilibrium notions of Theorem 8.1: the exact one of §6 and the approximate one of §7, both with prices normalized to the simplex as in the proof of Lemma 8.3.
--
--   **Formalization Note.** Supplies are not normalized to $1$: the §8 market has supplies $n^3+n/2$, $n^3+1$ and $n^3+1/6$, so clearing is stated as $\sum_i x_{ij}=\sum_i w_{ij}$, the form of p. 10:10 before its "without loss of generality". Clause 3 of an optimal bundle is the paper's convention made explicit: agents spend money on segments and leave unneeded money unspent (proofs of Claim 8.5 and Lemma 8.3, pp. 10:22–10:23). Without it an agent could spend leftover money on goods that give him no utility, and every instance of the §8 construction would have an exact equilibrium. Prices and allocations are real; market data are rational.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:10 (§6, (a) and (b)), p. 10:16 (§7, ϵ-approximate market equilibrium), p. 10:21 (proof of LEMMA 8.3, Σ p(j) = 1)

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_PLUtility

namespace PLCMarkets.ExactCover

/-- An Arrow–Debreu market with a finite set `A` of agents and a finite set `G` of divisible goods
(Vazirani–Yannakakis 2011, §6, p. 10:10): agent `i` owns the initial endowment `endow i j ≥ 0`
of good `j` and has the additively separable utility `u_i(x) = Σ_j f^i_j(x_j)`, where
`f^i_j = util i j` is piecewise-linear and concave. Total supplies are not normalized. -/
structure ADMarket (A G : Type) [Fintype A] [Fintype G] where
  /-- `endow i j = w_ij`, agent `i`'s initial endowment of good `j`. -/
  endow : A → G → ℚ
  endow_nonneg : ∀ i j, 0 ≤ endow i j
  /-- `util i j = f^i_j`, agent `i`'s utility function for good `j`. -/
  util : A → G → PLUtility

namespace ADMarket

variable {A G : Type} [Fintype A] [Fintype G]

/-- Agent `i`'s income `Σ_j p_j w_ij` at prices `p` (the value of the endowment). -/
def income (M : ADMarket A G) (p : G → ℝ) (i : A) : ℝ :=
  ∑ j, p j * (M.endow i j : ℝ)

/-- The total supply `Σ_i w_ij` of good `j`. -/
def supply (M : ADMarket A G) (j : G) : ℝ :=
  ∑ i, (M.endow i j : ℝ)

/-- Agent `i`'s utility `u_i(y) = Σ_j f^i_j(y_j)` for a bundle `y`. -/
noncomputable def utility (M : ADMarket A G) (i : A) (y : G → ℝ) : ℝ :=
  ∑ j, (M.util i j).eval (y j)

/-- `y` is an optimal bundle for agent `i` at prices `p`:
1. `y ≥ 0` and `y` is affordable, `Σ_j p_j y_j ≤ Σ_j p_j w_ij`;
2. no affordable bundle `z ≥ 0` gives agent `i` more utility;
3. the agent buys only along the pieces of his utility function that carry utility: when
   `f^i_j` is flat beyond its listed segments (`tail = 0`), `y_j` does not exceed their total
   length. This is the paper's convention (agents spend money on segments, and money not
   needed for them stays unspent; see the proofs of Claim 8.5 and Lemma 8.3, pp. 10:22–10:23). -/
def IsOptimalBundle (M : ADMarket A G) (p : G → ℝ) (i : A) (y : G → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧ ∑ j, p j * y j ≤ M.income p i ∧
    (∀ z : G → ℝ, (∀ j, 0 ≤ z j) → ∑ j, p j * z j ≤ M.income p i →
      M.utility i z ≤ M.utility i y) ∧
    ∀ j, (M.util i j).tail = 0 → y j ≤ ((M.util i j).length : ℝ)

/-- `p` lies in the unit simplex: `p ≥ 0` and `Σ_j p_j = 1`. -/
def InSimplex (p : G → ℝ) : Prop :=
  (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1

/-- `p` is a price equilibrium (p. 10:10): `p` is in the unit simplex and some allocation
`x = (x_ij)` gives every agent an optimal bundle and clears the market,
`Σ_i x_ij = Σ_i w_ij` for every good `j`. -/
def IsEquilibrium (M : ADMarket A G) (p : G → ℝ) : Prop :=
  InSimplex p ∧ ∃ x : A → G → ℝ, (∀ i, M.IsOptimalBundle p i (x i)) ∧
    ∀ j, ∑ i, x i j = M.supply j

/-- `p` is an `ε`-approximate market equilibrium (p. 10:16, normalized as on p. 10:21): `p` is in
the unit simplex and some allocation gives every agent an optimal bundle and clears the market
approximately, `|Σ_i x_ij − Σ_i w_ij| ≤ ε · Σ_i w_ij` for every good `j`. -/
def IsApproxEquilibrium (M : ADMarket A G) (ε : ℝ) (p : G → ℝ) : Prop :=
  InSimplex p ∧ ∃ x : A → G → ℝ, (∀ i, M.IsOptimalBundle p i (x i)) ∧
    ∀ j, |∑ i, x i j - M.supply j| ≤ ε * M.supply j

end ADMarket

end PLCMarkets.ExactCover


