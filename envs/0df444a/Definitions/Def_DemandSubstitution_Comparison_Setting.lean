-- Prove2me | Definitions.Def_DemandSubstitution_Comparison_Setting
-- name    : DemandSubstitution_Comparison_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:43.105407+00:00
-- url     : https://prove2.me/theorems/18e46e8f-2011-4783-9ade-1d0a7eef5897
-- title:
--   §2, §2.1, §2.2, pp. 2–3, 5, 8 — n-product substitution model, D^s_i, centralized profit π, centralized optimum, firm profit (9), best response, Nash equilibrium
-- statement:
--   This file sets up the single-period, $n$-product inventory model with stock-out based demand substitution of Netessine and Rudi.
--
--   **Data.** Products are indexed by $i = 1,\dots,n$. Product $i$ is stocked at $Q_i$ units at unit cost $c_i$, sold at unit price $r_i$, and leftover units are salvaged at unit value $s_i$, where
--   $$r_i > c_i > s_i > 0 .$$
--   The **underage cost** is $u_i = r_i - c_i$ and the **overage cost** is $o_i = c_i - s_i$. A fraction $a_{ij} \in [0,1]$ of the unmet first-choice demand for product $i$ buys product $j$ as a substitute, with $a_{ii} = 0$ and $\sum_{j=1}^n a_{ij} < 1$ for every $i$.
--
--   **Demand.** The first-choice demand vector $D = (D_1,\dots,D_n)$ has a law $\mu$ on $\mathbb R^n$. A **demand law** is a probability measure that is absolutely continuous with respect to Lebesgue measure, is concentrated on the open positive orthant, and has integrable coordinates. A demand law **has a positive density** if it has a Lebesgue density that is strictly positive at every point of the open positive orthant.
--
--   **Effective demand.** Given the stocking vector $Q$, the demand for product $i$ including substitution is
--   $$D^s_i = D_i + \sum_{j \ne i} a_{ji}\,(D_j - Q_j)^+ ,\qquad x^+ = \max(0,x).$$
--
--   **Centralized management.** A single company owns all products; its expected profit is
--   $$\pi(Q) = \mathbb E \sum_i \Big[ r_i \min(D^s_i, Q_i) - c_i Q_i + s_i (Q_i - D^s_i)^+ \Big].$$
--   A stocking vector $Q^c$ is **centrally optimal** if $Q^c \ge 0$ and $\pi(Q^c) \ge \pi(Q)$ for every $Q \ge 0$.
--
--   **Competition.** Each product is managed by a separate firm; firm $i$'s expected profit is
--   $$\pi_i(Q) = \mathbb E\big[u_i D^s_i - u_i (D^s_i - Q_i)^+ - o_i (Q_i - D^s_i)^+\big]. \tag{9}$$
--   A quantity $q \ge 0$ is firm $i$'s **best response** to the others' quantities $Q_{-i}$ if it maximizes $\pi_i(\cdot, Q_{-i})$ over all nonnegative quantities, and $Q^d \ge 0$ is a **Nash equilibrium** if every $Q^d_i$ is a best response to $Q^d_{-i}$.
--
--   These objects are shared by every statement of the mission: the expansion (1) and derivative (8) of $\pi$, the centralized first-order condition (Proposition 1), and the comparison of centralized and competitive stocking levels (Proposition 6(ii)).
--
--   **Formalization Note** Products are indexed by `Fin n` (0-based). Expectations are Bochner integrals with respect to $\mu$; under a demand law every integrand of the mission is integrable. The positive-density property is a disclosed strengthening of the paper's "continuous multivariate demand distribution with positive support": the paper uses that the distribution function of $D^s_i$ is strictly increasing without stating it. Best responses and optima maximize over nonnegative quantities. The centralized optimum and the Nash equilibrium are defined as maximizers, never by their first-order conditions. The two demand-law predicates (`IsDemandLaw`, `HasPositiveDensity`) are taken from the shared module `DemandSubstitution.Competitive.Setting`, which this file imports.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), pp. 2–3 §2 and §2.1 (three-part profit, D^s_i, u_i, o_i), p. 5 Proposition 1 (Q^c), p. 8 §2.2 ((9), best response, Nash equilibrium)

import Mathlib
import Definitions.Def_DemandSubstitution_Competitive_Setting

open MeasureTheory

namespace DemandSubstitution.Comparison

/-- The data of the `n`-product single-period model with demand substitution (Netessine & Rudi,
SSRN 303779, §2, pp. 2–3): unit price `r i`, unit cost `c i`, unit salvage value `s i`, and the
substitution fractions `a i j` (the fraction of the unmet first-choice demand for product `i` that
buys product `j` as a substitute). The fields `hrc`, `hcs`, `hs` are the standing assumption
`r_i > c_i > s_i > 0`; `ha_nonneg`, `ha_le_one` say `a_ij ∈ [0,1]`; `ha_diag` is `a_ii = 0`;
`ha_row` is `∑_j a_ij < 1`. Products are indexed `0, …, n-1` (the paper's `1, …, n`). -/
structure Model (n : ℕ) where
  r : Fin n → ℝ
  c : Fin n → ℝ
  s : Fin n → ℝ
  a : Fin n → Fin n → ℝ
  hrc : ∀ i, c i < r i
  hcs : ∀ i, s i < c i
  hs : ∀ i, 0 < s i
  ha_nonneg : ∀ i j, 0 ≤ a i j
  ha_le_one : ∀ i j, a i j ≤ 1
  ha_diag : ∀ i, a i i = 0
  ha_row : ∀ i, ∑ j, a i j < 1

variable {n : ℕ}

/-- Unit underage cost `u_i = r_i − c_i` (p. 3). -/
def Model.u (M : Model n) (i : Fin n) : ℝ := M.r i - M.c i

/-- Unit overage cost `o_i = c_i − s_i` (p. 3). -/
def Model.o (M : Model n) (i : Fin n) : ℝ := M.c i - M.s i

/-- Demand for product `i` including substitution (p. 3):
`D^s_i = D_i + ∑_{j ≠ i} a_ji (D_j − Q_j)⁺`, at the demand realization `x` and stocking vector
`Q`. Note the index order `a_ji`: demand flows from product `j` to product `i`. -/
def Ds (M : Model n) (Q x : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i + ∑ j ∈ Finset.univ.erase i, M.a j i * max (x j - Q j) 0

/-- Expected profit of firm `i` under competition, (9), p. 8:
`π_i = E[u_i D^s_i − u_i (D^s_i − Q_i)⁺ − o_i (Q_i − D^s_i)⁺]`. -/
noncomputable def firmProfit (M : Model n) (μ : Measure (Fin n → ℝ)) (Q : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  ∫ x, (M.u i * Ds M Q x i - M.u i * max (Ds M Q x i - Q i) 0
    - M.o i * max (Q i - Ds M Q x i) 0) ∂μ

/-- `q` is firm `i`'s best response to the other firms' stocking quantities in `Q` (p. 8): `q ≥ 0`
maximizes `π_i(·, Q_{−i})` over all nonnegative stocking quantities of firm `i`. -/
def IsBestResponse (M : Model n) (μ : Measure (Fin n → ℝ)) (Q : Fin n → ℝ) (i : Fin n)
    (q : ℝ) : Prop :=
  0 ≤ q ∧ ∀ q' : ℝ, 0 ≤ q' →
    firmProfit M μ (Function.update Q i q') i ≤ firmProfit M μ (Function.update Q i q) i

/-- `Q` is a Nash equilibrium of the competitive game (p. 8): a nonnegative stocking vector from
which no firm gains by deviating unilaterally, i.e. each `Q i` is a best response to `Q_{−i}`. -/
def IsNash (M : Model n) (μ : Measure (Fin n → ℝ)) (Q : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ Q i) ∧ ∀ i, IsBestResponse M μ Q i (Q i)

/-- Expected centralized profit in its three-part form, §2.1, p. 3:
`π = E ∑_i [r_i min(D^s_i, Q_i) − c_i Q_i + s_i (Q_i − D^s_i)⁺]`. -/
noncomputable def centralProfit (M : Model n) (μ : Measure (Fin n → ℝ)) (Q : Fin n → ℝ) : ℝ :=
  ∫ x, ∑ i, (M.r i * min (Ds M Q x i) (Q i) - M.c i * Q i
    + M.s i * max (Q i - Ds M Q x i) 0) ∂μ

/-- `Q` is an optimal centralized stocking vector (`Q^c`, p. 5): it is nonnegative and maximizes
the centralized expected profit `π` over all nonnegative stocking vectors. -/
def IsCentralOptimal (M : Model n) (μ : Measure (Fin n → ℝ)) (Q : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ Q i) ∧
    ∀ Q' : Fin n → ℝ, (∀ i, 0 ≤ Q' i) → centralProfit M μ Q' ≤ centralProfit M μ Q

end DemandSubstitution.Comparison


