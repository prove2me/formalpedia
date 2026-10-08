-- Prove2me | Definitions.Def_DemandSubstitution_Competitive_Setting
-- name    : DemandSubstitution_Competitive_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:10.10599+00:00
-- url     : https://prove2.me/theorems/165abca6-084d-43e4-919c-afb344975c23
-- title:
--   §2 and §2.2, pp. 2–3, 8–9 — n-product substitution model, D^s_i, firm profit (9), best response, Nash equilibrium, condition (10)
-- statement:
--   This module fixes the competitive inventory model with demand substitution of Netessine and Rudi.
--
--   **Data and standing assumptions (§2, p. 2).** There are $n$ products, offered in a single period. Product $i$ is stocked at $Q_i$ units at unit cost $c_i$, sold at unit price $r_i$, and leftovers are salvaged at unit value $s_i$, with
--   $$
--   r_i > c_i > s_i > 0 .
--   $$
--   A fraction $a_{ij}\in[0,1]$ of the unmet demand for product $i$ switches to product $j$, with $a_{ii}=0$ and $\sum_{j=1}^n a_{ij}<1$ for every $i$. The unit underage and overage costs are $u_i=r_i-c_i$ and $o_i=c_i-s_i$ (p. 3).
--
--   **Demand.** The first-choice demand vector $D=(D_1,\dots,D_n)$ has law $\mu$, a probability measure on $\mathbb R^n$ that is "a known continuous multivariate demand distribution with positive support": $\mu$ is absolutely continuous with respect to Lebesgue measure, $D_i>0$ almost surely for every $i$, and every $D_i$ has finite mean. A second, stronger property is also defined: $\mu$ has a Lebesgue density that is strictly positive on the open positive orthant $\{x: x_i>0\ \forall i\}$.
--
--   **Effective demand (p. 3).** For a stocking vector $Q$,
--   $$
--   D^s_i = D_i + \sum_{j\ne i} a_{ji}\,(D_j-Q_j)^+ ,
--   $$
--   the first-choice demand for $i$ plus the substituting demand from the other products; it does not depend on $Q_i$.
--
--   **Competitive game (§2.2, pp. 8–9).** Firm $i$ controls product $i$, and its expected profit is (9)
--   $$
--   \pi_i(Q_i, Q_{-i}) = E\big[u_iD^s_i - u_i(D^s_i-Q_i)^+ - o_i(Q_i-D^s_i)^+\big].
--   $$
--   A quantity $q\ge 0$ is a **best response** of firm $i$ to $Q_{-i}$ if it maximizes $\pi_i(\cdot,Q_{-i})$ over all stocking quantities $q'\ge0$. A **Nash equilibrium** (p. 9) is "a strategy from which it will not be beneficial for any of the players to deviate": a nonnegative stocking vector $Q$ such that $\pi_i(q',Q_{-i})\le\pi_i(Q)$ for every firm $i$ and every $q'\ge0$; equivalently, every $Q_i$ is a best response to $Q_{-i}$. Finally, the condition (10) of firm $i$ at $Q$ is
--   $$
--   \Pr(D_i<Q_i) - \Pr(D_i<Q_i<D^s_i) = \frac{u_i}{u_i+o_i}.
--   $$
--
--   These objects are the vocabulary of Propositions 3 and 4 of the paper: the profit functions define the game, and (10) is the characterization of its equilibria.
--
--   **Formalization Note** Products are indexed by `Fin n` (0-based). `a i j` is the share of $i$'s unmet demand going to $j$, so $D^s_i$ uses `a j i`. The expectation is a Bochner integral against $\mu$; integrability of the coordinates makes it the true expectation. Probabilities are `μ.real` of the event, with the strict and weak inequalities exactly as printed. Best responses maximize over $q'\ge0$ only (the paper's $\max_{Q_i}$ ranges over stocking quantities). The Nash equilibrium is the published pure-strategy Nash equilibrium of an $n$-player game with nonnegative real strategies (`CachonCoord.Proportional.IsNash`) applied to the payoffs (9); it is the no-profitable-deviation property, not (10), which is a separate predicate. A structural lemma `isNash_iff` unfolds it to "nonnegative profile of mutual best responses". The positive-density property is a disclosed pin used by the uniqueness results: the paper divides by the density of $D^s_i$ (p. 9) and asserts single-valued best responses, which needs a strictly increasing distribution function of $D^s_i$.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), pp. 2–3, §2 (model, D^s_i, u_i, o_i); p. 8, §2.2, (9), best response and (10); p. 9, Nash equilibrium

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Nash

namespace DemandSubstitution.Competitive

open MeasureTheory
open scoped ENNReal

/-- The data of the `n`-product substitution model of Netessine & Rudi (SSRN 303779, §2, p. 2):
prices `r`, unit costs `c`, salvage values `s` and substitution fractions `a`, with the standing
assumptions `r_i > c_i > s_i > 0`, `a_ij ∈ [0,1]`, `a_ii = 0` and `∑_j a_ij < 1`.
`a i j` is the fraction of product `i`'s unmet demand that switches to product `j`.
Products are indexed by `Fin n` (0-based). -/
structure Model (n : ℕ) where
  r : Fin n → ℝ
  c : Fin n → ℝ
  s : Fin n → ℝ
  a : Fin n → Fin n → ℝ
  c_lt_r : ∀ i, c i < r i
  s_lt_c : ∀ i, s i < c i
  s_pos : ∀ i, 0 < s i
  a_nonneg : ∀ i j, 0 ≤ a i j
  a_le_one : ∀ i j, a i j ≤ 1
  a_diag : ∀ i, a i i = 0
  a_row_sum_lt_one : ∀ i, ∑ j, a i j < 1

namespace Model

variable {n : ℕ} (M : Model n)

/-- Unit underage cost `u_i = r_i - c_i` (p. 3). -/
def u (i : Fin n) : ℝ := M.r i - M.c i

/-- Unit overage cost `o_i = c_i - s_i` (p. 3). -/
def o (i : Fin n) : ℝ := M.c i - M.s i

end Model

/-- The first-choice demand vector `D = (D_1, …, D_n)` has law `μ`, "a known continuous
multivariate demand distribution with positive support" (p. 2): `μ` is absolutely continuous
with respect to Lebesgue measure on `ℝⁿ`, every coordinate is a.s. positive, and every
coordinate is integrable (so that the expected profits exist). Used with
`[IsProbabilityMeasure μ]`. -/
def IsDemandLaw {n : ℕ} (μ : Measure (Fin n → ℝ)) : Prop :=
  μ ≪ volume ∧ (∀ᵐ x ∂μ, ∀ i, 0 < x i) ∧ ∀ i, Integrable (fun x => x i) μ

/-- Disclosed pin: `μ` has a Lebesgue density that is strictly positive on the open positive
orthant. -/
def HasPositiveDensity {n : ℕ} (μ : Measure (Fin n → ℝ)) : Prop :=
  ∃ f : (Fin n → ℝ) → ℝ≥0∞, Measurable f ∧ μ = volume.withDensity f ∧
    ∀ x, (∀ i, 0 < x i) → 0 < f x

/-- Effective demand of product `i` after substitution (p. 3):
`D^s_i = D_i + ∑_{j ≠ i} a_ji (D_j - Q_j)⁺`, evaluated at the demand realization `x`. -/
def Ds {n : ℕ} (M : Model n) (Q x : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i + ∑ j ∈ Finset.univ.erase i, M.a j i * max (x j - Q j) 0

/-- Expected profit of firm `i` under competition, (9), p. 8:
`π_i = E[u_i D^s_i - u_i (D^s_i - Q_i)⁺ - o_i (Q_i - D^s_i)⁺]`. -/
noncomputable def firmProfit {n : ℕ} (M : Model n) (μ : Measure (Fin n → ℝ))
    (Q : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∫ x, (M.u i * Ds M Q x i - M.u i * max (Ds M Q x i - Q i) 0
      - M.o i * max (Q i - Ds M Q x i) 0) ∂μ

/-- `q` is firm `i`'s best response to the other firms' stocks `Q_{-i}` (p. 8):
`q ≥ 0` maximizes `π_i(·, Q_{-i})` over all stocking quantities `q' ≥ 0`. -/
def IsBestResponse {n : ℕ} (M : Model n) (μ : Measure (Fin n → ℝ))
    (Q : Fin n → ℝ) (i : Fin n) (q : ℝ) : Prop :=
  0 ≤ q ∧ ∀ q' : ℝ, 0 ≤ q' →
    firmProfit M μ (Function.update Q i q') i ≤ firmProfit M μ (Function.update Q i q) i

/-- Nash equilibrium (p. 9): "a strategy from which it will not be beneficial for any of the
players to deviate". It is the published pure-strategy Nash equilibrium of an `n`-player game
with nonnegative real strategies (`CachonCoord.Proportional.IsNash`), applied to the game whose
payoff to firm `i` at the profile `Q` is `π_i(Q)` of (9). -/
def IsNash {n : ℕ} (M : Model n) (μ : Measure (Fin n → ℝ)) (Q : Fin n → ℝ) : Prop :=
  CachonCoord.Proportional.IsNash (fun i P => firmProfit M μ P i) Q

/-- Unfolding: a Nash equilibrium is a nonnegative profile in which every `Q_i` is a best
response to `Q_{-i}`. -/
theorem isNash_iff {n : ℕ} (M : Model n) (μ : Measure (Fin n → ℝ)) (Q : Fin n → ℝ) :
    IsNash M μ Q ↔ (∀ i, 0 ≤ Q i) ∧ ∀ i, IsBestResponse M μ Q i (Q i) := by
  simp only [IsNash, CachonCoord.Proportional.IsNash, IsBestResponse, Function.update_eq_self]
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun i => ⟨h0 i, fun q' hq' => h i q' hq'⟩⟩
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun i q' hq' => (h i).2 q' hq'⟩

/-- The first-order condition (10) of firm `i`, p. 8:
`Pr(D_i < Q_i) - Pr(D_i < Q_i < D^s_i) = u_i / (u_i + o_i)`. -/
noncomputable def FOC10 {n : ℕ} (M : Model n) (μ : Measure (Fin n → ℝ))
    (Q : Fin n → ℝ) (i : Fin n) : Prop :=
  μ.real {x | x i < Q i} - μ.real {x | x i < Q i ∧ Q i < Ds M Q x i}
    = M.u i / (M.u i + M.o i)

end DemandSubstitution.Competitive


