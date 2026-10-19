-- Prove2me | Definitions.Def_SPPRevenue_SingleUnit_Setting
-- name    : SPPRevenue_SingleUnit_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:14.823638+00:00
-- url     : https://prove2.me/theorems/fd2763d1-5454-4950-8f11-519ef36ca49d
-- title:
--   §3–§4.1, pp. 8–15 — single-unit SPP revenue, threshold mechanisms (Lemma 1), s⋆, Myersonian and uniform prices, MP, UP, the program (FR)
-- statement:
--   A seller has one indivisible item and $n$ buyers, indexed $i \in [n]$. Buyer $i$ has a private value $v_i$ drawn independently from a known distribution $F_i$ (written $\mu_i$), so the value profile $v = (v_1,\dots,v_n)$ has the product law $\mu_1 \otimes \cdots \otimes \mu_n$.
--
--   1. **Sequential posted prices.** For a price vector $p = (p_1,\dots,p_n)$, the mechanism SPP$(p)$ approaches the buyers in decreasing order of price, offers $p_i$ to buyer $i$ while the item is unsold, and sells to the first buyer with $v_i \ge p_i$ at price $p_i$. The buyer served is one with the largest price among those who accept, so the revenue at the profile $v$ is
--   $$\mathrm{rev}_p(v) = \max\{p_i : v_i \ge p_i\}\qquad(0 \text{ if no buyer accepts}),$$
--   and $\mathrm{SPP}(p) = \mathbb E[\mathrm{rev}_p(v)]$.
--   2. **Threshold mechanisms (Lemma 1, taxation principle).** A single-unit threshold mechanism is a family of thresholds $t_i(v_{-i}) \ge 0$, measurable, depending only on the other buyers' values, such that almost surely at most one buyer has $v_i \ge t_i(v_{-i})$. Buyer $i$ wins and pays $t_i$ exactly when $v_i \ge t_i$, so the expected revenue is
--   $$\mathrm{Opt}(t) = \mathbb E\Big[\sum_{i} t_i(v_{-i})\,\mathbf 1\{v_i \ge t_i(v_{-i})\}\Big].$$
--   For the thresholds of Myerson's optimal mechanism this is the paper's $\mathrm{Opt}$.
--   3. **The function $s^\star$.** $s^\star_i(\tau) = \mathbb P[v_i \ge t_i(v_{-i}) \ge \tau]$ and $s^\star(\tau) = \sum_i s^\star_i(\tau)$.
--   4. **Myersonian prices.** For each buyer $i$ draw a fresh, independent copy $v'^{(i)}$ of the whole value profile, independent of $v$, and set $t'_i = t_i(v'^{(i)}_{-i})$. MP is the expected revenue of SPP$(t'_1,\dots,t'_n)$ over both the prices and the values; $m(\tau)$ is the probability that some buyer has $v_i \ge t'_i \ge \tau$ (equivalently, that this mechanism sells at a price of at least $\tau$); and $Z_\tau = \sum_i \mathbf 1(v_i \ge t'_i \ge \tau)$.
--   5. **Uniform price.** $\mathrm{UP} = \sup_{\tau \ge 0} \mathrm{SPP}(\tau,\dots,\tau)$.
--   6. **The program (FR).** With $f(x) = 1 - e^{-x}$, a function $s$ on $[0,\infty)$ is feasible when it is weakly decreasing, $0 \le s(\tau) \le \min(1, 1/\tau)$ for all $\tau \ge 0$, and $\int_0^\infty f(s(\tau))\,d\tau \le 1$; its objective is $\int_0^\infty s(\tau)\,d\tau$. Also $q_n(y) = (1 - y/n)^n$, and $\tau^\star$ is defined by the equation
--   $$(1 - e^{-1}) + \int_1^{\tau^\star} \big(1 - e^{-1/\tau}\big)\,d\tau = 1 .$$
--
--   These are the objects of Theorem 1: the benchmark is any single-unit threshold mechanism, and the two pricing rules (Myersonian and uniform) are compared with it through $s^\star$.
--
--   **Formalization Note** Buyer $i$ of the paper is index $i-1$ of `Fin n`. Revenues and probabilities are in $[0,\infty]$ (lower Lebesgue integrals and measures), so no revenue can collapse to a junk value. The re-sampled profile of buyer $i$ is a full copy of the profile whose $i$-th coordinate is ignored by $t_i$. The constraint $s(\tau) \le \min(1,1/\tau)$ is written $s(\tau) \le 1$ and $\tau\, s(\tau) \le 1$, which is the same constraint and avoids Lean's $1/0 = 0$ at $\tau = 0$. Feasibility of the threshold mechanism is required almost surely, which is what the paper's construction for atomless or finitely supported distributions provides (pp. 10–11).
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, pp. 8–15, §3, Lemma 1, §3.2, Equation (1), §4.1, (FR), Lemma 2

import Mathlib

namespace SPPRevenue.SingleUnit

open MeasureTheory
open scoped ENNReal

/-- Revenue of the single-unit sequential posted-price mechanism SPP(p) at the value profile `v`
(§3, p. 9). The mechanism approaches the buyers in decreasing order of price and sells to the first
buyer `i` with `p i ≤ v i`, at price `p i`; the winner is therefore a buyer with the largest price
among those who accept, and the revenue is `max {p i : p i ≤ v i}` (`0` if nobody accepts). Ties
between equal prices do not change the revenue. Buyer `i : Fin n` is the paper's buyer `i + 1`. -/
noncomputable def sppRevAt {n : ℕ} (p v : Fin n → ℝ) : ℝ≥0∞ :=
  (Finset.univ.filter (fun i => p i ≤ v i)).sup (fun i => ENNReal.ofReal (p i))

/-- The expected revenue SPP(p) (§3, p. 9) when the value profile `v` has law `Measure.pi μ`
(independent private values, buyer `i`'s value distributed as `μ i`). -/
noncomputable def sppRev {n : ℕ} (μ : Fin n → Measure ℝ) (p : Fin n → ℝ) : ℝ≥0∞ :=
  ∫⁻ v, sppRevAt p v ∂(Measure.pi μ)

/-- A single-unit threshold mechanism (Lemma 1, p. 9; feasibility pp. 10–11 and 14).
`t i v` is the threshold `t_i(v_{-i})` of buyer `i`: buyer `i` wins and pays `t i v` exactly when
`t i v ≤ v i`. The thresholds are measurable, nonnegative, do not depend on the buyer's own value,
and almost surely at most one buyer weakly exceeds their threshold. -/
structure IsThresholdMech {n : ℕ} (μ : Fin n → Measure ℝ) (t : Fin n → (Fin n → ℝ) → ℝ) :
    Prop where
  measurable : ∀ i, Measurable (t i)
  nonneg : ∀ i v, 0 ≤ t i v
  indep_own : ∀ i (v w : Fin n → ℝ), (∀ j, j ≠ i → v j = w j) → t i v = t i w
  single_unit : ∀ᵐ v ∂(Measure.pi μ), ∀ i j, t i v ≤ v i → t j v ≤ v j → i = j

/-- The expected revenue `E[Σ_i t_i 1{v_i ≥ t_i}]` of the threshold mechanism `t`; for the optimal
mechanism's thresholds this is the paper's Opt (pp. 9–12). -/
noncomputable def optRev {n : ℕ} (μ : Fin n → Measure ℝ) (t : Fin n → (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  ∫⁻ v, ∑ i, (if t i v ≤ v i then ENNReal.ofReal (t i v) else 0) ∂(Measure.pi μ)

/-- `s⋆_i(τ) = P[v_i ≥ t_i(v_{-i}) ≥ τ]` (§3.2, pp. 11–12). -/
noncomputable def sStarI {n : ℕ} (μ : Fin n → Measure ℝ) (t : Fin n → (Fin n → ℝ) → ℝ)
    (i : Fin n) (τ : ℝ) : ℝ≥0∞ :=
  Measure.pi μ {v | t i v ≤ v i ∧ τ ≤ t i v}

/-- `s⋆(τ) = Σ_i s⋆_i(τ)` (§3.2, p. 12). -/
noncomputable def sStar {n : ℕ} (μ : Fin n → Measure ℝ) (t : Fin n → (Fin n → ℝ) → ℝ)
    (τ : ℝ) : ℝ≥0∞ :=
  ∑ i, sStarI μ t i τ

/-- Law of the pair `(W, v)` used by the Myersonian prices (§3.2, p. 11): `v` is the value profile,
and `W i` is an independent fresh copy of the whole value profile drawn for buyer `i`, independent
across buyers and of `v`. The re-sampled threshold of buyer `i` is `t′_i = t i (W i)`; coordinate
`i` of `W i` is ignored by `t i`. -/
noncomputable def resampleLaw {n : ℕ} (μ : Fin n → Measure ℝ) :
    Measure ((Fin n → Fin n → ℝ) × (Fin n → ℝ)) :=
  (Measure.pi (fun _ : Fin n => Measure.pi μ)).prod (Measure.pi μ)

/-- MP: the expected revenue of the Myersonian SPP mechanism, which posts the re-sampled threshold
`t′_i` to buyer `i`, the expectation taken over both the prices and the values (pp. 11–12). -/
noncomputable def mpRev {n : ℕ} (μ : Fin n → Measure ℝ) (t : Fin n → (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, sppRevAt (fun i => t i (x.1 i)) x.2 ∂(resampleLaw μ)

/-- `m(τ)`: the probability that there is at least one buyer with `v_i ≥ t′_i ≥ τ`, which is the
probability that the Myersonian SPP mechanism sells at a price of at least `τ` (pp. 12, 14). -/
noncomputable def mSell {n : ℕ} (μ : Fin n → Measure ℝ) (t : Fin n → (Fin n → ℝ) → ℝ)
    (τ : ℝ) : ℝ≥0∞ :=
  resampleLaw μ {x | ∃ i, t i (x.1 i) ≤ x.2 i ∧ τ ≤ t i (x.1 i)}

/-- `Z_τ = Σ_i 1(v_i ≥ t′_i ≥ τ)`, the number of buyers clearing their re-sampled threshold at a
level of at least `τ` (p. 14, Lemma 2 p. 15), as a function of the pair `x = (W, v)`. -/
noncomputable def ZTau {n : ℕ} (t : Fin n → (Fin n → ℝ) → ℝ) (τ : ℝ)
    (x : (Fin n → Fin n → ℝ) × (Fin n → ℝ)) : ℕ :=
  (Finset.univ.filter (fun i => t i (x.1 i) ≤ x.2 i ∧ τ ≤ t i (x.1 i))).card

/-- UP: the expected revenue of the best uniform posted price, `sup_{τ ≥ 0} SPP(τ, …, τ)`
(§3.2, p. 11; §4.1, p. 12). -/
noncomputable def upRev {n : ℕ} (μ : Fin n → Measure ℝ) : ℝ≥0∞ :=
  ⨆ (τ : ℝ) (_ : 0 ≤ τ), sppRev μ (fun _ => τ)

/-- `q_n(y) = (1 − y/n)^n` (Lemma 2, p. 15). -/
noncomputable def qn (n : ℕ) (y : ℝ) : ℝ := (1 - y / n) ^ n

/-- Feasibility for the factor-revealing program (FR) (p. 13), with `f(x) = 1 − e^{−x}`:
`s` is weakly decreasing on `τ ≥ 0`, `0 ≤ s(τ) ≤ min(1, 1/τ)` for every `τ ≥ 0` (written
`s τ ≤ 1 ∧ τ * s τ ≤ 1`, which is the same constraint and reads `s 0 ≤ 1` at `τ = 0`), and
`∫_0^∞ f(s(τ)) dτ ≤ 1`. -/
def FRFeasible (s : ℝ → ℝ) : Prop :=
  AntitoneOn s (Set.Ici 0) ∧
    (∀ τ, 0 ≤ τ → 0 ≤ s τ ∧ s τ ≤ 1 ∧ τ * s τ ≤ 1) ∧
    ∫⁻ τ in Set.Ici 0, ENNReal.ofReal (1 - Real.exp (-s τ)) ≤ 1

/-- The objective `∫_0^∞ s(τ) dτ` of (FR) (p. 13). -/
noncomputable def frObj (s : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ τ in Set.Ici 0, ENNReal.ofReal (s τ)

/-- The equation `(1 − e^{−1}) + ∫_1^T (1 − e^{−1/τ}) dτ = 1` defining the threshold `τ⋆`
(§4.1, p. 15, Solving Problem (FR)). -/
def frRootEq (T : ℝ) : Prop :=
  (1 - Real.exp (-1)) + ∫ τ in (1 : ℝ)..T, (1 - Real.exp (-(1 / τ))) = 1

end SPPRevenue.SingleUnit


