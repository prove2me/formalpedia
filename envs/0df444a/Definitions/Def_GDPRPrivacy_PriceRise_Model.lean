-- Prove2me | Definitions.Def_GDPRPrivacy_PriceRise_Model
-- name    : GDPRPrivacy_PriceRise_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:28:39.804212+00:00
-- url     : https://prove2.me/theorems/5afd9d98-6c22-477f-9771-d361c4f32a25
-- title:
--   §3–§4, pp. 7–14, 31–32 — consumer types on [0,1]², utilities (1)–(2), demand before and after the GDPR, profits (3), thresholds α₁, α₂ and radicals β, Γ
-- statement:
--   This file sets up the monopoly model of Choe, Matsushima and Shekhar.
--
--   A monopolist sells an online service at zero marginal cost and price $p \in \mathbb{R}$. A consumer has a type $(v, c) \in [0,1]^2$: $v$ is the valuation for the service and $c$ the privacy cost of sharing data. Types are independent and uniform on $[0,1]^2$, so the mass of a set of consumers is its Lebesgue area. The firm offers an **opt-in benefit** $x$ to consumers who share data, and earns an exogenous **data revenue** $\alpha$ per unit of shared data.
--
--   The utilities of opt-in purchase (buy and share data) and of opt-out purchase (buy without sharing) are
--   $$U_S(v,c) = v + (x - c) - p, \qquad U_N(v,c) = v - p. \qquad (1)\text{–}(2)$$
--
--   1. **Before the GDPR** opt-out purchase is not available: a consumer buys, and shares data, iff $U_S \ge 0$, i.e. $c \le v + x - p$. The demand $\widehat D(p)$ is the area of this set of types, and the firm's profit is
--   $$\widehat\Pi(p) = (p + \alpha)\,\widehat D(p).$$
--   2. **After the GDPR** the consumer may buy without sharing. The opt-in and opt-out sets are, as on p. 13,
--   $$\{(v,c) \in [0,1]^2 \mid c \le v + x - p,\ c \le x\}, \qquad \{(v,c) \in [0,1]^2 \mid v \ge p,\ c > x\},$$
--   their areas are the opt-in demand $\widetilde D_S(p)$ and the opt-out demand $\widetilde D_N(p)$, the total demand is $\widetilde D = \widetilde D_S + \widetilde D_N$, and the profit is
--   $$\widetilde\Pi(p) = p\,\widetilde D(p) + \alpha\,\widetilde D_S(p).$$
--
--   Finally the file names the thresholds and radicals of the paper's appendix:
--   $$\alpha_1(x) = \max\Big\{\frac{1-2x}{2}, 0\Big\}, \quad \alpha_2(x) = \max\Big\{\frac{2-4x+x^2}{2x}, 0\Big\}, \quad \beta = \sqrt{6 + (x+\alpha-1)^2}, \quad \Gamma = \sqrt{6 + (2-2x+\alpha)^2}.$$
--
--   Every result of the mission is a statement about these demands and profits: the equilibrium price in each regime is a global maximizer of $\widehat\Pi$ or $\widetilde\Pi$ over all real prices.
--
--   **Formalization Note** A type is a pair `q : ℝ × ℝ` with `q.1 = v`, `q.2 = c`. Areas are `(volume S).toReal` for the Lebesgue measure on `ℝ × ℝ`; every set lies in the unit square, so the measure is finite and `toReal` loses nothing. The p. 8 decision rule (opt-in iff $U_S \ge \max\{U_N,0\}$, opt-out iff $U_N \ge \max\{U_S, 0\}$) is encoded by the two sets of p. 13, which send the tie $U_S = U_N \ge 0$ to opt-in; this changes only a null set. The profits are functions of the price on all of $\mathbb{R}$, so negative prices are admitted (footnote 22). The data revenue is written `α` in Lean. The definitions themselves place no restriction on $x$ and $\alpha$; the standing assumptions $0 < x < 1$, $\alpha \ge 0$ are hypotheses of every theorem.
-- source:
--   Choe, Matsushima & Shekhar, The Bright Side of the GDPR, ISER DP No. 1246 (June 2024), pp. 7–8 (§3, (1)–(3)), p. 10–11 (pre-GDPR demand and Π̂), pp. 13–14 (opt-in/opt-out sets, Π̃), pp. 31–32 (α₁, α₂, β, Γ)

import Mathlib

namespace GDPRPrivacy.PriceRise

open MeasureTheory

/-- The set of consumer types `[0,1]²`. A type is `q = (v, c)`: `q.1 = v` is the valuation for the
service and `q.2 = c` the privacy cost. Types are uniform on this square, so the mass of a set of
consumers is its Lebesgue area. (§3, p. 7) -/
def typeSquare : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

/-- Utility (1), p. 8, of opt-in purchase at price `p` with opt-in benefit `x`:
`U_S(v, c) = v + (x - c) - p`. -/
def utilS (x p : ℝ) (q : ℝ × ℝ) : ℝ := q.1 + (x - q.2) - p

/-- Utility (2), p. 8, of opt-out purchase at price `p`: `U_N(v, c) = v - p`. -/
def utilN (p : ℝ) (q : ℝ × ℝ) : ℝ := q.1 - p

/-- Before the GDPR a consumer buys (and shares data) iff `U_S ≥ 0` (p. 8). -/
def buyersBefore (x p : ℝ) : Set (ℝ × ℝ) := {q | q ∈ typeSquare ∧ 0 ≤ utilS x p q}

/-- After the GDPR, the opt-in purchasers, p. 13: `{(v, c) ∈ [0,1]² | c ≤ v + x - p, x ≥ c}`. -/
def optInSet (x p : ℝ) : Set (ℝ × ℝ) := {q | q ∈ typeSquare ∧ q.2 ≤ q.1 + x - p ∧ q.2 ≤ x}

/-- After the GDPR, the opt-out purchasers, p. 13: `{(v, c) ∈ [0,1]² | v ≥ p, x < c}`. -/
def optOutSet (x p : ℝ) : Set (ℝ × ℝ) := {q | q ∈ typeSquare ∧ p ≤ q.1 ∧ x < q.2}

/-- Demand before the GDPR, `D̂(p)`: the area of the buyer set. -/
noncomputable def demandBefore (x p : ℝ) : ℝ := (volume (buyersBefore x p)).toReal

/-- Opt-in demand after the GDPR, `D̃_S(p)`. -/
noncomputable def demandIn (x p : ℝ) : ℝ := (volume (optInSet x p)).toReal

/-- Opt-out demand after the GDPR, `D̃_N(p)`. -/
noncomputable def demandOut (x p : ℝ) : ℝ := (volume (optOutSet x p)).toReal

/-- Total demand after the GDPR, `D̃(p) = D̃_S(p) + D̃_N(p)`. -/
noncomputable def demandAfter (x p : ℝ) : ℝ := demandIn x p + demandOut x p

/-- Profit (3) before the GDPR as a function of the price, `Π̂(p) = (p + α) D̂(p)` (p. 11):
every buyer shares data, so the data revenue is `α D̂(p)`. -/
noncomputable def profitBefore (x α : ℝ) (p : ℝ) : ℝ := (p + α) * demandBefore x p

/-- Profit (3) after the GDPR as a function of the price, `Π̃(p) = p D̃(p) + α D̃_S(p)` (p. 14). -/
noncomputable def profitAfter (x α : ℝ) (p : ℝ) : ℝ := p * demandAfter x p + α * demandIn x p

/-- `α₁(x) := max{(1 - 2x)/2, 0}` (p. 31). -/
noncomputable def alpha1 (x : ℝ) : ℝ := max ((1 - 2 * x) / 2) 0

/-- `α₂(x) := max{(2 - 4x + x²)/(2x), 0}` (p. 32). -/
noncomputable def alpha2 (x : ℝ) : ℝ := max ((2 - 4 * x + x ^ 2) / (2 * x)) 0

/-- `β := √(6 + (x + α - 1)²)` (p. 31). -/
noncomputable def beta (x α : ℝ) : ℝ := Real.sqrt (6 + (x + α - 1) ^ 2)

/-- `Γ := √(6 + (2 - 2x + α)²)` (p. 32). -/
noncomputable def Gamma (x α : ℝ) : ℝ := Real.sqrt (6 + (2 - 2 * x + α) ^ 2)

end GDPRPrivacy.PriceRise


