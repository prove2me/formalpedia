-- Prove2me | Definitions.Def_HedgeInv_Order_Model
-- name    : HedgeInv_Order_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:38.936706+00:00
-- url     : https://prove2.me/theorems/1e36d396-f0cc-4364-9efb-d81c471c6957
-- title:
--   §2–§3.2, pp. 106–112 — the hedged newsvendor payoff (14), its expected utility, absolute prudence, the utility class and the ᾱ-condition
-- statement:
--   This file sets up the hedged newsvendor model of Gaur and Seshadri (2005), §3.2, in the scaled units of their display (11).
--
--   **Randomness.** The terminal price of a traded asset is $S_T\sim\nu$ and the scaled demand-forecast error is $\varepsilon\sim G$, where $\nu$ and $G$ are probability measures on $\mathbb R$ and $S_T$ and $\varepsilon$ are independent. Expectations are taken under the product law $\nu\otimes G$. Demand is $D=a+b(S_T+\varepsilon)$.
--
--   **Payoff.** A newsvendor stocks $I$ units. The firm also shorts an amount $\alpha$ of a hedging portfolio whose time-$T$ payoff is $X_T=\varphi(S_T)$ and whose time-$0$ price, compounded at the risk-free rate, is $x_0^r=X_0e^{rT}$. The scaled terminal wealth (14) is
--   $$\Pi_H(I,\alpha)=W+\min\Big\{S_T+\varepsilon,\ \frac{I-a}{b}\Big\}-c_1I-\alpha X_T+\alpha X_0e^{rT}.$$
--   Its expected utility is $E[u(\Pi_H(I,\alpha))]$. The conditional mean given $S_T=s$ is $E_\varepsilon[\Pi_H(I,\alpha)\mid S_T=s]=\int\Pi_H(I,\alpha)(s,e)\,dG(e)$. On the sell-out event $\{\varepsilon>(I-a)/b-S_T\}$ the payoff equals
--   $$\Pi_0=W+\frac{I-a}{b}-c_1I-\alpha X_T+\alpha X_0e^{rT}.$$
--
--   **Utility.** For a utility $u:\mathbb R\to\mathbb R$, absolute risk aversion is $R_A(w)=-u''(w)/u'(w)$ (Arrow–Pratt) and absolute prudence is $-u'''(w)/u''(w)$ (Kimball). Proposition 7 assumes $u$ increasing, concave and differentiable, with constant or decreasing absolute risk aversion and constant or decreasing absolute prudence. The utility class used here consists of the $C^3$ functions with $u'>0$ and $u''<0$ everywhere whose absolute risk aversion and absolute prudence are both nonincreasing.
--
--   **Standing assumptions** (§2, p. 106; §3, p. 107; (12), p. 111):
--   1. $\nu$ and $G$ are probability measures, with $E[\varepsilon]=0$ and $E[\varepsilon^2]<\infty$;
--   2. $b>0$;
--   3. $p>ce^{rT}>s$, which in scaled units reads $0<c_1$ and $c_1b<1$;
--   4. the hedge $\varphi$ is nondecreasing, measurable and $\nu$-integrable;
--   5. the hedge is a fair gamble: $E[X_T]=X_0e^{rT}$.
--
--   **The $\bar\alpha$-condition** (p. 112) states that $0\le\bar\alpha$ and that, for every $\alpha\in[0,\bar\alpha]$ and every admissible inventory $I>\max\{a,0\}$, $s\mapsto E_\varepsilon[\Pi_H(I,\alpha)\mid S_T=s]$ is nondecreasing.
--
--   **Regularity.** The proof of Proposition 7 differentiates under the expectation. Its regularity condition asks that, for every $I>\max\{a,0\}$ and $\alpha\in[0,\bar\alpha]$, the following are $\nu\otimes G$-integrable:
--   - $u(\Pi)$, $u'(\Pi)$ and $u''(\Pi)$;
--   - $u'(\Pi)\,\partial\Pi/\partial\alpha$ and $u''(\Pi)\,\partial\Pi/\partial\alpha$, where $\partial\Pi/\partial\alpha=X_0e^{rT}-X_T$.
--
--   It also asks that $\varepsilon\mapsto u''(\Pi)$ be $G$-integrable for every $s$.
--
--   **Formalization Note.** The parameters are the scaled ones of (11): $W=\{W_0e^{rT}+(p-s)a\}/\{(p-s)b\}$ and $c_1=(ce^{rT}-s)/\{(p-s)b\}$. The original prices $p,c,s$, the rate $r$ and the horizon $T$ enter only through $c_1$ and $x_0^r$. $R_A$ is the platform definition `MDPFinance.FinancialMarkets.arrowPrattCoefficient`, which is $-u''/u'$ with `deriv (deriv u)`. Derivatives of $u$ are written `deriv`, `deriv (deriv u)` and `deriv (deriv (deriv u))`. The conditional expectation given $S_T$ is an explicit integral over $G$, which independence makes exact; Mathlib's a.e.-defined `condExp` is not used.
--
--   Pinned relative to the page: (i) $u\in C^3$ with $u'>0$ and $u''<0$ on all of $\mathbb R$, because the paper's own argument uses $u'''$ and divides by $u'$ and $u''$, so both ratios must be defined; (ii) the paper defines $\bar\alpha$ as the largest $\alpha$ for which $E_\varepsilon[\Pi_H(I,\alpha)\mid S_T]$ is nondecreasing, for the inventory at hand; the $\bar\alpha$-condition asks this for every admissible $I$, since $I^*(\alpha)$ ranges over inventories. The set of such $\alpha\ge0$ is an interval containing $0$, so any $\bar\alpha$ satisfying the condition lies below the paper's; (iii) the paper writes $\Pi_0=(I-a)/b-c_1I-\alpha X_T+\alpha X_0$ on p. 119, without $W$ and $e^{rT}$; $\Pi_0$ here is the value of (14) itself on the sell-out event; (iv) "decreasing" is read weakly (nonincreasing), as in "constant or decreasing"; (v) the regularity condition is not in the paper, which differentiates under $E$ without comment. The assumption on p. 107 that $a$ is large enough for negative demand to be negligible is not formalized, because (14) involves demand only through $\min\{S_T+\varepsilon,(I-a)/b\}$.
-- source:
--   Gaur & Seshadri, Hedging Inventory Risk Through Market Instruments, Manuf. Serv. Oper. Manag. 7(2) (2005), p. 106 (§2 standing assumptions), p. 107 (§3 demand model), p. 110 (11), p. 111 (12), (14), R_A and absolute prudence, p. 112 (I*(α), ᾱ), p. 119 (Π₀)

import Mathlib
import Definitions.Def_MDPFinance_FinancialMarkets_Utility

namespace HedgeInv.Order

open MeasureTheory

/-- The hedged newsvendor payoff `Π_H(I, α)` of (14), p. 111, in the scaled units of (11), p. 110,
evaluated at `S_T = s` and `ε = e`:
`W + min{s + e, (I − a)/b} − c₁ I − α X_T + α X₀ e^{rT}`, with `X_T = φ(S_T)` and `x0r = X₀ e^{rT}`. -/
noncomputable def hedgedPayoff (W a b c₁ : ℝ) (φ : ℝ → ℝ) (x0r I α s e : ℝ) : ℝ :=
  W + min (s + e) ((I - a) / b) - c₁ * I - α * φ s + α * x0r

/-- The expected utility `E[u(Π_H(I, α))]` of (14), with `S_T ∼ ν` and `ε ∼ G` independent. -/
noncomputable def expUtil (ν G : Measure ℝ) (u : ℝ → ℝ) (W a b c₁ : ℝ) (φ : ℝ → ℝ)
    (x0r I α : ℝ) : ℝ :=
  ∫ p, u (hedgedPayoff W a b c₁ φ x0r I α p.1 p.2) ∂(ν.prod G)

/-- The conditional expectation `E_ε[Π_H(I, α) | S_T = s]` (p. 112), the integral over `ε ∼ G`
at fixed `S_T = s`. -/
noncomputable def condMeanPayoff (G : Measure ℝ) (W a b c₁ : ℝ) (φ : ℝ → ℝ)
    (x0r I α s : ℝ) : ℝ :=
  ∫ e, hedgedPayoff W a b c₁ φ x0r I α s e ∂G

/-- `Π₀(s)`, the value of (14) on the event `{ε > (I − a)/b − S_T}`, where the inventory sells out
(proof of Proposition 7, p. 119): `W + (I − a)/b − c₁ I − α φ(s) + α x0r`. -/
noncomputable def payoffSoldOut (W a b c₁ : ℝ) (φ : ℝ → ℝ) (x0r I α s : ℝ) : ℝ :=
  W + (I - a) / b - c₁ * I - α * φ s + α * x0r

/-- Absolute prudence `−u‴(w)/u″(w)` (Kimball 1990), p. 111. -/
noncomputable def absPrudence (u : ℝ → ℝ) (w : ℝ) : ℝ :=
  -(deriv (deriv (deriv u)) w) / deriv (deriv u) w

/-- The utility class of Proposition 7, p. 112: `u : ℝ → ℝ` three times continuously
differentiable, increasing (`u′ > 0`), strictly concave (`u″ < 0`), with constant or decreasing
absolute risk aversion `R_A = −u″/u′` and constant or decreasing absolute prudence `−u‴/u″`. -/
structure IsDARADAPUtility (u : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 3 u
  deriv_pos : ∀ w, 0 < deriv u w
  deriv2_neg : ∀ w, deriv (deriv u) w < 0
  dara : Antitone (MDPFinance.FinancialMarkets.arrowPrattCoefficient u)
  dap : Antitone (absPrudence u)

/-- The standing assumptions of §2 (p. 106), §3 (p. 107) and §3.2 (pp. 110–111) on the data:
`S_T ∼ ν` and `ε ∼ G` are probability laws, `E[ε] = 0` and `E[ε²] < ∞`; `b > 0`;
`p > c e^{rT} > s`, which in the scaled units of (11) reads `0 < c₁` and `c₁ b < 1`;
the hedge `X_T = φ(S_T)` is an increasing, measurable, integrable function of `S_T`;
and the fair-gamble constraint (12) `E[X_T] = X₀ e^{rT} = x0r`. -/
structure StandingAssumptions (ν G : Measure ℝ) (b c₁ : ℝ) (φ : ℝ → ℝ) (x0r : ℝ) : Prop where
  probν : IsProbabilityMeasure ν
  probG : IsProbabilityMeasure G
  mean_zero : ∫ e, e ∂G = 0
  memLp_two : MemLp id 2 G
  b_pos : 0 < b
  c₁_pos : 0 < c₁
  c₁b_lt_one : c₁ * b < 1
  mono : Monotone φ
  meas : Measurable φ
  integrable : Integrable φ ν
  fair : ∫ s, φ s ∂ν = x0r

/-- The `ᾱ`-condition of p. 112: `0 ≤ ᾱ`, and for every hedge ratio `α ∈ [0, ᾱ]` and every
admissible inventory `I > max{a, 0}`, `E_ε[Π_H(I, α) | S_T = s]` is nondecreasing in `s`. -/
def AlphaBarCond (G : Measure ℝ) (W a b c₁ : ℝ) (φ : ℝ → ℝ) (x0r αbar : ℝ) : Prop :=
  0 ≤ αbar ∧ ∀ α ∈ Set.Icc (0 : ℝ) αbar, ∀ I, max a 0 < I →
    Monotone (condMeanPayoff G W a b c₁ φ x0r I α)

/-- The integrability the proof of Proposition 7 uses when it differentiates under `E`
(pp. 118–119): for every `I > max{a, 0}` and `α ∈ [0, ᾱ]`, the functions `u(Π)`, `u′(Π)`,
`u′(Π)·∂Π/∂α`, `u″(Π)` and `u″(Π)·∂Π/∂α` (with `∂Π/∂α = x0r − φ(s)`) are integrable under the
joint law `ν ⊗ G`, and for every `s` the function `ε ↦ u″(Π)` is `G`-integrable, so that
`E_ε[u″(Π) | S_T = s]` is defined at every `s`. -/
def RegularityCond (ν G : Measure ℝ) (u : ℝ → ℝ) (W a b c₁ : ℝ) (φ : ℝ → ℝ)
    (x0r αbar : ℝ) : Prop :=
  ∀ I, max a 0 < I → ∀ α ∈ Set.Icc (0 : ℝ) αbar,
    Integrable (fun p : ℝ × ℝ => u (hedgedPayoff W a b c₁ φ x0r I α p.1 p.2)) (ν.prod G) ∧
    Integrable (fun p : ℝ × ℝ => deriv u (hedgedPayoff W a b c₁ φ x0r I α p.1 p.2))
      (ν.prod G) ∧
    Integrable (fun p : ℝ × ℝ =>
      deriv u (hedgedPayoff W a b c₁ φ x0r I α p.1 p.2) * (x0r - φ p.1)) (ν.prod G) ∧
    Integrable (fun p : ℝ × ℝ => deriv (deriv u) (hedgedPayoff W a b c₁ φ x0r I α p.1 p.2))
      (ν.prod G) ∧
    Integrable (fun p : ℝ × ℝ =>
      deriv (deriv u) (hedgedPayoff W a b c₁ φ x0r I α p.1 p.2) * (x0r - φ p.1)) (ν.prod G) ∧
    ∀ s, Integrable (fun e => deriv (deriv u) (hedgedPayoff W a b c₁ φ x0r I α s e)) G

end HedgeInv.Order


