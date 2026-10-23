-- Prove2me | Definitions.Def_RiskyBenefitCost_NthDegree_Model
-- name    : RiskyBenefitCost_NthDegree_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:34.029438+00:00
-- url     : https://prove2.me/theorems/1d0ab457-28f2-4398-9d56-7a2310883b66
-- title:
--   §2–§4, pp. 3626–3628 — linear-payoff problem, iterated CDFs, Ekern Nth-degree risk increase, problem classes, risk aversion, argmax sets
-- statement:
--   This file sets up the linear-payoff decision model of Menegatti and Peter (2022) and the higher-order risk notions it uses.
--
--   **Payoff and objective.** A decision maker chooses $b$ from a set $B\subset\mathbb R$. For a realization $X$ of a random variable $\tilde X$, the payoff is
--   $$z(X,b)=f(b)\,(X-x_0)+z_0,$$
--   where $f:\mathbb R\to\mathbb R$ links behaviour to the payoff and $x_0,z_0$ are constants. If $\tilde X$ has law $\mu$ and $U$ is a utility function, the expected utility of $b$ is
--   $$\mathrm{EU}_\mu(b)=\int U\big(f(b)(x-x_0)+z_0\big)\,\mu(dx),$$
--   and the maximizer set is $B^*=\operatorname{argmax}_{b\in B}\mathrm{EU}_\mu(b)=\{b\in B:\ \mathrm{EU}_\mu(b')\le \mathrm{EU}_\mu(b)\text{ for all }b'\in B\}$.
--
--   **Problem classes (Definition 1).** The problem is
--   1. *risk taking with a risky benefit* if $f$ is increasing on $B$ and $f\ge 0$ on $B$;
--   2. *risk mitigation with a risky benefit* if $f$ is decreasing on $B$ and $f\ge 0$ on $B$;
--   3. *risk mitigation with a risky cost* if $f$ is increasing on $B$ and $f\le 0$ on $B$;
--   4. *risk taking with a risky cost* if $f$ is decreasing on $B$ and $f\le 0$ on $B$.
--
--   "Increasing" and "decreasing" are meant in the weak sense.
--
--   **Iterated distribution functions and Nth-degree risk increases (Definition 2, Ekern 1980).** Let $F$ be the cumulative distribution function of a law $\mu$ on $[\underline x,\bar x]$. Set $F^{(1)}=F$ and $F^{(k+1)}(z)=\int_{\underline x}^{z}F^{(k)}(t)\,dt$ for $k\ge1$. If $F$ and $G$ are the distribution functions of $\tilde X_1$ and $\tilde X_2$, then $\tilde X_2$ is an *$N$th-degree risk increase* over $\tilde X_1$ if
--   1. $F^{(k)}(\bar x)=G^{(k)}(\bar x)$ for all $k=1,\dots,N$, and
--   2. $F^{(N)}(z)\le G^{(N)}(z)$ for all $z\in[\underline x,\bar x]$.
--
--   **Risk attitudes.** Write $U^{(N)}$ for the $N$th derivative of $U$. The decision maker is *$N$th-degree risk averse* on a domain $D$ if $(-1)^{N+1}U^{(N)}(z)\ge 0$ for all $z\in D$ (Definition 3). Where $(-1)^{N+1}U^{(N)}(z)>0$, the *relative $(N+1)$th-degree risk aversion* is
--   $$r_{N+1}(z)=-\frac{z\,U^{(N+1)}(z)}{U^{(N)}(z)}\qquad\text{(Definition 4)}.$$
--
--   **The sign-adjusted derivative (display (5)).** For fixed $X$, the function of $b$
--   $$(-1)^N f(b)^N\,U^{(N)}\big(f(b)(X-x_0)+z_0\big)$$
--   is the quantity whose monotonicity in $b$ decides the comparative statics (Lemma 3).
--
--   These objects are shared by every statement of the mission: the goal (Proposition 2) compares the maximizer sets under the laws of $\tilde X_1$ and $\tilde X_2$ in the strong set order.
--
--   **Formalization Note.** Random variables enter only through their laws $\mu:\mathrm{Measure}\,\mathbb R$; the CDF is Mathlib's right-continuous `cdf μ z = μ(-∞, z]`. The iterated CDF is indexed from $0$: `iterCDF μ xl k` is the page's $F^{(k+1)}$, so the page's $F^{(k)}$ ($k\ge1$) is `iterCDF μ xl (k-1)`, and Definition 2 is stated with that shift. The codomain conditions $C\subset\mathbb R_0^{\pm}$ of Definition 1 are read as the sign of $f$ on $B$. `relRiskAversion` divides by $U^{(N)}(z)$; Lean returns $0$ on division by zero, so every statement that uses it also assumes $(-1)^{N+1}U^{(N)}(z)>0$, as Definition 4 requires. Expected utility is a Bochner integral; statements that use it assume the law is a probability measure concentrated on $[\underline x,\bar x]$ and $U$ continuous, so the integral is finite.
-- source:
--   Menegatti & Peter, Changes in risky benefits and in risky costs: a question of the right order, Management Science 68(5) (2022), pp. 3626–3628 (PDF 3–5), displays (1), (2), (4), (5), Definitions 1–4

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

namespace RiskyBenefitCost.NthDegree

open MeasureTheory ProbabilityTheory

/-- Iterated cumulative distribution functions of §3 (p. 3626), with an index shift:
`iterCDF μ xl k` is the page's `F^(k+1)`. Index `0` is the cumulative distribution function
`F = F^(1)` of the law `μ` (Mathlib's right-continuous `cdf μ z = μ (-∞, z]`), and
`F^(k+2)(z) = ∫_{xl}^{z} F^(k+1)(t) dt`. So the page's `F^(k)` (for `k ≥ 1`) is
`iterCDF μ xl (k - 1)`. -/
noncomputable def iterCDF (μ : Measure ℝ) (xl : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun z => cdf μ z
  | k + 1 => fun z => ∫ t in xl..z, iterCDF μ xl k t

/-- Definition 2 (Ekern 1980), p. 3626. The law `μ₂` of `X̃₂` (CDF `G`) is an `N`th-degree risk
increase over the law `μ₁` of `X̃₁` (CDF `F`), both on `[xl, xu]`, if
(i) `F^(k)(xu) = G^(k)(xu)` for all `k = 1, …, N`, and
(ii) `F^(N)(z) ≤ G^(N)(z)` for all `z ∈ [xl, xu]`.
With the index shift of `iterCDF`, `F^(k)` is `iterCDF μ₁ xl (k - 1)`. Meaningful for `1 ≤ N`. -/
def IsNthDegreeRiskIncrease (N : ℕ) (xl xu : ℝ) (μ₁ μ₂ : Measure ℝ) : Prop :=
  (∀ k ∈ Finset.Icc 1 N, iterCDF μ₁ xl (k - 1) xu = iterCDF μ₂ xl (k - 1) xu) ∧
  ∀ z ∈ Set.Icc xl xu, iterCDF μ₁ xl (N - 1) z ≤ iterCDF μ₂ xl (N - 1) z

/-- Expected utility `E U(z(X̃, b))` of the decision `b` when `X̃` has law `μ`, with the
linear payoff (1) `z(X, b) = f(b)·(X − x0) + z0`; the objective of problem (2). -/
noncomputable def EU (U f : ℝ → ℝ) (x0 z0 : ℝ) (μ : Measure ℝ) (b : ℝ) : ℝ :=
  ∫ x, U (f b * (x - x0) + z0) ∂μ

/-- The maximizer set (4): `argmaxSet B g = {b ∈ B | g b' ≤ g b for all b' ∈ B}`. -/
def argmaxSet (B : Set ℝ) (g : ℝ → ℝ) : Set ℝ :=
  {b | b ∈ B ∧ ∀ b' ∈ B, g b' ≤ g b}

/-- Definition 1, p. 3626: risk taking with a risky benefit (`f` increasing, values `≥ 0`).
The codomain condition `C ⊂ ℝ₀⁺` is read as `f b ≥ 0` for every `b ∈ B`. -/
def RiskTakingBenefit (f : ℝ → ℝ) (B : Set ℝ) : Prop :=
  MonotoneOn f B ∧ ∀ b ∈ B, 0 ≤ f b

/-- Definition 1: risk mitigation with a risky benefit (`f` decreasing, values `≥ 0`). -/
def RiskMitigationBenefit (f : ℝ → ℝ) (B : Set ℝ) : Prop :=
  AntitoneOn f B ∧ ∀ b ∈ B, 0 ≤ f b

/-- Definition 1: risk mitigation with a risky cost (`f` increasing, values `≤ 0`). -/
def RiskMitigationCost (f : ℝ → ℝ) (B : Set ℝ) : Prop :=
  MonotoneOn f B ∧ ∀ b ∈ B, f b ≤ 0

/-- Definition 1: risk taking with a risky cost (`f` decreasing, values `≤ 0`). -/
def RiskTakingCost (f : ℝ → ℝ) (B : Set ℝ) : Prop :=
  AntitoneOn f B ∧ ∀ b ∈ B, f b ≤ 0

/-- Definition 3 (Ekern 1980), p. 3627: `U` is `N`th-degree risk averse on the domain `D`,
i.e. `(−1)^(N+1) U^(N)(z) ≥ 0` for all `z ∈ D`. -/
def NthDegreeRiskAverseOn (N : ℕ) (U : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∀ z ∈ D, 0 ≤ (-1 : ℝ) ^ (N + 1) * iteratedDeriv N U z

/-- Definition 4 (Eeckhoudt and Schlesinger 2008), p. 3628: relative `(N+1)`th-degree risk
aversion `r_{N+1}(z) = −z U^(N+1)(z) / U^(N)(z)`. The page defines it only where
`(−1)^(N+1) U^(N)(z) > 0`; every statement using it assumes this, so the division is never
by zero. -/
noncomputable def relRiskAversion (N : ℕ) (U : ℝ → ℝ) (z : ℝ) : ℝ :=
  -z * iteratedDeriv (N + 1) U z / iteratedDeriv N U z

/-- Display (5), p. 3627: the sign-adjusted `N`th derivative
`(−1)^N f(b)^N U^(N)(f(b)·(X − x0) + z0)`, as a function of the decision `b`. -/
noncomputable def signAdj (N : ℕ) (U f : ℝ → ℝ) (x0 z0 X b : ℝ) : ℝ :=
  (-1 : ℝ) ^ N * f b ^ N * iteratedDeriv N U (f b * (X - x0) + z0)

end RiskyBenefitCost.NthDegree


