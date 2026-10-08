-- Prove2me | Definitions.Def_CVPricing_Regret_Model
-- name    : CVPricing_Regret_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:31:05.75775+00:00
-- url     : https://prove2.me/theorems/74d7c327-eb72-4e54-a556-d0144463301e
-- title:
--   §2, p. 773 — the demand model (1), its standing assumptions, the revenue r(p, a) and the optimal price p(a)
-- statement:
--   A monopolist sells one product over periods $t = 1, 2, \dots$, choosing each period a price $p_t \in [p_l, p_h]$, where $0 < p_l < p_h$. Demand at price $p$ is a random variable $D(p)$ with
--
--   $$\mathbb E[D(p)] = h\big(a_0^{(0)} + a_1^{(0)} p\big), \qquad \operatorname{Var}[D(p)] = \sigma^2\, v\big(\mathbb E[D(p)]\big). \tag{1}$$
--
--   The **link function** $h$ and the **variance function** $v$ are known; the dispersion $\sigma > 0$ and the parameter $a^{(0)} = (a_0^{(0)}, a_1^{(0)})$ are unknown. The standing assumptions are:
--
--   1. $h$ and $v$ are twice continuously differentiable on $[0,\infty)$, with $h \ge 0$, $v > 0$ and $\dot h > 0$ there;
--   2. $a_0^{(0)} > 0$, $a_1^{(0)} < 0$ and $a_0^{(0)} + a_1^{(0)} p_h > 0$;
--   3. there is an open neighbourhood $U \subset \mathbb R^2$ of $a^{(0)}$ such that for every $a = (a_0, a_1) \in U$ the expected revenue
--   $$r(p, a) = p\, h(a_0 + a_1 p)$$
--   has a unique maximizer $p(a)$ over $[p_l, p_h]$, this maximizer lies in $(p_l, p_h)$, and $\partial_p^2 r(p(a), a) < 0$.
--
--   The **optimal price** is $p_{\mathrm{opt}} = p(a^{(0)})$. The definition also records the predicate "$q$ maximizes $r(\cdot, a)$ over a set $S$" used by the pricing rule.
--
--   These are the objects every statement of the mission is written in.
--
--   **Formalization Note** $h, v : \mathbb R \to \mathbb R$ are total functions constrained only on $[0,\infty)$, and $\dot h$ is the two-sided derivative of that extension; every $C^2$ function on $[0,\infty)$ has a $C^2$ extension, so no instance of the paper is lost. The paper prints $a_0^{(0)} + a_1^{(0)} p_h \ge 0$; the strict inequality is required here because in the boundary case the pricing rule's case (c) fires infinitely often and the proof of Theorem 1 does not cover it. The neighbourhood assumption is printed with $\arg\max_{p_l < p < p_h}$; it is read as a unique maximizer over the closed interval lying in the open one, because the pricing rule and the regret use the closed interval. $p(a)$ is defined by choice when the maximizer is unique and takes the junk value $p_l$ otherwise; statements only evaluate it for $a$ near $a^{(0)}$.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 773 (PDF 5), §2, eq. (1) and the neighbourhood assumption

import Mathlib

namespace CVPricing.Regret

/-- Expected single-period revenue `r(p, a) = p · h(a₀ + a₁ p)` at price `p` under the parameter
`a = (a₀, a₁)` and the link function `h` (den Boer–Zwart 2014, §2, p. 773). -/
def revenue (h : ℝ → ℝ) (a : ℝ × ℝ) (p : ℝ) : ℝ :=
  p * h (a.1 + a.2 * p)

/-- The demand model of den Boer and Zwart, *Simultaneously Learning and Optimizing Using
Controlled Variance Pricing*, Management Science 60(3) (2014), §2, p. 773 (PDF 5), with its standing
assumptions as fields.

* Prices lie in `[pl, ph]` with `0 < pl < ph`.
* `E[D(p)] = h(a₀⁽⁰⁾ + a₁⁽⁰⁾ p)` and `Var[D(p)] = σ² v(E[D(p)])` (eq. (1)); the link `h` and the
  variance function `v` are known, `σ` and `a0 = (a₀⁽⁰⁾, a₁⁽⁰⁾)` are unknown.
* The paper has `h : ℝ₊ → ℝ₊`, `v : ℝ₊ → ℝ₊₊`, both `C²`, with `ḣ > 0` on `ℝ₊`. Here `h, v : ℝ → ℝ`
  are total functions constrained only on `[0, ∞)`; `ḣ` is `deriv h`, the two-sided derivative of
  the chosen extension (every `C²` function on `[0, ∞)` has a `C²` extension to `ℝ`).
* `σ > 0`, `a₀⁽⁰⁾ > 0`, `a₁⁽⁰⁾ < 0`. The page prints `a₀⁽⁰⁾ + a₁⁽⁰⁾ p_h ≥ 0`; this structure requires
  the strict inequality `a₀⁽⁰⁾ + a₁⁽⁰⁾ p_h > 0`. In the boundary case the CVP rule's case (c) fires
  along a subsequence and the proof of Theorem 1 (p. 782) does not cover it.
* Neighbourhood assumption (p. 773): there is an open `U ∋ a⁽⁰⁾` such that for every `a ∈ U`,
  `r(·, a)` has a unique maximizer `p(a)` over `[pl, ph]`, it lies in the open interval `(pl, ph)`,
  and `r''(p(a), a) < 0`. The page writes the arg max over `pl < p < ph`; it is read here as a unique
  maximizer over the closed interval that lies in the open one, because the pricing rule and the
  regret use the closed interval. -/
structure Model where
  /-- minimum acceptable price `p_l` -/
  pl : ℝ
  /-- maximum acceptable price `p_h` -/
  ph : ℝ
  /-- the known link function `h` of (1) -/
  h : ℝ → ℝ
  /-- the known variance function `v` of (1) -/
  v : ℝ → ℝ
  /-- the unknown dispersion parameter `σ` -/
  σ : ℝ
  /-- the unknown true parameter `a⁽⁰⁾ = (a₀⁽⁰⁾, a₁⁽⁰⁾)` -/
  a0 : ℝ × ℝ
  pl_pos : 0 < pl
  pl_lt_ph : pl < ph
  h_contDiffOn : ContDiffOn ℝ 2 h (Set.Ici 0)
  v_contDiffOn : ContDiffOn ℝ 2 v (Set.Ici 0)
  deriv_h_pos : ∀ x : ℝ, 0 ≤ x → 0 < deriv h x
  h_nonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ h x
  v_pos : ∀ x : ℝ, 0 ≤ x → 0 < v x
  σ_pos : 0 < σ
  a00_pos : 0 < a0.1
  a01_neg : a0.2 < 0
  /-- strict version of the printed `a₀⁽⁰⁾ + a₁⁽⁰⁾ p_h ≥ 0` (disclosed) -/
  a0_ph_pos : 0 < a0.1 + a0.2 * ph
  /-- the neighbourhood assumption of p. 773 -/
  nbhd : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ a0 ∈ U ∧ ∀ a ∈ U, ∃ q ∈ Set.Ioo pl ph,
    (∀ q' ∈ Set.Icc pl ph, q' ≠ q → revenue h a q' < revenue h a q) ∧
    deriv (deriv (revenue h a)) q < 0

/-- `q` maximizes `r(·, a)` over the price set `S`, and `q ∈ S`. -/
def IsRevMaxOn (M : Model) (a : ℝ × ℝ) (S : Set ℝ) (q : ℝ) : Prop :=
  q ∈ S ∧ ∀ q' ∈ S, revenue M.h a q' ≤ revenue M.h a q

open Classical in
/-- The optimal price `p(a) = arg max_{p ∈ [pl, ph]} r(p, a)` when this maximizer is unique (which
holds for every `a` in the neighbourhood `U` of the model). When the maximizer is not unique or does
not exist the value is the junk value `pl`; no statement of the mission evaluates it there. -/
noncomputable def optPriceOf (M : Model) (a : ℝ × ℝ) : ℝ :=
  if hq : ∃ q, ∀ q', IsRevMaxOn M a (Set.Icc M.pl M.ph) q' ↔ q' = q then Classical.choose hq
  else M.pl

/-- The optimal price `p_opt = p(a⁽⁰⁾)` (p. 773); by `Model.nbhd` it is the unique maximizer of
`r(·, a⁽⁰⁾)` over `[pl, ph]` and lies in `(pl, ph)`. -/
noncomputable def pOpt (M : Model) : ℝ :=
  optPriceOf M M.a0

end CVPricing.Regret


