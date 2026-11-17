-- Prove2me | Definitions.Def_FixedPriceTrade_Supplement_deltaSharp
-- name    : FixedPriceTrade_Supplement_deltaSharp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:14:57.831447+00:00
-- url     : https://prove2.me/theorems/435cdc4f-88cd-49e7-a1d1-832c241d2041
-- title:
--   The sharp affine coefficient $\delta(\beta)$, the conditional guarantee $\rho(\kappa)$, $\beta(C)$, $\kappa(C)$ and bounded pairs
-- statement:
--   For the single-unit model of the mission (independent nonnegative values $V_s,V_b$ with $0<\mathbb E\max\{V_s,V_b\}<\infty$, seller mean $M=\mathbb EV_s$, first-best gains $G=\mathbb E(V_b-V_s)_+$ and best fixed-price gains $\Gamma_{\max}$), define for $0<\beta<1$ the **sharp affine coefficient**
--   $$
--   \delta(\beta)=\inf\{\delta\in\mathbb R:\ \Gamma_{\max}\ge\beta G-\delta M\ \text{for every admissible pair}\},
--   $$
--   and for $\kappa>0$ the **conditional GFT guarantee**
--   $$
--   \rho(\kappa)=\inf\Big\{\frac{\Gamma_{\max}}{G}:\ \text{admissible pairs with } M>0,\ G/M=\kappa\Big\}.
--   $$
--   With the scalar curve $S(C)=C(2+\mathcal I(C))$ and $\tau(C)$ of the mission, put, for $\tfrac14<C<\tfrac12$,
--   $$
--   \beta(C)=\frac1{S(C)},\qquad u=1-2C,\qquad \kappa(C)=\frac{\tau(C)\,(S(C)+u)}{u}.
--   $$
--   A pair is **bounded** if both laws put no mass above some real $R$.
--
--   $\delta$ describes the whole frontier of affine guarantees $\Gamma_{\max}\ge\beta G-\delta M$, and $\rho$ the exact guarantee on the gains from trade once the ratio $G/M$ is known; both are computed in closed form by Theorem B.
--
--   **Formalization Note** Pairs are the published `IsAdmissiblePair` laws, and $M$, $G$, $\Gamma_{\max}$, $S$, $\tau$ are the published definitions. $G/M=\kappa$ with $M>0$ is written $G=\kappa M$, $M>0$. The infima are `sInf` on $\mathbb R$; Theorem B states the bounds and their sharpness, so no statement depends on a default value.
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 2683234615efe3b875b8a3f0cde6b0637c6b82cf550767823ebc24d5cd1bca0e), §4, (9)–(10), p.11 (PDF p.11); (11)–(12) and "bounded hard pair", Theorem B, p.12 (PDF p.12)

import Mathlib
import Definitions.Def_FixedPriceTrade_welfareRatio
import Definitions.Def_FixedPriceTrade_SCurve

set_option autoImplicit false

namespace FixedPriceTrade.Supplement

open MeasureTheory Set

/-- **The sharp affine coefficient** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare Guarantee
of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), §4, (9), p.11:
`δ(β) = inf {δ ∈ ℝ : Γ_max ≥ β G − δ M for every pair in Section 3}`, `0 < β < 1`.

**Formalization Note.** "The pairs in Section 3" are exactly the admissible pairs of the published
`FixedPriceTrade.IsAdmissiblePair` (independent product law, a.s. nonnegative values,
`0 < E max < ∞`); `M`, `G`, `Γ_max` are the published `sellerMean`, `firstBestGFT`, `gammaMax`.
The infimum is Lean's `sInf` on `ℝ`; Theorem B states the bound and its sharpness separately, so
no statement relies on the value of `sInf` on an empty or unbounded set. -/
noncomputable def deltaSharp (β : ℝ) : ℝ :=
  sInf {δ : ℝ | ∀ μs μb : Measure ℝ, IsAdmissiblePair μs μb →
    β * firstBestGFT μs μb - δ * sellerMean μs ≤ gammaMax μs μb}

/-- **The conditional GFT guarantee** ((10), p.11): for `κ > 0`,
`ρ(κ) = inf {Γ_max / G : (F_s, F_b) as in Section 3, M > 0, G/M = κ}`.

**Formalization Note.** `G/M = κ` with `M > 0` is written `G = κ M` with `0 < M`, the same
condition; then `G = κ M > 0` and the ratio `Γ_max / G` is a genuine quotient. -/
noncomputable def rhoCond (κ : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ μs μb : Measure ℝ, IsAdmissiblePair μs μb ∧ 0 < sellerMean μs ∧
    firstBestGFT μs μb = κ * sellerMean μs ∧ r = gammaMax μs μb / firstBestGFT μs μb}

/-- `β(C) = 1/S(C)` ((11), p.12), with `S` the published `SCurve`; used for `1/4 < C < 1/2`. -/
noncomputable def betaC (C : ℝ) : ℝ := 1 / SCurve C

/-- `u = 1 − 2C` (Theorem B, p.12). -/
def uC (C : ℝ) : ℝ := 1 - 2 * C

/-- `κ(C) = τ(C)(S(C) + u)/u` ((12), p.12), with `τ = tauCurve`, `S = SCurve`; used for
`1/4 < C < 1/2`, where `u > 0`. -/
noncomputable def kappaC (C : ℝ) : ℝ := tauCurve C * (SCurve C + uC C) / uC C

/-- A **bounded** pair (Theorem B, p.12, "bounded hard pair"): both laws put no mass above some
real `R`. Together with admissibility (a.s. nonnegative values) both laws live in `[0, R]`. -/
def IsBoundedPair (μs μb : Measure ℝ) : Prop :=
  ∃ R : ℝ, μs (Ioi R) = 0 ∧ μb (Ioi R) = 0

end FixedPriceTrade.Supplement


