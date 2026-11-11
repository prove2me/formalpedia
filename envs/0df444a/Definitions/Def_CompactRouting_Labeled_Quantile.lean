-- Prove2me | Definitions.Def_CompactRouting_Labeled_Quantile
-- name    : CompactRouting_Labeled_Quantile
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:05:14.517288+00:00
-- url     : https://prove2.me/theorems/e6b1a902-2fdd-4f89-bf4f-b6fec70e97bf
-- title:
--   Distributions on a finite subset of $[1,\infty)$, the quantile function, and $C$, $r$, $\alpha_i$, $\varphi$, $\Psi$ of §B.1
-- statement:
--   Let $\nu$ be a probability distribution on a finite subset of $[1,\infty)$, with mean $m=\mathbb E_{\theta\sim\nu}[\theta]$ and tail $\bar F(\zeta)=\Pr_{\theta\sim\nu}[\theta\ge\zeta]$. Its **quantile function** is
--   $$f(\alpha)=\min\{\zeta\in\operatorname{supp}(\nu) : \Pr_{\theta\sim\nu}[\theta\le\zeta]>\alpha\}\qquad(0\le\alpha<1).$$
--   Given heights $x_0,\dots,x_\tau$, $y_0,\dots,y_\tau$ with $H=y_\tau$ and thresholds $\delta_i=y_{i+1}-x_i$, let $C=\min_{i\in[\tau]}(2x_i+2H\bar F(\delta_i))$, $r=C/(2H)$, $\alpha_i=1-r+x_i/H$,
--   $$\varphi(w)=1-r+r\,f\big(1-r+w/H\big)\ (0\le w<rH),\qquad \Psi(z)=\int_0^{\min\{z,rH\}}\frac{dw}{\varphi(w)}\ (z\ge0).$$
--
--   **Formalization Note.** $\nu$ is a finite set $S\subseteq[1,\infty)$ with nonnegative weights summing to $1$; $\operatorname{supp}(\nu)$ is the set of points of positive weight. The quantile and $C$ are real infima of finite sets, nonempty for $0\le\alpha<1$ and $\tau\ge1$, hence the page's minima. $\Psi$ is the lower Lebesgue integral of the nonnegative function $1/\varphi$ over $(0,\min\{z,rH\})$, valued in $[0,\infty]$, so no integrability condition is hidden.
-- source:
--   Lifshitz, Chechik, Kadria, Roditty, Optimal (Randomized) Compact Routing Schemes, arXiv:2611.04744 (held version, sha256 d7e0fc67…), pp. 35–36 (Appendix B, δ_i, H; §B.1 Quantiles, C; proof of Lemma 22, r, α_i, φ, Ψ)

import Mathlib

/-!
# Distributions on a finite subset of `[1, ∞)`, quantiles, and the functions `C`, `r`, `α_i`,
`φ`, `Ψ` of §B.1

Lifshitz, Chechik, Kadria, Roditty, *Optimal (Randomized) Compact Routing Schemes*,
arXiv:2611.04744 (held version, sha256 d7e0fc67…), Appendix B, pp. 35–36: `δ_i = y_{i+1} − x_i`,
`H = y_τ`; §B.1 "Quantiles" p. 36: `m = E_{θ∼ν}[θ]`, `F̄(ζ) = Pr_{θ∼ν}[θ ≥ ζ]`,
`f(α) = min{ζ ∈ supp(ν) | Pr_{θ∼ν}[θ ≤ ζ] > α}` (`0 ≤ α < 1`),
`C = min_{i∈[τ]}(2x_i + 2H F̄(δ_i))`; proof of Lemma 22, p. 36: `r = C/(2H)`,
`α_i = 1 − r + x_i/H`, `φ(w) = 1 − r + r f(1 − r + w/H)` (`0 ≤ w < rH`),
`Ψ(z) = ∫_0^{min{z, rH}} dw/φ(w)` (`z ≥ 0`).

Conventions.
* A distribution `ν` on a finite subset of `[1, ∞)` is a finite set `S ⊆ [1, ∞)` with
  nonnegative weights summing to `1`; `supp(ν)` is the set of points of positive weight.
* The heights `x, y : ℕ → ℝ` and `τ` are parameters; `H = y τ`.
* `quantile ν α` is the real infimum of the finite set
  `{ζ ∈ supp(ν) | Pr[θ ≤ ζ] > α}`; for `0 ≤ α < 1` this set is nonempty (it contains the
  largest point of the support), so the infimum is the page's minimum.
* `Cval` is the real infimum of the finite set `{2x_i + 2H F̄(δ_i) | i ∈ [τ]}`, the minimum
  for `τ ≥ 1`.
* `Ψ` is a lower Lebesgue integral of the nonnegative function `1/φ` over `(0, min{z, rH})`,
  with values in `[0, ∞]`; it needs no integrability side condition.
-/

namespace CompactRouting.Labeled

/-- A probability distribution `ν` on a finite subset of `[1, ∞)`. -/
structure FinDistGeOne where
  /-- a finite set containing the support -/
  S : Finset ℝ
  /-- the weight `ν(θ)` of every point -/
  w : ℝ → ℝ
  /-- the points lie in `[1, ∞)` -/
  ge_one : ∀ θ ∈ S, 1 ≤ θ
  /-- weights are nonnegative -/
  nonneg : ∀ θ ∈ S, 0 ≤ w θ
  /-- weights sum to one -/
  total : ∑ θ ∈ S, w θ = 1

namespace FinDistGeOne

/-- The mean `m = E_{θ∼ν}[θ]`. -/
noncomputable def mean (ν : FinDistGeOne) : ℝ := ∑ θ ∈ ν.S, ν.w θ * θ

/-- `F̄(ζ) = Pr_{θ∼ν}[θ ≥ ζ]`. -/
noncomputable def tail (ν : FinDistGeOne) (ζ : ℝ) : ℝ := by
  classical
  exact ∑ θ ∈ ν.S.filter (fun θ => ζ ≤ θ), ν.w θ

/-- `Pr_{θ∼ν}[θ ≤ ζ]`. -/
noncomputable def cdf (ν : FinDistGeOne) (ζ : ℝ) : ℝ := by
  classical
  exact ∑ θ ∈ ν.S.filter (fun θ => θ ≤ ζ), ν.w θ

/-- `supp(ν)`, the points of positive weight. -/
noncomputable def supp (ν : FinDistGeOne) : Finset ℝ := by
  classical
  exact ν.S.filter fun θ => 0 < ν.w θ

/-- The quantile function `f(α) = min{ζ ∈ supp(ν) | Pr_{θ∼ν}[θ ≤ ζ] > α}` (`0 ≤ α < 1`). -/
noncomputable def quantile (ν : FinDistGeOne) (α : ℝ) : ℝ :=
  sInf {ζ : ℝ | ζ ∈ ν.supp ∧ α < ν.cdf ζ}

end FinDistGeOne

open FinDistGeOne

/-- §B.1, p. 36: `C = min_{i∈[τ]} (2x_i + 2H F̄(δ_i))` with `H = y_τ`, `δ_i = y_{i+1} − x_i`. -/
noncomputable def Cval (x y : ℕ → ℝ) (τ : ℕ) (ν : FinDistGeOne) : ℝ := by
  classical
  exact sInf (((Finset.range τ).image fun i => 2 * x i + 2 * y τ * ν.tail (y (i + 1) - x i) :
    Finset ℝ) : Set ℝ)

/-- Proof of Lemma 22, p. 36: `r = C/(2H)`. -/
noncomputable def rr (x y : ℕ → ℝ) (τ : ℕ) (ν : FinDistGeOne) : ℝ :=
  Cval x y τ ν / (2 * y τ)

/-- Proof of Lemma 22, p. 36: `α_i = 1 − r + x_i/H`. -/
noncomputable def alphaLvl (x y : ℕ → ℝ) (τ : ℕ) (ν : FinDistGeOne) (i : ℕ) : ℝ :=
  1 - rr x y τ ν + x i / y τ

/-- Proof of Lemma 22, p. 36: `φ(w) = 1 − r + r f(1 − r + w/H)` (`0 ≤ w < rH`). -/
noncomputable def phi (x y : ℕ → ℝ) (τ : ℕ) (ν : FinDistGeOne) (w : ℝ) : ℝ :=
  1 - rr x y τ ν + rr x y τ ν * ν.quantile (1 - rr x y τ ν + w / y τ)

/-- Proof of Lemma 22, p. 36: `Ψ(z) = ∫_0^{min{z, rH}} dw/φ(w)` (`z ≥ 0`). -/
noncomputable def Psi (x y : ℕ → ℝ) (τ : ℕ) (ν : FinDistGeOne) (z : ℝ) : ENNReal :=
  ∫⁻ w in Set.Ioo 0 (min z (rr x y τ ν * y τ)), ENNReal.ofReal (1 / phi x y τ ν w)

end CompactRouting.Labeled


