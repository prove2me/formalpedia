-- Prove2me | Definitions.Def_ErrBoundCplx_Cplx_WorstCase
-- name    : ErrBoundCplx_Cplx_WorstCase
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:11.332984+00:00
-- url     : https://prove2.me/theorems/92279afb-eacb-4446-92cd-ec878cf1c134
-- title:
--   §4.2: the profile ψ = (φ|[0,r₀])⁻¹, assumption (A), ζ of (21), the worst-case proximal sequence (22), and (I + λψ′)⁻¹
-- statement:
--   This module fixes the one-dimensional objects of §4.2 of Bolte–Nguyen–Peypouquet–Suter.
--
--   1. **Profile setting.** Let $\bar r > 0$ and let $\varphi \in \mathcal K(0, \bar r)$, i.e. $\varphi$ is continuous on $[0, \bar r)$, $C^1$ on $(0, \bar r)$, $\varphi(0) = 0$, $\varphi$ is concave and $\varphi' > 0$. Let $0 < r_0 < \bar r$, put $\alpha_0 = \varphi(r_0)$, and let
--   $$\psi = \left(\varphi|_{[0, r_0]}\right)^{-1} : [0, \alpha_0] \to [0, r_0].$$
--   **Assumption (A)**: $\psi$ is differentiable on $[0, \alpha_0]$, its derivative $\psi'$ is Lipschitz continuous on $[0, \alpha_0]$ with constant $\ell > 0$, and $\psi'(0) = 0$.
--
--   2. **The constant (21).** For $a, b, \ell > 0$,
--   $$\zeta = \frac{\sqrt{1 + 2\ell a b^{-2}} - 1}{\ell}.$$
--
--   3. **The one-dimensional worst-case proximal sequence (22).** Starting from $\alpha_0$,
--   $$\alpha_{k+1} = \operatorname{argmin}\left\{\psi(u) + \frac{1}{2\zeta}(u - \alpha_k)^2 : u \in [0, \alpha_0]\right\}, \qquad k \ge 0.$$
--
--   4. **Resolvent points.** For $\lambda, \gamma \in \mathbb R$, $\delta = (I + \lambda\psi')^{-1}(\gamma)$ means $\delta \in [0, \alpha_0]$ and $\delta + \lambda\psi'(\delta) = \gamma$.
--
--   The function $\psi$ is the worst-case "profile" of $f$ near its minimizers, and the sequence $(\alpha_k)$ is the majorizing sequence of the paper's complexity theorem (Theorem 16).
--
--   **Formalization Note** $\psi$ is a function $\mathbb R \to \mathbb R$ given as data together with $\psi(\varphi(s)) = s$ for $s \in [0, r_0]$; since $\varphi$ is continuous and strictly increasing on $[0, r_0]$ this fixes $\psi$ on $[0, \alpha_0]$, and its values elsewhere never enter: $\psi'$ is the derivative of $\psi$ within $[0, \alpha_0]$ (one-sided at the endpoints) and the minimization in (22) runs over $[0, \alpha_0]$, which is the page's $u \ge 0$ with $\psi = +\infty$ beyond $\alpha_0$. The class $\mathcal K(0, \bar r)$ is the published `IsDesingularizer`. The argmin in (22) is unique (strictly convex objective), so (22) is encoded as the predicate "$\alpha_0$ is the start and each $\alpha_{k+1}$ minimizes the objective over $[0, \alpha_0]$".
-- source:
--   arXiv:1510.08234v3, §2.3, p. 6 (K(0, r₀)); §4.2, p. 17 (α₀ = φ(r₀), ψ = (φ|[0,r₀])⁻¹, assumption (A), (21), (22)); proof of Theorem 16, pp. 18–19 ((I + λψ′)⁻¹)

import Mathlib
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
open NonconvexSplitting.ADMMKL

namespace ErrBoundCplx.Cplx

/-- The derivative `ψ'` of the profile `ψ : [0, α₀] → [0, r₀]` (§4.2, p. 17), taken within
`[0, α₀]` (one-sided at the endpoints), so that values of `ψ` outside `[0, α₀]` never enter. -/
noncomputable def psiPrime (ψ : ℝ → ℝ) (α0 : ℝ) : ℝ → ℝ :=
  derivWithin ψ (Set.Icc 0 α0)

/-- Assumption (A), §4.2, p. 17: `ψ` is differentiable on `[0, α₀]`, its derivative `ψ'` is
Lipschitz continuous on `[0, α₀]` with constant `ℓ > 0`, and `ψ'(0) = 0`. -/
def AssumptionA (ψ : ℝ → ℝ) (α0 : ℝ) (ℓ : NNReal) : Prop :=
  DifferentiableOn ℝ ψ (Set.Icc 0 α0) ∧ 0 < ℓ ∧
    LipschitzOnWith ℓ (psiPrime ψ α0) (Set.Icc 0 α0) ∧ psiPrime ψ α0 0 = 0

/-- The setting of §4.2 (p. 17) for the one-dimensional objects:
* `φ ∈ K(0, r̄)` is a desingularizing function (§2.3, p. 6);
* `0 < r₀ < r̄`;
* `α₀ = φ(r₀)` and `ψ = (φ|[0,r₀])⁻¹ : [0, α₀] → [0, r₀]`, given as a function `ℝ → ℝ` with
  `ψ(φ(s)) = s` for every `s ∈ [0, r₀]` (this fixes `ψ` on `φ([0, r₀]) = [0, α₀]`; its values
  elsewhere are never used);
* assumption (A) holds on `[0, α₀]` with constant `ℓ`. -/
def ProfileSetting (φ ψ : ℝ → ℝ) (rbar r0 : ℝ) (ℓ : NNReal) : Prop :=
  IsDesingularizer rbar φ ∧ 0 < r0 ∧ r0 < rbar ∧
    (∀ s ∈ Set.Icc 0 r0, ψ (φ s) = s) ∧ AssumptionA ψ (φ r0) ℓ

/-- (21), p. 17: `ζ = (√(1 + 2ℓ a b⁻²) − 1)/ℓ`, with `a, b` the constants of (H1), (H2) and `ℓ`
the Lipschitz constant of (A). -/
noncomputable def zeta (ℓ a b : ℝ) : ℝ :=
  (Real.sqrt (1 + 2 * ℓ * a * b⁻¹ ^ 2) - 1) / ℓ

/-- (22), p. 17: the one-dimensional worst-case proximal sequence started at `α₀`:
`α_{k+1} = argmin { ψ(u) + (u − α_k)²/(2ζ) }` for `k ≥ 0`. Since `ψ` is defined on `[0, α₀]`
only, the minimization runs over `u ∈ [0, α₀]` (the page's `u ≥ 0` with `ψ = +∞` beyond `α₀`).
The minimizer is unique (strictly convex objective), so the sequence is pinned down by this
property. -/
def IsWorstCaseProxSeq (ψ : ℝ → ℝ) (α0 ζ : ℝ) (α : ℕ → ℝ) : Prop :=
  α 0 = α0 ∧
    ∀ k, α (k + 1) ∈ Set.Icc 0 α0 ∧
      ∀ u ∈ Set.Icc 0 α0,
        ψ (α (k + 1)) + (α (k + 1) - α k) ^ 2 / (2 * ζ) ≤ ψ u + (u - α k) ^ 2 / (2 * ζ)

/-- `δ = (I + λψ')⁻¹(γ)` (pp. 18–19): `δ ∈ [0, α₀]` and `δ + λ ψ'(δ) = γ`, with `ψ'` the derivative
of `ψ` within `[0, α₀]`. -/
def IsResolventPoint (ψ : ℝ → ℝ) (α0 lam γ δ : ℝ) : Prop :=
  δ ∈ Set.Icc 0 α0 ∧ δ + lam * psiPrime ψ α0 δ = γ

end ErrBoundCplx.Cplx


