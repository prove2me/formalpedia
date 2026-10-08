-- Prove2me | Definitions.Def_LariviereIGFR_Char_Setting
-- name    : LariviereIGFR_Char_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:37:31.414328+00:00
-- url     : https://prove2.me/theorems/de539a27-282f-48fa-8e7b-ad76a64e2a06
-- title:
--   §1–§2, pp. 602–603 — survival Φ̄, failure rate h, g(ξ) = ξh(ξ), regular density, IFR, IGFR, ⪯hr, TP₂
-- statement:
--   This file fixes the objects of §1 and §2 of Lariviere's note. A nonnegative random variable $X$ is represented by its law $\mu$, a probability measure on $\mathbb R$, and its distribution function is $\Phi(\xi) = \mu((-\infty,\xi])$. For a law $\nu$ on $\mathbb R$ with density $\psi$:
--
--   1. The **survival function** is $\bar\Phi(\xi) = 1 - \Phi(\xi)$.
--   2. The **failure rate** is $h(\xi) = \psi(\xi)/\bar\Phi(\xi)$.
--   3. The **generalized failure rate** (Lariviere and Porteus 2001) is
--   $$g(\xi) = \xi\, h(\xi).$$
--   4. $\psi$ is a **regular density** of $\nu$ if $\psi \ge 0$, $\nu(A) = \int_A \psi(x)\,dx$ for every Borel set $A$, $\psi(\xi)$ is the right derivative of $\Phi$ at every $\xi$ with $0 < \Phi(\xi) < 1$ (the open support $(\alpha,\beta)$), and $\psi(\xi) = 0$ wherever $\Phi(\xi) = 0$.
--   5. $\nu$ is **IFR** (increasing failure rate) if $h$ is weakly increasing on $\{\xi : \Phi(\xi) < 1\}$, and **IGFR** (increasing generalized failure rate) if $g$ is weakly increasing on $\{\xi : \Phi(\xi) < 1\}$.
--   6. Two laws with failure rates $h_1, h_2$ are ordered in the **hazard rate order**, $X_1 \preceq_{hr} X_2$, if $h_1(\xi) \ge h_2(\xi)$ for all $\xi \ge 0$ with $\Phi_1(\xi) < 1$.
--   7. A function $f(x, y)$ is **totally positive of order 2** (TP₂) on $S \times T$ if for $x_1 < x_2$ in $S$ and $y_1 < y_2$ in $T$,
--   $$f(x_1, y_1) f(x_2, y_2) - f(x_1, y_2) f(x_2, y_1) \ge 0.$$
--
--   These are the objects of Theorem 1 and its corollaries: every statement of the mission is phrased through them.
--
--   **Formalization Note** A density is fixed by the law only up to a Lebesgue-null set, while IFR and IGFR read it pointwise; changing $\psi$ at one point can destroy IFR without changing the law. The regular-density predicate pins the version the paper uses: the right derivative of $\Phi$ on the support and $0$ to its left. A right derivative rather than a two-sided one is used so that laws whose density jumps inside the support (for instance a piecewise-constant failure rate) are not excluded. Lean's division returns $0$ where $\bar\Phi = 0$, so the rates are read only on $\{\Phi < 1\}$, where $\bar\Phi > 0$; there the paper's definitions apply verbatim. In the hazard-rate order the paper's $h_1$ is $+\infty$ where $\bar\Phi_1 = 0$ and the inequality holds trivially, so the order quantifies over $\xi \ge 0$ with $\Phi_1(\xi) < 1$. Monotonicity is weak ("weakly increasing", §1). The support $(\alpha,\beta)$ is not a separate parameter: it is $\{\xi : 0 < \Phi(\xi) < 1\}$, an open interval because $\Phi$ is continuous and nondecreasing.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 602, §1 ("Let X be a nonnegative random variable with distribution Φ, and let Φ̄(ξ) = 1 − Φ(ξ). We assume that Φ has density φ. Let (α, β) for 0 ⩽ α < β ⩽ ∞ be the support of X. h(ξ) = φ(ξ)/Φ̄(ξ) is the failure rate of X. ... g(ξ) = ξh(ξ). X has an increasing generalized failure rate (IGFR) ... if g(ξ) is weakly increasing for all ξ such that Φ(ξ) < 1.") and p. 602, §2 (hazard rate order, log-concavity, TP₂)

import Mathlib

namespace LariviereIGFR.Char

open MeasureTheory ProbabilityTheory

/-- The survival function `Φ̄(ξ) = 1 - Φ(ξ)` of a law `ν` on `ℝ`, where `Φ = cdf ν`. -/
noncomputable def survival (ν : Measure ℝ) (ξ : ℝ) : ℝ := 1 - cdf ν ξ

/-- The failure rate `h(ξ) = ψ(ξ) / Φ̄(ξ)` of the law `ν` with density `ψ`.
(Lean's division gives `0` where `Φ̄(ξ) = 0`; every statement reads `h` only where `cdf ν ξ < 1`.) -/
noncomputable def failureRate (ν : Measure ℝ) (ψ : ℝ → ℝ) (ξ : ℝ) : ℝ := ψ ξ / survival ν ξ

/-- The generalized failure rate `g(ξ) = ξ h(ξ)`. -/
noncomputable def genFailureRate (ν : Measure ℝ) (ψ : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ξ * failureRate ν ψ ξ

/-- `ψ` is a regular version of the density of `ν`: it is nonnegative, `ν` has density `ψ`
with respect to Lebesgue measure, `ψ` is the right derivative of the cdf at every point of the
open support `{0 < cdf ν < 1}`, and `ψ` vanishes wherever the cdf is `0` (left of the support).
(A right derivative, not a two-sided one, so that laws whose density jumps inside the support,
such as a piecewise-constant failure rate, are covered.) -/
def IsRegDensity (ν : Measure ℝ) (ψ : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ ψ x) ∧
  ν = volume.withDensity (fun x => ENNReal.ofReal (ψ x)) ∧
  (∀ ξ, 0 < cdf ν ξ → cdf ν ξ < 1 → HasDerivWithinAt (fun x => cdf ν x) (ψ ξ) (Set.Ici ξ) ξ) ∧
  (∀ ξ, cdf ν ξ = 0 → ψ ξ = 0)

/-- IFR: the failure rate is weakly increasing on `{ξ | Φ(ξ) < 1}`. -/
def IsIFR (ν : Measure ℝ) (ψ : ℝ → ℝ) : Prop :=
  MonotoneOn (failureRate ν ψ) {ξ | cdf ν ξ < 1}

/-- IGFR: the generalized failure rate is weakly increasing on `{ξ | Φ(ξ) < 1}`. -/
def IsIGFR (ν : Measure ℝ) (ψ : ℝ → ℝ) : Prop :=
  MonotoneOn (genFailureRate ν ψ) {ξ | cdf ν ξ < 1}

/-- Hazard rate order `X₁ ⪯hr X₂` (failure-rate form): `h₁(ξ) ≥ h₂(ξ)` for every `ξ ≥ 0`
at which `h₁(ξ)` is finite, i.e. `Φ₁(ξ) < 1` (where `Φ̄₁(ξ) = 0` the paper's `h₁` is `+∞`). -/
def HazardRateLE (ν₁ : Measure ℝ) (ψ₁ : ℝ → ℝ) (ν₂ : Measure ℝ) (ψ₂ : ℝ → ℝ) : Prop :=
  ∀ ξ : ℝ, 0 ≤ ξ → cdf ν₁ ξ < 1 → failureRate ν₂ ψ₂ ξ ≤ failureRate ν₁ ψ₁ ξ

/-- `f` is totally positive of order 2 on `s × t`: for `x₁ < x₂` in `s` and `y₁ < y₂` in `t`,
`f(x₁, y₁) f(x₂, y₂) - f(x₁, y₂) f(x₂, y₁) ≥ 0`. -/
def IsTP2On (f : ℝ → ℝ → ℝ) (s t : Set ℝ) : Prop :=
  ∀ x₁ ∈ s, ∀ x₂ ∈ s, ∀ y₁ ∈ t, ∀ y₂ ∈ t, x₁ < x₂ → y₁ < y₂ →
    0 ≤ f x₁ y₁ * f x₂ y₂ - f x₁ y₂ * f x₂ y₁

end LariviereIGFR.Char


