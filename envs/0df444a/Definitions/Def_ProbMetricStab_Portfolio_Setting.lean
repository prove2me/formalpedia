-- Prove2me | Definitions.Def_ProbMetricStab_Portfolio_Setting
-- name    : ProbMetricStab_Portfolio_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:16.864853+00:00
-- url     : https://prove2.me/theorems/70ef99dc-b356-4555-a3e0-14a847aeffe4
-- title:
--   §5, pp. 23–25 (with p. 3, p. 8) — Σ^s, 𝒫(Σ^s), X, f₀, r_{α,Γ}, v, S, ζ₁, nonsingularity, ψ, ψ⁻¹, Ψ
-- statement:
--   This file fixes the minimal-risk stable portfolio problem of Section 5 and the objects its stability theory uses.
--
--   Fix $s\in\mathbb N$ and work in $\mathbb R^s$ with the Euclidean scalar product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$.
--
--   1. **Unit sphere.** $\Sigma^s=\{\xi\in\mathbb R^s:\langle\xi,\xi\rangle=1\}$.
--   2. **Spectral measures.** $\mathcal P(\Sigma^s)$ is the set of Borel probability measures $\Gamma$ on $\Sigma^s$ (normalized spectral measures, $\Gamma(\Sigma^s)=1$).
--   3. **Portfolios.** $X=\{x\in\mathbb R^s_+:\sum_{i=1}^s x_i=1\}$, the standard simplex.
--   4. **Integrand and risk.** For a stability index $\alpha$, $f_0(\xi,x)=|\langle x,\xi\rangle|^\alpha$ and
--   $$r_{\alpha,\Gamma}(x)=\int_{\Sigma^s}|\langle x,\xi\rangle|^\alpha\,\Gamma(d\xi).$$
--   5. **Problem (22).** $\min\{r_{\alpha,\Gamma}(x):x\in X\}$, with optimal value $v(\alpha,\Gamma)=\inf_{x\in X}r_{\alpha,\Gamma}(x)$ and solution set $S(\alpha,\Gamma)=\{x\in X: r_{\alpha,\Gamma}(x)\le r_{\alpha,\Gamma}(y)\ \forall y\in X\}$.
--   6. **The metric $\zeta_1$.** $\mathcal F_1(\Sigma^s)$ is the class of functions $f:\Sigma^s\to\mathbb R$ with $|f(\xi)-f(\tilde\xi)|\le\|\xi-\tilde\xi\|$ for all $\xi,\tilde\xi\in\Sigma^s$, and
--   $$\zeta_1(\Gamma,\tilde\Gamma)=\sup_{f\in\mathcal F_1(\Sigma^s)}\Big|\int_{\Sigma^s}f(\xi)\,(\Gamma-\tilde\Gamma)(d\xi)\Big|.$$
--   7. **Nonsingularity.** $\Gamma$ is nonsingular if $\int_{\Sigma^s}|\langle x,\xi\rangle|^2\,\Gamma(d\xi)=0$ implies $x=0$.
--   8. **Growth function and modulus.** With $d(x,A)$ the distance from $x$ to $A$,
--   $$\psi(\tau)=\min\{r_{\alpha,\Gamma}(x)-v(\alpha,\Gamma): d(x,S(\alpha,\Gamma))\ge\tau,\ x\in X\}\quad(\tau\in\mathbb R_+),$$
--   $\psi^{-1}(t)=\sup\{\tau\in\mathbb R_+:\psi(\tau)\le t\}$ and $\Psi(\eta)=\eta+\psi^{-1}(2\eta)$ for $\eta\in\mathbb R_+$.
--
--   Problem (22) is the classical choice of an efficient portfolio when the asset returns follow an $\alpha$-stable law with spectral measure $\Gamma$; $r_{\alpha,\Gamma}$ is the scaled dispersion of the portfolio. The stability theorems of the mission compare $S(\alpha,\Gamma)$ with the solution set of a perturbed pair $(\tilde\alpha,\tilde\Gamma)$.
--
--   **Formalization Note** $\mathbb R^s$ is `EuclideanSpace ℝ (Fin s)` (coordinates indexed $0,\dots,s-1$); $\Sigma^s$ is `Metric.sphere 0 1`, which equals $\{\langle\xi,\xi\rangle=1\}$. A spectral measure is a probability measure on $\mathbb R^s$ with $\Gamma((\Sigma^s)^c)=0$, and every integral is a set integral over $\Sigma^s$. The integrand of $r_{\alpha,\Gamma}$ is continuous and bounded on $\Sigma^s$, so no integrability hypothesis is needed. Test functions of $\mathcal F_1$ are functions on $\mathbb R^s$ that are $1$-Lipschitz on $\Sigma^s$; only their values on $\Sigma^s$ enter, and on the compact set $\Sigma^s$ they are continuous, hence integrable. $\zeta_1$ is a supremum in $[0,\infty]$; for probability measures it is at most $2$ (subtract $f(\xi_0)$ and use $\operatorname{diam}\Sigma^s=2$). $v$ is a real infimum, well defined because $X\neq\emptyset$ for $s\ge1$ and $r_{\alpha,\Gamma}\ge0$; for $s=0$ there is no probability measure on $\Sigma^0=\emptyset$. The paper's "min" in $\psi$ is read as an infimum in the extended reals ($+\infty$ when no $x\in X$ has $d(x,S)\ge\tau$), the distance is the extended distance (`Metric.infEDist`, $+\infty$ to the empty set), and $\psi^{-1}$, $\Psi$ take values in $[0,\infty]$.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), pp. 23–25, Section 5, (22); p. 3, definition of ζ_p and 𝓕_p(Ξ) (p = 1); p. 8, Theorem 2.3 (definition of ψ^{-1}); p. 25, Theorem 5.2 (definitions of Ψ, ψ)

import Mathlib

namespace ProbMetricStab.Portfolio

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

/-- The space `ℝ^s` with its Euclidean scalar product `⟨·, ·⟩` (p. 23). Coordinates are indexed by
`Fin s`, i.e. `0, …, s - 1` instead of the paper's `1, …, s`. -/
abbrev Rs (s : ℕ) : Type := EuclideanSpace ℝ (Fin s)

/-- The unit sphere `Σ^s = {ξ ∈ ℝ^s : ⟨ξ, ξ⟩ = 1}` (p. 23). -/
def unitSphere (s : ℕ) : Set (Rs s) := Metric.sphere 0 1

/-- `Γ ∈ 𝒫(Σ^s)`: a normalized spectral measure, i.e. a Borel probability measure on `Σ^s`, encoded as a
Borel probability measure on `ℝ^s` that gives no mass to the complement of `Σ^s` (p. 24). -/
def IsSpectral {s : ℕ} (Γ : Measure (Rs s)) : Prop :=
  IsProbabilityMeasure Γ ∧ Γ (unitSphere s)ᶜ = 0

/-- The feasible set `X = {x ∈ ℝ^s_+ : ∑_{i=1}^s x_i = 1}` of problem (22) (p. 24). -/
def simplex (s : ℕ) : Set (Rs s) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

/-- The integrand `f₀(ξ, x) = |⟨x, ξ⟩|^α` (p. 24). -/
noncomputable def f0 {s : ℕ} (α : ℝ) (ξ x : Rs s) : ℝ := |(inner ℝ x ξ : ℝ)| ^ α

/-- The risk `r_{α,Γ}(x) = ∫_{Σ^s} |⟨x, ξ⟩|^α Γ(dξ)` (p. 24), a Bochner integral over `Σ^s`. -/
noncomputable def risk {s : ℕ} (α : ℝ) (Γ : Measure (Rs s)) (x : Rs s) : ℝ :=
  ∫ ξ in unitSphere s, f0 α ξ x ∂Γ

/-- The optimal value `v(α, Γ)` of problem (22): `inf {r_{α,Γ}(x) : x ∈ X}` (p. 24). -/
noncomputable def optVal {s : ℕ} (α : ℝ) (Γ : Measure (Rs s)) : ℝ :=
  sInf (risk α Γ '' simplex s)

/-- The solution set `S(α, Γ)` of problem (22): the minimizers of `r_{α,Γ}` over `X` (p. 24). -/
def solSet {s : ℕ} (α : ℝ) (Γ : Measure (Rs s)) : Set (Rs s) :=
  {x | x ∈ simplex s ∧ ∀ y ∈ simplex s, risk α Γ x ≤ risk α Γ y}

/-- The test class `𝓕₁(Σ^s)` (p. 3 with `p = 1`): functions with
`|f(ξ) - f(ξ̃)| ≤ ‖ξ - ξ̃‖` for all `ξ, ξ̃ ∈ Σ^s`. They are given as functions on `ℝ^s`; only their values
on `Σ^s` enter `zeta1`. -/
def lipTest (s : ℕ) : Set (Rs s → ℝ) := {f | LipschitzOnWith 1 f (unitSphere s)}

/-- The probability metric `ζ₁(Γ, Γ̃) = sup_{f ∈ 𝓕₁(Σ^s)} |∫_{Σ^s} f(ξ) (Γ - Γ̃)(dξ)|` (p. 3), as an
`ℝ≥0∞`-valued supremum. -/
noncomputable def zeta1 {s : ℕ} (Γ Γ' : Measure (Rs s)) : ℝ≥0∞ :=
  ⨆ f ∈ lipTest s,
    ENNReal.ofReal |(∫ ξ in unitSphere s, f ξ ∂Γ) - ∫ ξ in unitSphere s, f ξ ∂Γ'|

/-- `Γ` is nonsingular if `∫_{Σ^s} |⟨x, ξ⟩|² Γ(dξ) = 0` implies `x = 0` (p. 24). -/
def Nonsingular {s : ℕ} (Γ : Measure (Rs s)) : Prop :=
  ∀ x : Rs s, (∫ ξ in unitSphere s, |(inner ℝ x ξ : ℝ)| ^ 2 ∂Γ) = 0 → x = 0

/-- The growth function `ψ(τ) = min {r_{α,Γ}(x) - v(α, Γ) : d(x, S(α, Γ)) ≥ τ, x ∈ X}` (p. 25), read as an
extended-real infimum (`⊤` when no feasible point is at distance `≥ τ` from `S(α, Γ)`). The distance is
`Metric.infEDist` (`⊤` to the empty set). -/
noncomputable def psi {s : ℕ} (α : ℝ) (Γ : Measure (Rs s)) (τ : ℝ) : EReal :=
  ⨅ x ∈ {x | x ∈ simplex s ∧ ENNReal.ofReal τ ≤ Metric.infEDist x (solSet α Γ)},
    ((risk α Γ x - optVal α Γ : ℝ) : EReal)

/-- `ψ⁻¹(t) = sup {τ ∈ ℝ₊ : ψ(τ) ≤ t}` (p. 8), an `ℝ≥0∞`-valued supremum. -/
noncomputable def psiInv {s : ℕ} (α : ℝ) (Γ : Measure (Rs s)) (t : ℝ) : ℝ≥0∞ :=
  ⨆ τ ∈ {τ : ℝ | 0 ≤ τ ∧ psi α Γ τ ≤ (t : EReal)}, ENNReal.ofReal τ

/-- `Ψ(η) = η + ψ⁻¹(2η)` (p. 25), for `η ∈ ℝ₊`. -/
noncomputable def Psi {s : ℕ} (α : ℝ) (Γ : Measure (Rs s)) (η : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal η + psiInv α Γ (2 * η)

end ProbMetricStab.Portfolio


