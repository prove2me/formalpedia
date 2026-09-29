-- Prove2me | Definitions.Def_ConnesRZ_weil_defs
-- name    : ConnesRZ_weil_defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T12:52:07.965273+00:00
-- url     : https://prove2.me/theorems/1ba757cc-8991-4e58-abf7-f8eee1db65da
-- title:
--   Weil distribution and zero sum of $\zeta$ (Connes, section 3, $k=\mathbb{Q}$)
-- statement:
--   Working objects for the case $k=\mathbb{Q}$ with trivial Grössencharakter of section 3 of Connes' paper. The module of the idele class group of $\mathbb{Q}$ is $\mathbb{R}^{*}_{+}$, which is written additively via $u=e^{t}$, $d^{*}u=dt$; so every "function on the idele class group" below is a function of a real variable $t$.
--
--   **Test functions.** `IsTest g` says that $g:\mathbb{R}\to\mathbb{C}$ is $C^{\infty}$ and compactly supported.
--
--   **Transform.** `mellinHat` is Connes' $\widehat h(z)=\int_{C_k}h(u)|u|^{z}\,d^{*}u$ of eq. (12), written in the coordinate $u=e^{t}$ and shifted by $\tfrac12$ so that $z$ is the variable of the zeta function:
--   $$\widehat g(z)=\int_{\mathbb{R}}g(t)\,e^{(z-1/2)t}\,dt .$$
--   On the critical line it is the Fourier transform: $\widehat g(\tfrac12+ir)=\int_{\mathbb{R}}g(t)e^{irt}\,dt$.
--
--   **Involution and convolution.** `starInv` is $g^{*}(t)=\overline{g(-t)}$, i.e. $h^{*}(u)=\overline{h(u^{-1})}$; `conv` is $(g_1\star g_2)(t)=\int_{\mathbb{R}}g_1(s)g_2(t-s)\,ds$.
--
--   **Zeros.** `IsCriticalZero s` says $\zeta(s)=0$ and $0<\operatorname{Re}s<1$; `zeroMult s` is the order of vanishing of $\zeta$ at $s$ as a natural number.
--
--   **The two sides of the explicit formula.** The Weil distribution is
--   $$W(g)=\widehat g(0)+\widehat g(1)-\sum_{n\ge 2}\frac{\Lambda(n)}{\sqrt n}\bigl(g(\log n)+g(-\log n)\bigr)+\frac{1}{2\pi}\int_{\mathbb{R}}\widehat g\!\left(\tfrac12+ir\right)\left(\operatorname{Re}\psi\!\left(\tfrac14+\tfrac{ir}{2}\right)-\log\pi\right)dr,$$
--   with $\Lambda$ the von Mangoldt function and $\psi=\Gamma'/\Gamma$ (`weilDistribution`, assembled from `mellinHat`, `primeSum` and `archTerm`); the first two terms are the contributions of the poles of the completed zeta function, the sum is the contribution of the finite places, and the integral is the contribution of the real place. The spectral side is
--   $$Z(g)=\sum_{\rho}m_{\rho}\,\widehat g(\rho),$$
--   the sum over the zeros of $\zeta$ in the open critical strip, each counted with multiplicity (`zeroSum`).
-- source:
--   A. Connes, Noncommutative geometry and the Riemann zeta function, in: Mathematics: Frontiers and Perspectives, AMS (2000); section 3 "Weil positivity and the Trace formula", pp. 13-22. Transform: eq. (12), p. 15. Explicit formula: eq. (11), p. 15. Positivity/RH equivalence: concluding paragraph, p. 22. Specialised throughout to the global field k = Q with trivial Grossencharakter, so that the L-function is the Riemann zeta function.

import Mathlib

open Complex MeasureTheory

noncomputable section

namespace ConnesRZ

/-- Test functions on the idele class group component `ℝ*₊`, written additively via
`u = e^t`: smooth, compactly supported, complex valued functions on `ℝ`. -/
def IsTest (g : ℝ → ℂ) : Prop := ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g

/-- Connes (12): `ĥ(z) = ∫_{C_k} h(u) |u|^z d*u`, written in the coordinate `u = e^t`
and shifted by `1/2` so that `z` is the variable of the zeta function:
`ĝ(z) = ∫_ℝ g(t) e^{(z - 1/2) t} dt`. -/
def mellinHat (g : ℝ → ℂ) (z : ℂ) : ℂ := ∫ t : ℝ, g t * Complex.exp ((z - 1 / 2) * t)

/-- The involution `h*(u) = conj (h (u⁻¹))`, written additively. -/
def starInv (g : ℝ → ℂ) : ℝ → ℂ := fun t => starRingEnd ℂ (g (-t))

/-- Convolution on the group `ℝ*₊ ≃ ℝ`. -/
def conv (g₁ g₂ : ℝ → ℂ) : ℝ → ℂ := fun t => ∫ s : ℝ, g₁ s * g₂ (t - s)

/-- A zero of the Riemann zeta function in the critical strip. -/
def IsCriticalZero (s : ℂ) : Prop := riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1

/-- The multiplicity of `s` as a zero of the Riemann zeta function. -/
def zeroMult (s : ℂ) : ℕ := analyticOrderNatAt riemannZeta s

/-- The finite (non archimedean) part of the Weil distribution: the sum over prime powers
`Σ_{n ≥ 2} Λ(n) n^{-1/2} (g (log n) + g (-log n))`. -/
def primeSum (g : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
    (g (Real.log n) + g (-Real.log n))

/-- The archimedean local term of the Weil distribution:
`(1/2π) ∫_ℝ ĝ(1/2 + i r) (Re ψ(1/4 + i r/2) - log π) dr`, where `ψ = Γ'/Γ`. -/
def archTerm (g : ℝ → ℂ) : ℂ :=
  ((1 : ℂ) / (2 * Real.pi)) * ∫ r : ℝ, mellinHat g (1 / 2 + I * r) *
    ((((logDeriv Complex.Gamma (1 / 4 + I * r / 2)).re - Real.log Real.pi : ℝ) : ℂ))

/-- The Weil distribution evaluated at a test function `g`: the arithmetic side of the
explicit formula, namely the two pole terms, minus the prime powers term, plus the
archimedean term. -/
def weilDistribution (g : ℝ → ℂ) : ℂ :=
  mellinHat g 0 + mellinHat g 1 - primeSum g + archTerm g

/-- The spectral side: the sum of `ĝ(ρ)` over the zeros `ρ` of zeta in the critical strip,
each counted with its multiplicity. -/
def zeroSum (g : ℝ → ℂ) : ℂ :=
  ∑' ρ : {s : ℂ // IsCriticalZero s}, (zeroMult ρ.1 : ℂ) * mellinHat g ρ.1

end ConnesRZ


