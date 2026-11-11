-- Prove2me | Definitions.Def_LLROPI_Shamir_Fourier
-- name    : LLROPI_Shamir_Fourier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:33:00.407499+00:00
-- url     : https://prove2.me/theorems/bce10863-4f7f-4680-8ba5-dfdd124bee59
-- title:
--   The character $e_p$, the normalized Fourier transform on $\mathbb F_p$, centered indicators $g$, $\gamma(\rho)$ and the sup norm
-- statement:
--   Fix a prime $p$. The **additive character** is $e_p(t):=\exp(2\pi i t/p)$ for $t\in\mathbb F_p$, and the **normalized Fourier transform** of $f:\mathbb F_p\to\mathbb C$ is
--   $$\hat f(\xi):=\mathbb E_{x\in\mathbb F_p}\big[f(x)\,e_p(x\xi)\big]=\frac1p\sum_{x\in\mathbb F_p}f(x)e_p(x\xi),$$
--   with a plus sign in the exponent and the normalized expectation, so that $f(x)=\sum_\xi\hat f(\xi)e_p(-x\xi)$ (§2.3).
--
--   For $S\subseteq\mathbb F_p$ write $1_S$ for its indicator and $\rho=|S|/p$ for its **density**. The **centered indicator** is
--   $$g(x):=\frac{1_S(x)-\rho}{\sqrt{\rho(1-\rho)}},$$
--   used when $\rho\in(0,1)$; then $\mathbb E g=\hat g(0)=0$ and $\|g\|_2=1$. The function
--   $$\gamma(\rho):=\frac{\sin(\pi\rho)}{\pi\sqrt{\rho(1-\rho)}}\qquad(2.2)$$
--   bounds the nonzero Fourier coefficients of $g$ (Corollary 2.5); $\gamma(0)=\gamma(1)=0$. The **sup norm** of $f:\mathbb F_p\to\mathbb C$ is $\|f\|_\infty=\max_x|f(x)|$.
--
--   **Formalization Note.** `ep t` reads $t$ as its representative $t.\mathrm{val}\in\{0,\dots,p-1\}$ (the value of $e_p$ does not depend on the representative). `fourier` is the one-variable transform; the paper's transform on $\mathbb F_p^n$ only enters through the one-variable coefficients $\hat g_i(y_i)$. `centered S` is real-valued, coerced to $\mathbb C$. `gammaFn` is the formula of (2.2) on all of $\mathbb R$; at $\rho=0,1$ it evaluates to $0$ (vanishing numerator), the paper's continuous extension.
-- source:
--   Sun, Wootters, Improved Local Leakage Resilience of Shamir Secret Sharing and Worst-Case Optimal Polynomial Intersection, arXiv:2610.12357 (held version, sha256 f154f5ce…), §2.3, p. 21 (PDF 23); Corollary 2.5, (2.2), p. 21 (PDF 23); (3.1), p. 29 (PDF 31)

import Mathlib

namespace LLROPI.Shamir

/-!
# Fourier analysis on `𝔽_p`: the character `e_p`, the normalized transform, centered indicators,
# `γ(ρ)` and the sup norm

Y. Sun, M. Wootters, *Improved Local Leakage Resilience of Shamir Secret Sharing and Worst-Case
Optimal Polynomial Intersection*, arXiv:2610.12357 (held version, sha256 f154f5ce…), §2.3,
p. 21 (PDF 23), Corollary 2.5 / (2.2); §2.1, p. 20 (PDF 22).

* `ep t = e_p(t) = exp(2πi t / p)` for `t ∈ 𝔽_p`, with `t` read as its representative in
  `{0, …, p − 1}` (the value does not depend on the representative).
* `fourier f ξ = f̂(ξ) = E_{x ∈ 𝔽_p} [f(x) e_p(x ξ)]`: normalized expectation and a **plus** sign.
* `density S = |S| / p` and `centered S = g = (1_S − ρ)/√(ρ(1 − ρ))` with `ρ = density S`.
* `gammaFn ρ = γ(ρ) = sin(πρ) / (π √(ρ(1 − ρ)))` of (2.2).
* `supNorm f = ‖f‖_∞ = max_x |f(x)|`.
-/

/-- The additive character `e_p(t) := exp(2πi t / p)` on `𝔽_p` (§2.3, p. 21), `t` read as its
representative `t.val ∈ {0, …, p − 1}`. -/
noncomputable def ep {p : ℕ} [NeZero p] (t : ZMod p) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (t.val : ℂ) / (p : ℂ))

/-- The normalized Fourier transform on `𝔽_p` (§2.3, p. 21, case `n = 1`):
`f̂(ξ) := E_{x ∈ 𝔽_p} [f(x) e_p(x ξ)] = p⁻¹ ∑_x f(x) e_p(x ξ)`. -/
noncomputable def fourier {p : ℕ} [NeZero p] (f : ZMod p → ℂ) (ξ : ZMod p) : ℂ :=
  (∑ x : ZMod p, f x * ep (x * ξ)) / (p : ℂ)

/-- The indicator function `1_S : 𝔽_p → ℂ` of a set `S ⊆ 𝔽_p`. -/
def indicatorC {p : ℕ} (S : Finset (ZMod p)) (x : ZMod p) : ℂ :=
  if x ∈ S then 1 else 0

/-- The density `ρ = |S| / p` of a set `S ⊆ 𝔽_p`. -/
noncomputable def density {p : ℕ} (S : Finset (ZMod p)) : ℝ :=
  (S.card : ℝ) / (p : ℝ)

/-- The centered, normalized indicator `g(x) := (1_S(x) − ρ) / √(ρ(1 − ρ))` with `ρ = |S|/p`
((2.2), p. 21; (3.1), p. 29). It is only used for `ρ ∈ (0, 1)`. -/
noncomputable def centered {p : ℕ} (S : Finset (ZMod p)) (x : ZMod p) : ℂ :=
  (((if x ∈ S then (1 : ℝ) else 0) - density S) / Real.sqrt (density S * (1 - density S)) : ℝ)

/-- `γ(ρ) := sin(πρ) / (π √(ρ(1 − ρ)))` ((2.2), p. 21). At `ρ = 0` and `ρ = 1` the formula
evaluates to `0` (the numerator vanishes), which is the paper's continuous extension
`γ(0) = γ(1) = 0`. -/
noncomputable def gammaFn (ρ : ℝ) : ℝ :=
  Real.sin (Real.pi * ρ) / (Real.pi * Real.sqrt (ρ * (1 - ρ)))

/-- The sup norm `‖f‖_∞ := max_{x ∈ 𝔽_p} |f(x)|` of a function `f : 𝔽_p → ℂ`. -/
noncomputable def supNorm {p : ℕ} [NeZero p] (f : ZMod p → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x => ‖f x‖)

end LLROPI.Shamir


