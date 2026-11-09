-- Prove2me | Definitions.Def_SpectralSharpness_NormalWindow_ExponentialType
-- name    : SpectralSharpness_NormalWindow_ExponentialType
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:18:38.204192+00:00
-- url     : https://prove2.me/theorems/8d0ab86c-d0db-4f38-bd49-98338a4c6828
-- title:
--   Entire functions of exponential type at most $\tau$
-- statement:
--   Let $\tau\in\mathbb R$. An entire function $g:\mathbb C\to\mathbb C$ is **of exponential type at most $\tau$** if for every $\varepsilon>0$ there is a constant $C$ such that
--
--   $$
--   |g(z)|\le C\,e^{(\tau+\varepsilon)|z|}\qquad\text{for all } z\in\mathbb C .
--   $$
--
--   Equivalently, $\limsup_{r\to\infty}\frac{1}{r}\log\max_{|z|=r}|g(z)|\le\tau$. The predicate bundles the two requirements: $g$ is complex differentiable on all of $\mathbb C$ (entire), and it satisfies the growth bound above.
--
--   This is the class of functions to which Bernstein's inequality for entire functions of exponential type applies. In the source, the restriction of a band-limited trigonometric polynomial with spectrum in the Euclidean ball of radius $d$ to a complex line $x_0+wv$ ($v$ a unit vector) is such a function with $\tau=d$.
--
--   **Formalization Note** `IsEntireOfExponentialTypeLE τ g` is `Differentiable ℂ g` together with `∀ ε > 0, ∃ C, ∀ z, ‖g z‖ ≤ C * exp ((τ + ε) * ‖z‖)`. No boundedness on the real axis, periodicity or other regularity is included.
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript (STOC 2027 submission #122; SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, §9, proof of Lemma 9.1, p. 27 ("entire function of exponential type ≤ d"); classical definition as in R. P. Boas, Entire Functions, Academic Press, 1954

import Mathlib

namespace SpectralSharpness.NormalWindow

/-- `g : ℂ → ℂ` is an entire function of exponential type at most `τ`: it is complex
differentiable on all of `ℂ`, and for every `ε > 0` there is a constant `C` with
`‖g z‖ ≤ C · exp((τ + ε)‖z‖)` for every `z ∈ ℂ` (equivalently,
`limsup_{r → ∞} log max_{|z| = r} |g z| / r ≤ τ`). -/
def IsEntireOfExponentialTypeLE (τ : ℝ) (g : ℂ → ℂ) : Prop :=
  Differentiable ℂ g ∧
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖)

end SpectralSharpness.NormalWindow


