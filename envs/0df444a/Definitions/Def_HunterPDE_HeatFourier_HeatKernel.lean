-- Prove2me | Definitions.Def_HunterPDE_HeatFourier_HeatKernel
-- name    : HunterPDE_HeatFourier_HeatKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:55:45.082985+00:00
-- url     : https://prove2.me/theorems/d21cd182-505a-4e53-92d0-f123eaa9369f
-- title:
--   Eq. (5.5)–(5.6) — the heat kernel Γ(x,t) = (4πt)^{−n/2} e^{−|x|²/4t}, the heat convolution, and the Schrödinger kernel
-- statement:
--   For $x \in \mathbb{R}^n$ and $t > 0$ the **heat kernel** (Green's function, fundamental solution of the heat equation) is
--   $$\Gamma(x,t) = \frac{1}{(4\pi t)^{n/2}}\, e^{-|x|^2/4t}.$$
--   For data $f : \mathbb{R}^n \to \mathbb{R}$ the **heat convolution** is the function
--   $$u(x,t) = \int_{\mathbb{R}^n} \Gamma(x-y,t)\, f(y)\, dy \qquad (t > 0).$$
--   The **free Schrödinger kernel** is, for $t \ne 0$,
--   $$\Gamma_S(x,t) = \frac{1}{(4\pi i t)^{n/2}}\, e^{\,i|x|^2/4t},$$
--   with the principal branch of the complex power $(4\pi i t)^{n/2}$.
--
--   **Formalization Note.** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)` with Lebesgue measure; $|x|$ is the Euclidean norm; $(4\pi t)^{n/2}$ is a real power. The heat convolution is a Bochner integral; values of $\Gamma$ for $t \le 0$ and of $\Gamma_S$ at $t = 0$ are junk and never used (every theorem assumes $t > 0$, resp. $t \ne 0$). The book prints the Schrödinger kernel with $e^{-i|x|^2/4t}$ (Theorem 5.15, p. 138); that sign contradicts the book's own Fourier solution (5.15) $\hat u(k,t) = e^{-it|k|^2}\hat f(k)$, and the kernel defined here carries the corrected sign $e^{+i|x|^2/4t}$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 130, Eq. (5.5)–(5.6); p. 138, Theorem 5.15

import Mathlib

namespace HunterPDE.HeatFourier

open MeasureTheory

/-- The Green's function (fundamental solution) of the heat equation on `ℝⁿ`, (5.6) of Hunter,
*Notes on PDEs* (p. 130):
`Γ(x, t) = 1 / (4πt)^{n/2} · e^{−|x|²/4t}`.
`ℝⁿ` is `EuclideanSpace ℝ (Fin n)` and `|x|` is the Euclidean norm; `(4πt)^{n/2}` is a real
power. The book uses `Γ` only for `t > 0`; every theorem about it assumes `0 < t`, and the values
for `t ≤ 0` are junk. -/
noncomputable def heatKernel (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  1 / (4 * Real.pi * t) ^ ((n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))

/-- The function `u` of (5.5) (Hunter, *Notes on PDEs*, p. 130): the convolution of the data
`f : ℝⁿ → ℝ` with the heat kernel,
`u(x, t) = ∫_{ℝⁿ} Γ(x − y, t) f(y) dy`,
a Lebesgue (Bochner) integral with respect to `volume`. It is used only for `t > 0`. -/
noncomputable def heatSolution (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  ∫ y, heatKernel n (x - y) t * f y

/-- The kernel of the free Schrödinger equation `i u_t = −Δu` on `ℝⁿ` (Hunter, *Notes on PDEs*,
Theorem 5.15, p. 138), for `t ≠ 0`:
`Γ(x, t) = 1 / (4πit)^{n/2} · e^{+i|x|²/4t}`.
`(4πit)^{n/2}` is the principal-branch complex power `Complex.cpow`. The exponent's sign is
`+i|x|²/4t`; the book prints `e^{−i|x|²/4t}`, which is a misprint: the kernel of
`u_t = iΔu` is `(4πit)^{−n/2} e^{−|x|²/(4it)}` and `−1/(4it) = +i/(4t)`, consistent with the
book's own Fourier solution (5.15) `û(k, t) = e^{−it|k|²} f̂(k)`. The value at `t = 0` is junk
and never used. -/
noncomputable def schrodingerKernel (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℂ :=
  1 / ((4 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ ((n : ℂ) / 2)) *
    Complex.exp (Complex.I * ((‖x‖ ^ 2 / (4 * t) : ℝ) : ℂ))

end HunterPDE.HeatFourier


