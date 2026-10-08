-- Prove2me | Definitions.Def_JSQHalfinWhitt_Ergodicity_Operators
-- name    : JSQHalfinWhitt_Ergodicity_Operators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:22.99582+00:00
-- url     : https://prove2.me/theorems/462c9df2-db2c-4811-acbc-1f6ddc4b7497
-- title:
--   §1.2, (3.4), p. 16, (5.5) — the domain Ω, one-sided partials, the generator G_Y, the fluid operator L and the smoothed indicator φ^{(ℓ,u)}
-- statement:
--   This file fixes the analytic language of the Foster–Lyapunov analysis of the join-the-shortest-queue (JSQ) diffusion limit.
--
--   **Domain.** The state space of the diffusion is the closed quadrant
--   $$\Omega=(-\infty,0]\times[0,\infty)\subset\mathbb R^2 .$$
--   For $f:\Omega\to\mathbb R$ we write $f_1=\partial f/\partial x_1$, $f_2=\partial f/\partial x_2$ and $f_{11}=\partial f_1/\partial x_1$. At points of the boundary $\partial\Omega$ where a two-sided derivative is not defined, these are one-sided derivatives (left derivative in $x_1$ at $x_1=0$, right derivative in $x_2$ at $x_2=0$). $C^k(\Omega)$ is the class of $k$ times continuously differentiable functions on $\Omega$ in this one-sided sense.
--
--   **Generator.** For $\beta>0$ and $f\in C^2(\Omega)$ satisfying the reflection condition $f_1(0,x_2)=f_2(0,x_2)$ for $x_2\ge0$, the generator of the diffusion limit of the JSQ model acts by
--   $$G_Yf(x)=(-x_1+x_2-\beta)f_1(x)-x_2f_2(x)+f_{11}(x),\qquad x\in\Omega .$$
--
--   **Fluid operator (3.4).** For an integer $n\ge1$,
--   $$Lf(x)=\Big(-x_1+x_2-\frac{\beta}{\sqrt n}\Big)f_1(x)-x_2f_2(x).$$
--
--   **Smoothed indicator (5.5).** For $\ell<u$, with midpoint $m=(u+\ell)/2$,
--   $$\phi^{(\ell,u)}(x)=\begin{cases}0,& x\le \ell,\\ (x-\ell)^2\Big(\dfrac{-(x-\ell)}{(m-\ell)^2(u-\ell)}+\dfrac{2}{(m-\ell)(u-\ell)}\Big),& x\in[\ell,m],\\ 1-(x-u)^2\Big(\dfrac{x-u}{(m-u)^2(u-\ell)}-\dfrac{2}{(m-u)(u-\ell)}\Big),& x\in[m,u],\\ 1,& x\ge u.\end{cases}$$
--   It increases from $0$ to $1$ on $[\ell,u]$ and is continuously differentiable, but not twice differentiable at $\ell$, $m$, $u$.
--
--   These objects state Theorem 4 (the drift inequality for $G_Y$) and the PDEs (5.9)–(5.10) of Lemma 8, whose solutions build the Lyapunov function.
--
--   **Formalization Note** Points are pairs `ℝ × ℝ` and $\Omega$ is `Set.Iic 0 ×ˢ Set.Ici 0`. The partials are `fderivWithin ℝ f Ω x` applied to $(1,0)$ and $(0,1)$; since $\Omega$ is convex with nonempty interior, the derivative within $\Omega$ is unique and at boundary points equals the one-sided derivative of p. 4. $C^2(\Omega)$ is `ContDiffOn ℝ 2 f Ω` in the theorems. `genY` is the generator *formula* of p. 16, not the extended generator (5.1) of the process (2.1), which is not constructed; every theorem applies it only to $C^2(\Omega)$ functions with the reflection condition, the class on which p. 16 identifies the two. The operator $L$ uses the same partials on $\Omega$, which is where (5.9)–(5.10) apply it.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 4, §1.2, (1.4); p. 7, (3.4); p. 16, display after (5.1); p. 17, (5.5)

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_PDE

namespace JSQHalfinWhitt.Ergodicity

/-- The partial derivative `f₁(x) = ∂f(x)/∂x₁` on `Ω` (§1.2, p. 4): the derivative of `f` within `Ω`
in the direction `(1, 0)`. Since `Ω` is convex with nonempty interior, at a point of `∂Ω` this is the
one-sided derivative, as on p. 4. -/
noncomputable def d1 (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  fderivWithin ℝ f JSQHalfinWhitt.Tightness.Omega x (1, 0)

/-- The partial derivative `f₂(x) = ∂f(x)/∂x₂` on `Ω` (one-sided on `∂Ω`), as `d1`. -/
noncomputable def d2 (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  fderivWithin ℝ f JSQHalfinWhitt.Tightness.Omega x (0, 1)

/-- The second partial derivative `f₁₁ = ∂(f₁)/∂x₁` on `Ω`. -/
noncomputable def d11 (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  d1 (d1 f) x

/-- The generator of the JSQ diffusion limit (2.1) on functions `f ∈ C²(Ω)` with
`f₁(0, x₂) = f₂(0, x₂)` (p. 16, unnumbered display):
`G_Y f(x) = (−x₁ + x₂ − β) f₁(x) − x₂ f₂(x) + f₁₁(x)`. It is the formula only; the theorems apply it
to functions of that class. -/
noncomputable def genY (β : ℝ) (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  (-x.1 + x.2 - β) * d1 f x - x.2 * d2 f x + d11 f x

/-- The fluid-model operator (3.4), p. 7: `Lf(x) = (−x₁ + x₂ − β/√n) f₁(x) − x₂ f₂(x)`, with the partial
derivatives of `f` on `Ω`. -/
noncomputable def opL (n : ℕ) (β : ℝ) (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  (-x.1 + x.2 - β / Real.sqrt n) * d1 f x - x.2 * d2 f x

/-- The smoothed indicator `φ^{(ℓ,u)}` of (5.5), p. 17 (meant for `ℓ < u`). -/
noncomputable def smoothInd (l u : ℝ) (x : ℝ) : ℝ :=
  if x ≤ l then 0
  else if x ≤ (u + l) / 2 then
    (x - l) ^ 2 * (-(x - l) / (((u + l) / 2 - l) ^ 2 * (u - l)) + 2 / (((u + l) / 2 - l) * (u - l)))
  else if x ≤ u then
    1 - (x - u) ^ 2 * ((x - u) / (((u + l) / 2 - u) ^ 2 * (u - l)) - 2 / (((u + l) / 2 - u) * (u - l)))
  else 1

end JSQHalfinWhitt.Ergodicity


