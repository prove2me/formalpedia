-- Prove2me | Definitions.Def_PathoSubgrad_Circle_Construction
-- name    : PathoSubgrad_Circle_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:44.242864+00:00
-- url     : https://prove2.me/theorems/e2caa2b0-23a9-4abd-b36e-572d55e369e3
-- title:
--   §2.1, p. 6 — the points x_i, step sizes ε_i, directions v_i, the bumps ψ_i, the affine pieces V_i and the function f of (4)
-- statement:
--   The ingredients of the example on the circle. For $i\ge2$ let
--   $$\vartheta_i=\sum_{k=2}^{i}\frac{1}{k\log k},\qquad x_i=\Bigl[1+\frac{(-1)^i}{i}\Bigr](\cos\vartheta_i,\sin\vartheta_i),$$
--   $$\varepsilon_i=\|x_{i+1}-x_i\|,\qquad v_i=-\frac{x_{i+1}-x_i}{\|x_{i+1}-x_i\|},$$
--   so that $x_{i+1}=x_i-\varepsilon_i v_i$. The points alternate between just outside and just inside the unit circle $S^1$ while their angle drifts slowly and without bound.
--
--   Let $\varphi(x)=|1-\|x\||$ be the distance to $S^1$. A **bump profile** is a $C^\infty$ function $\psi:\mathbb R^2\to[0,1]$ that is radially symmetric ($\psi(x)=\psi(y)$ whenever $\|x\|=\|y\|$), equals $1$ on the open unit ball $B_1(0)$, vanishes for $\|x\|\ge2$, and is non-increasing along every ray from the origin. Put $\psi_i(x)=\psi(2^i(x-x_i))$, which equals $1$ on $B_{1/2^i}(x_i)$ and vanishes outside $B_{1/2^{i-1}}(x_i)$, and $V_i(x)=(x-x_i)\cdot v_i+1/i$. For $i_0\ge2$ the function of (4) is
--   $$f(x)=\Bigl(1-\sum_{i=i_0}^{\infty}\psi_i(x)\Bigr)\varphi(x)+\sum_{i=i_0}^{\infty}\psi_i(x)V_i(x).$$
--
--   The function $f$ is the distance to the circle, modified on small balls around the $x_i$ so that its gradient there is exactly $v_i$; this is what makes $(x_i)$ a subgradient sequence of $f$.
--
--   **Formalization Note.** The bump is a structure `BumpProfile` carrying exactly the properties listed on p. 6, and every theorem of the mission holds for an arbitrary bump profile. The infinite sums are `tsum`s over all $i$ of the terms with $i\ge i_0$; at each point only finitely many $\psi_i$ are nonzero, so the series are finite sums. The formulas are defined for all $i\in\mathbb N$, but the values at $i<2$ (where Lean gives $1/0=0$, $\log 1=0$ and an empty sum) are never used: every statement takes $i_0\ge2$ or a large index.
-- source:
--   Ríos-Zertuche, Examples of pathological dynamics of the subgradient method for Lipschitz path-differentiable functions, arXiv:2007.11699v1, p. 6, §2.1, definitions of x_i, ϑ_i, ε_i, v_i, φ, ψ, ψ_i, V_i and (4)

import Mathlib

open scoped InnerProductSpace ContDiff

namespace PathoSubgrad.Circle

/-- §2.1, p. 6: `ϑ_i = Σ_{k=2}^{i} 1/(k log k)`. -/
noncomputable def theta (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 i, 1 / ((k : ℝ) * Real.log k)

/-- §2.1, p. 6: `x_i = [1 + (−1)^i/i](cos ϑ_i, sin ϑ_i)`, for `i ≥ 2`. -/
noncomputable def xs (i : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  (1 + (-1 : ℝ) ^ i / i) • !₂[Real.cos (theta i), Real.sin (theta i)]

/-- §2.1, p. 6: the step size `ε_i = ‖x_{i+1} − x_i‖`. -/
noncomputable def eps (i : ℕ) : ℝ := ‖xs (i + 1) - xs i‖

/-- §2.1, p. 6: `v_i = −(x_{i+1} − x_i)/‖x_{i+1} − x_i‖`, so that `x_{i+1} = x_i − ε_i v_i`. -/
noncomputable def vs (i : ℕ) : EuclideanSpace ℝ (Fin 2) := -((eps i)⁻¹ • (xs (i + 1) - xs i))

/-- §2.1, p. 6: `φ(x) = |1 − ‖x‖|`, the distance to the unit circle. -/
noncomputable def phi (x : EuclideanSpace ℝ (Fin 2)) : ℝ := |1 - ‖x‖|

/-- §2.1, p. 6: a bump `ψ : ℝ² → [0, 1]`, `C^∞`, radially symmetric, equal to `1` on the open
unit ball `B_1(0)`, equal to `0` for `‖x‖ ≥ 2`, and non-increasing on rays from the origin. -/
structure BumpProfile where
  ψ : EuclideanSpace ℝ (Fin 2) → ℝ
  smooth : ContDiff ℝ ∞ ψ
  mem_Icc : ∀ x, ψ x ∈ Set.Icc (0 : ℝ) 1
  radial : ∀ x y, ‖x‖ = ‖y‖ → ψ x = ψ y
  one_of_lt : ∀ x, ‖x‖ < 1 → ψ x = 1
  zero_of_ge : ∀ x, 2 ≤ ‖x‖ → ψ x = 0
  antitone_ray : ∀ x (s t : ℝ), 0 ≤ s → s ≤ t → ψ (t • x) ≤ ψ (s • x)

/-- §2.1, p. 6: `ψ_i(x) = ψ(2^i (x − x_i))`. -/
noncomputable def psiI (Ψ : BumpProfile) (i : ℕ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Ψ.ψ ((2 : ℝ) ^ i • (x - xs i))

/-- §2.1, p. 6: `V_i(x) = (x − x_i) · v_i + 1/i`. -/
noncomputable def Vi (i : ℕ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ := ⟪x - xs i, vs i⟫_ℝ + 1 / i

/-- (4), p. 6: `f(x) = (1 − Σ_{i ≥ i0} ψ_i(x)) φ(x) + Σ_{i ≥ i0} ψ_i(x) V_i(x)`. -/
noncomputable def fCirc (Ψ : BumpProfile) (i0 : ℕ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (1 - ∑' i : ℕ, if i0 ≤ i then psiI Ψ i x else 0) * phi x +
    ∑' i : ℕ, if i0 ≤ i then psiI Ψ i x * Vi i x else 0

end PathoSubgrad.Circle


