-- Prove2me | Definitions.Def_ShorNonsmooth_Ellipsoid_EllipsoidMethod
-- name    : ShorNonsmooth_Ellipsoid_EllipsoidMethod
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T16:16:36.595985+00:00
-- url     : https://prove2.me/theorems/a5634e92-d015-47c1-8039-0820fec480ae
-- title:
--   The space-dilation operator $R_\alpha(\xi)$ and Shor's ellipsoid algorithm (3.57)–(3.60)
-- statement:
--   Throughout, $E_n$ is the $n$-dimensional Euclidean space with inner product $(x, y)$.
--
--   1. **Space dilation.** For a unit vector $\xi \in E_n$ and a real number $\alpha$, the **operator of space dilation along $\xi$ with coefficient $\alpha$** is
--   $$
--   R_\alpha(\xi) = I + (\alpha - 1)\,\xi\xi^{T}, \qquad R_\alpha(\xi)\,x = \alpha (x, \xi)\,\xi + \bigl[x - (x, \xi)\,\xi\bigr].
--   $$
--   It multiplies the component of $x$ along $\xi$ by $\alpha$ and leaves the component orthogonal to $\xi$ unchanged.
--
--   2. **Constants.** For $n > 1$ put
--   $$
--   \beta = \sqrt{\frac{n-1}{n+1}}, \qquad r = \frac{n}{\sqrt{n^2 - 1}}, \qquad q_n = \sqrt{\frac{n-1}{n+1}}\left(\frac{n}{\sqrt{n^2-1}}\right)^{n}.
--   $$
--
--   3. **The algorithm (3.57)–(3.60).** Given a vector field $g : E_n \to E_n$ (not necessarily continuous), a radius $R$ and a starting point $x_0$, set $B_0 = I_n$ and $h_0 = R/(n+1)$. From $(x_k, B_k, h_k)$ the $(k+1)$-st iteration is:
--      - compute $g(x_k)$; if $g(x_k) = 0$, then $x_k$ is a solution and the computation stops;
--      - otherwise $\xi_k = B_k^{*} g(x_k) / \|B_k^{*} g(x_k)\|$, where $B_k^* = B_k^T$ is the adjoint (3.57);
--      - $x_{k+1} = x_k - h_k B_k \xi_k$ (3.58);
--      - $B_{k+1} = B_k R_\beta(\xi_k)$ (3.59);
--      - $h_{k+1} = r\,h_k$ (3.60).
--
--   4. **Ellipsoids.** For an $n\times n$ matrix $A$, a center $c$ and a radius $\rho$, $\{x : \|A(x - c)\| \le \rho\}$. With $A_k = B_k^{-1}$ and $\rho = (n+1)h_k$ this is the set $\Phi_k$ that localizes the solution.
--
--   The algorithm is a subgradient-type method with space dilation along the transformed gradient; in the original coordinates it is the ellipsoid method of Yudin–Nemirovskii and Shor.
--
--   **Formalization Note** $E_n$ is `EuclideanSpace ℝ (Fin n)` and matrices act through `Matrix.toEuclideanLin`. $R_\alpha(\xi)$ is defined by its matrix representation (property 10 on p. 50), which for $\|\xi\| = 1$ is the book's operator (formula (3.3)). The state $(x_k, B_k, h_k)$ is the structure `EllState`; `ellipsoidMethod g R x₀ k` is the state after $k$ iterations. When $g(x_k) = 0$ the state is repeated from then on, which is the book's stopping rule; the division by $\|B_k^* g(x_k)\|$ is only performed when $g(x_k) \neq 0$, and then $B_k^* g(x_k) \neq 0$ because $B_k$ is nonsingular. $A_k$ is the matrix inverse `B⁻¹`, which is a true inverse since $\det B_k = \beta^k > 0$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 49–50, formulas (3.1)–(3.3), the Definition of $R_\alpha(\xi)$ and property 10); p. 86, the algorithm (3.57)–(3.60); p. 87, the ellipsoid $\Phi_k$; p. 88, $q_n$

import Mathlib

namespace ShorNonsmooth.Ellipsoid

/-- Shor (1985), p. 50, Definition (§3.2), in the matrix representation of property 10):
the **operator of space dilation** `R_α(ξ)` along a unit vector `ξ` with coefficient `α`,
`R_α(ξ) = I + (α - 1) ξ ξᵀ`. For `‖ξ‖ = 1` it maps `x = (x, ξ) ξ + d_ξ(x)` to
`α (x, ξ) ξ + d_ξ(x) = (α - 1)(x, ξ) ξ + x` (formula (3.3)). -/
noncomputable def dilationMatrix {n : ℕ} (α : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  1 + (α - 1) • Matrix.vecMulVec (WithLp.ofLp ξ) (WithLp.ofLp ξ)

/-- The dilation coefficient `β = √((n - 1)/(n + 1))` of (3.59) (Shor 1985, p. 86). -/
noncomputable def beta (n : ℕ) : ℝ := Real.sqrt (((n : ℝ) - 1) / ((n : ℝ) + 1))

/-- The stepsize ratio `r = n / √(n² - 1)` of (3.60) (Shor 1985, p. 86). -/
noncomputable def ratio (n : ℕ) : ℝ := (n : ℝ) / Real.sqrt ((n : ℝ) ^ 2 - 1)

/-- The volume ratio `q_n = √((n - 1)/(n + 1)) (n / √(n² - 1))ⁿ` (Shor 1985, p. 88). -/
noncomputable def qRatio (n : ℕ) : ℝ := beta n * ratio n ^ n

/-- The state of the algorithm (3.57)–(3.60) after `k` iterations: the point `x_k`,
the `n × n` matrix `B_k` and the stepsize `h_k` (Shor 1985, p. 86). -/
structure EllState (n : ℕ) where
  /-- the current point `x_k` -/
  x : EuclideanSpace ℝ (Fin n)
  /-- the matrix `B_k` -/
  B : Matrix (Fin n) (Fin n) ℝ
  /-- the stepsize `h_k` -/
  h : ℝ

/-- The direction `ξ = B* v / ‖B* v‖` of (3.57) for the matrix `B` and the vector `v = g(x_k)`,
where `B* = Bᵀ` is the adjoint of `B` (Shor 1985, p. 86). It is only used when `v ≠ 0`. -/
noncomputable def direction {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ‖Matrix.toEuclideanLin B.transpose v‖⁻¹ • Matrix.toEuclideanLin B.transpose v

/-- One iteration (the `(k+1)`-st) of the algorithm (3.57)–(3.60) (Shor 1985, p. 86) for the
vector field `g`, from the state `(x_k, B_k, h_k)`:

(1) evaluate `g(x_k)`; if `g(x_k) = 0` then `x_k` is a solution, the computation stops, and the
    state is repeated from then on;
(2) `ξ_k = B_k* g(x_k) / ‖B_k* g(x_k)‖` (3.57), `B_k* = B_kᵀ` the adjoint;
(3) `x_{k+1} = x_k - h_k B_k ξ_k` (3.58);
(4) `B_{k+1} = B_k R_β(ξ_k)`, `β = √((n - 1)/(n + 1))` (3.59);
(5) `h_{k+1} = r h_k`, `r = n / √(n² - 1)` (3.60). -/
noncomputable def ellStep {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (s : EllState n) : EllState n :=
  if g s.x = 0 then s
  else
    { x := s.x - s.h • Matrix.toEuclideanLin s.B (direction s.B (g s.x)),
      B := s.B * dilationMatrix (beta n) (direction s.B (g s.x)),
      h := ratio n * s.h }

/-- The algorithm (3.57)–(3.60) (Shor 1985, p. 86) for the field `g`, started from
`x₀`, `B₀ = I_n` and `h₀ = R/(n + 1)`: `ellipsoidMethod g R x₀ k` is the state
`(x_k, B_k, h_k)` after `k` iterations. -/
noncomputable def ellipsoidMethod {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (R : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → EllState n
  | 0 => { x := x₀, B := 1, h := R / ((n : ℝ) + 1) }
  | k + 1 => ellStep g (ellipsoidMethod g R x₀ k)

/-- The ellipsoid `{x : ‖A (x - c)‖ ≤ ρ}` with center `c`, shape matrix `A` and radius `ρ`
(Shor 1985, p. 87, the set `Φ_k` with `A = A_k`, `ρ = (n + 1) h_k`). -/
def ellipsoid {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ‖Matrix.toEuclideanLin A (x - c)‖ ≤ ρ}

end ShorNonsmooth.Ellipsoid


