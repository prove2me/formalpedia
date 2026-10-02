-- Prove2me | Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod
-- name    : ShorNonsmooth_SpaceDilation_SDGMethod
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T16:04:53.935982+00:00
-- url     : https://prove2.me/theorems/80f350dc-e3c9-439d-8733-dc40bdc4322c
-- title:
--   The space-dilation operator $R_\alpha(\xi)$ and the subgradient method with space dilation along the gradient (SDG)
-- statement:
--   Throughout, $E_n$ is the $n$-dimensional Euclidean space with inner product $(x, y)$.
--
--   1. **Space dilation.** Let $\xi \in E_n$ with $\|\xi\| = 1$ and let $\alpha$ be a real number (the book takes $\alpha \ge 0$). Every $x \in E_n$ splits as $x = \gamma_\xi(x)\,\xi + d_\xi(x)$ with $\gamma_\xi(x) = (x, \xi)$ and $d_\xi(x) = x - (x, \xi)\,\xi$. The **operator of space dilation along $\xi$ with coefficient $\alpha$** is the linear map
--   $$
--   R_\alpha(\xi)\,x = \alpha\,\gamma_\xi(x)\,\xi + d_\xi(x) = x + (\alpha - 1)(x, \xi)\,\xi .
--   $$
--   It stretches the component of $x$ along $\xi$ by the factor $\alpha$ and leaves the orthogonal component unchanged.
--
--   2. **The SDG method.** Fix a map $g : E_n \to E_n$ (the generalized gradient: a subgradient of a convex $f$, or an almost-gradient of an almost differentiable $f$), a stepsize rule $h$, space-dilation coefficients $\alpha_1, \alpha_2, \dots$, a starting point $x_0$, and a nonsingular operator $B_0$, with $A_0 = B_0^{-1}$. The $(k+1)$-st iteration, $k = 0, 1, \dots$, from $(x_k, B_k, A_k)$ is:
--      - if $g(x_k) = 0$ the computation stops;
--      - otherwise $\tilde g_k = B_k^{*} g(x_k)$, where $B_k^*$ is the adjoint of $B_k$ (3.6), and $\xi_{k+1} = \tilde g_k / \|\tilde g_k\|$ (3.7);
--      - with the stepsize $h_{k+1}$ and the coefficient $\alpha_{k+1}$,
--   $$
--   x_{k+1} = x_k - h_{k+1} B_k \xi_{k+1}, \qquad B_{k+1} = B_k\, R_{1/\alpha_{k+1}}(\xi_{k+1}), \qquad A_{k+1} = R_{\alpha_{k+1}}(\xi_{k+1})\, A_k ,
--   $$
--      formulas (3.8) and (3.9). Thus $A_k = R_{\alpha_k}(\xi_k) \cdots R_{\alpha_1}(\xi_1) A_0$ is the accumulated space transformation and $B_k = A_k^{-1}$.
--
--   The method performs a subgradient step for $\varphi_k(y) = f(B_k y)$ in the transformed variables $y = A_k x$, and then dilates the space along the normalized transformed gradient. These objects underlie every convergence result of Section 3.4.
--
--   **Formalization Note** $E_n$ is `EuclideanSpace ℝ (Fin n)`; operators are continuous linear maps, $B_0$ is a continuous linear equivalence (hence nonsingular) and $A_0$ is its inverse. The state $(x_k, B_k, A_k)$ is a structure `SDGState`, and `sdg g h α x₀ B₀ k` is the state after $k$ iterations; `gTilde … k` is $\tilde g_k = B_k^* g(x_k)$. The stepsize rule `h` receives the index $k+1$, the point $x_k$ and $\tilde g_k$, so rules such as (3.19) that depend on $f(x_k)$ and $\|\tilde g_k\|$ are expressible; the coefficient used at step $k$ is `α (k+1)` and `α 0` is never used. When $g(x_k) = 0$ the state is repeated from then on, which is the book's stopping rule; no division by zero is used.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 49–50, formulas (3.1)–(3.3) and the Definition of $R_\alpha(\xi)$; pp. 51–52, the SDG method, steps 1)–7), formulas (3.6)–(3.9)

import Mathlib

namespace ShorNonsmooth.SpaceDilation

/-- Shor (1985), p. 50, Definition (§3.2): the **operator of space dilation** `R_α(ξ)` along the
direction `ξ` (a unit vector, `‖ξ‖ = 1`) with coefficient `α`. Writing `x = γ_ξ(x) ξ + d_ξ(x)` with
`γ_ξ(x) = (x, ξ)` and `d_ξ(x) = x - (x, ξ) ξ` (p. 49, (3.1)–(3.2)), it maps
`x ↦ α γ_ξ(x) ξ + d_ξ(x)`. Here `innerSL ℝ ξ x = (ξ, x) = (x, ξ)`. -/
noncomputable def dilation {n : ℕ} (α : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  α • (innerSL ℝ ξ).smulRight ξ +
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) - (innerSL ℝ ξ).smulRight ξ)

/-- The state of the SDG method after `k` iterations: the point `x_k`, the matrix
`B_k = A_k⁻¹` and the space-transformation operator `A_k` (Shor 1985, pp. 51–52). -/
structure SDGState (n : ℕ) where
  /-- the current point `x_k` -/
  x : EuclideanSpace ℝ (Fin n)
  /-- the operator `B_k` of (3.9) -/
  B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)
  /-- the space-transformation operator `A_k = R_{α_k}(ξ_k) ⋯ R_{α_1}(ξ_1) A_0` -/
  A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)

/-- One iteration (the `(k+1)`-st, `k = 0, 1, …`) of the **SDG method** (Shor 1985, pp. 51–52,
steps 1)–7), formulas (3.6)–(3.9)), from the state `(x_k, B_k, A_k)`:

1) evaluate `g(x_k)`; if `g(x_k) = 0` the computation stops, and the state is repeated;
2) `g̃_k = B_k* g(x_k)` (3.6), `B_k*` the adjoint of `B_k`;
3) `ξ_{k+1} = g̃_k / ‖g̃_k‖` (3.7);
4)–5) the stepsize `h_{k+1} = h (k+1) x_k g̃_k` and the coefficient `α_{k+1} = α (k+1)`;
6) `x_{k+1} = x_k - h_{k+1} B_k ξ_{k+1}` (3.8);
7) `B_{k+1} = B_k R_{1/α_{k+1}}(ξ_{k+1})` (3.9) and `A_{k+1} = R_{α_{k+1}}(ξ_{k+1}) A_k`.

The stepsize rule `h` may depend on the iteration index, the current point and `g̃_k`. -/
noncomputable def sdgStep {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) (α : ℕ → ℝ)
    (k : ℕ) (s : SDGState n) : SDGState n :=
  if g s.x = 0 then s
  else
    { x := s.x - h (k + 1) s.x (ContinuousLinearMap.adjoint s.B (g s.x)) •
          s.B (‖ContinuousLinearMap.adjoint s.B (g s.x)‖⁻¹ •
            ContinuousLinearMap.adjoint s.B (g s.x)),
      B := s.B.comp (dilation (1 / α (k + 1))
          (‖ContinuousLinearMap.adjoint s.B (g s.x)‖⁻¹ •
            ContinuousLinearMap.adjoint s.B (g s.x))),
      A := (dilation (α (k + 1))
          (‖ContinuousLinearMap.adjoint s.B (g s.x)‖⁻¹ •
            ContinuousLinearMap.adjoint s.B (g s.x))).comp s.A }

/-- The SDG method (Shor 1985, pp. 51–52) started at `x₀` with a nonsingular initial operator
`B₀ = A₀⁻¹`: the state `(x_k, B_k, A_k)` after `k` iterations. -/
noncomputable def sdg {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) : ℕ → SDGState n
  | 0 => ⟨x₀, (B₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      (B₀.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))⟩
  | k + 1 => sdgStep g h α k (sdg g h α x₀ B₀ k)

/-- The transformed gradient `g̃_k = B_k* g(x_k)` of (3.6) at iteration `k` of the SDG method. -/
noncomputable def gTilde {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.adjoint (sdg g h α x₀ B₀ k).B (g (sdg g h α x₀ B₀ k).x)

end ShorNonsmooth.SpaceDilation


