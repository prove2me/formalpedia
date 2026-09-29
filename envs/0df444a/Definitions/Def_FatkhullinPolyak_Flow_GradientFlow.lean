-- Prove2me | Definitions.Def_FatkhullinPolyak_Flow_GradientFlow
-- name    : FatkhullinPolyak_Flow_GradientFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:43:42.105116+00:00
-- url     : https://prove2.me/theorems/4916825e-d065-444e-98ec-fa0ba66411ce
-- title:
--   Solution on $[0,\infty)$ of the gradient flow (4.1) $\dot K = -\nabla f(K)$, $K(0)=K_0$
-- statement:
--   The continuous-time gradient method of Fatkhullin and Polyak, §4.1.
--
--   With the LQR data $A, B, C, Q, R, \Sigma$, the stabilizing set $\mathcal S$ and the gradient formula $\nabla f$ of (3.3), consider the system of ordinary differential equations (4.1)
--   $$\dot K(t) = -\nabla f(K(t)),\qquad K(0) = K_0 .$$
--   A curve $K:\mathbb R\to\mathbb R^{m\times r}$ is a **solution of (4.1) on $[0,\infty)$** if
--
--   1. $K(0)=K_0$;
--   2. $K(t)\in\mathcal S$ for every $t\ge0$;
--   3. for every $t\ge0$ and every entry $(i,j)$, the derivative of $t\mapsto K(t)_{ij}$ within $[0,\infty)$ at $t$ exists and equals $-\nabla f(K(t))_{ij}$ (a right derivative at $t=0$, an ordinary derivative for $t>0$).
--
--   Theorem 4.1 asserts that such a solution exists and describes its behaviour.
--
--   **Formalization Note** The derivative is written entrywise, because Mathlib puts no normed-space structure on matrices by default; this is equivalent to the matrix-valued derivative in any norm. Condition 2 is part of the notion of solution because $\nabla f$ has meaning only on $\mathcal S$ (the formula is evaluated with a placeholder value off $\mathcal S$). Values of $K(t)$ for $t<0$ are irrelevant.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 10, §4.1, (4.1)

import Mathlib
import Definitions.Def_FatkhullinPolyak_Flow_LQR

namespace FatkhullinPolyak.Flow

open Matrix

/-- `K : ℝ → ℝ^{m×r}` is a solution on `[0, ∞)` of the gradient flow (4.1)
`K̇(t) = -∇f(K(t))`, `K(0) = K₀`: it starts at `K₀`, stays in the stabilizing set `S` for
`t ≥ 0` (where `∇f` is meaningful), and every entry has right-derivative-within-`[0, ∞)` equal to
the corresponding entry of `-∇f(K(t))` at each `t ≥ 0` (one-sided at `t = 0`). -/
def IsGradFlow {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (K₀ : Matrix (Fin m) (Fin r) ℝ)
    (K : ℝ → Matrix (Fin m) (Fin r) ℝ) : Prop :=
  K 0 = K₀ ∧
    ∀ t : ℝ, 0 ≤ t →
      K t ∈ stabSet A B C ∧
        ∀ i j, HasDerivWithinAt (fun s => K s i j) (-(grad A B C Q R Sig (K t)) i j)
          (Set.Ici 0) t

end FatkhullinPolyak.Flow


