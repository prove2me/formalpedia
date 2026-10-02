-- Prove2me | Definitions.Def_TeschlODE_Linear_IsPrincipalMatrixSolution
-- name    : TeschlODE_Linear_IsPrincipalMatrixSolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:54:24.534159+00:00
-- url     : https://prove2.me/theorems/9e8d415a-69d1-4425-bf8e-f7738f2d0bfb
-- title:
--   Principal matrix solution Π(t, t₀) of ẋ = A(t)x, Eq. (3.83)
-- statement:
--   Let $I \subseteq \mathbb{R}$ and $A : \mathbb{R} \to \mathbb{R}^{n\times n}$. A two-time matrix function $\Phi : \mathbb{R}\times\mathbb{R} \to \mathbb{R}^{n\times n}$ is the **principal matrix solution** of $\dot x = A(t)x$ on $I$ (the book writes $\Pi(t,t_0)$) if for every $t_0 \in I$ it solves the matrix initial value problem
--   $$\frac{d}{dt}\Phi(t,t_0) = A(t)\,\Phi(t,t_0), \quad t \in I, \qquad \Phi(t_0,t_0) = \mathbb{I}. \qquad (3.83)$$
--
--   Equivalently, the columns of $\Phi(\cdot, t_0)$ are the solutions of (3.79) starting at the canonical basis vectors. For continuous $A$ on an interval such a $\Phi$ exists (Theorem 3.10) and is unique on $I \times I$ (Theorem 3.9 applied column by column), so a statement hypothesising this property speaks about *the* principal matrix solution.
--
--   **Formalization Note.** The derivative is taken entrywise and relative to $I$ (`HasDerivWithinAt` for every entry $(i,j)$), which for matrices is the same as the derivative in any norm. The values of $\Phi(t,t_0)$ for $t$ or $t_0$ outside $I$ are unconstrained and never used.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 82, §3.4, Eq. (3.83)

import Mathlib

namespace TeschlODE.Linear

/-- Teschl (3.83), p. 82: `Φ` is the principal matrix solution of `ẋ = A(t) x` on the interval
`I`: for every `t₀ ∈ I`, the matrix function `t ↦ Φ t t₀` satisfies `Φ̇(t, t₀) = A(t) Φ(t, t₀)`
at every `t ∈ I` (derivative within `I`, entrywise) and `Φ(t₀, t₀) = I`. The book writes `Π`. -/
def IsPrincipalMatrixSolution {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (I : Set ℝ)
    (Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ t₀ ∈ I, Φ t₀ t₀ = 1 ∧
    ∀ t ∈ I, ∀ i j : Fin n, HasDerivWithinAt (fun s => Φ s t₀ i j) ((A t * Φ t t₀) i j) I t

end TeschlODE.Linear


