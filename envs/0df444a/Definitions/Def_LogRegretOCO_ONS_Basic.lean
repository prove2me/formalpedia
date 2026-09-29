-- Prove2me | Definitions.Def_LogRegretOCO_ONS_Basic
-- name    : LogRegretOCO_ONS_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:34:11.362989+00:00
-- url     : https://prove2.me/theorems/cb964ac1-9b0b-4475-9d8a-2aa6b5d2631c
-- title:
--   Quadratic forms, generalized projections and the regularised Gram matrix
-- statement:
--   This file fixes three objects used throughout the analysis of the Online Newton Step.
--
--   1. **Quadratic form.** For a real $n\times n$ matrix $A$ and a vector $v\in\mathbb R^n$, write $\mathrm{quadForm}(A,v)=v^\top A v$.
--
--   2. **Generalized projection.** Let $\mathcal P\subseteq\mathbb R^n$ and let $A$ be an $n\times n$ matrix. A point $z$ is a *generalized projection of $y$ onto $\mathcal P$ with respect to $A$*, written $z=\Pi^{A}_{\mathcal P}(y)$, if
--   $$
--   z\in\mathcal P\quad\text{and}\quad (y-z)^\top A\,(y-z)\le (y-w)^\top A\,(y-w)\ \text{ for every } w\in\mathcal P,
--   $$
--   that is, $z$ is a minimiser over $\mathcal P$ of $x\mapsto (y-x)^\top A(y-x)$. When $A=I_n$ this is the Euclidean projection.
--
--   3. **Regularised Gram matrix.** For $\varepsilon\in\mathbb R$ and vectors $u_1,u_2,\dots\in\mathbb R^n$,
--   $$
--   V_t=\sum_{\tau=1}^{t}u_\tau u_\tau^\top+\varepsilon I_n .
--   $$
--   With $u_\tau=\nabla f_\tau(x_\tau)$ this is the matrix $A_t$ of the Online Newton Step; with general $u_\tau$ it is the matrix $V_t$ of Lemma 11.
--
--   **Formalization Note** Points live in `EuclideanSpace ℝ (Fin n)`, so norms are Euclidean; matrices act on the underlying coordinate vectors. The projection is a predicate rather than a chosen minimiser: when $A$ is only positive semidefinite the argmin can be a set, and every element of it qualifies. Rounds are 1-based; $u_0$ is never used.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 176, Fig. 2; p. 188, §4 (generalized projection); p. 190, Lemma 11 (V_t)

import Mathlib
open Matrix

namespace LogRegretOCO.ONS

/-- The quadratic form `vᵀ A v` of a real `n × n` matrix `A` at a point `v` of `ℝⁿ`
(Euclidean space; `WithLp.ofLp` reads off the coordinate vector). -/
noncomputable def quadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  WithLp.ofLp v ⬝ᵥ (A *ᵥ WithLp.ofLp v)

/-- Generalized projection (Hazan–Agarwal–Kale 2007, Fig. 2 and §4, p. 188):
`z` is *a* generalized projection of `y` onto `P` with respect to `A`, i.e. `z ∈ P` and `z`
minimises `(y − x)ᵀ A (y − x)` over `x ∈ P`. Every minimiser qualifies (any tie-break). -/
def IsGenProj {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (A : Matrix (Fin n) (Fin n) ℝ)
    (y z : EuclideanSpace ℝ (Fin n)) : Prop :=
  z ∈ P ∧ ∀ w ∈ P, quadForm A (y - z) ≤ quadForm A (y - w)

/-- The regularised Gram matrix `V_t = Σ_{τ=1}^t u_τ u_τᵀ + ε Iₙ` of a sequence of vectors
(rounds are 1-based; `u 0` is never used). -/
noncomputable def regGram {n : ℕ} (ε : ℝ) (u : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ τ ∈ Finset.Icc 1 t, Matrix.vecMulVec (WithLp.ofLp (u τ)) (WithLp.ofLp (u τ)) +
    ε • (1 : Matrix (Fin n) (Fin n) ℝ)

end LogRegretOCO.ONS


