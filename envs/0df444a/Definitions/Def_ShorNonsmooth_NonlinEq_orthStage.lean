-- Prove2me | Definitions.Def_ShorNonsmooth_NonlinEq_orthStage
-- name    : ShorNonsmooth_NonlinEq_orthStage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T13:08:09.083814+00:00
-- url     : https://prove2.me/theorems/0b5f57ac-a123-45c8-9ea2-5c9b5013b4de
-- title:
--   One stage of the gradient orthogonalization method (3.27)
-- statement:
--   Let $\psi_1, \dots, \psi_n : E_n \to \mathbb{R}$ be continuously differentiable, with gradients $g_{\psi_i}(x)$. One **stage** of the gradient orthogonalization method for the system $\psi_i(x) = 0$ starts at a point $x_0$ and performs $n$ steps.
--
--   1. **Step 1.** Compute
--   $$
--   x_1 = x_0 - \frac{\psi_1(x_0)}{\|g_{\psi_1}(x_0)\|^2}\, g_{\psi_1}(x_0).
--   $$
--   2. **Step $k+1$** ($1 \le k < n$). Let $\varphi_{k+1}$ be the projection of $g_{\psi_{k+1}}(x_k)$ on the subspace orthogonal to $g_{\psi_1}(x_0), \dots, g_{\psi_k}(x_{k-1})$, and compute
--   $$
--   x_{k+1} = x_k - \frac{\psi_{k+1}(x_k)}{\|\varphi_{k+1}\|^2}\, \varphi_{k+1}.
--   $$
--
--   The point $x_n$ is the starting point of the next stage: $x_0^{(r+1)} = x_n^{(r)}$. Step 1 is Step $k+1$ with $k = 0$ and $\varphi_1 = g_{\psi_1}(x_0)$.
--
--   **Formalization Note** Indices are zero-based: for $k \in \{0, \dots, n-1\}$, `orthDir ψ x k` is the book's $\varphi_{k+1}$ (the projection of $\nabla\psi_k(x_k)$ on the orthogonal complement of $\operatorname{span}\{\nabla\psi_j(x_j) : j < k\}$), and `IsOrthStage ψ x` says that $x_{k+1}$ is obtained from $x_k$ by the displayed step for every $k < n$. The stage is written as a condition on a sequence $x : \mathbb{N} \to E_n$ (only $x_0, \dots, x_n$ are constrained), so it is determined by $x_0$. **Corrected misprint:** the printed Step 1, formula (3.27a), divides by $\|g_{\psi_1}(x_0)\|$ without the square; the square is restored because (3.27b) and the proof's (3.31)–(3.33), which cover $k = 0$, use it. The book gives no rule for $\varphi_{k+1} = 0$; Lean's $t/0 = 0$ would then repeat the point, but every theorem of the mission applies the step only near the solution, where $\|\varphi_{k+1}\|$ is bounded away from zero (Eq. (3.29)).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 65, Eqs. (3.27a)-(3.27b) (3.27a corrected: squared norm)

import Mathlib

namespace ShorNonsmooth.NonlinEq

/-- Shor (1985), p. 65, Step k + 1 of (3.27): the vector `φ_{k+1}^{(r)}` obtained by projecting
the gradient `g_{ψ_{k+1}}(x_k^{(r)})` on the subspace orthogonal to
`g_{ψ_1}(x_0^{(r)}), …, g_{ψ_k}(x_{k-1}^{(r)})`.

Indexing is zero-based: for `k : Fin n`, `orthDir ψ x k` is the book's `φ_{k+1}`, the projection
of `∇ψ_k(x_k)` (the book's `g_{ψ_{k+1}}(x_k)`) on the orthogonal complement of
`span {∇ψ_j(x_j) : j < k}`. For `k = 0` the span is `{0}` and `orthDir ψ x 0 = ∇ψ_0(x_0)`. -/
noncomputable def orthDir {n : ℕ} (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (k : Fin n) : EuclideanSpace ℝ (Fin n) :=
  (Submodule.span ℝ (Set.range fun j : Fin k.val =>
      gradient (ψ ⟨j.val, j.isLt.trans k.isLt⟩) (x j.val)))ᗮ.starProjection
    (gradient (ψ k) (x k.val))

/-- Shor (1985), p. 65, (3.27a)–(3.27b): the points `x_0, x_1, …, x_n` form one stage of the
gradient orthogonalization method for the system `ψ_i(x) = 0` (3.26):
for every `k < n`,
`x_{k+1} = x_k - ψ_{k+1}(x_k) / ‖φ_{k+1}‖² · φ_{k+1}` (book indexing).
Step 1 (`k = 0`, where `φ_1 = g_{ψ_1}(x_0)`) uses the squared norm, as (3.27b) and the proof's
(3.31)–(3.33) do; the printed (3.27a) omits the square (a misprint). The next stage starts from
`x_n`, so a stage is determined by `x 0`; entries `x k` for `k > n` are unconstrained. -/
def IsOrthStage {n : ℕ} (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ k : Fin n, x (k.val + 1) =
    x k.val - (ψ k (x k.val) / ‖orthDir ψ x k‖ ^ 2) • orthDir ψ x k

end ShorNonsmooth.NonlinEq


