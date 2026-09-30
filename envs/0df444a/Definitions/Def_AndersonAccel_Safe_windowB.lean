-- Prove2me | Definitions.Def_AndersonAccel_Safe_windowB
-- name    : AndersonAccel_Safe_windowB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:04:53.807877+00:00
-- url     : https://prove2.me/theorems/0308697c-d057-4dac-8dc6-6dfddf3d44bf
-- title:
--   Powell-regularized rank-one window matrices $B^i$ of Eqs. (3.2), (3.3), (3.5)
-- statement:
--   Fix $\bar\theta\in\mathbb R$ and two finite sequences $s_0,s_1,\dots$ and $y_0,y_1,\dots$ in $\mathbb R^n$ (a memory window, re-indexed to start at $0$).
--
--   1. **Orthogonalization (3.2).** $\hat s_i=s_i-\sum_{j<i}\dfrac{\hat s_j^T s_i}{\hat s_j^T\hat s_j}\,\hat s_j$ (Gram–Schmidt without normalization).
--   2. **Matrices (3.5).** $B^0=I$ and, for $i\ge0$,
--   $$B^{i+1}=B^i+\frac{(\tilde y_i-B^i s_i)\,\hat s_i^T}{\hat s_i^T s_i},$$
--   where the **Powell-regularized** vector is (3.3)
--   $$\tilde y_i=\theta^i y_i+(1-\theta^i)B^i s_i,\qquad \theta^i=\phi_{\bar\theta}(\eta^i),\qquad \eta^i=\frac{\hat s_i^T (B^i)^{-1}y_i}{\|\hat s_i\|_2^2}.$$
--
--   For a window of length $m_k$ the paper's $B_k$ is $B^{m_k}$, and $H_k=B_k^{-1}$. These matrices are the approximate Jacobians of the residual built by type-I Anderson acceleration; the Powell weight is chosen so that each update keeps them invertible.
--
--   **Formalization Note** Matrices are continuous linear maps of `EuclideanSpace ℝ (Fin n)`, so $\|\cdot\|$ is the induced $\ell_2$ operator norm, and $u\hat s^T$ is `rankOne ℝ u ŝ` ($z\mapsto\langle\hat s,z\rangle u$). The orthogonalization is Mathlib's `InnerProductSpace.gramSchmidt ℝ s`, which is formula (3.2) (a zero $\hat s_j$ contributes nothing, as the formula with $0/0=0$ does). $(B^i)^{-1}$ is `Ring.inverse`, which is $0$ for a singular map; Lemma 3.2 shows every $B^i$ is invertible when the updates are well-defined. In Lean $x/0=0$, so an update with $\hat s_i^Ts_i=0$ adds nothing; the paper excludes that case by assumption. The window in the paper is $s_{k-m_k},\dots,s_{k-1}$; since the lemmas hold for arbitrary sequences, the offset $k-m_k$ carries no content and the window starts at index $0$ here.
-- source:
--   Zhang, O'Donoghue, Boyd, SIAM J. Optim. 30 (2020), p. 3176, Eqs. (3.2), (3.3), (3.4), (3.5) and Lemma 3.2; p. 3177 (H_k = B_k^{-1})

import Mathlib
import Definitions.Def_AndersonAccel_Safe_Basic

namespace AndersonAccel.Safe

open InnerProductSpace

/-- The orthogonalization (3.2) of a window `s 0, s 1, …` (Gram–Schmidt without normalization):
`ŝ_i = s_i - ∑_{j < i} (ŝ_jᵀ s_i / ŝ_jᵀ ŝ_j) ŝ_j` (p. 3176). -/
noncomputable def windowShat {n : ℕ} (s : ℕ → EuclideanSpace ℝ (Fin n)) (i : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  InnerProductSpace.gramSchmidt ℝ s i

/-- The Powell-regularized rank-one window matrices `B^i` of Eqs. (3.3)–(3.5) (p. 3176), for a window
`s 0, …, s (m_k - 1)`, `y 0, …, y (m_k - 1)` re-indexed to start at `0`:
`B^0 = I`, `B^{i+1} = B^i + (ỹ_i - B^i s_i) ŝ_iᵀ / (ŝ_iᵀ s_i)`, where
`ỹ_i = θ^i y_i + (1 - θ^i) B^i s_i`, `θ^i = φ_θ̄(η^i)`, `η^i = ŝ_iᵀ (B^i)⁻¹ y_i / ‖ŝ_i‖²`. -/
noncomputable def windowB {n : ℕ} (θbar : ℝ) (s y : ℕ → EuclideanSpace ℝ (Fin n)) :
    ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  | 0 => 1
  | i + 1 =>
    let B := windowB θbar s y i
    let sh := windowShat s i
    let η := inner ℝ sh ((Ring.inverse B) (y i)) / ‖sh‖ ^ 2
    let θ := phiTheta θbar η
    let yt := θ • y i + (1 - θ) • B (s i)
    B + (inner ℝ sh (s i))⁻¹ • rankOne ℝ (yt - B (s i)) sh

end AndersonAccel.Safe


