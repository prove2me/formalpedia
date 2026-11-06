-- Prove2me | Definitions.Def_AnchoredEP_tensorRun
-- name    : AnchoredEP_tensorRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:25.146374+00:00
-- url     : https://prove2.me/theorems/24bc9086-9de9-4bd3-bca4-d752086042d7
-- title:
--   Run of the AEP Tensor Method (Algorithm 3)
-- statement:
--   Given the order $p$, the constant $L_p$, the accuracy $\varepsilon$, an exact subproblem solver, an initial point $z_0$ and a vector $v_0\in H(z_0)$, the run of the **Anchored Extra-Proximal Tensor Method** starts at $(z_0,v_0,A_0=0)$ and applies the outer iteration repeatedly; the regularization parameter is $\lambda=L_p$ and $M_p=(p+1)L_p$. The $k$-th state is the state after $k$ executions of the outer loop body.
--
--   **Formalization Note** If the stop test returns $z_k$ at iteration $k$, or the upper trial returns during iteration $k$, the run is in the returned state from index $k+1$ on.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Algorithm 3, p.37

import Mathlib
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_RunState
import Definitions.Def_AnchoredEP_outerStep

namespace AnchoredEP

/-- **The run of the AEP Tensor Method, Algorithm 3.** Jiang–Yoon, arXiv:2609.30212, Algorithm 3,
p.37: input order `p`, initial point `z₀`, accuracy `ε`, constant `L_p`; initialize with
`v₀ ∈ H(z₀)`, `A₀ = 0`, `λ = L_p`, `M_p = (p + 1)L_p`, and repeat the outer iteration.

`tensorRun F p L ε sol z0 v0 k` is the state after `k` executions of the outer loop body
(`outerStep`), starting from `(z₀, v₀, 0)`; `sol` is the subproblem solver (`IsSubSolver`).

**Formalization Note (iteration count).** `tensorRun … k = .running s` means that outer
iterations `0, …, k − 1` were performed and `s = (z_k, v_k, A_k)`. If the stop test returns `z_k`
at outer iteration `k`, or the upper trial returns `z_{k+1}(ā_k)` during outer iteration `k`,
then `tensorRun … (k + 1)` is `.returned`. -/
noncomputable def tensorRun {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (p : ℕ) (L ε : ℝ)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 v0 : EuclideanSpace ℝ (Fin d)) : ℕ → RunState d
  | 0 => .running ⟨z0, v0, 0⟩
  | k + 1 => outerStep F p L ε sol z0 (tensorRun F p L ε sol z0 v0 k)

end AnchoredEP


