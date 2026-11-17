-- Prove2me | Definitions.Def_AnchoredEP_Supplement_newtonRun
-- name    : AnchoredEP_Supplement_newtonRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:10:44.312983+00:00
-- url     : https://prove2.me/theorems/7287a218-bf1c-49f5-a4af-b0d7f02338de
-- title:
--   Run of the AEP Newton method (Algorithm 1)
-- statement:
--   Algorithm 1 (Anchored Extra-Proximal Newton) takes an initial point $z_0\in\operatorname{dom}H$, a target accuracy $\varepsilon>0$ and the Jacobian Lipschitz constant $L_2>0$, chooses $v_0\in H(z_0)$, sets $A_0=0$, and repeats the outer iteration.
--
--   The run after $k$ executions of the outer loop body is either a running state $(z_k,v_k,A_k)$, meaning that $k$ accepted AEP Newton updates have been made, or a returned point $\hat z$ with its certificate $\hat v\in H(\hat z)$. A return by the stop test or by the upper trial during iteration $k$ (after $k$ accepted updates) shows up as a returned state after $k+1$ executions.
--
--   **Formalization Note** The subproblem solver is a parameter (see the exact-solver definition).
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Algorithm 1, p.8

import Mathlib
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_RunState
import Definitions.Def_AnchoredEP_Supplement_newtonOuterStep

namespace AnchoredEP.Supplement

/-- **The run of the AEP Newton method, Algorithm 1.** Jiang–Yoon, arXiv:2609.30212, Algorithm 1,
p.8: input `z₀ ∈ dom H`, `ε > 0`, `L₂ > 0`; initialize with `v₀ ∈ H(z₀)` and `A₀ = 0`, and repeat
the outer iteration.

`newtonRun F L ε sol z0 v0 k` is the state after `k` executions of the outer loop body
(`newtonOuterStep`), starting from `(z₀, v₀, 0)`; `sol` is the subproblem solver
(`IsNewtonSolver`).

**Formalization Note (iteration count).** `newtonRun … k = .running s` means that the outer
iterations `0, …, k − 1` each performed one accepted AEP Newton update and `s = (z_k, v_k, A_k)`.
If the stop test returns `z_k` at iteration `k`, or the upper trial returns `z_{k+1}(ā_k)` during
iteration `k`, then `newtonRun … (k + 1)` is `.returned`, after `k` accepted updates. -/
noncomputable def newtonRun {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L ε : ℝ)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 v0 : EuclideanSpace ℝ (Fin d)) : ℕ → RunState d
  | 0 => .running ⟨z0, v0, 0⟩
  | k + 1 => newtonOuterStep F L ε sol z0 (newtonRun F L ε sol z0 v0 k)

end AnchoredEP.Supplement


