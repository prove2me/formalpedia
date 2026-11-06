-- Prove2me | Definitions.Def_RollingProbeQN_Convex_iterAt
-- name    : RollingProbeQN_Convex_iterAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:26:28.229104+00:00
-- url     : https://prove2.me/theorems/e74fa599-00ff-4353-8a76-8134fb78c0ef
-- title:
--   The quantities of iteration $k$ along the run
-- statement:
--   The values $\tau_k$, $M_k$, $B_k$, $\bar E_k$, $\lambda_k$, $a_k$, $A_{k+1}$, $y_k$, $r_k$, $x_{k+1}$, $z_{k+1}$ that iteration $k$ of the run computes from the state at the start of iteration $k$. They are the paper's quantities whenever iteration $k$ is executed.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Algorithm 1, pp. 9–10

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_run

namespace RollingProbeQN.Convex

/-- **The quantities of iteration `k` along the run.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 1, pp. 9–10.

`iterAt cfg G x₀ k` is `iterData` at the state `run cfg G x₀ k`: the values `τ_k`, `M_k`, `B_k`,
`Ē_k`, `λ_k`, `a_k`, `A_{k+1}`, `y_k`, `r_k`, `x_{k+1}`, `z_{k+1}` of iteration `k`. They are the
paper's quantities when iteration `k` is executed (`Active`). -/
noncomputable def iterAt {d χ : ℕ} (cfg : Config d χ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x₀ : EuclideanSpace ℝ (Fin d))
    (k : ℕ) : IterData d :=
  iterData cfg G k (run cfg G x₀ k)

end RollingProbeQN.Convex


