-- Prove2me | Definitions.Def_RollingProbeQN_Convex_run
-- name    : RollingProbeQN_Convex_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:25:39.365809+00:00
-- url     : https://prove2.me/theorems/f392516e-41c4-4123-9ac8-7d4a47e97237
-- title:
--   The run of Algorithm 1 (RP-QNPE) with Subroutine 1.1 against an oracle
-- statement:
--   The run of Algorithm 1 against an oracle $G$ from a start $x_0$: the state at iteration $0$ is $x_0=z_0$, $A_0=0$, $M_{-1}=0$ with the oracle value $G(x_0)$ (the first query), and the state at iteration $k+1$ is one step of the state at iteration $k$. Along this run, $x_k$, $z_k$ and $A_k$ are the paper's iterates when $G=\nabla f$.
--
--   **Formalization Note** The run is a function of the oracle only, which is how "uses at most three gradients per iteration" is stated.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Algorithm 1, p. 9

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_step

namespace RollingProbeQN.Convex

/-- **The run of Algorithm 1 (RP-QNPE) with Subroutine 1.1 against an oracle `G`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 1, p. 9: "Initialize `x0 = z0`, `A0 = 0`, `M−1 = 0`, and compute `∇f(x0)`. For
`k = 0, 1, …`: […]".

`run cfg G x₀ k` is the state at the start of iteration `k`; `run cfg G x₀ 0` has `x = z = x₀`,
`A = 0`, `M = 0`, the oracle answer `G x₀` (the first query) and no recorded displacement.

**Formalization Note.** The run is a function of the oracle `G` (reading R3); the theorems take
`G = gradient f`. -/
noncomputable def run {d χ : ℕ} (cfg : Config d χ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x₀ : EuclideanSpace ℝ (Fin d)) :
    ℕ → RunState d
  | 0 => { x := x₀, z := x₀, A := 0, M := 0, gx := G x₀, δ := fun _ => 0, done := false }
  | k + 1 => step cfg G k (run cfg G x₀ k)

end RollingProbeQN.Convex


