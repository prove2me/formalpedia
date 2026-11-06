-- Prove2me | Definitions.Def_RollingProbeQN_Convex_RunState
-- name    : RollingProbeQN_Convex_RunState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:05.087446+00:00
-- url     : https://prove2.me/theorems/ce09cf38-a541-4c6d-8043-f7a319f1e5cb
-- title:
--   The state of Algorithm 1 at the start of an iteration
-- statement:
--   The state of Algorithm 1 at the start of iteration $k$ consists of the iterate $x_k$, the momentum point $z_k$, the mass $A_k$, the stored matrix $M_{k-1}$, the cached oracle value $\nabla f(x_k)$, the displacements $\delta_j=\|y_j-x_j\|+\|r_j\|$ for $j<k$, and a flag recording whether Step 1 has returned. The initial state is $x_0=z_0$, $A_0=0$, $M_{-1}=0$, with $\nabla f(x_0)$ computed.
--
--   **Formalization Note** After the return of Step 1 at a zero gradient the state is frozen.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Algorithm 1, p. 9

import Mathlib

namespace RollingProbeQN.Convex

/-- **The state of Algorithm 1 at the start of iteration `k`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 1, p. 9: "Initialize `x0 = z0`, `A0 = 0`, `M−1 = 0`, and compute `∇f(x0)`".

Fields: the iterate `x = x_k`, the momentum point `z = z_k`, the mass `A = A_k`, the stored matrix
`M = M_{k−1}`, the cached oracle value `gx` at `x_k` (the paper's cached `∇f(x_k)`), the
displacements `δ j = δ_j = m_j + ‖r_j‖` for `j < k`, and the flag `done`, set when Step 1 has
returned.

**Formalization Note.** Reading R2: after the return of Step 1 at a zero gradient the state is
frozen. Entries `δ j` with `j ≥ k` are `0` and unused. -/
structure RunState (d : ℕ) where
  /-- the iterate `x_k` -/
  x : EuclideanSpace ℝ (Fin d)
  /-- the momentum point `z_k` -/
  z : EuclideanSpace ℝ (Fin d)
  /-- the mass `A_k` -/
  A : ℝ
  /-- the stored matrix `M_{k−1}` -/
  M : Matrix (Fin d) (Fin d) ℝ
  /-- the cached oracle answer at `x_k` -/
  gx : EuclideanSpace ℝ (Fin d)
  /-- the displacements `δ_j`, `j < k` -/
  δ : ℕ → ℝ
  /-- whether Step 1 has returned -/
  done : Bool

end RollingProbeQN.Convex


