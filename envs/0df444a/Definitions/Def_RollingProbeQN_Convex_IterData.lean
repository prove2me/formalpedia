-- Prove2me | Definitions.Def_RollingProbeQN_Convex_IterData
-- name    : RollingProbeQN_Convex_IterData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:07.826068+00:00
-- url     : https://prove2.me/theorems/6e638999-eb8c-48c5-9f8d-7f4f4aca7f96
-- title:
--   The quantities computed by one iteration of Algorithm 1
-- statement:
--   The record of one iteration $k$ of Algorithm 1: the probe radius $\tau_k$ and probe point $x_k+\tau_kv_{g_{i_k}}$, the refreshed matrix $M_k$, the model $B_k$, the certificate $\bar E_k$, the stepsize $\lambda_k$ with the number of surrogate evaluations, the weight $a_k$, the mass $A_{k+1}$, the extrapolated point $y_k$, the model step $r_k$, the new iterate $x_{k+1}$, the oracle value at $x_{k+1}$ and the momentum point $z_{k+1}$.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Algorithm 1, (4), (5), Subroutine 1.1, pp. 9–10

import Mathlib

namespace RollingProbeQN.Convex

/-- **The quantities one iteration of Algorithm 1 computes.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 1, (4), (5) and Subroutine 1.1, pp. 9–10.

Fields: the probe radius `τ_k`, the probe point `x_k + τ_k v_{g_{i_k}}`, the stored matrix `M_k`, the
model `B_k`, the certificate `Ē_k`, the stepsize `λ_k` and the number of evaluations of `Ψ̂_k`
spent by Subroutine 1.1, the weight `a_k`, the mass `A_{k+1}`, the point `y_k`, the model step
`r_k`, the new iterate `x_{k+1}`, the oracle answer at `x_{k+1}` and the momentum point `z_{k+1}`. -/
structure IterData (d : ℕ) where
  /-- the probe radius `τ_k` -/
  τ : ℝ
  /-- the probe point `x_k + τ_k v_{g_{i_k}}` -/
  probe : EuclideanSpace ℝ (Fin d)
  /-- the refreshed matrix `M_k` -/
  M : Matrix (Fin d) (Fin d) ℝ
  /-- the model `B_k` -/
  B : Matrix (Fin d) (Fin d) ℝ
  /-- the certificate `Ē_k` -/
  Ebar : ℝ
  /-- the stepsize `λ_k` -/
  lam : ℝ
  /-- the number of evaluations of `Ψ̂_k` in Subroutine 1.1 -/
  nEval : ℕ
  /-- the weight `a_k` -/
  a : ℝ
  /-- the mass `A_{k+1}` -/
  A' : ℝ
  /-- the extrapolated point `y_k` -/
  y : EuclideanSpace ℝ (Fin d)
  /-- the model step `r_k` -/
  r : EuclideanSpace ℝ (Fin d)
  /-- the new iterate `x_{k+1}` -/
  x' : EuclideanSpace ℝ (Fin d)
  /-- the oracle answer at `x_{k+1}` -/
  gx' : EuclideanSpace ℝ (Fin d)
  /-- the momentum point `z_{k+1}` -/
  z' : EuclideanSpace ℝ (Fin d)

end RollingProbeQN.Convex


