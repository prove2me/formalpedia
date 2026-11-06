-- Prove2me | Definitions.Def_MatchedUCLB_Gam
-- name    : MatchedUCLB_Gam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:28.243778+00:00
-- url     : https://prove2.me/theorems/3d951132-e937-450e-ae5c-6c98f9214ca1
-- title:
--   The chain endpoint gradient $\Gamma_j=\lambda\tau_j^{q-1}/\sqrt m$
-- statement:
--   For $\lambda>0$, a scale $\tau>0$ and a chain length $m$, the **chain endpoint gradient** is $\Gamma=\lambda\tau^{q-1}/\sqrt m$, the size of the gradient of the chain at its endpoint along the starting direction.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Sec. 4.3, p.8; Definition E.1, p.83

import Mathlib

namespace MatchedUCLB

/-- **The chain's endpoint gradient `Γ_j = λ τ_j^{q−1}/√m`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Sec. 4.3, p.8 ("The
remaining chain gradient is `∇Q_j(h_j) = Γ_j v_j`, with `Γ_j = λτ_j^{q−1}/√m`"), and
Definition E.1, p.83. -/
noncomputable def Gam (q : ℝ) (m : ℕ) (lam τ : ℝ) : ℝ :=
  lam * τ ^ (q - 1) / Real.sqrt m

end MatchedUCLB


