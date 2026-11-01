-- Prove2me | Definitions.Def_HomotopyProxVM_tauSeq
-- name    : HomotopyProxVM_tauSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:36:08.390175+00:00
-- url     : https://prove2.me/theorems/de4ff1cf-3a2d-410b-9ea7-aafc38a34aa7
-- title:
--   The update rule (19) of $\tau_k$
-- statement:
--   For $\tau_0\in(0,1)$ and the rate $\sigma$, the parameter is updated by
--
--   $$
--   \tau_k:=1-\frac{(1-\tau_0)\sigma^k}{\tau_0+(1-\tau_0)\sigma^k}.
--   $$
--
--   At $k=0$ this returns $\tau_0$.
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, Theorem 4, (19), p.9

import Mathlib

namespace HomotopyProxVM

/-- The update rule (19) of the parameter:
`τ_k := 1 − (1 − τ₀) σᵏ / (τ₀ + (1 − τ₀) σᵏ)` (Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, Theorem 4, (19), p.9).
At `k = 0` it returns `τ₀` for `τ₀ ∈ (0,1)`. -/
noncomputable def tauSeq (τ₀ σ : ℝ) (k : ℕ) : ℝ :=
  1 - (1 - τ₀) * σ ^ k / (τ₀ + (1 - τ₀) * σ ^ k)

end HomotopyProxVM


