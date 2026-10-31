-- Prove2me | Definitions.Def_DualRCD_histAvg
-- name    : DualRCD_histAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:44:39.736337+00:00
-- url     : https://prove2.me/theorems/8a3f9f9a-511f-4f31-a96d-67ce367d3e91
-- title:
--   Expectation over the first $k$ uniform block indices
-- statement:
--   For a function $F$ of the history $t\in[m]^k$, the expectation over independent indices $i_0,\dots,i_{k-1}$, uniform on $[m]$, is
--   $$
--   \mathbb E[F]=\frac1{m^k}\sum_{t\in[m]^k}F(t).
--   $$
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, p.5 (uniform distribution on [m]) and the RCD box, p.15

import Mathlib

namespace DualRCD

/-- The expectation `E[F(i₀, …, i_{k−1})] = m⁻ᵏ Σ_{t ∈ [m]ᵏ} F(t)` over `k` independent indices,
uniform on `[m]` (Necoara & Fercoq, arXiv:1911.06014v1, p.5 and the RCD box, p.15). -/
noncomputable def histAvg {m : ℕ} (k : ℕ) (F : (Fin k → Fin m) → ℝ) : ℝ :=
  1 / (m : ℝ) ^ k * ∑ t, F t

end DualRCD


