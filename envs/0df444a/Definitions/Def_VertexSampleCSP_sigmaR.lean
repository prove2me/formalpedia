-- Prove2me | Definitions.Def_VertexSampleCSP_sigmaR
-- name    : VertexSampleCSP_sigmaR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:28.317197+00:00
-- url     : https://prove2.me/theorems/3cd96c29-c11d-44ce-b3ac-7bbd3fe3544e
-- title:
--   The sum $\sigma_r(\rho)=\sum_{s<r}\rho^{-s}$
-- statement:
--   For $0<\rho\le1$ and $r\ge1$,
--
--   $$\sigma_r(\rho)=\sum_{s=0}^{r-1}\rho^{-s}.$$
--
--   For $\rho\ge\tfrac12$ it is at most $2^r-1$. It is the factor that the telescoping of the polynomial $P$ contributes to the comparison of the two optima.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix A, "Notation", p.13 (PDF p.15)

import Mathlib

namespace VertexSampleCSP

/-- **`σ_r(ρ)`.** Chang, *Optimal Vertex Sampling for Constraint Satisfaction Problems*, STOC 2027
submission (manuscript sha256 1e0edd23…), Appendix A, "Notation", p.13 (PDF p.15): "For 0 < ρ ≤ 1 and
r ≥ 1 let σr(ρ) = Σ_{s=0}^{r−1} ρ^{−s}, so that σr(ρ) ≤ 2^r − 1 for ρ ≥ 1/2." -/
noncomputable def sigmaR (r : ℕ) (ρ : ℝ) : ℝ :=
  ∑ s ∈ Finset.range r, (ρ ^ s)⁻¹

end VertexSampleCSP


