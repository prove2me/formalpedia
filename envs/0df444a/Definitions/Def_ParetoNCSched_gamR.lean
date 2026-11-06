-- Prove2me | Definitions.Def_ParetoNCSched_gamR
-- name    : ParetoNCSched_gamR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:29.460147+00:00
-- url     : https://prove2.me/theorems/80da493e-4cc8-4818-bc19-31e92e6a049c
-- title:
--   The constant $\gamma=R/(R+2)$ of (14)
-- statement:
--   $$\gamma=\frac{R}{R+2}.$$
--
--   **Formalization Note** Named `gamR` to avoid a clash with the rates $\gamma_c,\gamma_r$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.3, Eq. (14), p.28

import Mathlib

namespace ParetoNCSched

/-- **The constant `γ = R/(R + 2)`** of (14). Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.3, (14), p.28.

**Formalization Note.** Named `gamR` to avoid a clash with the rates `γ_c`, `γ_r`. -/
noncomputable def gamR (R : ℝ) : ℝ :=
  R / (R + 2)

end ParetoNCSched


