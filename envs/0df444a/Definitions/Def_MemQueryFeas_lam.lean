-- Prove2me | Definitions.Def_MemQueryFeas_lam
-- name    : MemQueryFeas_lam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:41.046192+00:00
-- url     : https://prove2.me/theorems/68bde78b-b224-4b1e-a0d8-e6e88643b924
-- title:
--   The ratios $\lambda_p=d^{-p}$
-- statement:
--   $\lambda_p=d^{-p}$, the factor between consecutive accuracies of layer $p$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), §3.1, p.7 (PDF p.8)

import Mathlib

namespace MemQueryFeas

/-- **The ratio `λ_p = d^{−p}`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), §3.1, p.7 (PDF p.8): "`λ_p := d^{−p}`". -/
noncomputable def lam (d p : ℕ) : ℝ := (d : ℝ) ^ (-(p : ℝ))

end MemQueryFeas


