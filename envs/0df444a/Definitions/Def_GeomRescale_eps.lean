-- Prove2me | Definitions.Def_GeomRescale_eps
-- name    : GeomRescale_eps
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:06.200444+00:00
-- url     : https://prove2.me/theorems/e710cd9c-4909-4638-87ea-aa25f752a40a
-- title:
--   The parameter $\varepsilon = 1/(20n)$
-- statement:
--   Algorithm Rescaling-SFM uses
--
--   $$\varepsilon = \frac{1}{20n}.$$
--
--   This choice gives the determinant factor $16/9$ of Lemma 3.12.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §3.2, p.9

import Mathlib

namespace GeomRescale

/-- The parameter `ε = 1/(20n)` of Algorithm Rescaling-SFM (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §3.2, p.9). -/
noncomputable def eps (n : ℕ) : ℝ :=
  1 / (20 * (n : ℝ))

end GeomRescale


