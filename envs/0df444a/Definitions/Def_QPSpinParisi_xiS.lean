-- Prove2me | Definitions.Def_QPSpinParisi_xiS
-- name    : QPSpinParisi_xiS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:50.552353+00:00
-- url     : https://prove2.me/theorems/254d1151-089e-4e02-97b8-7a0ff925dc2f
-- title:
--   The mixture function $\xi(q)=\sum_{p\ge2}c_p^2q^p$
-- statement:
--   For real coefficients $(c_p)_{p\ge2}$, the mixture function is
--   $$\xi(q)=\sum_{p\ge2}c_p^2q^p.$$
--   It records the covariance of the mean-field models of the mission and enters every Parisi functional.
--
--   **Formalization Note** The series is written explicitly, reindexed by $p+2$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.4 (PDF p.4)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The mixture function `ξ(q) = ∑_{p≥2} c_p² q^p` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.4, PDF p.4).

**Formalization Note** The series is written with `p + 2` in place of `p`. Under `MixHyp c` it converges for
`|q| ≤ 2`, and it is only evaluated on `[-1, 1]`, except in `PiStep`, which enters only finite mixtures. -/
noncomputable def xiS (c : ℕ → ℝ) (q : ℝ) : ℝ :=
  ∑' p : ℕ, c (p + 2) ^ 2 * q ^ (p + 2)

end QPSpinParisi


