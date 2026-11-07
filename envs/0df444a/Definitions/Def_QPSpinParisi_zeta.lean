-- Prove2me | Definitions.Def_QPSpinParisi_zeta
-- name    : QPSpinParisi_zeta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:25.126555+00:00
-- url     : https://prove2.me/theorems/d9481f7c-48f6-4a98-ace3-9aa1da6305f4
-- title:
--   $\zeta=\xi''$ as the series $\sum_{p\ge2}p(p-1)c_p^2q^{p-2}$
-- statement:
--   The second derivative of the mixture function:
--   $$\zeta(q)=\xi''(q)=\sum_{p\ge2}p(p-1)\,c_p^2\,q^{p-2}.$$
--   On $[0,1]$ it is nonnegative and continuous, and $\sqrt{\zeta}$ is the diffusion coefficient of the control problems.
--
--   **Formalization Note** It is the explicit series, reindexed by $p+2$, with $\zeta(0)=2c_2^2$ from Lean's $0^0=1$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.4 (PDF p.4); p.16 (PDF p.16)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- `ζ(q) = ξ''(q) = ∑_{p≥2} p(p-1) c_p² q^{p-2}` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.4, PDF p.4; the series on p.16, PDF p.16).

**Formalization Note** It is the explicit series, with `p + 2` in place of `p`, not an iterated `deriv`.
Lean's `0 ^ 0 = 1` gives `ζ(0) = 2 c₂²`, the correct value. -/
noncomputable def zeta (c : ℕ → ℝ) (q : ℝ) : ℝ :=
  ∑' p : ℕ, ((p : ℝ) + 2) * ((p : ℝ) + 1) * c (p + 2) ^ 2 * q ^ p

end QPSpinParisi


