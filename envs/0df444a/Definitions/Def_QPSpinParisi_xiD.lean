-- Prove2me | Definitions.Def_QPSpinParisi_xiD
-- name    : QPSpinParisi_xiD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:19.47221+00:00
-- url     : https://prove2.me/theorems/a4d3a7be-2ef5-4faf-9158-416008155f53
-- title:
--   The first derivative $\xi'(q)=\sum_{p\ge2}pc_p^2q^{p-1}$
-- statement:
--   The derivative of the mixture function, given by its series:
--   $$\xi'(q)=\sum_{p\ge2}p\,c_p^2\,q^{p-1}.$$
--   It sets the variances in the cascade recursion and appears in the derivative formula for the free energy.
--
--   **Formalization Note** It is the explicit series, reindexed by $p+2$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.16 (PDF p.16)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The first derivative `ξ'(q) = ∑_{p≥2} p c_p² q^{p-1}` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.16, PDF p.16).

**Formalization Note** It is the explicit series, with `p + 2` in place of `p`, not `deriv` of `xiS`. -/
noncomputable def xiD (c : ℕ → ℝ) (q : ℝ) : ℝ :=
  ∑' p : ℕ, ((p : ℝ) + 2) * c (p + 2) ^ 2 * q ^ (p + 1)

end QPSpinParisi


