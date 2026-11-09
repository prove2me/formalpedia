-- Prove2me | Definitions.Def_MWCSherali_flowDiv
-- name    : MWCSherali_flowDiv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:09.533401+00:00
-- url     : https://prove2.me/theorems/02381714-c724-4626-9e78-1a92bc3c7652
-- title:
--   The flow-conservation functional $I^R_a(\varphi)$
-- statement:
--   For commodity-$a$ flow measures $\{F^R_{a,i}\mid i\neq a\}$ supported on a region $R$ and a test function $\varphi$,
--
--   $$I^R_a(\varphi)=\sum_{i\neq a}\int_{\Delta_4}\nabla\varphi\cdot(e_a-e_i)\,dF^R_{a,i},$$
--
--   the contribution of the region to the left-hand side of the continuous flow-conservation equation. Section 4 computes it for the corners, simplex edges, tubes and central region.
--
--   **Formalization Note** Defined for any $k$; the family $(F^R_{a,i})_i$ is passed as a function of the direction $i$, and its value at $i=a$ is ignored.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §4, p.32 (I^R_a)

import Mathlib

namespace MWCSherali

open MeasureTheory

/-- **The flow-conservation functional `I^R_a(φ)`.** Brakensiek–Huang–Potechin–Zwick,
arXiv:2611.05511 (version of Nov. 3, 2026), §4, p.32: for flow measures `{F^R_{a,i} | i ≠ a}` of
commodity `a` supported on a region `R`,
`I^R_a(φ) = ∑_{i ≠ a} ∫_{Δ_4} ∇φ · (e_a − e_i) dF^R_{a,i}`,
the left-hand side of the continuous flow conservation equation (it is the same functional as in
(Continuous-Flow-LP), p.28).

**Formalization Note.** `flowDiv k F a φ` takes the family `F i = F^R_{a,i}` of commodity `a`'s
flow measures in the region (direction `i`); `F a` is ignored. `∇φ(t) · (e_a − e_i)` is
`fderiv ℝ φ t (e_a − e_i)` with `e_a = Pi.single a 1`; indices are 0-based. -/
noncomputable def flowDiv (k : ℕ) (F : Fin k → Measure (Fin k → ℝ)) (a : Fin k)
    (φ : (Fin k → ℝ) → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (· ≠ a), ∫ t, fderiv ℝ φ t (Pi.single a 1 - Pi.single i 1) ∂(F i)

end MWCSherali


