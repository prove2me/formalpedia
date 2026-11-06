-- Prove2me | Definitions.Def_MatchedUCLB_psi
-- name    : MatchedUCLB_psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:12.95507+00:00
-- url     : https://prove2.me/theorems/865e5e4d-9523-41b8-bae3-baf2495db6a7
-- title:
--   The smooth positive part $\psi_\delta(t)=\int_{-1}^1(t-\delta u)_+\varphi(u)\,du$
-- statement:
--   For a smoothing width $\delta>0$ and $t\in\mathbb R$, with $t_+=\max\{t,0\}$, the **smooth positive part** is
--
--   $$
--   \psi_\delta(t)=\int_{-1}^{1}(t-\delta u)_+\,\varphi(u)\,du .
--   $$
--
--   It is the average of the positive part over a window of width $\delta$; it equals $t_+$ when $|t|\ge\delta$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Definition 4.1, Eq. (4.1), p.5

import Mathlib
import Definitions.Def_MatchedUCLB_phi

namespace MatchedUCLB

/-- **The smooth positive part `ψ_δ`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Definition 4.1, Eq. (4.1), p.5: "For
`t_+ := max{t, 0}` and smoothing width `δ > 0`, define `ψ_δ(t) := ∫_{−1}^1 (t − δu)_+ φ(u) du`".

**Formalization Note.** The integrand `max (t − δu) 0 · φ(u)` is continuous in `u`, so the interval
integral is a genuine Riemann integral (no junk value). -/
noncomputable def psi (δ t : ℝ) : ℝ :=
  ∫ u in (-1 : ℝ)..1, (max (t - δ * u) 0 * phi u)

end MatchedUCLB


