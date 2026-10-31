-- Prove2me | Definitions.Def_CompositeSAA_SmoothingAssumption
-- name    : CompositeSAA_SmoothingAssumption
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:49.809068+00:00
-- url     : https://prove2.me/theorems/81d253b1-04b1-4e37-8f72-887073707333
-- title:
--   Assumption 6 on the smoothing measures $\mu_N$
-- statement:
--   A sequence of measures $\mu_N$ on $\mathbb R^m$ satisfies **Assumption 6** if each $\mu_N$ is a probability measure and
--
--   1. $\mu_N\to\delta(0)$ weakly as $N\to\infty$;
--   2. $\int\|z\|\,d\mu_N(z)<\infty$ for every $N$, and
--
--   $$
--   \lim_{r\to\infty}\ \limsup_{N\to\infty}\int_{\|z\|>r}\|z\|\,d\mu_N(z)=0 .
--   $$
--
--   It holds, for example, when all $\mu_N$ have bounded support, or for kernels $d\mu_N(z)=h_N^{-m}K(z/h_N)\,dz$ with $h_N\to0$ and a kernel with a finite first moment.
--
--   **Formalization Note** The $\mu_N$ are deterministic ("independent of $P_N$"). Weak convergence means $\int g\,d\mu_N\to g(0)$ for every bounded continuous $g$. The inner limit is read as a limit superior (the printed form presupposes that the limit exists), with the tail integrals in $[0,\infty]$.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, Assumption 6, p.9

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, Assumption 6, p.9: the smoothing measures `µ_N` on
`ℝ^m` are normalized (`µ_N(ℝ^m) = 1`) and satisfy

* `µ_N → δ(0)` weakly as `N → ∞`;
* `∫ ‖z‖ dµ_N(z) < ∞` for every `N`, and
  `lim_{r→∞} lim_{N→∞} ∫_{‖z‖>r} ‖z‖ dµ_N(z) = 0`.

**Formalization Note**
1. The `µ_N` are a deterministic sequence of probability measures; "independent of `P_N`" is read
   as: they do not depend on the sample.
2. Weak convergence is written out: `∫ g dµ_N → g(0)` for every bounded continuous `g`.
3. The inner `lim_{N→∞}` is read as `limsup_{N→∞}` (the printed form presupposes that the limit
   exists), and the tail integrals are lower Lebesgue integrals in `ℝ≥0∞`, so that the limsup
   is never a junk value. -/
structure SmoothingAssumption {m : ℕ} (μ : ℕ → Measure (EuclideanSpace ℝ (Fin m))) : Prop where
  isProb : ∀ N, IsProbabilityMeasure (μ N)
  tendsto_dirac : ∀ g : EuclideanSpace ℝ (Fin m) →ᵇ ℝ,
    Tendsto (fun N => ∫ z, g z ∂(μ N)) atTop (𝓝 (g 0))
  moment_finite : ∀ N, ∫⁻ z, ‖z‖ₑ ∂(μ N) < ∞
  tail : Tendsto (fun r : ℝ => limsup (fun N => ∫⁻ z in {z | r < ‖z‖}, ‖z‖ₑ ∂(μ N)) atTop)
    atTop (𝓝 0)

end CompositeSAA


