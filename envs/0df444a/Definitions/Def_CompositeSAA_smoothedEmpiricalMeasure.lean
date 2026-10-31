-- Prove2me | Definitions.Def_CompositeSAA_smoothedEmpiricalMeasure
-- name    : CompositeSAA_smoothedEmpiricalMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:46.495346+00:00
-- url     : https://prove2.me/theorems/95bc8e39-96d4-4d9f-8da2-7d9cdeedd6c7
-- title:
--   Smoothed empirical measure $P_N*\mu_N$ (12)
-- statement:
--   For a sample $x_1,\dots,x_N$ with empirical measure $P_N$ and a smoothing measure $\mu_N$, the **smoothed empirical measure** is the convolution
--
--   $$
--   P_N*\mu_N=\frac1N\sum_{i=1}^N(\text{law of }x_i+Z),\qquad Z\sim\mu_N,
--   $$
--
--   so that $\int g\,d(P_N*\mu_N)=\frac1N\sum_{i=1}^N\int g(x_i+z)\,d\mu_N(z)$ is the smooth estimator (12) of $\mathbb E[g(X)]$.
--
--   **Formalization Note** Written as $\frac1N\sum_i$ of the image of $\mu_N$ under $z\mapsto x_i+z$; the sample is 0-based, and the measure is $0$ at $N=0$.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, display (12), p.9

import Mathlib

open MeasureTheory Finset
open scoped ENNReal

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, display (12), p.9: the smoothed empirical measure
`P_N ∗ µ_N`, the convolution of the empirical measure of the sample `x_1, …, x_N` with the
smoothing measure `µ_N`,

`P_N ∗ µ_N = (1/N) Σ_{i=1}^N (law of x_i + Z, Z ∼ µ_N)`,

so that `∫ g d(P_N ∗ µ_N) = (1/N) Σ_i ∫ g(x_i + z) dµ_N(z)`, the smooth estimator (12).

**Formalization Note** Written as `(1/N) Σ_i µ_N.map (x_i + ·)`, not with `Measure.conv`. The
sample `x_1, …, x_N` is `xs 0, …, xs (N − 1)`; at `N = 0` the measure is `0`. -/
noncomputable def smoothedEmpiricalMeasure {m : ℕ} (μN : Measure (EuclideanSpace ℝ (Fin m)))
    (N : ℕ) (xs : ℕ → EuclideanSpace ℝ (Fin m)) : Measure (EuclideanSpace ℝ (Fin m)) :=
  (N : ℝ≥0∞)⁻¹ • ∑ i ∈ range N, μN.map (fun z => xs i + z)

end CompositeSAA


