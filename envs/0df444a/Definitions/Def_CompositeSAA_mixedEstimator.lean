-- Prove2me | Definitions.Def_CompositeSAA_mixedEstimator
-- name    : CompositeSAA_mixedEstimator
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:34.135296+00:00
-- url     : https://prove2.me/theorems/22e97f78-fb77-4a43-8caa-51e80a204379
-- title:
--   Mixed smoothed/empirical composite estimator $\varrho^{(N,J)}_\mu[u,X]$ (13)
-- statement:
--   Let $J\subseteq\{1,\dots,k+1\}$, a smoothing measure $\mu_N$ on $\mathbb R^m$ and a sample $x_1,\dots,x_N$ be given. The **mixed estimator** $\varrho^{(N,J)}_\mu[u,X]$ is the nested composite whose level $j$ is
--
--   $$
--   [h^{(N,J)}_\mu]_j(u,\eta)=\begin{cases}\dfrac1N\displaystyle\sum_{i=1}^N\int f_j(u,\eta,x_i+z)\,d\mu_N(z), & j\in J,\\[2mm] \dfrac1N\displaystyle\sum_{i=1}^N f_j(u,\eta,x_i), & j\notin J,\end{cases}
--   $$
--
--   and likewise for $f_{k+1}$. Smoothed levels integrate against $P_N*\mu_N$ (the smooth estimator (12)), the others against the empirical measure $P_N$; every level uses the whole sample. With a kernel, $d\mu_N(z)=h_N^{-m}K(z/h_N)\,dz$, this is a kernel estimator of the composite functional.
--
--   **Formalization Note** For $k+1\notin J$ the innermost level is $\frac1N\sum_i f_{k+1}(u,x_i)$, as the text of p.10 ("$Q^j_N=P_N$ for $j\notin J$") and the display of $\Delta^{(N)}_j$ on p.11 state; the last line of (13) prints $x_i+z$ there. The sample is 0-based in Lean.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, displays (12)–(13), pp.9–10

import Mathlib
import Definitions.Def_CompositeSAA_nestedComposite
import Definitions.Def_CompositeSAA_CompositeModel

open MeasureTheory Finset

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, displays (12)–(13), pp.9–10: the mixed
(partially smoothed) estimator `ϱ^{(N,J)}_µ` of the composite functional. For an index set
`J ⊆ {1, …, k + 1}`, level `j` uses the smoothed empirical measure `P_N ∗ µ_N` if `j ∈ J` and
the empirical measure `P_N` otherwise:

* `j ∈ J`: `(1/N) Σ_{i=1}^N ∫ f_j(u, η, x_i + z) dµ_N(z)` (the smooth estimator (12));
* `j ∉ J`: `(1/N) Σ_{i=1}^N f_j(u, η, x_i)`;

and likewise for the innermost function `f_{k+1}`; the levels are then composed as in (8).

**Formalization Note** `μN` is the smoothing measure `µ_N` and `xs` the sample, with the paper's
`x_1, …, x_N` being `xs 0, …, xs (N − 1)`. For `k + 1 ∉ J` the innermost level is
`(1/N) Σ f_{k+1}(u, x_i)`, as the text on p.10 ("`Q^j_N = P_N` for `j ∉ J`") and the display of
`Δ^{(N)}_j` on p.11 say; the last line of (13) prints `x_i + z` there, a typo. -/
noncomputable def mixedEstimator {n mX k : ℕ} (D : CompositeModel n mX k) (J : Finset ℕ)
    (μN : Measure (EuclideanSpace ℝ (Fin mX))) (N : ℕ) (xs : ℕ → EuclideanSpace ℝ (Fin mX))
    (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  nestedComposite D.m D.m_zero k n
    (fun j u η => if j ∈ J then (N : ℝ)⁻¹ • ∑ i ∈ range N, ∫ z, D.f j u η (xs i + z) ∂μN
      else (N : ℝ)⁻¹ • ∑ i ∈ range N, D.f j u η (xs i))
    (fun u => if k + 1 ∈ J then (N : ℝ)⁻¹ • ∑ i ∈ range N, ∫ z, D.fLast u (xs i + z) ∂μN
      else (N : ℝ)⁻¹ • ∑ i ∈ range N, D.fLast u (xs i)) u

end CompositeSAA


