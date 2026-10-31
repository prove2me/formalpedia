-- Prove2me | Definitions.Def_CompositeSAA_empiricalEstimator
-- name    : CompositeSAA_empiricalEstimator
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:37.401505+00:00
-- url     : https://prove2.me/theorems/34f8c806-037a-495f-81fb-84566e5778ed
-- title:
--   Empirical composite estimator $\varrho^{(N)}_E[u,X]$ (11)
-- statement:
--   Given a sample $x_1,\dots,x_N$, the **empirical estimator** of the composite functional replaces every expectation by the sample average over the entire sample:
--
--   $$
--   \varrho^{(N)}_E[u,X]=\sum_{i_0=1}^N\frac1N\Bigl[f_1\Bigl(u,\sum_{i_1=1}^N\frac1N\Bigl[f_2\Bigl(u,\cdots f_k\Bigl(u,\sum_{i_k=1}^N\frac1N f_{k+1}(u,x_{i_k})\Bigr)\cdots,x_{i_1}\Bigr)\Bigr],x_{i_0}\Bigr)\Bigr].
--   $$
--
--   It is (8) with $Q^j_N=P_N$, the empirical measure, at every level. Because the objective is not a single expectation, this is not a sample average approximation in the usual sense.
--
--   **Formalization Note** The sample is a sequence `xs` and the paper's $x_1,\dots,x_N$ are `xs 0, …, xs (N-1)`.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, display (11), p.8 and p.9

import Mathlib
import Definitions.Def_CompositeSAA_nestedComposite
import Definitions.Def_CompositeSAA_CompositeModel

open Finset

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, display (11), p.8 and p.9 (`ϱ^{(N)}_E`): the
empirical estimator of the composite functional from a sample `x_1, …, x_N`,

`ϱ^{(N)}_E[u] = (1/N) Σ_{i₀} f₁(u, (1/N) Σ_{i₁} f₂(u, ⋯ f_k(u, (1/N) Σ_{i_k} f_{k+1}(u, x_{i_k}), ⋯), x_{i₁}), x_{i₀})`,

i.e. (8) with `Q^j_N = P_N`, the empirical measure, at every level; the entire sample is used at
every level.

**Formalization Note** The sample is `xs : ℕ → ℝ^{mX}` and the paper's `x_1, …, x_N` are
`xs 0, …, xs (N − 1)` (0-based). At `N = 0` the empty average is `0`; the theorems only concern
large `N`. -/
noncomputable def empiricalEstimator {n mX k : ℕ} (D : CompositeModel n mX k) (N : ℕ)
    (xs : ℕ → EuclideanSpace ℝ (Fin mX)) (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  nestedComposite D.m D.m_zero k n
    (fun j u η => (N : ℝ)⁻¹ • ∑ i ∈ range N, D.f j u η (xs i))
    (fun u => (N : ℝ)⁻¹ • ∑ i ∈ range N, D.fLast u (xs i)) u

end CompositeSAA


