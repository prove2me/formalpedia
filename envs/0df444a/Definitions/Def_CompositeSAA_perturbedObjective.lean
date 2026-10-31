-- Prove2me | Definitions.Def_CompositeSAA_perturbedObjective
-- name    : CompositeSAA_perturbedObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:31.637147+00:00
-- url     : https://prove2.me/theorems/c6df0f6d-1607-4bdb-ae81-e08d5aa08062
-- title:
--   Measure-perturbed composite objective $\varrho^{(Q^1..Q^{k+1})}[u,X]$ (8)
-- statement:
--   For a measure $Q$ on the data space let $\bar f^Q_j(u,\eta_j)=\int f_j(u,\eta_j,x)\,Q(dx)$ ($j=1,\dots,k$) and $\bar f^Q_{k+1}(u)=\int f_{k+1}(u,x)\,Q(dx)$, as in (6). For measures $Q^1,\dots,Q^{k+1}$, one per level, the **perturbed composite objective** is
--
--   $$
--   \varrho^{(Q^1..Q^{k+1})}[u,X]=\bar f^{Q^1}_1\Bigl(u,\bar f^{Q^2}_2\bigl(u,\cdots\bar f^{Q^k}_k(u,\bar f^{Q^{k+1}}_{k+1}(u))\cdots\bigr)\Bigr).
--   $$
--
--   It models a composite problem in which the distribution $P$ of the data is replaced by a different measure at each level of nesting; stability theory asks how its minimum and minimizers depend on the $Q^j$.
--
--   **Formalization Note** $Q^j$ is `Q j`; `Q 0` is unused. The integrals are Bochner integrals over the whole data space, which equal the paper's integrals over $\mathcal X$ for $Q\in\mathcal P(\mathcal X)$.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, displays (6) and (8), pp.4–5

import Mathlib
import Definitions.Def_CompositeSAA_nestedComposite
import Definitions.Def_CompositeSAA_CompositeModel

open MeasureTheory

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, displays (6) and (8), pp.4–5: the measure-perturbed
composite objective

`ϱ^{(Q¹..Q^{k+1})}[u, X] = f̄^{Q¹}_1(u, f̄^{Q²}_2(u, ⋯ f̄^{Q^k}_k(u, f̄^{Q^{k+1}}_{k+1}(u)) ⋯))`,

where `f̄^Q_j(u, η) = ∫ f_j(u, η, x) Q(dx)` and `f̄^Q_{k+1}(u) = ∫ f_{k+1}(u, x) Q(dx)`.

**Formalization Note** `Q j` is the measure used at level `j = 1, …, k + 1` (`Q 0` is unused).
The integrals are Bochner integrals over the whole data space; for the paper's measures
`Q ∈ 𝒫(𝒳)` these are the integrals over `𝒳`. -/
noncomputable def perturbedObjective {n mX k : ℕ} (D : CompositeModel n mX k)
    (Q : ℕ → Measure (EuclideanSpace ℝ (Fin mX))) (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  nestedComposite D.m D.m_zero k n (fun j u η => ∫ x, D.f j u η x ∂(Q j))
    (fun u => ∫ x, D.fLast u x ∂(Q (k + 1))) u

end CompositeSAA


