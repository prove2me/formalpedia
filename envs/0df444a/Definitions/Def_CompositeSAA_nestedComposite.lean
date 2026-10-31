-- Prove2me | Definitions.Def_CompositeSAA_nestedComposite
-- name    : CompositeSAA_nestedComposite
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:32:32.201545+00:00
-- url     : https://prove2.me/theorems/55c047c8-5bf2-457d-9f3a-a307e714aa3f
-- title:
--   The real-valued nested composite $\ell_1(u,\ell_2(u,\cdots\ell_k(u,t(u))\cdots))$
-- statement:
--   Let $m_0=1,m_1,\dots,m_k$ be dimensions. Given level maps $\ell_j(u,\cdot):\mathbb R^{m_j}\to\mathbb R^{m_{j-1}}$ ($j=1,\dots,k$) and an innermost map $t(u)\in\mathbb R^{m_k}$, all depending on a decision $u\in\mathbb R^n$, the **nested composite** is the real number
--
--   $$
--   u\;\mapsto\;\ell_1\bigl(u,\ell_2(u,\cdots\ell_k(u,t(u))\cdots)\bigr)\in\mathbb R^{m_0}=\mathbb R .
--   $$
--
--   The composite risk functional (2), its measure-perturbed version (8), the empirical estimator (11) and the mixed smoothed estimator (13) are all nested composites with different level maps; defining the composition once keeps these objects literally comparable.
--
--   **Formalization Note** Since $m_0=1$, the outermost value lies in $\mathbb R^1$ and its single coordinate is returned.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, display (2), p.1 and display (8), p.5

import Mathlib
import Definitions.Def_CompositeSAA_nestStage

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, display (2), p.1 and display (8), p.5: the
real-valued nested composite

`u ↦ lvl₁(u, lvl₂(u, ⋯ lvl_k(u, top(u)) ⋯))`,

where `lvl j u : ℝ^{m_j} → ℝ^{m_{j-1}}` (`j = 1, …, k`), `top u ∈ ℝ^{m_k}` and `m_0 = 1`. The
paper's composite functional ϱ[u, X] (2), its measure-perturbed version (8) and the sample-based
estimators (11)–(13) are all of this form, with different level maps.

**Formalization Note** `ℝ^d` is `EuclideanSpace ℝ (Fin d)`. Since `m 0 = 1`, the outermost value
lies in `ℝ^1`, and its single coordinate is the real number returned. -/
noncomputable def nestedComposite (m : ℕ → ℕ) (hm : m 0 = 1) (k n : ℕ)
    (lvl : (j : ℕ) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m j)) →
      EuclideanSpace ℝ (Fin (m (j - 1))))
    (top : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m k)))
    (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  nestStage m k (fun j => lvl j u) (top u) 0 ⟨0, by rw [hm]; exact Nat.one_pos⟩

end CompositeSAA


