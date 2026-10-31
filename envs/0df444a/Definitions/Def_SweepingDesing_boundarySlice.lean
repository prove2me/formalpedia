-- Prove2me | Definitions.Def_SweepingDesing_boundarySlice
-- name    : SweepingDesing_boundarySlice
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:08.679089+00:00
-- url     : https://prove2.me/theorems/0a81d307-91ea-49e4-923f-f543f2a5ee1c
-- title:
--   §3.1 — the boundary slices $H_S(t)$
-- statement:
--   For $S:\mathbb R\rightrightarrows\mathbb R^n$ with graph $\mathcal S\subset\mathbb R^{n+1}$, define $H_S:\mathbb R\rightrightarrows\mathbb R^{n+1}$ by
--
--   $$
--   H_S(t)=\partial\mathcal S\cap(\{t\}\times\mathbb R^n),
--   $$
--
--   where $\partial\mathcal S$ is the topological boundary of $\mathcal S$. Continuity of $H_S$ in the Pompeiu–Hausdorff metric is the continuity assumption (A3).
--
--   **Formalization Note** $\mathbb R^{n+1}=\mathbb R\times\mathbb R^n$, $\partial\mathcal S$ is `frontier`.
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §3.1, p.8

import Mathlib
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §3.1, p.8: the multivalued map `H_S : ℝ ⇉ ℝⁿ⁺¹`,
`H_S(t) := ∂𝒮 ∩ ({t} × ℝⁿ)`, where `𝒮 = gph S` and `∂𝒮` is its topological boundary.

**Formalization Note** `ℝⁿ⁺¹ = ℝ × ℝⁿ`, `∂𝒮 = frontier 𝒮`. -/
def boundarySlice {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) (t : ℝ) :
    Set (ℝ × EuclideanSpace ℝ (Fin n)) :=
  frontier (GenNewtonSubgrad.ProxReg.gph S) ∩ {p | p.1 = t}

end SweepingDesing


