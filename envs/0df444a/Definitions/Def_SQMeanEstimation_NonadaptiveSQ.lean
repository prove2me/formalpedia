-- Prove2me | Definitions.Def_SQMeanEstimation_NonadaptiveSQ
-- name    : SQMeanEstimation_NonadaptiveSQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:00.024132+00:00
-- url     : https://prove2.me/theorems/6f5110cb-f803-4013-8ebb-c83a2d31870a
-- title:
--   Deterministic non-adaptive statistical query algorithm with $m$ queries
-- statement:
--   A **deterministic non-adaptive statistical query (SQ) algorithm** on $\mathbb R^d$ with $m$ queries consists of
--
--   1. $m$ Borel measurable queries $\phi_1,\dots,\phi_m:\mathbb R^d\to[0,1]$, fixed in advance, and
--   2. an output map that sends the vector $v\in\mathbb R^m$ of oracle answers to an estimate $\tilde w(v)\in\mathbb R^d$.
--
--   The algorithm sees the input distribution only through the answers of a statistical query oracle to its queries (Definition 2.1). The paper's upper bounds for mean estimation use algorithms of this kind (Table 1, p.4: "Upper bounds use at most $3d\log d$ (non-adaptive) queries").
--
--   **Formalization Note** The queries are defined on all of $\mathbb R^d$; only their values on the support of the input distribution matter.
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, Definition 2.1, p.11; Table 1, p.4

import Mathlib

namespace SQMeanEstimation

/-- **A deterministic non-adaptive statistical query algorithm on ℝᵈ with `m` queries.**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, Definition 2.1, p.11 (queries `φ : W → [0, 1]` to
VSTAT) and Table 1, p.4 ("Upper bounds use at most 3d log d (non-adaptive) queries").

The algorithm fixes its `m` queries `query i : ℝᵈ → [0, 1]` in advance, each Borel measurable;
after receiving the oracle's answers `v : Fin m → ℝ` it outputs the vector `output v ∈ ℝᵈ`.

**Formalization Note.** ℝᵈ is `Fin d → ℝ`. The queries are defined on all of ℝᵈ; only their
values on the support of the input distribution (the unit ℓq ball) matter. -/
structure NonadaptiveSQ (d m : ℕ) where
  /-- The `i`-th statistical query. -/
  query : Fin m → (Fin d → ℝ) → ℝ
  /-- Every query is Borel measurable. -/
  measurable_query : ∀ i, Measurable (query i)
  /-- Every query takes values in `[0, 1]`, as VSTAT requires. -/
  query_mem : ∀ i w, query i w ∈ Set.Icc (0 : ℝ) 1
  /-- The output, as a function of the oracle's answers. -/
  output : (Fin m → ℝ) → (Fin d → ℝ)

end SQMeanEstimation


