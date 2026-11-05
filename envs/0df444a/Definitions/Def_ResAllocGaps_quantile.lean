-- Prove2me | Definitions.Def_ResAllocGaps_quantile
-- name    : ResAllocGaps_quantile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:29:32.218995+00:00
-- url     : https://prove2.me/theorems/23eee5c4-bcd2-4103-90c4-9dc8e8d7ef24
-- title:
--   Generalized inverse $F^{-1}(q)=\inf\{v: F(v)\ge q\}$ of a candidate-ability distribution
-- statement:
--   For a law $\mu$ on $\mathbb R$ with distribution function $F(v)=\mu((-\infty,v])$, the **generalized inverse** (quantile function) is
--   $$F^{-1}(q)=\inf\{v\in\mathbb R:\ F(v)\ge q\}.$$
--   The paper defines it for $q\in[0,1]$; it is a real number for every $q\in(0,1]$ when $\mu$ is a probability measure, and it is the object on which the clustering condition of Definition 1 is stated.
--
--   **Formalization Note** $F$ is Mathlib's `cdf μ` and the infimum is `sInf` over $\mathbb R$. At $q\le0$ the set is all of $\mathbb R$ and Lean returns the junk value $0$; every statement of this mission evaluates $F^{-1}$ only on $(0,1]$.
-- source:
--   O. Besbes, Y. Kanoria and A. Kumar, Dynamic Resource Allocation: Algorithmic Design Principles and Spectrum of Achievable Performances, arXiv:2205.09078v2 (6 Oct 2023), https://arxiv.org/abs/2205.09078v2, §3.1, p.11 (definition of F⁻¹ before Definition 1)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ResAllocGaps

/-- The **generalized inverse** (quantile function) of a candidate-ability distribution,
Besbes, Kanoria & Kumar, arXiv:2205.09078v2, §3.1, p.11: "For any q ∈ [0, 1], we define
F⁻¹(q) ≜ inf {v : F(v) ≥ q}", where `F = cdf μ` is the cumulative distribution function of the
law `μ` on `ℝ`.

**Formalization Note.** The law is a measure `μ` on `ℝ` and `F` is Mathlib's `cdf μ`, which is
`v ↦ μ((-∞, v])` for a probability measure. The infimum is `sInf` over `ℝ`. For `q ∈ (0, 1]` and
a probability measure the set `{v | q ≤ F v}` is nonempty and bounded below, so `sInf` is the
paper's infimum; at `q ≤ 0` the set is all of `ℝ` and Lean's `sInf` returns the junk value `0`.
Every statement of this mission evaluates `quantile μ q` only at `q ∈ (0, 1]` (Definition 1 uses
the half-open quantile intervals `(q⋆ᵢ₋₁, q⋆ᵢ]`). -/
noncomputable def quantile (μ : Measure ℝ) (q : ℝ) : ℝ :=
  sInf {v : ℝ | q ≤ cdf μ v}

end ResAllocGaps


