-- Prove2me | Definitions.Def_MetricMinTest_Supplement_IsRegionalCover
-- name    : MetricMinTest_Supplement_IsRegionalCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:31:05.610711+00:00
-- url     : https://prove2.me/theorems/cb998b7f-0b38-44ab-92e8-98e49500d33b
-- title:
--   Feasible regional cover (feasible point of (7.1))
-- statement:
--   Let $\mathcal A$ be the set of **admissible regions** $(Z,r)$: $Z$ a nonempty set of indices and $r<\gamma$ a distance occurring in the matrix (zero included). A **feasible regional cover** is a weighting $y\ge0$ of $\mathcal A$ with
--   $$\sum_{(Z,r)\in\mathcal A:\ i\in S(Z,r)}y_{Z,r}\ge1\qquad\text{for every }i,$$
--   where $S(Z,r)=\bigcup_{z\in Z}B(z,r)$ is the screening region.
--
--   **Formalization Note** A region is indexed by $(Z,(i_0,j_0))$ with radius $d(i_0,j_0)$, so every occurring distance is available; a repeated distance duplicates a region at the same cost, which changes no optimum.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition 7.1 and (7.1), pp.15–16

import Mathlib

namespace MetricMinTest.Supplement

/-- **Feasible regional cover** (a feasible point of program (7.1)). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §7, p.16: "Let A consist
of all such pairs [(Z, r), Z nonempty, r ∈ [0, γ)] with r a distance occurring in the matrix and
r < γ, including zero", and the constraints `y ≥ 0`,
`∑_{(Z,r) : i ∈ S(Z,r)} y_{Z,r} ≥ 1` for every `i`, where `S(Z, r) = ⋃_{z∈Z} B(z, r)`.

**Formalization Note.** A region is indexed by `(Z, (i₀, j₀))` with radius `r = d i₀ j₀`, so every
occurring distance is available; it is admissible when `Z` is nonempty and `d i₀ j₀ < γ` (for a
pseudometric occurring distances are `≥ 0` and `0 = d i i` occurs). Repeated distances duplicate
a region at the same cost, which changes no optimum. Coordinates at inadmissible indices do not
count. -/
def IsRegionalCover {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ) (γ : ℝ)
    (y : Finset ι × (ι × ι) → ℝ) : Prop :=
  (∀ q, 0 ≤ y q) ∧
  ∀ i, 1 ≤ ∑ q ∈ Finset.univ.filter (fun q : Finset ι × (ι × ι) =>
      q.1.Nonempty ∧ d q.2.1 q.2.2 < γ ∧ ∃ z ∈ q.1, d i z ≤ d q.2.1 q.2.2), y q

end MetricMinTest.Supplement


