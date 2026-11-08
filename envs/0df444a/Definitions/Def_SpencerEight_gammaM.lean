-- Prove2me | Definitions.Def_SpencerEight_gammaM
-- name    : SpencerEight_gammaM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:19.569163+00:00
-- url     : https://prove2.me/theorems/6f0d6392-facc-42e9-bde2-669aa10a9a1d
-- title:
--   Standard Gaussian measure $\gamma_m$ on $\mathbb R^S$
-- statement:
--   For a finite index set $S$ with $m=|S|$, the measure $\gamma_m$ is the law on $\mathbb R^S$ of a vector $\xi=(\xi_i)_{i\in S}$ of independent standard Gaussians: $\gamma_m(K)=\Pr[\xi\in K]$.
--
--   This is the reference measure of every small-ball estimate in the mission.
--
--   **Formalization Note** The product of copies of `gaussianReal 0 1` on `ι → ℝ`. On a non-measurable set the value is the outer measure; a convex set is null-measurable, so this does not change the mass of any set used here.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 4.1, p.22 (PDF p.22)

import Mathlib
open MeasureTheory ProbabilityTheory

namespace SpencerEight

/-- The standard Gaussian law `γ_m` on `ℝ^S` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 4.1, p.22 (PDF p.22): `ξ ∼ N(0, I_m)`, `γ_m(K) := Pr[ξ ∈ K]`).

**Formalization Note** The law of `m` independent standard Gaussians on `ι → ℝ` for a finite index type `ι`, as the product of `N(0,1)`; `m = Fintype.card ι`. Applied to a non-measurable set this is the outer measure; a convex set is null-measurable, so nothing changes for the sets of this mission. -/
noncomputable def gammaM (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => gaussianReal 0 1

end SpencerEight


