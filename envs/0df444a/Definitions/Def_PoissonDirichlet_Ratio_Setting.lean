-- Prove2me | Definitions.Def_PoissonDirichlet_Ratio_Setting
-- name    : PoissonDirichlet_Ratio_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:21.607209+00:00
-- url     : https://prove2.me/theorems/d13a31b6-50da-4c91-8d9d-33ca873f21e0
-- title:
--   Definition 1 and equations (4), (21), (23): PD law and ratio coordinates
-- statement:
--   For $0\leq\alpha<1$ and $\theta>-\alpha$, let $\widetilde Y_n$ be independent beta$(1-\alpha,\theta+n\alpha)$ variables. Their stick lengths and ranked values are
--
--   $$
--   \widetilde V_n=\widetilde Y_n\prod_{i<n}(1-\widetilde Y_i),\qquad
--   (V_1,V_2,\ldots)=\operatorname{rank}(\widetilde V_1,\widetilde V_2,\ldots),\quad V_1\geq V_2\geq\cdots.
--   $$
--
--   The law of $(V_n)$ is $\mathrm{PD}(\alpha,\theta)$. Equation (21) defines $R_n=V_{n+1}/V_n$; equation (23) reconstructs the $V_n$ from the ratios. These common objects give each theorem in this mission the same meaning of a Poisson–Dirichlet sequence.
--
--   **Formalization Note** Sequences use zero-based indices, so Lean's `v k` denotes $V_{k+1}$. The ranked-value definition counts multiplicity with an extended cardinality. Distributional equality is expressed on measurable preimages.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 857, Definition 1 and (4); pp. 861–862, (21), (23)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Ratio

/-- Equation (4), with the paper's index shifted down by one. -/
def stick (y : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∏ i ∈ Finset.range k, (1 - y i)) * y k

/-- The (k+1)-st largest value, counted with multiplicity, for a nonnegative
sequence tending to zero. The extended cardinality also handles infinite
upper level sets without assigning them the finite cardinality zero. -/
noncomputable def ranked (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ {i | t < x i}.encard ≤ k}

/-- The independent beta stick factors of Definition 1. -/
def IsStickLaw (α θ : ℝ) (μ : Measure (ℕ → ℝ)) : Prop :=
  IsProbabilityMeasure μ ∧
    iIndepFun (fun k (y : ℕ → ℝ) => y k) μ ∧
    ∀ k : ℕ, HasLaw (fun y : ℕ → ℝ => y k)
      (betaMeasure (1 - α) (θ + ((k : ℝ) + 1) * α)) μ

/-- Definition 1: the distribution of the ranked stick lengths. -/
def HasPD {Ω : Type*} [MeasurableSpace Ω]
    (α θ : ℝ) (P : Measure Ω) (V : Ω → ℕ → ℝ) : Prop :=
  AEMeasurable V P ∧
    ∃ μ : Measure (ℕ → ℝ), IsStickLaw α θ μ ∧
      ∀ s : Set (ℕ → ℝ), MeasurableSet s →
        P (V ⁻¹' s) = μ ((fun y => ranked (stick y)) ⁻¹' s)

/-- Equation (21): ratio R_(k+1) of consecutive ranked masses. -/
noncomputable def ratio (v : ℕ → ℝ) (k : ℕ) : ℝ := v (k + 1) / v k

/-- Equation (23), reconstructing the ranked masses from the ratios. -/
noncomputable def fromRatios {Ω : Type*} (R : ℕ → Ω → ℝ) (ω : Ω) (k : ℕ) : ℝ :=
  let first := 1 / (1 + ∑' j : ℕ, ∏ i ∈ Finset.range (j + 1), R i ω)
  if k = 0 then first else
    first * ∏ i ∈ Finset.range k, R i ω

end PoissonDirichlet.Ratio


