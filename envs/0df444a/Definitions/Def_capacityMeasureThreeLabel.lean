-- Prove2me | Definitions.Def_capacityMeasureThreeLabel
-- name    : capacityMeasureThreeLabel
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-07T23:44:39.87711+00:00
-- url     : https://prove2.me/theorems/a1f32f1e-8b0e-4420-b1da-868534c6e2ec
-- title:
--   Three-label density data, deficits, and stability hypotheses
-- statement:
--   Let $X$ be a set. Three-label density data consist of seven arbitrary real-valued functions on $X$: $f_1,f_2,f_3$ and $\beta_{123},\beta_{12},\beta_{13},\beta_{23}$. For $ij\in\{12,13,23\}$, define the pair-deficit function by
--
--   $$
--   d_{ij}(x)=\min(f_i(x),f_j(x))-\beta_{123}(x)-\beta_{ij}(x).
--   $$
--
--   The canonical functions are defined pointwise by
--
--   $$
--   \begin{aligned}
--   \gamma_{123}&=\min(f_1,\min(f_2,f_3)),\\
--   \gamma_{12}&=\max(\min(f_1,f_2)-f_3,0),\\
--   \gamma_{23}&=\max(\min(f_2,f_3)-f_1,0).
--   \end{aligned}
--   $$
--
--   For arbitrary weight functions $q_{12},q_{23}:X\to\mathbb R$, the actual and canonical scores are
--
--   $$
--   \begin{aligned}
--   A_q&=\beta_{123}+q_{12}\beta_{12}+q_{23}\beta_{23},\\
--   C_q&=\gamma_{123}+q_{12}\gamma_{12}+q_{23}\gamma_{23}.
--   \end{aligned}
--   $$
--
--   Validity at a point means that all four block intensities are nonnegative there and that
--
--   $$
--   \begin{aligned}
--   \beta_{123}+\beta_{12}+\beta_{13}&\le f_1,\\
--   \beta_{123}+\beta_{12}+\beta_{23}&\le f_2,\\
--   \beta_{123}+\beta_{13}+\beta_{23}&\le f_3.
--   \end{aligned}
--   $$
--
--   Admissibility at a point means
--
--   $$
--   \begin{aligned}
--   0\le q_{12}\le1,&\qquad 0\le q_{23}\le1,\\
--   q_{12}+q_{23}&\ge1,\\
--   f_2&\ge\min(f_1,f_3).
--   \end{aligned}
--   $$
--
--   Finally, on a measurable space with an arbitrary measure $\mu$, the bundled integrability condition requires each of $C_q,A_q,d_{12},d_{13},d_{23}$ to be real-integrable with respect to $\mu$.
--
--   These definitions separate the algebraic data from the validity, weight, and integrability assumptions used in later stability theorems. Merely supplying the seven functions imposes no positivity, measurability, normalization, or coupling-realization condition. The predicates do not assert the existence of a stochastic process or a random partition.
-- source:
--   Interval-Möbius capacity and temporal block flow, unpublished project note (2026), equations (2.2)–(2.4) and (3.1)–(3.2), with explicit integration hypotheses added by the formal source. CAPACITY_FLOW_THEOREM.md SHA-256 700d20415a4a673e5b27b1e6d508a89204afb85dfe54daddf8d4d84b1492d15f. Exact formal source: formal_capacity/FormalCapacity/Measure/ThreeLabel.lean, ThreeLabelDensities (18–26), deficit12 (32–34), deficit13 (36–38), deficit23 (40–42), actualScore (44–46), canonical123 (48–50), canonical12 (52–54), canonical23 (56–58), canonicalScore (60–62), ValidAt (69–78), AdmissibleAt (80–89), IntegrableFor (135–143). Source-file SHA-256 be25fa12896fcf4b5371133ccd12aef7584a76154ca7363db31d8866b6730642. Ranges are compiler-derived and include source docstrings where present. Local source archive; no public repository URL, commit, externally established authorship, or novelty claim is asserted. Target environment: Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_capacityThreeLabel

set_option autoImplicit false

/-!
# Measure-theoretic three-label stability

This file lifts the scalar theorem `FormalCapacity.Finite.threeLabel_stability`
to densities over an arbitrary measure space.  Pair deficits are defined
pointwise, proved nonnegative almost everywhere from the block-capacity
constraints, and then integrated.  Nothing here assumes a stochastic process
or a Brownian law.
-/

open MeasureTheory

namespace FormalCapacity.Measure

/-- The seven density functions needed for the three-label block calculation. -/
structure ThreeLabelDensities (α : Type*) where
  f1 : α → ℝ
  f2 : α → ℝ
  f3 : α → ℝ
  beta123 : α → ℝ
  beta12 : α → ℝ
  beta13 : α → ℝ
  beta23 : α → ℝ

namespace ThreeLabelDensities

variable {α : Type*}

/-- Deficit from the maximal common density of labels `1,2`. -/
def deficit12 (d : ThreeLabelDensities α) (x : α) : ℝ :=
  min (d.f1 x) (d.f2 x) - d.beta123 x - d.beta12 x

/-- Deficit from the maximal common density of labels `1,3`. -/
def deficit13 (d : ThreeLabelDensities α) (x : α) : ℝ :=
  min (d.f1 x) (d.f3 x) - d.beta123 x - d.beta13 x

/-- Deficit from the maximal common density of labels `2,3`. -/
def deficit23 (d : ThreeLabelDensities α) (x : α) : ℝ :=
  min (d.f2 x) (d.f3 x) - d.beta123 x - d.beta23 x

/-- The score of the actual block densities at `x`. -/
def actualScore (d : ThreeLabelDensities α) (q12 q23 : α → ℝ) (x : α) : ℝ :=
  Finite.threeScore (q12 x) (q23 x) (d.beta123 x) (d.beta12 x) (d.beta23 x)

/-- Canonical triple-block density. -/
def canonical123 (d : ThreeLabelDensities α) (x : α) : ℝ :=
  Finite.canonical123 (d.f1 x) (d.f2 x) (d.f3 x)

/-- Canonical `12`-block density. -/
def canonical12 (d : ThreeLabelDensities α) (x : α) : ℝ :=
  Finite.canonical12 (d.f1 x) (d.f2 x) (d.f3 x)

/-- Canonical `23`-block density. -/
def canonical23 (d : ThreeLabelDensities α) (x : α) : ℝ :=
  Finite.canonical23 (d.f1 x) (d.f2 x) (d.f3 x)

/-- The score of the canonical layer-cake block densities at `x`. -/
def canonicalScore (d : ThreeLabelDensities α) (q12 q23 : α → ℝ) (x : α) : ℝ :=
  Finite.canonicalScore (q12 x) (q23 x) (d.f1 x) (d.f2 x) (d.f3 x)



/-- The pointwise nonnegativity and marginal-capacity conditions on block
densities. -/
structure ValidAt (d : ThreeLabelDensities α) (x : α) : Prop where
  beta123_nonneg : 0 ≤ d.beta123 x
  beta12_nonneg : 0 ≤ d.beta12 x
  beta13_nonneg : 0 ≤ d.beta13 x
  beta23_nonneg : 0 ≤ d.beta23 x
  marginal1 : d.beta123 x + d.beta12 x + d.beta13 x ≤ d.f1 x
  marginal2 : d.beta123 x + d.beta12 x + d.beta23 x ≤ d.f2 x
  marginal3 : d.beta123 x + d.beta13 x + d.beta23 x ≤ d.f3 x

/-- The admissible triangular weight region and the order-quasiconcavity
condition at a density point. -/
structure AdmissibleAt (d : ThreeLabelDensities α) (q12 q23 : α → ℝ)
    (x : α) : Prop where
  q12_nonneg : 0 ≤ q12 x
  q12_le_one : q12 x ≤ 1
  q23_nonneg : 0 ≤ q23 x
  q23_le_one : q23 x ≤ 1
  q_sum : 1 ≤ q12 x + q23 x
  middle_not_smallest : min (d.f1 x) (d.f3 x) ≤ d.f2 x









variable [MeasurableSpace α]

/-- Integrability assumptions needed to turn the pointwise stability theorem
into a statement about finite real masses. -/
structure IntegrableFor (d : ThreeLabelDensities α) (q12 q23 : α → ℝ)
    (μ : Measure α) : Prop where
  canonicalScore : Integrable (d.canonicalScore q12 q23) μ
  actualScore : Integrable (d.actualScore q12 q23) μ
  deficit12 : Integrable d.deficit12 μ
  deficit13 : Integrable d.deficit13 μ
  deficit23 : Integrable d.deficit23 μ









end ThreeLabelDensities
end FormalCapacity.Measure


