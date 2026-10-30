-- Prove2me | Definitions.Def_BasisWeightLearning_Exact_FunctionFrontier
-- name    : BasisWeightLearning_Exact_FunctionFrontier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:20:32.705239+00:00
-- url     : https://prove2.me/theorems/7b62d7f0-a236-4d12-9bf5-1cb331c51eb9
-- title:
--   Density normals and the function-space positive-normal frontier
-- statement:
--   An admissible normal is a nonnegative $L^2([0,1])$ density $\pi$ with $\int_0^1\pi=1$. For a finite set $Z$ of square-integrable functions, retain precisely each $u\in Z$ for which some such density satisfies $\int_0^1\pi v<\int_0^1\pi u$ for all $v\in Z\setminus\{u\}$. This uses all admissible densities, including nonpolynomial ones. Inputs in this mission are $L^2$ functions, so their products with density normals are integrable by Hölder. The predicate itself does not identify functions with coefficient vectors.
-- source:
--   Hao Zhang, Dynamic Learning and Decision Making via Basis Weight Vectors, Operations Research (2022), DOI 10.1287/opre.2021.2240, supplied PDF p. 12 (printed p. 12), §3.3 and Eq. (10).

import Definitions.Def_BasisWeightLearning_Exact_Domain
open MeasureTheory

namespace BasisWeightLearning.Exact
def IsDensity (π : ValueFunction) : Prop :=
  MemLp π 2 intervalMeasure ∧ (∀ θ, 0 ≤ π θ) ∧
    (∫ θ, π θ ∂intervalMeasure) = 1

noncomputable def functionFrontier (Z : Set ValueFunction) : Set ValueFunction :=
  {u | u ∈ Z ∧ ∃ π : ValueFunction, IsDensity π ∧
    ∀ v ∈ Z, v ≠ u →
      (∫ θ, π θ * v θ ∂intervalMeasure) < ∫ θ, π θ * u θ ∂intervalMeasure}
end BasisWeightLearning.Exact


