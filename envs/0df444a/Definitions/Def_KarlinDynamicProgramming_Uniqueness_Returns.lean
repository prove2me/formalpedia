-- Prove2me | Definitions.Def_KarlinDynamicProgramming_Uniqueness_Returns
-- name    : KarlinDynamicProgramming_Uniqueness_Returns
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:54:08.471413+00:00
-- url     : https://prove2.me/theorems/324a9af5-75f8-4df8-ac98-0cafbbd09c2f
-- title:
--   Actual return series and finite uniform convergence
-- statement:
--   The stage return is the decision reward times its preceding product weight. The partial return is the sum of the first N stage returns. UniformFiniteReturns requires, for each initial state separately, a finite real limit function of all infinite strategies and convergence to it uniformly in the strategy. totalReturn is the actual real series; under UniformFiniteReturns it is summable, so the nonsummable default of real tsum is excluded from the goal. The empty sum is zero.
-- source:
--   Karlin, The Structure of Dynamic Programing Models, Naval Research Logistics Quarterly 2(4) (1955), 285–294, doi:10.1002/nav.3800020408; Display (1), PDF 3 / printed 287

import Definitions.Def_KarlinDynamicProgramming_Uniqueness_Model

namespace KarlinDynamicProgramming.Uniqueness

variable {Ω D : Type*} [TopologicalSpace Ω] [TopologicalSpace D]

/-- Actual weighted reward of decision j. -/
def stageReturn (m : Model Ω D) (ω : Ω) (s : Strategy D) (j : ℕ) : ℝ :=
  weight m s j * m.L (trajectory m ω s j) (s j)

/-- Actual first N rewards; the empty sum is zero. -/
def partialReturn (m : Model Ω D) (ω : Ω) (s : Strategy D) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, stageReturn m ω s j

/-- The source's finite uniform convergence, separately for each initial state.
The witness is a limit of the actual partial sums, not free payoff data. -/
def UniformFiniteReturns (m : Model Ω D) : Prop :=
  ∀ ω, ∃ f : Strategy D → ℝ,
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ s : Strategy D, |partialReturn m ω s n - f s| < ε

/-- Actual reward series. UniformFiniteReturns ensures summability, so the
nonsummable default of real tsum is never used in the goal. -/
noncomputable def totalReturn (m : Model Ω D) (ω : Ω) (s : Strategy D) : ℝ :=
  ∑' j : ℕ, stageReturn m ω s j

end KarlinDynamicProgramming.Uniqueness


