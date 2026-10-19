-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_Resampling
-- name    : OAI_Probability_CriticalZ3_Resampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:54:48.268288+00:00
-- url     : https://prove2.me/theorems/29595158-a8cc-443d-8bc0-e8cc0bed4c97
-- title:
--   Finite stochastic matrices and their averaging action
-- statement:
--   Elementary tools for finite Markov transitions on a finite nonempty set $I$.
--
--   1. **Extremes.** For $f:I\to\mathbb R$, the lower and upper values are $\min_if(i)$ and $\max_if(i)$.
--   2. **Transitions.** A transition consists of weights $K(i,j)\ge0$ with $\sum_jK(i,j)=1$ for every $i$.
--   3. **Action.** A transition acts on functions by averaging,
--   $$
--   (Kf)(i)=\sum_jK(i,j)\,f(j),
--   $$
--   so $Kf$ lies between the minimum and the maximum of $f$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Resampling.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Resampling.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CriticalZ3 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces

namespace OAI

universe uI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
open scoped ENNReal

open scoped BigOperators Matrix
open Filter

namespace FiniteResampling
variable {I : Type uI} [Fintype I] [Nonempty I]

noncomputable def lower (f : I → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty f
noncomputable def upper (f : I → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty f

structure Transition (I : Type uI) [Fintype I] where
  weight : I → I → ℝ
  nonneg : ∀ i j, 0 ≤ weight i j
  total : ∀ i, ∑ j, weight i j = 1

namespace Transition
variable (K : Transition I)
noncomputable def act (f : I → ℝ) (i : I) : ℝ := ∑ j, K.weight i j * f j

end Transition
end FiniteResampling

end OAI


