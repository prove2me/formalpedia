-- Prove2me | Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
-- name    : OAI_Combinatorics_BooleanFunctions_Projection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:21:39.784127+00:00
-- url     : https://prove2.me/theorems/165209c0-16df-4d36-aaeb-0753acceacdb
-- title:
--   Occupied cells have positive mass, and conditioning fixes functions of the observation
-- statement:
--   Let $A$ be a finite nonempty set with the uniform average $\mathbb{E}$ and let $F:A\to B$ be a map. Use the cell masses $m_F(b)=|F^{-1}(b)|/|A|$ and the conditional averages $\mathbb{E}[\,\cdot\mid F]$ (fibre averages) of the conditioning file. This file records two basic facts.
--
--   1. **Occupied cells have positive mass.** For every $x\in A$,
--   $$m_F\big(F(x)\big)>0 .$$
--   2. **Conditioning fixes functions of the observation.** For every $g:B\to\mathbb{R}$,
--   $$\mathbb{E}[\,g\circ F\mid F\,]=g\circ F .$$
--
--   The first fact guarantees that the denominator in $\mathbb{E}[g\mid F](x)$ never vanishes, so the conditional value at an actual point is a genuine fibre average. The second is the familiar rule that a known quantity is its own conditional expectation; for example, applied to the identity map of the one-coordinate cube it shows that the score of that observation is the cube sum itself.
--
--   **Formalization Note** The lemmas are `Projection.cellMass_pos` and `Projection.conditional_comp`; both assume `Fintype` and `Nonempty` for the domain and no finiteness of the label type.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Projection.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Projection.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SquareRootDegree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Projection
attribute [local instance] Classical.propDecidable
variable {α β γ κ : Type*} [Fintype α] [Nonempty α] [Fintype β] [Fintype γ]

end Projection
end SquareRootDegree

namespace SquareRootDegree
namespace Projection
attribute [local instance] Classical.propDecidable

variable {α β γ : Type*} [Fintype α] [Nonempty α] [Fintype β]

omit [Fintype β] in
theorem cellMass_pos (F : α → β) (x : α) : 0 < cellMass F (F x) := by
  unfold cellMass average
  apply mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  apply Finset.sum_pos'
  · intro y _
    unfold cell
    split_ifs <;> positivity
  · exact ⟨x,Finset.mem_univ x,by simp [cell]⟩

omit [Fintype β] in
theorem conditional_comp (F : α → β) (g : β → ℝ) :
    conditionalAverage F (fun x => g (F x)) = fun x => g (F x) := by
  funext x
  unfold conditionalAverage conditionalValue
  have he : cellMoment F (fun y => g (F y)) (F x) = g (F x)*cellMass F (F x) := by
    unfold cellMoment cellMass
    rw [← average_const_mul]
    congr 1
    funext y
    by_cases h : F y = F x <;> simp [cell,h]
  rw [he,mul_div_cancel_right₀ _ (cellMass_pos F x).ne']

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end Projection
end SquareRootDegree

end

end OAI


