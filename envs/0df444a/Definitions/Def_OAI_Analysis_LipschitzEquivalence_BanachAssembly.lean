-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
-- name    : OAI_Analysis_LipschitzEquivalence_BanachAssembly
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:35:32.755148+00:00
-- url     : https://prove2.me/theorems/3a373db4-a244-44b9-8448-5d6b182ba44d
-- title:
--   Separability of real ℓ²
-- statement:
--   A preliminary for assembling the final Banach spaces of the counterexample: the real sequence space
--   $$
--   \ell^2=\Bigl\{x:\mathbb N\to\mathbb R:\ \sum_n|x_n|^2<\infty\Bigr\}
--   $$
--   is separable. Finitely supported sequences with rational entries form a countable dense set.
--
--   This instance is needed so that the spaces built from $\ell^2$, such as $c_0(\ell^2)$ and the $\ell^2$-sums used later, are separable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/BanachAssembly.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/BanachAssembly.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LipschitzEquivalence mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget

namespace OAI

universe uE uX uY

noncomputable section

namespace LipschitzCounterexample
open Filter in
instance : TopologicalSpace.SeparableSpace RealL2 := by
  let S : Set RealL2 := ⋃ i : ℕ, Set.range (lp.single (E := fun _ : ℕ => ℝ) 2 i)
  have hs : TopologicalSpace.IsSeparable S :=
    TopologicalSpace.IsSeparable.iUnion (fun i =>
      TopologicalSpace.isSeparable_range (lp.isometry_single i).continuous)
  have hd : Dense (Submodule.span ℝ S : Set RealL2) := by
    intro s
    apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by simp) s).tendsto_sum_nat
    apply Eventually.of_forall
    intro n
    apply subset_closure
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.subset_span
    exact Set.mem_iUnion.2 ⟨i, ⟨s i, rfl⟩⟩
  exact hd.isSeparable_iff.mp hs.span

namespace Criterion
open WeakSequences
open scoped NNReal

end Criterion
end LipschitzCounterexample

end

end OAI


