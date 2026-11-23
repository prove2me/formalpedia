-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LcgLinCombEqProd
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LcgLinCombEqProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:40:14.825059+00:00
-- url     : https://prove2.me/theorems/36a8f649-426b-478d-ab39-d55607bcda49
-- title:
--   Lcg Lin Comb Eq Prod
-- statement:
--   Definitions and structural lemmas for Lcg Lin Comb Eq Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LcgLinCombEqProd.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
lemma boxGen_overlap_le {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (a b : K → (LB.LinComb L F (fun _ => 1)).ι) (i : J) :
    LB.wchart (LB.LinComb L F (fun _ => 1)) φ a ⊓ LB.wchart (LB.LinComb L F (fun _ => 1)) φ b ≤
      LB.wchart (L.pull (F i)) φ (fun k _ => a k i) ⊓
        LB.wchart (L.pull (F i)) φ (fun k _ => b k i) := by
  have key : ∀ c : K → (LB.LinComb L F (fun _ => 1)).ι,
      LB.wchart (LB.LinComb L F (fun _ => 1)) φ c ≤ LB.wchart (L.pull (F i)) φ (fun k _ => c k i) := by
    intro c y hy
    simp only [LB.wchart, LB.pull, LB.LinComb, TopologicalSpace.Opens.mem_mk, Set.mem_iInter,
      Set.mem_preimage, SetLike.mem_coe] at hy ⊢
    intro k _
    exact hy k i
  exact inf_le_inf (key a) (key b)
end GlobalTheory


