-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:18.287749+00:00
-- url     : https://prove2.me/theorems/41cda904-7ec1-4912-9645-2725e285a49b
-- title:
--   Exists Gen Transfer
-- statement:
--   Definitions and structural lemmas for Exists Gen Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/ExistsGenTransfer.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
section Germs
def gU {X : Scheme.{0}} {O : X.Opens} (x : X) (hx : x ∈ O) : Γ(X, O)ˣ →* (X.presheaf.stalk x)ˣ :=
  Units.map (X.presheaf.germ O x hx).hom
theorem mem_wchart_pu {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (j : PUnit.{1} → L.ι) (y : Y) :
    y ∈ LB.wchart L (fun _ : PUnit.{1} => φ) j ↔ φ.base y ∈ L.U (j PUnit.unit) := by
  show y ∈ (⋂ k : PUnit.{1}, φ.base ⁻¹' (L.U (j k) : Set X)) ↔ _
  rw [Set.mem_iInter]
  exact ⟨fun h => h PUnit.unit, fun h _ => h⟩
end Germs
section Transfer
variable {X Y Z Y' : Scheme.{0}}
theorem pull_le_lemma_5 (L : LB X) (a : Y ⟶ X) (i j : PUnit.{1} → L.ι) :
    (L.pull a).U i ⊓ (L.pull a).U j ≤ a ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
  fun y hy => ⟨(mem_wchart_pu L a i y).1 hy.1, (mem_wchart_pu L a j y).1 hy.2⟩
theorem pull_inf_le (L : LB X) (a : Y ⟶ X) (i j : PUnit.{1} → L.ι) :
    (L.pull a).U i ⊓ (L.pull a).U j ≤ a ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) := fun y hy => ⟨(mem_wchart_pu L a i y).1 hy.1, (mem_wchart_pu L a j y).1 hy.2⟩
end Transfer
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison


