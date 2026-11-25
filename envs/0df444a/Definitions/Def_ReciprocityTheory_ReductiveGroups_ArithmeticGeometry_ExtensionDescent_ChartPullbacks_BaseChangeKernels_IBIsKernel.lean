-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_IBIsKernel
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_IBIsKernel
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:22:19.262874+00:00
-- url     : https://prove2.me/theorems/fe9f23c0-cb63-5b77-aa8f-8428621fb587
-- title:
--   IBIs Kernel
-- statement:
--   Definitions and structural lemmas for IBIs Kernel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/IBIsKernel.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PullbackSquarePartialSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor PullGtPf
section Maps
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X]
def hT : (splitTorus S' X).left ⟶ (splitTorus S X).left :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ f) (specULiftZIsTerminal.hom_ext _ _)
lemma hT_snd : hT f X ≫ (splitTorus S X).hom = (splitTorus S' X).hom ≫ f := by
  unfold hT
  exact pullback.lift_snd _ _ _
variable {G B : Over S} [GrpObj G] [GrpObj B] (q : G ⟶ B)
abbrev qB : (Over.pullback f).obj G ⟶ (Over.pullback f).obj B := (Over.pullback f).map q
variable (i : splitTorus S X ⟶ G)
def iB : splitTorus S' X ⟶ (Over.pullback f).obj G :=
  Over.homMk ((isGrpPullback_pullback G f).1.lift (hT f X ≫ i.left) (splitTorus S' X).hom (by
    rw [Category.assoc, Over.w i]; exact hT_snd f X))
    ((isGrpPullback_pullback G f).1.lift_snd _ _ _)
end Maps
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf


