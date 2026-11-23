-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_HomExtDvrSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_HomExtDvrSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:29.78965+00:00
-- url     : https://prove2.me/theorems/c39b3489-a04d-4962-8603-a8bb7f3366fc
-- title:
--   Hom Ext Dvr St
-- statement:
--   Definitions and structural lemmas for Hom Ext Dvr St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/HomExtDvrSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableReductionPlusSplit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
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
namespace ReciprocityTheory.ChartRestriction.G.Out
open Semi
def HomExtDvrSt : Prop :=
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    (G G' : Over (Spec (CommRingCat.of T))) [GrpObj G] [GrpObj G'],
    IsSemiAbelian G → IsSemiAbelian G' →
    ∀ φ : genFibre T G ⟶ genFibre T G', IsMonHom φ →
      ∃! ψ : G ⟶ G', IsMonHom ψ ∧ (Over.pullback (specMap T (FractionRing T))).map ψ = φ
structure Laws7 : Prop where
  homExtDvr : HomExtDvrSt
end ReciprocityTheory.ChartRestriction.G.Out


