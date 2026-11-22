-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_SplitExtDefs
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_SplitExtDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:23:09.888274+00:00
-- url     : https://prove2.me/theorems/d6e738d4-b7fe-4e46-b152-ae565348a789
-- title:
--   Split Ext Defs
-- statement:
--   Definitions and structural lemmas for Split Ext Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/AbelianSchemeQuotients/SplitExtDefs.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Semi
structure SplitExt (S : Scheme.{u}) where

  B : Over S
  [grpB : GrpObj B]
  isAbelian : IsAbelianScheme B

  X : Type u
  [addCommGroup : AddCommGroup X]
  [free : Module.Free ℤ X]
  [finite : Module.Finite ℤ X]

  O : X → RigLB B

  addIso : ∀ χ χ' : X, ∃ t : LB.Iso (O χ').L (LB.div (O (χ + χ')).L (O χ).L), t.IsGen

  zeroTriv : ∃ t : LB.Gen (O 0).L, t.IsGen

  primitive : ∀ χ : X, ∃ t : LB.Gen (abelian₂ B (O χ).L), t.IsGen
attribute [instance] SplitExt.grpB SplitExt.addCommGroup
end ReciprocityTheory.ChartRestriction.G.Semi


