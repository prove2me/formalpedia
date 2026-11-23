-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LbPowDescendsOfIsotropic
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_LbPowDescendsOfIsotropic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:52.545976+00:00
-- url     : https://prove2.me/theorems/bde1c6f6-db56-4d95-98c5-fee7718d7d27
-- title:
--   Lb Pow Descends Of Isotropic
-- statement:
--   Definitions and structural lemmas for Lb Pow Descends Of Isotropic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LbPowDescendsOfIsotropic.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.ThetaSplit
@[ext] structure CocycleExt {C U : Type} (a : C → C → U) where

  u : U

  c : C
section Bundles
variable {X Y : Scheme.{0}} {L : LB X}
end Bundles
section Group
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
abbrev transl (c : 𝟙_ (Over S) ⟶ A) : A.left ⟶ A.left := ((toUnit A ≫ c) * 𝟙 A).left
end Group
end GlobalTheory.ThetaSplit
namespace GlobalTheory
end GlobalTheory


