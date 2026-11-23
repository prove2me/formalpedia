-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:31.543134+00:00
-- url     : https://prove2.me/theorems/fe67e609-683d-4e72-921b-5bbd44f60560
-- title:
--   Is Scheme Theoretically Dominant Spec Of Injective
-- statement:
--   Definitions and structural lemmas for Is Scheme Theoretically Dominant Spec Of Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecOfInjective.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
namespace GlobalTheory.ExtUnique
variable {U S : Scheme.{u}} (j : U ⟶ S) [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
end GlobalTheory.ExtUnique
namespace GlobalTheory.ExtUnique
variable {U S : Scheme.{0}} {j : U ⟶ S} [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
def intAct {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] : OAct ℤ G where
  act n := 𝟙 G ^ n
  hom n := by
    induction n using Int.induction_on with
    | zero => rw [zpow_zero, Hom.one_def]; infer_instance
    | succ n ih => rw [zpow_add_one, Hom.mul_def]; infer_instance
    | pred n ih => rw [zpow_sub_one, Hom.mul_def]; infer_instance
  one := zpow_one _
  mul a b := by rw [GrpObj.comp_zpow, Category.comp_id, zpow_mul]
  add a b := zpow_add _ _ _
end GlobalTheory.ExtUnique
namespace GlobalTheory
open ExtUnique
end GlobalTheory


