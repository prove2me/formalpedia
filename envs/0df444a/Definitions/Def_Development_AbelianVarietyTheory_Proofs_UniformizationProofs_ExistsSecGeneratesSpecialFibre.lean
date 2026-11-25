-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecGeneratesSpecialFibre
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecGeneratesSpecialFibre
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:19:58.989485+00:00
-- url     : https://prove2.me/theorems/133ddb64-718b-5611-ad74-039dab559993
-- title:
--   Exists Sec Generates Special Fibre
-- statement:
--   Definitions and structural lemmas for Exists Sec Generates Special Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecGeneratesSpecialFibre.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Theorems.Thm_GlobalTheory_PrimeSection_appLE_res
import Theorems.Thm_GlobalTheory_PrimeSection_res_appLE
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ


set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory
namespace SpecialFibreGenerator
open TopologicalSpace Opposite
variable {X Y : Scheme.{0}}
noncomputable def secAlong {L : LB X} (s : L.Sec) (φ : Y ⟶ X) :
    (LB.LinComb L (K := Fin 1) (fun _ ↦ φ) fun _ ↦ ((1 : ℕ) : ℤ)).Sec where
  f a := φ.appLE (L.U (a 0)) (LB.wchart L (fun _ ↦ φ) a) (LB.wchart_le L (fun _ ↦ φ) a 0) (s.f (a 0))
  compat a b := by
    have hle : LB.wchart L (fun _ : Fin 1 ↦ φ) a ⊓ LB.wchart L (fun _ : Fin 1 ↦ φ) b ≤
        φ ⁻¹ᵁ (L.U (a 0) ⊓ L.U (b 0)) :=
      inf_le_inf (LB.wchart_le L (fun _ ↦ φ) a 0) (LB.wchart_le L (fun _ ↦ φ) b 0)
    have h := congrArg (φ.appLE (L.U (a 0) ⊓ L.U (b 0)) _ hle) (s.compat (a 0) (b 0))
    rw [map_mul] at h
    have hg : ((LB.LinComb L (K := Fin 1) (fun _ ↦ φ) fun _ ↦ ((1 : ℕ) : ℤ)).g a b).val =
        φ.appLE (L.U (a 0) ⊓ L.U (b 0)) _ hle (L.g (a 0) (b 0)).val := by
      simp only [LB.LinComb, Fin.prod_univ_one, Nat.cast_one, zpow_one]
      rfl
    rw [hg]
    refine ((PrimeSection.res_appLE φ _ _ _).trans (PrimeSection.appLE_res φ _ _ _).symm).trans
      (h.trans (congrArg (_ * ·) ?_))
    exact (PrimeSection.appLE_res φ _ _ _).trans (PrimeSection.res_appLE φ _ _ _).symm
end SpecialFibreGenerator
end GlobalTheory


