-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FinrankSecPullSandwich
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FinrankSecPullSandwich
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:56:20.100269+00:00
-- url     : https://prove2.me/theorems/9898ae96-9654-496e-9baa-89acc4e371ab
-- title:
--   Finrank Sec Pull Sandwich
-- statement:
--   Definitions and structural lemmas for Finrank Sec Pull Sandwich, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FinrankSecPullSandwich.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCommonMultiple
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecValEqIff
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_compat
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_FiniteCover_generic_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom


set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.FiniteCover
variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
theorem generic_mem_preimage (φ : X' ⟶ X) [Surjective φ] {U : X.Opens} (h : genericPoint X ∈ U) :
    genericPoint X' ∈ φ ⁻¹ᵁ U := by
  obtain ⟨y, hy⟩ := φ.surjective (genericPoint X)
  exact generic_mem (x := y) (show φ y ∈ U from hy ▸ h)
def powSec {X : Scheme.{0}} {H : LB X} (s : LB.Sec H) (t : ℕ) : LB.Sec (pw H t) where
  f k := (s.f k : Γ(X, H.U k)) ^ t
  compat i j := by
    have e := congrArg (· ^ t) (s.compat i j)
    simp only [mul_pow, ← map_pow] at e
    refine e.trans ?_
    congr 1
end GlobalTheory.FiniteCover
namespace GlobalTheory
open FiniteCover
end GlobalTheory


