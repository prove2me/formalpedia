-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueOfIsAdicComplete
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueOfIsAdicComplete
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:57:56.574507+00:00
-- url     : https://prove2.me/theorems/35725b93-96c3-4a28-9a9f-6af2832a26b0
-- title:
--   Exists Unique Of Is Adic Complete
-- statement:
--   Definitions and structural lemmas for Exists Unique Of Is Adic Complete, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueOfIsAdicComplete.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedSplitTorusOfPowEqOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id)
open IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TorsionLift
variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  [IsCommMonObj G] [Smooth G.hom]
noncomputable def step (I : Ideal R) (n : ℕ) : (R ⧸ I ^ (n + 1 + 1)) →ₐ[R] R ⧸ I ^ (n + 1) :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ _))
noncomputable def ptsEquiv {S S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] (T : Over S')
    (t : T.left ⟶ S) (ht : T.hom ≫ p = t) :
    (T ⟶ (Over.pullback p).obj G) ≃* (Over.mk t ⟶ G) := by
  subst ht
  exact { ((Over.mapPullbackAdj p).homEquiv T G).symm with
    map_mul' := adjunction_homEquiv_symm_mul (Over.mapPullbackAdj p) }
end GlobalTheory.TorsionLift
namespace GlobalTheory
open TorsionLift
end GlobalTheory


