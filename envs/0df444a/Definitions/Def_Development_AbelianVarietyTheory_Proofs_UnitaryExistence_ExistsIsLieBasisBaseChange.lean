-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsLieBasisBaseChange
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsLieBasisBaseChange
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T14:40:19.820955+00:00
-- url     : https://prove2.me/theorems/4b87c4ff-d32a-59fa-95b7-25d7f7595232
-- title:
--   Exists Is Lie Basis Base Change
-- statement:
--   Definitions and structural lemmas for Exists Is Lie Basis Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIsLieBasisBaseChange.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp

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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp IsTan
open TrivSqZeroExt (inl inr)
namespace GlobalTheory.LieBaseChange
open GlobalTheory.SqZero
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
def pushRHom (P : Type) [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P] :
    (sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) →* (sp (R₀ := R) P ⟶ G) where
  toFun := pushR G
  map_one' := pushR_one G
  map_mul' y y' := by
    have h := map_mul (pushHom (isGrpPullback_pullback G (fB R R')) (sp (R₀ := R') P)) y y'
    exact (congrArg (iotaB ≫ ·) h).trans (MonObj.comp_mul _ _ _)
variable {G} {n : ℕ}
def bcVec (R' : Type) [CommRing R'] [Algebra R R'] (v : Fin n → (epsR R ⟶ G)) (i : Fin n) :
    epsR R' ⟶ (Over.pullback (fB R R')).obj G :=
  pullR (R' := R') G (spMap (dualMapA R R') ≫ v i)
end GlobalTheory.LieBaseChange
namespace GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (spMap)
end GlobalTheory


