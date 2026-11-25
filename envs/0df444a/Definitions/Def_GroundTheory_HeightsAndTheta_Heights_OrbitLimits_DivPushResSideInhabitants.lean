-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_DivPushResSideInhabitants
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_DivPushResSideInhabitants
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T12:46:40.442378+00:00
-- url     : https://prove2.me/theorems/a28db80c-72d7-5510-a0a5-7b1bd82f6826
-- title:
--   Div Push Res Side Inhabitants
-- statement:
--   Definitions and structural lemmas for Div Push Res Side Inhabitants, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/DivPushResSideInhabitants.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_KerEqBotOfCoord
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsPushForwardOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularDens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
def PushForwardOpen.projLineAffineCoordinate : OnePoint ℂ → Fin 1 → ℂ := fun x _ => crd0 x
def PushForwardOpen.finitePlane : Set (OnePoint ℂ) := Set.range ((↑) : ℂ → OnePoint ℂ)
abbrev ProjRegular.pointV : Set ProjectiveLineResolution.res.X := {((0 : ℂ) : OnePoint ℂ)}
instance ProjRegular.instUniquePointV : Unique ProjRegular.pointV :=
  Set.uniqueSingleton _
def ProjRegular.projFirstCoordinate : (((k : Unit) → PBlk 2 k) → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) :=
  LinearMap.pi fun _ : Fin 1 =>
    LinearMap.proj (R := ℂ) (φ := fun _ : ((k : Unit) → PBlk 2 k) => ℂ) (fun _ => 0)
end GroundTheory.Heights₂.Heights.Targets


