-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsGoodProjFirstCoordinate
-- name    : Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsGoodProjFirstCoordinate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:25.978697+00:00
-- url     : https://prove2.me/theorems/96d65430-ad21-4d1f-b376-9f29841bb2ee
-- title:
--   Exists Good Proj First Coordinate
-- statement:
--   Definitions and structural lemmas for Exists Good Proj First Coordinate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/ExistsGoodProjFirstCoordinate.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__PoincareLelong_e61d89ea90cf58ae
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__SheetDensityEqSetSheetDensity_cb85824e9bfdd8ba
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_CxPosDens
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_CxSimple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartProjObjects
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MemChartComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreCoordGoodProj
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
def segMonC (i : (k : K) → ι k) : MRingOver ℂ ι := ∏ k, X ⟨k, i k⟩
def segC (Q : Ideal (MRingOver ℂ ι)) (i : (k : K) → ι k) : MRingOver ℂ ι ⧸ Q :=
  Ideal.Quotient.mk _ (segMonC i)
def evC (Q : Ideal (MRingOver ℂ ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ conePts Q) :
    (MRingOver ℂ ι ⧸ Q) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ Q (aeval z) fun a ha => by
    have h := hz.2 a ha
    rw [← coe_aeval_eq_eval] at h
    exact h
end GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj


