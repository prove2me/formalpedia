-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AemeasurableCxPosDensity
-- name    : Development_AutomorphicSpectrum_Proofs_MetricProofs_AemeasurableCxPosDensity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:41.373331+00:00
-- url     : https://prove2.me/theorems/99282437-25b4-4547-99f7-74465b48ba42
-- title:
--   Aemeasurable Cx Pos Density
-- statement:
--   Definitions and structural lemmas for Aemeasurable Cx Pos Density, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/AemeasurableCxPosDensity.lean

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
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsSumMeasurableA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SetFibreFiniteOfGoodProj
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
namespace GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas
open MvPolynomial MeasureTheory Metric Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
  GlobalTheory.CompanionTheory.Ar.Pub.CxComp
open ReciprocityTheory.AnForm.R (conePts)
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
def setSecSet (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (B : Set (Fin e → ℂ)) : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) :=
  {G | (∀ y ∉ B, G y = 0) ∧ DifferentiableOn ℂ G B ∧ ∀ y ∈ B, G y ∈ setFibre S Ψ y}
def setBadSet (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Set (Fin e → ℂ) :=
  {y | ∃ w γ γ', IsSetSheet S Ψ y w γ ∧ IsSetSheet S Ψ y w γ' ∧
    ¬ ((fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y'))}
end GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas


