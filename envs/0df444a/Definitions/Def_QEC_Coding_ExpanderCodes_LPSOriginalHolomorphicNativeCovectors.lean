-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicNativeCovectors
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicNativeCovectors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:33:15.260597+00:00
-- url     : https://prove2.me/theorems/b541e19c-99f2-472b-a32c-47233481ccda
-- title:
--   LPSOriginal Holomorphic Native Covectors
-- statement:
--   Definitions and structural lemmas for LPSOriginal Holomorphic Native Covectors, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicNativeCovectors.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorCoordinates
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_complexChartTransition_analytic_unit
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCovectorChartCoefficient_cocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
lemma lpsOriginalHolomorphicCovector_allChart_analytic
    (sigma : LPSOriginalHolomorphicCovectorSections N hN)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z ∈ (chartAt ℂ x).target) :
    AnalyticAt ℂ (lpsOriginalFilledCovectorChartCoefficient N hN (fun y => sigma y) x) z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let e := chartAt ℂ x
  let y := e.symm z
  let d := chartAt ℂ y
  let g := e.symm.trans d
  have hy : y ∈ e.source := e.map_target hz
  have hsrc : z ∈ g.source := ⟨hz, mem_chart_source ℂ y⟩
  have hvalue : g z = d y := rfl
  have ha := complexChartTransition_analytic_unit x y z hsrc
  have hc : AnalyticAt ℂ
      (lpsOriginalFilledCovectorChartCoefficient N hN (fun t => sigma t) y) (g z) := by
    change AnalyticAt ℂ (lpsOriginalHolomorphicCovectorChartCoefficient N hN sigma y) (g z)
    rw [hvalue]
    exact lpsOriginalHolomorphicCovectorChartCoefficient_analytic N hN sigma y
  have he : lpsOriginalFilledCovectorChartCoefficient N hN (fun t => sigma t) x =ᶠ[𝓝 z]
      ((lpsOriginalFilledCovectorChartCoefficient N hN (fun t => sigma t) y ∘ g) * deriv g) := by
    filter_upwards [g.open_source.mem_nhds hsrc] with w hw
    exact lpsOriginalFilledCovectorChartCoefficient_cocycle N hN (fun t => sigma t) x y w hw
  exact ((hc.comp ha.1).mul ha.1.deriv).congr he.symm
def lpsOriginalHolomorphicCovectorToMeromorphicLinearMap :
    LPSOriginalHolomorphicCovectorSections N hN →ₗ[ℂ]
      LPSOriginalFilledMeromorphicCovectorRepresentatives N hN := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact
    { toFun := fun sigma => ⟨fun y => sigma y, fun x z hz =>
        (lpsOriginalHolomorphicCovector_allChart_analytic N hN sigma x z hz).meromorphicAt⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
def lpsOriginalHolomorphicCovectorToClassLinearMap :
    LPSOriginalHolomorphicCovectorSections N hN →ₗ[ℂ]
      LPSOriginalCompactMeromorphicCovectorGerms N hN :=
  (lpsOriginalCompactMeromorphicCovectorClass N hN).comp
    (lpsOriginalHolomorphicCovectorToMeromorphicLinearMap N hN)
end
end QEC.Coding.TannerLiftedProduct


