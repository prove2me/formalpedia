-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualEnergyCharts
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualEnergyCharts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:21.575818+00:00
-- url     : https://prove2.me/theorems/83da032f-c76a-4d26-bf98-d74f25b11c4a
-- title:
--   PDual Energy Charts
-- statement:
--   Definitions and structural lemmas for PDual Energy Charts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualEnergyCharts.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualEnergyCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_restr_bijective_ef7ba566aeb7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter Topology Matrix NumberField
open scoped ComplexOrder
noncomputable section
namespace DualEnergyChartsAlt
open StandardDualMassAtPoint DualGeometricDegreeCharts
variable {K : Type} [Field K] [NumberField K] {T : Type} [Fintype T] [DecidableEq T]
  {D : ℕ} {F : HermLattice K (D + 1)}
def chartMat (hOf : DualPtsOfPlane.Statement) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    {Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)} (hΨ : IsGoodProj (dualIdeal b) Ψ)
    (σ : K →+* ℂ) : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ :=
  LinearMap.toMatrix' (LinearEquiv.ofBijective _ (restr_bijective hOf b hb hΨ σ)).symm.toLinearMap
end DualEnergyChartsAlt
end
end GroundTheory.Heights₂.Heights


