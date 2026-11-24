-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegCharts
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegCharts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:49.043458+00:00
-- url     : https://prove2.me/theorems/30792b89-34da-4525-a736-6e9deb2960bb
-- title:
--   PDual Geom Deg Charts
-- statement:
--   Definitions and structural lemmas for PDual Geom Deg Charts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegCharts.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualGeomDegCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOfPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOnPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt
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
namespace DualGeometricDegreeCharts
open StandardDualMassAtPoint
variable {K : Type} [Field K] [NumberField K] {T : Type} [Fintype T] [DecidableEq T]
  {D : ℕ} {F : HermLattice K (D + 1)}
def planeLin (b : Module.Basis T ℤ (dualLattice F)) (σ : K →+* ℂ) :
    (Fin (D + 1) → ℂ) →ₗ[ℂ] (((k : Unit) → dualBlocks T k) → ℂ) where
  toFun v := segre (ι := dualBlocks T) (dualPlanePt b σ v)
  map_add' v v' := by
    funext s
    simp [segre, dualPlanePt, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext s
    simp [segre, dualPlanePt, Finset.mul_sum, mul_left_comm]
def recLin (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) :
    ((Σ _ : Unit, T) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ) :=
  (LinearMap.pi fun j => LinearMap.proj (σ, j)) ∘ₗ (dualRecover b hb).toLinearMap ∘ₗ
    (LinearMap.pi fun t => LinearMap.proj ⟨(), t⟩)
end DualGeometricDegreeCharts
end
end GroundTheory.Heights₂.Heights


