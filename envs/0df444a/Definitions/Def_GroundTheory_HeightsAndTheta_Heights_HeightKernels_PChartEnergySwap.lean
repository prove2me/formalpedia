-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:52:50.16221+00:00
-- url     : https://prove2.me/theorems/fc4673ae-2369-4a31-b07a-95105e8642f6
-- title:
--   PChart Energy Swap
-- statement:
--   Definitions and structural lemmas for PChart Energy Swap, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySwap.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartHessHolo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Matrix MeasureTheory Filter Topology
open scoped ComplexOrder
noncomputable section
namespace ChartEnergySwapHessian
open ChartMongeAmpereAffineInvariance
variable {e : ℕ}
def chartInv (y : Fin (e + 1) → ℂ) : Fin (e + 1) → ℂ := fun j => (y 0)⁻¹ * (if j = 0 then 1 else y j)
def logCoord (y : Fin (e + 1) → ℂ) (y' : Fin (e + 1) → ℂ) : ℂ :=
  Complex.log (y' 0 / y 0) + (Real.log ‖y 0‖ : ℂ)
end ChartEnergySwapHessian
end
end GroundTheory.Heights₂.Heights


