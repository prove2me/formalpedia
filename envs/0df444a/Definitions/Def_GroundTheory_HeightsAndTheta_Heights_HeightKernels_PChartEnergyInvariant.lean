-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyInvariant
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyInvariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:45.13134+00:00
-- url     : https://prove2.me/theorems/d2c159f9-1ff3-4705-901b-e862187a3cec
-- title:
--   PChart Energy Invariant
-- statement:
--   Definitions and structural lemmas for PChart Energy Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyInvariant.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartMassInvariant
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace ChartEnergyInvariance
open ChartMongeAmpereAffineInvariance
def EnergyInvariantUnder {e : ℕ} (C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) : Prop :=
  ∀ M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ, M.PosDef → N.PosDef → ∀ k : ℕ,
    chartMixedEnergy (Cᴴ * M * C) (Cᴴ * N * C) k = chartMixedEnergy M N k
variable {e : ℕ}
end ChartEnergyInvariance
end
end GroundTheory.Heights₂.Heights


