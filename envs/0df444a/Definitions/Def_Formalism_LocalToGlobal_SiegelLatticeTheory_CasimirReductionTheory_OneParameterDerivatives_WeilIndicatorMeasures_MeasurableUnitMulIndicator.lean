-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CasimirReductionTheory_OneParameterDerivatives_WeilIndicatorMeasures_MeasurableUnitMulIndicator
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CasimirReductionTheory_OneParameterDerivatives_WeilIndicatorMeasures_MeasurableUnitMulIndicator
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:11:49.84467+00:00
-- url     : https://prove2.me/theorems/01eb68d2-b6a4-4805-bf3e-0a86229e05d7
-- title:
--   Measurable Unit Mul Indicator
-- statement:
--   Definitions and structural lemmas for Measurable Unit Mul Indicator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CasimirReductionTheory/OneParameterDerivatives/WeilIndicatorMeasures/MeasurableUnitMulIndicator.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Set Filter
open scoped ENNReal NNReal Pointwise
namespace Formalism.L2.SG.Pf.Weil
namespace QuotInt
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] {H : Subgroup G}
noncomputable def fib (κ : Measure H) (f : G → ℝ≥0∞) (g : G) : ℝ≥0∞ := ∫⁻ h, f (g * h) ∂κ
section Main
variable (μ : Measure G) (ν : Measure H)
noncomputable def qmeas (H : Subgroup G) (μ : Measure G) (β : G → ℝ≥0∞) : Measure (G ⧸ H) :=
  (μ.withDensity β).map ((↑) : G → G ⧸ H)
variable [SFinite μ] [μ.IsMulRightInvariant] [SFinite ν] [ν.IsMulLeftInvariant]
  {β : G → ℝ≥0∞} (hβ : Measurable β) (hβ1 : ∀ x, ∫⁻ h, β (x * (h : G)⁻¹) ∂ν = 1)
include hβ hβ1
end Main
end QuotInt
end Formalism.L2.SG.Pf.Weil


