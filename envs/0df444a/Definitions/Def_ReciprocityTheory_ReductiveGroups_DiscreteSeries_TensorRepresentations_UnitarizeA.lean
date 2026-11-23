-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_UnitarizeA
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_UnitarizeA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:31:50.682876+00:00
-- url     : https://prove2.me/theorems/beb5137a-2a04-4be4-9712-cc16515b0a87
-- title:
--   Unitarize A
-- statement:
--   Definitions and structural lemmas for Unitarize A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/UnitarizeA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.UnitA
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] (μ : Measure G)
def pr (a b : G → ℂ) : ℂ := ∫ x, star (a x) * b x ∂μ
def nrm (a : G → ℂ) : ℝ := (eLpNorm a 2 μ).toReal
variable {μ}
section Invariant
variable [μ.IsMulRightInvariant]
end Invariant
section Flow
variable [μ.IsMulRightInvariant] [SFinite μ]
end Flow
end ReciprocityTheory.ChartRestriction.DS.UnitA


