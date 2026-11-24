-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeG
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:34.171901+00:00
-- url     : https://prove2.me/theorems/4f2bcf31-31c5-4336-bc7d-ae2c006ff3b0
-- title:
--   Inter Bridge G
-- statement:
--   Definitions and structural lemmas for Inter Bridge G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeG.lean

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
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Set Filter Topology Function
variable {e : ℕ}
def jacN (Q : (Fin e → ℂ) → (Fin e → ℂ)) (u : Fin e → ℂ) : ℝ :=
  ‖LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2
def fibSum (D : Set (Fin e → ℂ)) (Q : (Fin e → ℂ) → (Fin e → ℂ)) (h : (Fin e → ℂ) → ℝ)
    (y : Fin e → ℂ) : ℝ :=
  ∑ᶠ u ∈ D ∩ Q ⁻¹' {y}, h u / jacN Q u
end ReciprocityTheory.ChartRestriction.G.Geo


