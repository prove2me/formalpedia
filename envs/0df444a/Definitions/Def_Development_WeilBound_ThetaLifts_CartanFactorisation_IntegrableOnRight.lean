-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_IntegrableOnRight
-- name    : Development_WeilBound_ThetaLifts_CartanFactorisation_IntegrableOnRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:44.497333+00:00
-- url     : https://prove2.me/theorems/d713a4aa-a50a-4303-8ea5-116d2da29f31
-- title:
--   Integrable On Right
-- statement:
--   Definitions and structural lemmas for Integrable On Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/IntegrableOnRight.lean

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
namespace PositivityTheory.ThKF.L2
open MeasureTheory
open scoped ComplexConjugate Pointwise
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G}
def Inv (Γ : Subgroup G) (F : G → ℂ) : Prop := ∀ γ ∈ Γ, ∀ x, F (γ * x) = F x
end PositivityTheory.ThKF.L2
end


