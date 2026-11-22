-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:40:21.7664+00:00
-- url     : https://prove2.me/theorems/881fb68a-0e9f-451c-b2c4-4af9f4319742
-- title:
--   Fold Bound
-- statement:
--   Definitions and structural lemmas for Fold Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/FoldBound.lean

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
open scoped ENNReal NNReal
namespace Formalism.L2.SG.FoldBound
def mult {G : Type*} [Group G] (Γ : Subgroup G) (Ω : Set G) (x : G) : ℝ≥0∞ :=
  ⨆ y : G, ((({γ : Γ | x⁻¹ * ((γ : G) * y) ∈ Ω} : Set Γ).encard : ℕ∞) : ℝ≥0∞)
def IsRightTransversal {G : Type*} [Group G] (Γ S : Subgroup G) (D : Set G) : Prop :=
  D ⊆ (Γ : Set G) ∧ ∀ γ ∈ Γ, ∃! p : S × D, ((p.1 : G) * (p.2 : G)) = γ
def quotientLIntegral {G : Type*} [MeasurableSpace G] (μ : Measure G) (F : Set G) (Ph : G → ℂ) : ℝ≥0∞ :=
  ∫⁻ y in F, ‖Ph y‖ₑ ∂μ
set_option linter.dupNamespace false in

def FoldBound (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] : Prop :=
  ∀ (Γ S : Subgroup G), DiscreteTopology Γ → S ≤ Γ →
  ∀ (Ω : Set G), MeasurableSet Ω →
  ∀ (a : ℝ≥0) (Ph : G → ℂ), Measurable Ph →
    (∀ s ∈ S, ∀ y : G, Ph (s * y) = Ph y) →
    (∀ y : G, ‖Ph y‖ₑ ≤ (a : ℝ≥0∞) * ∫⁻ ω in Ω, ‖Ph (y * ω)‖ₑ ∂μ) →
  ∀ (F : Set G), IsFundamentalDomain S F μ →
  ∀ (D : Set G), IsRightTransversal Γ S D →
  ∀ x : G,
    ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ ≤ (a : ℝ≥0∞) * mult Γ Ω x * quotientLIntegral μ F Ph
end Formalism.L2.SG.FoldBound


