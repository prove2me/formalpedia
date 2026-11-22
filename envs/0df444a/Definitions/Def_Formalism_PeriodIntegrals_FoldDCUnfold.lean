-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_FoldDCUnfold
-- name    : Formalism_PeriodIntegrals_FoldDCUnfold
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:54.740038+00:00
-- url     : https://prove2.me/theorems/8650e9e0-a40a-43bb-b977-de8f91975062
-- title:
--   Fold DCUnfold
-- statement:
--   Definitions and structural lemmas for Fold DCUnfold, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/FoldDCUnfold.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_PoincareSeriesSquareIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
namespace PI.FoldDCUnfold
def FoldDCUnfold : Prop :=
  ∀ (G : Type*) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ S S' : Subgroup G) [Countable Γ], S ≤ Γ → S' ≤ Γ →
  ∀ (D D' : Set G), Formalism.L2.SG.FoldBound.IsRightTransversal Γ S D →
    Formalism.L2.SG.FoldBound.IsRightTransversal Γ S' D' →
  ∀ (R : Set G), Formalism.L2.SG.PoincareSeriesSquareIntegrable.IsDoubleTransversal Γ S S' R →
  ∀ (Fs : G → Set G), (∀ r ∈ R, IsFundamentalDomain (Formalism.L2.SG.PoincareSeriesSquareIntegrable.stab S S' r) (Fs r) μ) →
  ∀ (FΓ : Set G), IsFundamentalDomain Γ FΓ μ →
  ∀ (g h : G → ℝ≥0∞), Measurable g → Measurable h →
    (∀ s ∈ S, ∀ y : G, g (s * y) = g y) → (∀ s ∈ S', ∀ y : G, h (s * y) = h y) →
    (∫⁻ x in FΓ, (∑' δ : D, g ((δ : G) * x)) * (∑' δ' : D', h ((δ' : G) * x)) ∂μ)
      = ∑' r : R, ∫⁻ x in Fs r, g x * h ((r : G)⁻¹ * x) ∂μ
end PI.FoldDCUnfold


