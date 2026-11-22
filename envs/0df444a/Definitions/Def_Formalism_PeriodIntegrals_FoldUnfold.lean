-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_FoldUnfold
-- name    : Formalism_PeriodIntegrals_FoldUnfold
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:04.663624+00:00
-- url     : https://prove2.me/theorems/209d598c-99ed-4c74-b0cc-d5f5ee1f4b5e
-- title:
--   Fold Unfold
-- statement:
--   Definitions and structural lemmas for Fold Unfold, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/FoldUnfold.lean

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
namespace PI.FoldUnfold
def FoldUnfold : Prop :=
  ∀ (G : Type*) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ S : Subgroup G) [Countable Γ], S ≤ Γ →
  ∀ (F : Set G), IsFundamentalDomain S F μ →
  ∀ (FΓ : Set G), IsFundamentalDomain Γ FΓ μ →
  ∀ (D : Set G), Formalism.L2.SG.FoldBound.IsRightTransversal Γ S D →
  ∀ (f : G → ℝ≥0∞), Measurable f → (∀ s ∈ S, ∀ y : G, f (s * y) = f y) →
    (∫⁻ x in FΓ, ∑' δ : D, f ((δ : G) * x) ∂μ) = ∫⁻ y in F, f y ∂μ
end PI.FoldUnfold


