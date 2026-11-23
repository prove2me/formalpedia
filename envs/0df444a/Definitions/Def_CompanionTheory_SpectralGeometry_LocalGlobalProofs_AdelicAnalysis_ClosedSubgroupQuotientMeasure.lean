-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ClosedSubgroupQuotientMeasure
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ClosedSubgroupQuotientMeasure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:49.43142+00:00
-- url     : https://prove2.me/theorems/173050c2-c4e5-42a8-b63b-221a89652ba9
-- title:
--   Closed Subgroup Quotient Measure
-- statement:
--   Definitions and structural lemmas for Closed Subgroup Quotient Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ClosedSubgroupQuotientMeasure.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_Bruhat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW
noncomputable def closedEmbeddingRangeEquiv {G G₁ : Type} [Group G] [TopologicalSpace G]
    [Group G₁] [TopologicalSpace G₁] (ι : G₁ →* G) (hι : IsClosedEmbedding ι) :
    G₁ ≃ₜ* ι.range :=
  have hemb : IsEmbedding ι.rangeRestrict :=
    IsEmbedding.of_comp (hι.continuous.subtype_mk _) continuous_subtype_val hι.isEmbedding
  { MulEquiv.ofBijective ι.rangeRestrict
      ⟨hemb.injective, ι.rangeRestrict_surjective⟩ with
    continuous_toFun := hemb.continuous
    continuous_invFun :=
      (hemb.toHomeomorphOfSurjective ι.rangeRestrict_surjective).symm.continuous }
end GlobalTheory.CompanionTheory.SW


