-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularLocusDense
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularLocusDense
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:36.750949+00:00
-- url     : https://prove2.me/theorems/437dd541-2b39-4dae-a8b1-1544f8a53ec4
-- title:
--   PRegular Locus Dense
-- statement:
--   Definitions and structural lemmas for PRegular Locus Dense, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularLocusDense.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticImplicitChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Module
open scoped ContDiff
section Germs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Germs
noncomputable def conormalSpan {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) (z : σ → ℂ) :
    Submodule ℂ ((σ → ℂ) →L[ℂ] ℂ) :=
  Submodule.span ℂ {ℓ | ∃ h : (σ → ℂ) → ℂ, AnalyticAt ℂ h z ∧ (∀ᶠ u in 𝓝 z, u ∈ Y → h u = 0) ∧
    fderiv ℂ h z = ℓ}
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


