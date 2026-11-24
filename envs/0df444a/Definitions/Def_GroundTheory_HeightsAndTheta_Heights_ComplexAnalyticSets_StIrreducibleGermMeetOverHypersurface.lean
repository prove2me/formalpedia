-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermMeetOverHypersurface
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermMeetOverHypersurface
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:21.643002+00:00
-- url     : https://prove2.me/theorems/9de8562e-68a1-4bea-bebb-d1f1001b3a65
-- title:
--   St Irreducible Germ Meet Over Hypersurface
-- statement:
--   Definitions and structural lemmas for St Irreducible Germ Meet Over Hypersurface, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StIrreducibleGermMeetOverHypersurface.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
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
open Topology Filter
def IrreducibleGermMeetOverHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y Z : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear Y w → GermIrreducibleAt Y w → (∃ W ∈ 𝓝 w, ∀ x ∈ Y ∩ W, A x = A w → x = w) →
    IsAnalyticNear Z w → (¬ ∀ᶠ z in 𝓝 w, z ∈ Y → z ∈ Z) →
    ∃ e : (Fin d → ℂ) → ℂ, AnalyticAt ℂ e (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), e y = 0) ∧
      ∀ᶠ z in 𝓝 w, z ∈ Y → z ∈ Z → e (A z) = 0
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


