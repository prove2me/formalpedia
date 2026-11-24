-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsBis
-- name    : GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsBis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:44.79286+00:00
-- url     : https://prove2.me/theorems/412929c1-19d0-4b03-8a7d-bb721e687566
-- title:
--   Imports Bis
-- statement:
--   Definitions and structural lemmas for Imports Bis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/ImportsBis.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_SymbolExtensionProperty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.EffectiveHS
open ReciprocityTheory.AnForm.M
def TopFormNormEqIntegral.Statement : Prop :=
  ∀ (D : ℕ) (X : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    (A : FinHolAtlas D X) (B : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A)
    (ψ : Fin A.n → X → ℝ) (F : Fin A.n → X → ℂ),
    IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.IsWeight B ψ → F ∈ IndefiniteRowSideFullHecke.EffectiveHS.topForms B →
    topNormSq A ψ F = IndefiniteRowSideFullHecke.EffectiveHS.topFormWeightedL2 ψ F
end GroundTheory.Heights₂.Heights.EffectiveHS


