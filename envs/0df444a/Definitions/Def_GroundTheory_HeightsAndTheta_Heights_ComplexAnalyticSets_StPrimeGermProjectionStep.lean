-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermProjectionStep
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermProjectionStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:54.483713+00:00
-- url     : https://prove2.me/theorems/6f74eccc-2c0c-4b96-bcbb-1e7108b24908
-- title:
--   St Prime Germ Projection Step
-- statement:
--   Definitions and structural lemmas for St Prime Germ Projection Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPrimeGermProjectionStep.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionObjects
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
noncomputable section
def PrimeGermProjectionStep.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (P : Ideal (holGerms w)), P.IsPrime → P ≠ ⊥ →
    (∀ (τ : Type) [Fintype τ], Fintype.card τ < Fintype.card σ →
      ∀ (v : τ → ℂ) (Q : Ideal (holGerms v)), Q.IsPrime →
        ∃ (d : ℕ) (B : (τ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection v Q B) →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w P A
def originIdealLine : Ideal (holGerms (0 : Fin 1 → ℂ)) :=
  RingHom.ker (Germ.valueRingHom.comp (holGerms (0 : Fin 1 → ℂ)).subtype)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


