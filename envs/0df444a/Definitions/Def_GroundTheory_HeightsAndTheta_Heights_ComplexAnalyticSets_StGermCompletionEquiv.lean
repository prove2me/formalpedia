-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermCompletionEquiv
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermCompletionEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:02.679898+00:00
-- url     : https://prove2.me/theorems/af6add88-85d0-4354-b0b9-2a6666b7f716
-- title:
--   St Germ Completion Equiv
-- statement:
--   Definitions and structural lemmas for St Germ Completion Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StGermCompletionEquiv.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiObjects
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
def GermCompletionEquiv.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    ∃ e : AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w)) ≃+*
        AdicCompletion (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I),
      ∀ q : MvPolynomial σ ℂ,
        e (AdicCompletion.of (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))
            (Ideal.Quotient.mk (I.map (polyGerm w)) (polyGerm w q))) =
          AdicCompletion.of (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I) (Ideal.Quotient.mk I q)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


