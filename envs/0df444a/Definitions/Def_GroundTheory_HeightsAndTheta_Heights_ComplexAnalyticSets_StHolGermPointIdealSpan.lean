-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermPointIdealSpan
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermPointIdealSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:01.59481+00:00
-- url     : https://prove2.me/theorems/fb9b3caa-8413-49c6-9956-42aa37364f72
-- title:
--   St Hol Germ Point Ideal Span
-- statement:
--   Definitions and structural lemmas for St Hol Germ Point Ideal Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StHolGermPointIdealSpan.lean

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
open MvPolynomial
def HolGermPointIdealSpan.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ),
    holGermPointIdeal w = Ideal.span (Set.range fun i : σ => polyGerm w (X i - C (w i)))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


