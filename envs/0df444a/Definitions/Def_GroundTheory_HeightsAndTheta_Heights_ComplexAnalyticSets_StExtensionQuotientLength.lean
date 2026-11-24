-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StExtensionQuotientLength
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StExtensionQuotientLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:05.492297+00:00
-- url     : https://prove2.me/theorems/66821d37-6c0a-4252-b826-5011ec728518
-- title:
--   St Extension Quotient Length
-- statement:
--   Definitions and structural lemmas for St Extension Quotient Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StExtensionQuotientLength.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
def ExtensionQuotientLength.Statement : Prop :=
  ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (r : R),
    Function.Injective (algebraMap R B) → algebraMap R B r ∈ nonZeroDivisors B →
    Module.length R (B ⧸ LinearMap.range (Algebra.linearMap R B)) ≠ ⊤ →
    Module.length R (R ⧸ Ideal.span {r}) = Module.length R (B ⧸ Ideal.span {algebraMap R B r})
end GroundTheory.Heights₂.Heights


