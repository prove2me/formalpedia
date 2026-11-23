-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_EmbTraceSum
-- name    : Formalism_PeriodIntegrals_EmbTraceSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:34.606659+00:00
-- url     : https://prove2.me/theorems/5b37c4ee-6dd7-4dc7-8e76-0b808ef40dfe
-- title:
--   Emb Trace Sum
-- statement:
--   Definitions and structural lemmas for Emb Trace Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/EmbTraceSum.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
def EmbTraceSum : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (K : IntermediateField ℚ E) (φ₀ : E →+* ℂ) (S : Type) [Fintype S]
    (emb : S → E →+* ℂ), Function.Injective emb → (∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E)) →
    Fintype.card S = Module.finrank K E →
    ∀ y : E, ∑ s, emb s y = φ₀ ((Algebra.trace K E y : K) : E)
end PI


