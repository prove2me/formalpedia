-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpanTopFamily
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpanTopFamily
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:54:06.946232+00:00
-- url     : https://prove2.me/theorems/e0234105-c171-4fa3-9e3a-1eae302a9a8f
-- title:
--   Span Top Family
-- statement:
--   Definitions and structural lemmas for Span Top Family, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SpanTopFamily.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.SpanTopFamily.Mι :
    {E K : Type} →
      [inst : Field E] →
        [inst_1 : Field K] →
          (O : ValuationSubring K) →
            (E →+* K) → {n : Type} → Submodule (NumberField.RingOfIntegers E) (n → E) → Submodule (↥O) (n → K) :=
    fun {E K : Type} [Field E] [Field K] (O : ValuationSubring K) (ι : E →+* K) {n : Type}
        (L : Submodule (NumberField.RingOfIntegers E) (n → E)) ↦
      Submodule.span (↥O) ((fun (l : n → E) (j : n) ↦ (ι : E → K) (l j)) '' (↑L : Set (n → E)))


