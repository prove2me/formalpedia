-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpanSInduction
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpanSInduction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:01.688545+00:00
-- url     : https://prove2.me/theorems/6a271364-8bfd-4d30-bb71-d4af1dd4da78
-- title:
--   Span SInduction
-- statement:
--   Definitions and structural lemmas for Span SInduction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SpanSInduction.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Qe24.spanS.{u_1, u_2} :
    {K : Type u_1} →
      {V : Type u_2} →
        [inst : Field K] →
          [inst_1 : AddCommGroup V] →
            [inst_2 : _root_.Module K V] → (S : Subring K) → {n : ℕ} → (Fin n → V) → Submodule (↥S) V :=
    fun {K : Type u_1} {V : Type u_2} [Field K] [AddCommGroup V] [_root_.Module K V] (S : Subring K) {n : ℕ}
        (x : Fin n → V) ↦
      Submodule.span (↥S) (Set.range x)


