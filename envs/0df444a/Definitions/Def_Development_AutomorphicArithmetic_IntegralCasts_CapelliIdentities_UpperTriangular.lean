-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UpperTriangular
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UpperTriangular
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:31.201826+00:00
-- url     : https://prove2.me/theorems/9f75e505-c0f9-4f51-88a6-4da1f1444b42
-- title:
--   Upper Triangular
-- statement:
--   Definitions and structural lemmas for Upper Triangular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/UpperTriangular.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.UpperTriangular.UT :
    {L : Type} → [Field L] → {n : ℕ} → Matrix (Fin n) (Fin n) L → Prop :=
  fun {_} _ {n} A => (∀ i j : Fin n, j < i → A i j = 0) ∧ ∀ i : Fin n, A i i = 1


