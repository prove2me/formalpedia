-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ClosureUpperUni
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ClosureUpperUni
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:34:33.896853+00:00
-- url     : https://prove2.me/theorems/328ee440-fdbb-4163-bf4b-d27ed53dadee
-- title:
--   Closure Upper Uni
-- statement:
--   Definitions and structural lemmas for Closure Upper Uni, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ClosureUpperUni.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Qe27.upperUni :
    (k : ℕ) → (A : Type) → [inst : CommRing A] → Set (GL (Fin k) A) :=
    fun (k : ℕ) (A : Type) [CommRing A] ↦
      {x : GL (Fin k) A |
        ∀ (i j : Fin k),
          (j < i → (↑x : Matrix (Fin k) (Fin k) A) i j = (0 : A)) ∧ (↑x : Matrix (Fin k) (Fin k) A) i i = (1 : A)}


