-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CutSub
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CutSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:54.310801+00:00
-- url     : https://prove2.me/theorems/552cf46d-2e7c-483a-a345-5743598ca474
-- title:
--   Cut Sub
-- statement:
--   Definitions and structural lemmas for Cut Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CutSub.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.FirstCoordinatesSubmodule.cutSub :
    (K : Type) → [inst : Field K] → [NumberField K] → (r : ℕ) → ℕ → Submodule (NumberField.RingOfIntegers K) (Fin r → K) :=
  fun K _ _ r n =>
    { carrier := {v : Fin r → K | ∀ i : Fin r, n ≤ (i : ℕ) → v i = 0}
      add_mem' := by
        intro v w hv hw i hi
        rw [Pi.add_apply, hv i hi, hw i hi, add_zero]
      zero_mem' := fun _ _ => rfl
      smul_mem' := by
        intro c v hv i hi
        rw [Pi.smul_apply, hv i hi, smul_zero] }


