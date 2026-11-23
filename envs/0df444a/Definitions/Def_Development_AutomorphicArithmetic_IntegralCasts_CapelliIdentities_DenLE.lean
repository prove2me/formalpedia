-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DenLE
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DenLE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:43.506053+00:00
-- url     : https://prove2.me/theorems/9c68c72c-ac14-4043-95ce-192a4eec0c6b
-- title:
--   Den LE
-- statement:
--   Definitions and structural lemmas for Den LE, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DenLE.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Yhb9.DenLE :
    {V H : Type} →
      [inst : MeasurableSpace V] →
        [inst_1 : MeasurableSpace H] → MeasureTheory.Measure V → MeasureTheory.Measure H → (V → H) → Set V → ENNReal → Prop :=
    fun {V H : Type} [MeasurableSpace V] [MeasurableSpace H] (μ : MeasureTheory.Measure V) (ν : MeasureTheory.Measure H)
        (q : V → H) (S : Set V) (C : ENNReal) ↦
      ∀ (Y : Set H), MeasurableSet Y → (μ : Set V → ENNReal) (S ∩ q ⁻¹' Y) ≤ C * (ν : Set H → ENNReal) Y


