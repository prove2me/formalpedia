-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftErrorLocal
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftErrorLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:44:41.544239+00:00
-- url     : https://prove2.me/theorems/1596c7b2-ae14-4712-b582-f0b2a9583ef1
-- title:
--   Lift Error Local
-- statement:
--   Definitions and structural lemmas for Lift Error Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/LiftErrorLocal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.LiftErrorLocal.ShellInt :
    Prop :=
    ∀ (X : Type) [inst : MeasurableSpace X] (μ : MeasureTheory.Measure X) (N : X → ℝ) (C d A : ℝ),
      Measurable N →
        (∀ᵐ (x : X) ∂μ, (1 : ℝ) ≤ N x) →
          (0 : ℝ) ≤ d →
            (∀ (R : ℝ), (1 : ℝ) ≤ R → (μ : Set X → ENNReal) {x : X | N x ≤ R} ≤ ENNReal.ofReal (C * R ^ d)) →
              d < A → ∫⁻ (x : X), ENNReal.ofReal (N x ^ (-A)) ∂μ < ⊤


