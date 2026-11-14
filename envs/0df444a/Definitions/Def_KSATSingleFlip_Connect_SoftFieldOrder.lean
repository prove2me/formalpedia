-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_SoftFieldOrder
-- name    : KSATSingleFlip_Connect_SoftFieldOrder
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T10:19:08.655389+00:00
-- url     : https://prove2.me/theorems/cf99f086-bc7d-4936-b625-551cdffc2437
-- title:
--   Concave-test order for soft-field measures
-- statement:
--   The relation ν′ ⪯ ν holds when the weighted pairing against every continuous concave test on [0,1] vanishing at both endpoints is no larger for ν′ than for ν. The paper applies this relation to symmetric measures with finite scaled unfrozen mass; those assumptions are stated where needed.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, immediately before Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
namespace KSATSingleFlip.Connect

/-- Concave-test order from Lemma 4.5. In the paper it is applied to symmetric measures with finite unfrozen mass. -/
def softFieldLE (ν' ν : Measure ℝ) : Prop :=
  ∀ ψ : ℝ → ℝ, ContinuousOn ψ (Icc 0 1) → ConcaveOn ℝ (Icc 0 1) ψ → ψ 0 = 0 → ψ 1 = 0 →
    pairing ψ ν' ≤ pairing ψ ν

end KSATSingleFlip.Connect


