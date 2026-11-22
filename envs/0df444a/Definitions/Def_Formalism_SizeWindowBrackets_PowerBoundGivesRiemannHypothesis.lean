-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_PowerBoundGivesRiemannHypothesis
-- name    : Formalism_SizeWindowBrackets_PowerBoundGivesRiemannHypothesis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:17:14.021376+00:00
-- url     : https://prove2.me/theorems/d57efbff-66bd-4278-b0c5-83caed685e3f
-- title:
--   Power Bound Gives Riemann Hypothesis
-- statement:
--   Definitions and structural lemmas for Power Bound Gives Riemann Hypothesis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/PowerBoundGivesRiemannHypothesis.lean

import Definitions.Def_Formalism_StatementOC
import Mathlib.NumberTheory.LSeries.RiemannZeta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LFunctionChainParameters.ConditionalMainTheorem
open Formalism
def LandauZeroFreeHalfPlane : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ y₀ : ℝ, (∀ y : ℝ, y₀ ≤ y → Gz y ≤ y ^ θ) →
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0
def PowerBoundGivesRiemannHypothesis : Prop :=
  ∀ C ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Gz x ≤ x ^ (1 / 2 + C * ε)) →
    RiemannHypothesis
end Formalism.LFunctionChainParameters.ConditionalMainTheorem


