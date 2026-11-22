-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPF
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:09:56.540561+00:00
-- url     : https://prove2.me/theorems/157faf4d-2bed-43af-b704-9283626fc75f
-- title:
--   Is PF
-- statement:
--   Definitions and structural lemmas for Is PF, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsPF.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF :
    {A : Type} → [inst : Ring A] → [Algebra ℂ A] → (ℂ → A) → Prop :=
  fun {A} _ _ f => ∃ p : Polynomial A, ∀ Y : ℂ, f Y = Polynomial.eval (algebraMap ℂ A Y) p


