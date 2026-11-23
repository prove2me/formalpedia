-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__LogDerOne_a1ce1da79bfc3842
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__LogDerOne_a1ce1da79bfc3842
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:55.495342+00:00
-- url     : https://prove2.me/theorems/51307be5-4d17-4901-91f6-1c929d46a20a
-- title:
--   Log Der One
-- statement:
--   Definitions and structural lemmas for Log Der One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/LogDerOne.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GlobalTheory.Mem.An
def LogDerOne : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
    ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 - zsum χ 0 1 (fun ρ => 1 / (1 - ρ))‖ ≤
      C * Real.log (3 * q)
end GlobalTheory.Mem.An


