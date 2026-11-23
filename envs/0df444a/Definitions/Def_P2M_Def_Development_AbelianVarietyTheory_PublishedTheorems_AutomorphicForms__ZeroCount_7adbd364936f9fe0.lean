-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ZeroCount_7adbd364936f9fe0
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ZeroCount_7adbd364936f9fe0
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:38.941798+00:00
-- url     : https://prove2.me/theorems/5d2629e8-27a7-4da3-84d0-0eb4eb4eb459
-- title:
--   Zero Count
-- statement:
--   Definitions and structural lemmas for Zero Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ZeroCount.lean

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
def ZeroCount : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ t : ℝ,
    zsumR χ t 1 (fun _ => 1) ≤ C * Real.log (q * (|t| + 2))
end GlobalTheory.Mem.An


