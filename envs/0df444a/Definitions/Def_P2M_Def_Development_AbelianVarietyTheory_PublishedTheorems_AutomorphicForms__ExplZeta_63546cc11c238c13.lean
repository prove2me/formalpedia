-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExplZeta_63546cc11c238c13
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExplZeta_63546cc11c238c13
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:46.821814+00:00
-- url     : https://prove2.me/theorems/14a2126e-269e-4398-8776-4dca1630ec4b
-- title:
--   Expl Zeta
-- statement:
--   Definitions and structural lemmas for Expl Zeta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExplZeta.lean

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
def ExplZeta : Prop :=
  ∃ C : ℝ, ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    ‖psiChi (1 : DirichletCharacter ℂ 1) x - (x : ℂ) + zsum (1 : DirichletCharacter ℂ 1) 0 T (fun ρ => (x : ℂ) ^ ρ / ρ) +
        ((Real.log (2 * Real.pi) + Real.log (1 - 1 / x ^ 2) / 2 : ℝ) : ℂ)‖ ≤
      C * (Real.log x + x / T * Real.log (x * T) ^ 2)
end GlobalTheory.Mem.An


