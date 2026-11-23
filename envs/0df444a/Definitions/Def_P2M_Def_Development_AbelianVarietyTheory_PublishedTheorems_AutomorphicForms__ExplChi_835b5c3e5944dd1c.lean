-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExplChi_835b5c3e5944dd1c
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExplChi_835b5c3e5944dd1c
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:10.551802+00:00
-- url     : https://prove2.me/theorems/3d8f1417-18c4-469c-ac5f-7e1c17a35b3a
-- title:
--   Expl Chi
-- statement:
--   Definitions and structural lemmas for Expl Chi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExplChi.lean

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
def ExplChi : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive → ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    ‖psiChi χ x + zsum χ 0 T (fun ρ => (x : ℂ) ^ ρ / ρ) + ((Real.log (x - 1) / 2 : ℝ) : ℂ) +
        χ (-1) / 2 * ((Real.log (x + 1) : ℝ) : ℂ) -
        (deriv (DirichletCharacter.LFunction χ⁻¹) 1 / DirichletCharacter.LFunction χ⁻¹ 1 +
          ((Real.log (q / (2 * Real.pi)) - Real.eulerMascheroniConstant : ℝ) : ℂ))‖ ≤
      C * (Real.log x + x / T * Real.log (q * x * T) ^ 2)
end GlobalTheory.Mem.An


