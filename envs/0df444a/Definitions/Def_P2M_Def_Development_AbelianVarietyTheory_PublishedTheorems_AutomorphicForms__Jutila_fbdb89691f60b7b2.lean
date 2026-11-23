-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__Jutila_fbdb89691f60b7b2
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__Jutila_fbdb89691f60b7b2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:14.910629+00:00
-- url     : https://prove2.me/theorems/8490a280-8857-4723-826f-69a150c95570
-- title:
--   Jutila
-- statement:
--   Definitions and structural lemmas for Jutila, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/Jutila.lean

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
def Jutila : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, ∀ α Q T : ℝ, 4 / 5 ≤ α → α ≤ 1 → 1 ≤ Q → 1 ≤ T →
    (({p : (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) × ℂ | 1 ≤ p.1.1 ∧ ((p.1.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.1.2.IsPrimitive ∧
        α ≤ p.2.re ∧ |p.2.im| ≤ T ∧ DirichletCharacter.LFunction p.1.2 p.2 = 0}.encard : ℕ∞) : ENNReal) ≤
      ENNReal.ofReal (c * (Q ^ 2 * T) ^ ((2 + ε) * (1 - α)))
end GlobalTheory.Mem.An


