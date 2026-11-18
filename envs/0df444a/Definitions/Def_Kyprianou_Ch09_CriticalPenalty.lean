-- Prove2me | Definitions.Def_Kyprianou_Ch09_CriticalPenalty
-- name    : Kyprianou_Ch09_CriticalPenalty
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T15:16:15.761752+00:00
-- url     : https://prove2.me/theorems/0ae939cf-7380-4450-81c0-633cb48d346c
-- title:
--   Kyprianou (2006) Chapter 9 canonical source owner CriticalPenalty
-- statement:
--   Common critical stopping-game penalty and boundary-regime definitions. This source Definition module provides the actual declarations: gameLowerBarrier, gameCriticalPenalty, gamePenaltyAt. The binding scopes, mathematical hypotheses and exact meaning are given by the complete Lean source included here; no published theorem proof is assumed.
-- source:
--   A. E. Kyprianou (2006), first edition, Chapter 9, printed pp. 239–270, physical PDF pp. 247–278; Chapter 3 completed-natural-filtration provider as cited in source imports.

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace Kyprianou.Ch09.B1

/-- Equation (9.39) in the log-price coordinate. -/
noncomputable def gameLowerBarrier (K psiPrime psiOne : ℝ) : ℝ :=
  Real.log (K * psiPrime / psiOne)

/-- The common corrected penalty threshold of Theorem 9.14(a,b).
The printed part (b) has the closing parenthesis outside this logarithm. -/
noncomputable def gameCriticalPenalty
    (K psiPrime psiOne : ℝ) (W : ℝ → ℝ) : ℝ :=
  K * psiOne *
    ∫ y in (0 : ℝ)..Real.log (psiOne / psiPrime),
      Real.exp (-y) * W y

/-- The game penalty as a function of the lower log-price threshold. -/
noncomputable def gamePenaltyAt
    (K psiOne z : ℝ) (W : ℝ → ℝ) : ℝ :=
  K * psiOne *
    ∫ y in (0 : ℝ)..(Real.log K - z),
      Real.exp (-y) * W y

/-- The source's (9.39) identifies the two integration limits exactly. -/
theorem gameLowerBarrier_log_identity
    (K psiPrime psiOne : ℝ)
    (hK : 0 < K) (hp : 0 < psiPrime) (hψ : 0 < psiOne) :
    Real.log K - gameLowerBarrier K psiPrime psiOne =
      Real.log (psiOne / psiPrime) := by
  unfold gameLowerBarrier
  rw [Real.log_div (mul_ne_zero (ne_of_gt hK) (ne_of_gt hp))
        (ne_of_gt hψ)]
  rw [Real.log_mul (ne_of_gt hK) (ne_of_gt hp)]
  rw [Real.log_div (ne_of_gt hψ) (ne_of_gt hp)]
  ring

/-- The critical penalty is the game penalty at the McKean lower barrier. -/
theorem gameCriticalPenalty_eq_at_lower_barrier
    (K psiPrime psiOne : ℝ) (W : ℝ → ℝ)
    (hK : 0 < K) (hp : 0 < psiPrime) (hψ : 0 < psiOne) :
    gameCriticalPenalty K psiPrime psiOne W =
      gamePenaltyAt K psiOne (gameLowerBarrier K psiPrime psiOne) W := by
  unfold gameCriticalPenalty gamePenaltyAt
  rw [gameLowerBarrier_log_identity K psiPrime psiOne hK hp hψ]

end Kyprianou.Ch09.B1


