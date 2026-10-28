-- Prove2me | Definitions.Def_fd04_upperBarrierTouched
-- name    : fd04_upperBarrierTouched
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T10:47:32.490992+00:00
-- url     : https://prove2.me/theorems/907162cc-c6b5-4bdd-9bae-476ce24fb392
-- title:
--   Discrete upper-barrier touch event
-- statement:
--   The barrier is hit if an explicitly supplied observation path contains any stock price greater than or equal to level B. Equality counts as a touch.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic

namespace FinancialDerivatives.FD04

/-- A discretely observed upper barrier, with equality a touch. -/
noncomputable def upperBarrierTouched (B : ℝ) (observedSpots : List ℝ) : Bool := by
  classical
  exact observedSpots.any (fun spot => decide (B ≤ spot))

end FinancialDerivatives.FD04


