-- Prove2me | Definitions.Def_fd01_FinitePriceSystem
-- name    : fd01_FinitePriceSystem
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T13:28:20.837989+00:00
-- url     : https://prove2.me/theorems/a4199cb5-e8fc-417b-9fe6-346c5e005612
-- title:
--   Finite-state nonnegative pricing system
-- statement:
--   Finite-state nonnegative pricing system. This definition fixes the meaning of a terminal contingent payment, its valuation date, or the finite market structure used by the option-price surface. All amounts are real-valued and share the same expiry.
--
--   $$
--   \pi_\omega\geq0,\quad D=\sum_\omega\pi_\omega>0
--   $$
--
--   This is a model definition, and any mathematical consequences require separate proofs.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 41, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. Finite-state nonnegative pricing system

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FinancialDerivatives.FD01

structure FinitePriceSystem (Ω : Type*) [Fintype Ω] [Nonempty Ω] where
  statePrice : Ω → ℝ
  statePrice_nonneg : ∀ ω, 0 ≤ statePrice ω
  discount : ℝ
  discount_pos : 0 < discount
  statePrice_sum : (∑ ω, statePrice ω) = discount

end FinancialDerivatives.FD01


