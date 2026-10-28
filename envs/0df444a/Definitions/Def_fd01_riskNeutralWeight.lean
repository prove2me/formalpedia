-- Prove2me | Definitions.Def_fd01_riskNeutralWeight
-- name    : fd01_riskNeutralWeight
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T13:29:30.521835+00:00
-- url     : https://prove2.me/theorems/4156a2c1-0e99-43d7-8c09-7511f4a2d4b4
-- title:
--   Normalised state price at one terminal state
-- statement:
--   Normalised state price at one terminal state. This definition fixes the meaning of a terminal contingent payment, its valuation date, or the finite market structure used by the option-price surface. All amounts are real-valued and share the same expiry.
--
--   $$
--   q_\omega=\pi_\omega/D
--   $$
--
--   This is a model definition, and any mathematical consequences require separate proofs.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 41, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. Normalised state price at one terminal state

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem

namespace FinancialDerivatives.FD01

noncomputable def FinitePriceSystem.riskNeutralWeight {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (m : FinitePriceSystem Ω) (ω : Ω) : ℝ :=
  m.statePrice ω / m.discount

end FinancialDerivatives.FD01


