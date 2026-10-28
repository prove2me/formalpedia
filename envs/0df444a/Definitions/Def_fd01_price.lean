-- Prove2me | Definitions.Def_fd01_price
-- name    : fd01_price
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T13:28:33.440501+00:00
-- url     : https://prove2.me/theorems/56b5a5f2-33e5-4286-9b45-f681fd22b0b1
-- title:
--   State-price valuation of a terminal claim
-- statement:
--   State-price valuation of a terminal claim. This definition fixes the meaning of a terminal contingent payment, its valuation date, or the finite market structure used by the option-price surface. All amounts are real-valued and share the same expiry.
--
--   $$
--   \mathcal V(f)=\sum_\omega\pi_\omega f_\omega
--   $$
--
--   This is a model definition, and any mathematical consequences require separate proofs.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 41, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. State-price valuation of a terminal claim

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem

namespace FinancialDerivatives.FD01

noncomputable def FinitePriceSystem.price {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (m : FinitePriceSystem Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, m.statePrice ω * f ω

end FinancialDerivatives.FD01


