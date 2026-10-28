-- Prove2me | Definitions.Def_fd01_callValue
-- name    : fd01_callValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T13:29:03.060053+00:00
-- url     : https://prove2.me/theorems/14a386d0-2014-481b-a696-084221e7a6a9
-- title:
--   European call price under state-price valuation
-- statement:
--   European call price under state-price valuation. This definition fixes the meaning of a terminal contingent payment, its valuation date, or the finite market structure used by the option-price surface. All amounts are real-valued and share the same expiry.
--
--   $$
--   C(K)=\sum_\omega\pi_\omega\max(s_\omega-K,0)
--   $$
--
--   This is a model definition, and any mathematical consequences require separate proofs.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 36, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. European call price under state-price valuation

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price

namespace FinancialDerivatives.FD01

noncomputable def FinitePriceSystem.callValue {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K : ℝ) : ℝ :=
  m.price (fun ω => max (s ω - K) 0)

end FinancialDerivatives.FD01


