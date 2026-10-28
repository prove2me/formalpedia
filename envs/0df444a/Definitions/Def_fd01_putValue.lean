-- Prove2me | Definitions.Def_fd01_putValue
-- name    : fd01_putValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T13:29:14.660339+00:00
-- url     : https://prove2.me/theorems/0e1e0a37-7f3b-480f-b1dd-c2ce82c7014a
-- title:
--   European put price under state-price valuation
-- statement:
--   European put price under state-price valuation. This definition fixes the meaning of a terminal contingent payment, its valuation date, or the finite market structure used by the option-price surface. All amounts are real-valued and share the same expiry.
--
--   $$
--   P(K)=\sum_\omega\pi_\omega\max(K-s_\omega,0)
--   $$
--
--   This is a model definition, and any mathematical consequences require separate proofs.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 38, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. European put price under state-price valuation

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price

namespace FinancialDerivatives.FD01

noncomputable def FinitePriceSystem.putValue {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K : ℝ) : ℝ :=
  m.price (fun ω => max (K - s ω) 0)

end FinancialDerivatives.FD01


