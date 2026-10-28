-- Prove2me | Definitions.Def_fd01_spotValue
-- name    : fd01_spotValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T13:28:48.385983+00:00
-- url     : https://prove2.me/theorems/040bd10a-5a20-46f8-84a0-033c3be73cbe
-- title:
--   Current price of the modelled underlying
-- statement:
--   Current price of the modelled underlying. This definition fixes the meaning of a terminal contingent payment, its valuation date, or the finite market structure used by the option-price surface. All amounts are real-valued and share the same expiry.
--
--   $$
--   S_0=\mathcal V(s)=\sum_\omega\pi_\omega s_\omega
--   $$
--
--   This is a model definition, and any mathematical consequences require separate proofs.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 41, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. Current price of the modelled underlying

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price

namespace FinancialDerivatives.FD01

noncomputable def FinitePriceSystem.spotValue {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (m : FinitePriceSystem Ω) (s : Ω → ℝ) : ℝ := m.price s

end FinancialDerivatives.FD01


