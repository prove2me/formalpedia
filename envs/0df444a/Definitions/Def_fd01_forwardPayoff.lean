-- Prove2me | Definitions.Def_fd01_forwardPayoff
-- name    : fd01_forwardPayoff
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T13:28:11.453166+00:00
-- url     : https://prove2.me/theorems/6cb932e2-340c-43f1-be35-339128988c90
-- title:
--   European forward terminal payoff
-- statement:
--   European forward terminal payoff. This definition fixes the meaning of a terminal contingent payment, its valuation date, or the finite market structure used by the option-price surface. All amounts are real-valued and share the same expiry.
--
--   $$
--   f_K(s)=s-K
--   $$
--
--   This is a model definition, and any mathematical consequences require separate proofs.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 40, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. European forward terminal payoff

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FinancialDerivatives.FD01

noncomputable def forwardPayoff (s K : ℝ) : ℝ := s - K

end FinancialDerivatives.FD01


