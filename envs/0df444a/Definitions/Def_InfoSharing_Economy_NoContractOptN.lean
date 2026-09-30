-- Prove2me | Definitions.Def_InfoSharing_Economy_NoContractOptN
-- name    : InfoSharing_Economy_NoContractOptN
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T23:31:32.594801+00:00
-- url     : https://prove2.me/theorems/3116bff8-04be-41d1-aa88-05ce9979c9e8
-- title:
--   Numbers of informed manufacturers attained without information contracting ($n_e^N$), §6.1
-- statement:
--   Given a payoff table $(M, R)$, information sharing without side payment (§6.1) lets the retailer choose the statuses freely, so an outcome is a status profile $X$ with $R(X) \ge R(X')$ for every profile $X'$. The set
--
--   $$\mathrm{NoContractOptN} = \{\, n(X) : X \text{ is such an outcome} \,\}$$
--
--   collects the numbers of informed manufacturers attained by these outcomes: the possible values of the paper's $n_e^N$.
--
--   Proposition 6(b) and Proposition 8(a) locate $n_e^N$ through this set.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 255, §6.1

import Mathlib
import Definitions.Def_InfoSharing_Shared_PayoffTable
open InfoSharing.Shared

namespace InfoSharing.Economy

/-- The set of numbers of informed manufacturers attained by outcomes without information
contracting (the possible values of the paper's `n_e^N`, §6.1, p. 255). -/
def NoContractOptN (P : PayoffTable) : Set ℕ :=
  {n | ∃ X : Fin 2 → Status, IsNoContractOutcome P X ∧ numInformed X = n}

end InfoSharing.Economy


