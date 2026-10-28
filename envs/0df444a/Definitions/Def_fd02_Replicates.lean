-- Prove2me | Definitions.Def_fd02_Replicates
-- name    : fd02_Replicates
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T23:36:37.408645+00:00
-- url     : https://prove2.me/theorems/5c5a37d7-1820-428a-9395-224a7180bf63
-- title:
--   Exact payoff replication in both states
-- statement:
--   Exact replication requires equality of the portfolio and contingent-claim payoffs in both terminal states.
-- source:
--   Original derived definition based on Wilmott, Howison and Dewynne (1995), §2.4 and §10.3, printed pp. 30–31 and 187; https://doi.org/10.1017/CBO9780511812545. The same object is fixed for all FD-02 theorem statements.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_terminalPayoff

namespace FinancialDerivatives.FD02

/-- A trade replicates a claim if its payoff matches in each state. -/
def Replicates (m : TwoStateMarket) (t : Trade) (H : Bool → ℝ) : Prop :=
  ∀ ω : Bool, terminalPayoff m t ω = H ω

end FinancialDerivatives.FD02


