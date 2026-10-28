-- Prove2me | Definitions.Def_fd03_localHedge
-- name    : fd03_localHedge
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:58:59.193534+00:00
-- url     : https://prove2.me/theorems/bfb18e24-7741-4e7a-8954-1cfb54b85ecf
-- title:
--   One-step stock-and-bank replicating holdings
-- statement:
--   For a node stock price S, market multipliers u,d,R and required up/down continuation payments Vᵤ,Vₔ, the local hedge is a pair of real holdings (shares Δ, bank value b). It is defined by Δ=(Vᵤ−Vₔ)/(S(u−d)) and b=(uVₔ−dVᵤ)/(R(u−d)). Exact up/down replication is a separate theorem assuming S>0.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.2–10.4, printed pp. 182–189. Original explicit stock-and-bank holdings obtained by solving the two-state replication equations.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_BinomialMarket

namespace FinancialDerivatives.FD03

/-- One-step replicating shares and current bank holdings. -/
noncomputable def localHedge (m : BinomialMarket)
    (spot upValue downValue : ℝ) : ℝ × ℝ :=
  ((upValue - downValue) / (spot * (m.up - m.down)),
   (m.up * downValue - m.down * upValue) /
     (m.growth * (m.up - m.down)))

end FinancialDerivatives.FD03


