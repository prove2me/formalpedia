-- Prove2me | Definitions.Def_MehtaOnlineAdAllocation_MSVV_psi
-- name    : MehtaOnlineAdAllocation_MSVV_psi
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:36:40.732351+00:00
-- url     : https://prove2.me/theorems/08c3b9e1-a889-487f-990f-c4e2f874f5de
-- title:
--   Algorithm 10 — exponential bid scaling
-- statement:
--   The exact exponential scaling function is $\psi(x)=1-\exp(x-1)$. The MSVV rule evaluates it at the fraction of the advertiser’s actual capped budget spent. In particular $\psi(0)=1-\exp(-1)$ and $\psi(1)=0$. There is no discretization parameter in this function.
-- source:
--   Aranyak Mehta, Online Matching and Ad Allocation, Foundations and Trends in Theoretical Computer Science 8(4), 265–368, 2013, DOI 10.1561/0400000057 (published), Algorithm 10, printed p. 311 (PDF p. 49).

import Mathlib

namespace MehtaOnlineAdAllocation.MSVV

noncomputable def psi (x : ℝ) : ℝ := 1 - Real.exp (x - 1)

end MehtaOnlineAdAllocation.MSVV


