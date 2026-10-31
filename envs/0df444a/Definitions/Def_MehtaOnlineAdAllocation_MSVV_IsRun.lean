-- Prove2me | Definitions.Def_MehtaOnlineAdAllocation_MSVV_IsRun
-- name    : MehtaOnlineAdAllocation_MSVV_IsRun
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:38:20.058831+00:00
-- url     : https://prove2.me/theorems/2f0f6d93-51d9-415d-ba5c-6b1e77d2ac3f
-- title:
--   Algorithm 10 — capped MSVV run
-- statement:
--   At query $t$, set $\widehat b_{ut}=\min\{b_{ut},B_u-S_u(t)\}$ and give advertiser $u$ score $\widehat b_{ut}\psi(S_u(t)/B_u)$. A run either selects an advertiser with unspent budget whose score is maximal over all advertisers, or rejects only if every score is zero. The selected advertiser pays the capped bid, through the spend definition, rather than its score. All ties are allowed. Zero-score assignments to available advertisers have no state or revenue effect and may instead be rejected.
--
--   The test at time $t$ uses only earlier assignments, known budgets and the current bid column. Quantifying over every run includes every online tie-breaking rule, with no requirement that the entire input be supplied to a policy. It also allows every possible legal tie resolution on a fixed input, so cannot omit an online run.
-- source:
--   Aranyak Mehta, Online Matching and Ad Allocation, Foundations and Trends in Theoretical Computer Science 8(4), 265–368, 2013, DOI 10.1561/0400000057 (published), Algorithm 10, printed p. 311 (PDF p. 49), together with the all-algorithms capping convention, p. 308 (PDF p. 46).

import Definitions.Def_MehtaOnlineAdAllocation_MSVV_Spend
import Definitions.Def_MehtaOnlineAdAllocation_MSVV_psi

namespace MehtaOnlineAdAllocation.MSVV

noncomputable def cappedBid {N M : ℕ} (I : Instance N M)
    (σ : Allocation N M) (u : Fin N) (t : Fin M) : ℝ :=
  min (I.bid u t) (I.budget u - spend I σ u t.val)

noncomputable def score {N M : ℕ} (I : Instance N M)
    (σ : Allocation N M) (u : Fin N) (t : Fin M) : ℝ :=
  cappedBid I σ u t * psi (spend I σ u t.val / I.budget u)

def IsRun {N M : ℕ} (I : Instance N M) (σ : Allocation N M) : Prop :=
  ∀ t, match σ t with
  | none => ∀ u, score I σ u t = 0
  | some u => spend I σ u t.val < I.budget u ∧
      ∀ v, score I σ v t ≤ score I σ u t

end MehtaOnlineAdAllocation.MSVV


