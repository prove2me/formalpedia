-- Prove2me | Definitions.Def_CountingLLL_CoinCost
-- name    : CountingLLL_CoinCost
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T09:23:02.421049+00:00
-- url     : https://prove2.me/theorems/5d08c365-808c-4d08-b6dc-4a2e6177d6ba
-- title:
--   Operational oracle cost of a local Coin call
-- statement:
--   Starting from the initial local Coin phase of Algorithm 6, define the first return as the first state that has reached either the true or false continuation. The operational Coin oracle cost is the oracle-call counter at that first return, and is infinite if the local call never returns. This is a single local call; it does not by itself represent all Coin calls of ReciprocalTest.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
set_option autoImplicit false
namespace CountingLLL.ReciprocalTest
open scoped ENNReal

/-- The local initial Coin call has returned to either its success or failure continuation. -/
def CoinReturned (ω : Entropy) : Prop :=
  ∃ t, ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase = .initialCheck ∨
    ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase = .loop

/-- Oracle calls used by the first local Coin return; infinite on nonreturning tapes. -/
noncomputable def coinOracleCost (ω : Entropy) : ℝ≥0∞ := by
  classical
  exact if h : CoinReturned ω then
    (((step ω)^[Nat.find h] ({phase := .coinOracle .initial} : State)).oracleUsed : ℝ≥0∞)
    else ⊤
end CountingLLL.ReciprocalTest


