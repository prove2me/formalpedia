-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSideRanks
-- name    : IntMul_Kappa_R8_Data_BitOppbankSideRanks
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:33:04.52811+00:00
-- url     : https://prove2.me/theorems/3ff13a77-e37e-4439-95e0-ceefc4d2c061
-- title:
--   R7/R8 side-chain rank multiset (Jain witness 2)
-- statement:
--   # Side-chain rank multiset
--
--   From Jain `certificate_round7.build` on witness 2: the multiset of charged $h$-space chain-step ranks used when rebuilding bit histograms (plain and opp-bank). Twenty rank bins; total multiplicity $162155$. Schedule metadata for the BitNB transplant.
-- source:
--   Jain integer-mult-kappa certificate_round7.build (rk) on certificates/round7 witness 2.

import Mathlib.Data.Nat.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Side-chain rank multiset of Jain round-7 witness 2

`rk` from `certificate_round7.build`: counts of charged h-space chain steps by rank.
Used by both plain and opp-bank histogram rebuilds. Schedule metadata for BitNB transplant.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank

def sideChainRankHist : List (ℕ × ℕ) :=
  [(1, 50763), (2, 71662), (3, 9939), (4, 13176), (5, 6400), (6, 1869), (7, 703), (8, 1127), (9, 585), (10, 219), (11, 235), (12, 243), (13, 188), (14, 141), (15, 668), (16, 1009), (17, 473), (18, 36), (19, 2219), (21, 500)]

def sideChainRankHist_count : ℕ := (sideChainRankHist.map (·.2)).sum

theorem sideChainRankHist_count_eq :
    sideChainRankHist_count = 162155 := by decide

end IntMul.Kappa.R8.Bit.Oppbank


