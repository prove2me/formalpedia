-- Prove2me | Definitions.Def_Submission_Weighted_Schedule
-- name    : Submission_Weighted_Schedule
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:09.139456+00:00
-- url     : https://prove2.me/theorems/db7b29f2-f307-4ddb-a620-c3e94d8bb719
-- title:
--   Schedule
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Schedule.lean

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
set_option autoImplicit false
namespace ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration
def fixedLength (m : ℕ) : ℕ := 30000000000000*m
def fixedPi (m : ℕ) : DigitType :=
  ![24361752111000*m,4760008248000*m,878239641000*m]
def fixedAlpha (m : ℕ) : DigitType :=
  ![27034502782000*m,2672750671000*m,292746547000*m]
def sourceRank (m : ℕ) : ℕ := 3258243765000*m
def bankCut (m : ℕ) : ℕ := 3130753934820264*m
def dropBudget (m : ℕ) : ℕ := 206565920180736*m
def treeBudget (m : ℕ) : ℕ := dropBudget m+1024
end ThreeSum.WeightedSchedule


