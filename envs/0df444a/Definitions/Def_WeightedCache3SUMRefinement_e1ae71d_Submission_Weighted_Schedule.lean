-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Schedule
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Schedule
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:08:27.633236+00:00
-- url     : https://prove2.me/theorems/388342f6-96c8-458b-9390-7ce2b4ca90ab
-- title:
--   Schedule
-- statement:
--   Definitions and structural lemmas for Schedule, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Schedule.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration
def fixedLength (m : ℕ) : ℕ := 30000000000000000*m
def fixedPi (m : ℕ) : DigitType :=
  ![24361677233089140*m,4759532833568040*m,878789933342820*m]
def fixedAlpha (m : ℕ) : DigitType :=
  ![27034373627654100*m,2672696394564960*m,292929977780940*m]
def sourceRank (m : ℕ) : ℕ := 3258556350126840*m
def bankCut (m : ℕ) : ℕ := 8371360984307726883*m
def dropBudget (m : ℕ) : ℕ := 552323882206246677*m
def treeBudget (m : ℕ) : ℕ := dropBudget m+2739
end ThreeSum.WeightedSchedule
end WeightedCache3SUMRefinement_e1ae71d


