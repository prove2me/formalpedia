-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryPhysicalMomentSupport
-- name    : Submission_ThreeSum_TernaryPhysicalMomentSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:55.629319+00:00
-- url     : https://prove2.me/theorems/f27ab6a9-6c22-4772-8d32-6c39b31c6125
-- title:
--   Ternary Physical Moment Support
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalMomentSupport.lean

import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Mathlib.Data.Finset.Sort
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryPhysicalMomentSupport
open Finset FiniteMomentZeroDetector
open scoped BigOperators
variable {P : Type*} [Fintype P]
set_option maxHeartbeats 3000000
def support (mode : P → ℤ) : Finset ℤ := univ.image mode
def enumeration (mode : P → ℤ) : Fin (support mode).card ≃o {d : ℤ // d∈support mode} :=
  (support mode).orderIsoOfFin rfl
def values (mode : P → ℤ) (i : Fin (support mode).card) : ℤ := (enumeration mode i).val
def weights (mode mass : P → ℤ) (i : Fin (support mode).card) : ℤ :=
  ∑ a, if mode a=values mode i then mass a else 0
end ThreeSum.TernaryPhysicalMomentSupport


