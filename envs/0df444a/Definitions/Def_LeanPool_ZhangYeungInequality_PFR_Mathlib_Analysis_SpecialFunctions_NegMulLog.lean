-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Analysis_SpecialFunctions_NegMulLog
-- name    : LeanPool_ZhangYeungInequality_PFR_Mathlib_Analysis_SpecialFunctions_NegMulLog
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:22:01.408821+00:00
-- url     : https://prove2.me/theorems/3c103a6a-dc20-4e75-ac68-a654ed4e9ea2
-- title:
--   Neg Mul Log
-- statement:
--   Definitions and structural lemmas for Neg Mul Log, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Analysis/SpecialFunctions/NegMulLog.lean

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open scoped ENNReal NNReal Topology
namespace Real
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {p : ι → ℝ}
end Real


