-- Prove2me | Definitions.Def_QEC_Locality_OptimalTradeoff_CountComposition
-- name    : QEC_Locality_OptimalTradeoff_CountComposition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T13:10:37.580995+00:00
-- url     : https://prove2.me/theorems/c7200d7a-1f00-4fb3-b22e-60c9c65baace
-- title:
--   Count Composition
-- statement:
--   Definitions and structural lemmas for Count Composition, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CountComposition.lean

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
set_option autoImplicit false
noncomputable section
namespace QEC.Locality
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
def daiLiFourthRoot (x : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt x)
def daiLiKGeDFourthRootThreshold (k d n : ℝ) : ℝ :=
  daiLiFourthRoot (k * d ^ 2 / n) / 100
def daiLiKGeDGridWidth (d ell : ℝ) : ℝ :=
  d / (100 * ell)
end QEC.Locality


