-- Prove2me | Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
-- name    : QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:06:25.004145+00:00
-- url     : https://prove2.me/theorems/85f4d446-0eee-4d0e-a428-f82a92be7341
-- title:
--   Quantitative Recurrence
-- statement:
--   Definitions and structural lemmas for Quantitative Recurrence, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
set_option autoImplicit false
noncomputable section
namespace QEC.Locality
open Set
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
def bkRpowGap (c : ℝ) : ℝ :=
  (2 / 3 : ℝ) ^ c + (1 / 3 : ℝ) ^ c - 1
def bkEntropyGap : ℝ :=
  -((2 / 3 : ℝ) * Real.log (2 / 3 : ℝ) +
      (1 / 3 : ℝ) * Real.log (1 / 3 : ℝ))
def bkRpowCoefficient (beta c : ℝ) : ℝ :=
  beta / (bkRpowGap c * (1 / 3 : ℝ) ^ (1 - c))
def bkRpowPotential (beta c : ℝ) (d parent : Nat) : ℝ :=
  (beta / bkRpowGap c) * (d : ℝ) ^ c *
    (((parent : ℝ) / d) / (1 / 3 : ℝ) ^ (1 - c) -
      ((parent : ℝ) / d) ^ c)
namespace BKQLDPCFamily
variable {iota : Nat → Type u} {kappa : Nat → Type v}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable [∀ n, Fintype (kappa n)]
def EventuallyCMaxAtMostBKLogThreshold
    (family : BKQLDPCFamily iota kappa) : Prop :=
  family.EventuallyOnValidIndices (fun i ↦
    family.cMax i ≤ 1 + Real.logb (i.1 : ℝ) (1 / 3 : ℝ))
end BKQLDPCFamily
end QEC.Locality


