-- Prove2me | Definitions.Def_QEC_Locality_OptimalTradeoff_FinalComposition
-- name    : QEC_Locality_OptimalTradeoff_FinalComposition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T13:14:41.030474+00:00
-- url     : https://prove2.me/theorems/7210d397-f021-49b3-8874-93787f674f9f
-- title:
--   Final Composition
-- statement:
--   Definitions and structural lemmas for Final Composition, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/FinalComposition.lean

import Definitions.Def_QEC_Locality_OptimalTradeoff_CountComposition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
set_option autoImplicit false
noncomputable section
namespace QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
def daiLiFirstLengthScale (d n : ℝ) : ℝ :=
  d / Real.sqrt n
def daiLiInteractionCountThreshold (k d n : ℝ) : ℝ :=
  (1 / 200 : ℝ) * max (daiLiFirstLengthScale d n)
    (daiLiFourthRoot (k * d ^ 2 / n))
def daiLiFinalAboveBPTConstant : ℝ := (1000 : ℝ) ^ 4
end QEC.Locality


