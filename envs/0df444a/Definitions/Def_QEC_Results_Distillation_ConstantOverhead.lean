-- Prove2me | Definitions.Def_QEC_Results_Distillation_ConstantOverhead
-- name    : QEC_Results_Distillation_ConstantOverhead
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:40:24.162457+00:00
-- url     : https://prove2.me/theorems/aeb39c05-421b-4c77-92dd-a3e8268c3aea
-- title:
--   Constant Overhead
-- statement:
--   Definitions and structural lemmas for Constant Overhead, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/ConstantOverhead.lean

import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_OneRound
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_ResourceConversions
set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Why24ConstantOverhead
open Filter Topology
open Semantics
open Why24AGFamily Why24OneRoundProtocol
open QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
open Triorthogonal.BH12Concatenation
open Triorthogonal.BH12EvenFamily
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12Protocol
def why24ThresholdRate : Real :=
  1 / (140 * 2 ^ 240)
def why24OverheadConstant : Real := 1680
def why24GeometricErrorEnvelope (index : Nat) : Real :=
  (1 / 2 : Real) ^ (f1024Why24OddDecodingRadius index + 1)
def why24CatalystSeedParameter : ErrorParameter where
  rate := 1 / 200
  rate_nonneg := by norm_num
  rate_le_one := by norm_num
theorem why24CatalystSeedParameter_le_half :
    why24CatalystSeedParameter.rate <= 1 / 2 := by
  norm_num [why24CatalystSeedParameter]
theorem why24CatalystSeedParameter_small :
    (bh12InputCount 1 : Real) * why24CatalystSeedParameter.rate <= 1 / 4 := by
  norm_num [bh12InputCount, resourceCount, Column, logicalCount,
    why24CatalystSeedParameter]
theorem why24CatalystSeedParameter_strong :
    quadraticCoefficient 1 * why24CatalystSeedParameter.rate <= 1 / 2 := by
  norm_num [quadraticCoefficient, why24CatalystSeedParameter]
def why24CatalystSeedPort : OddRow 1 := (0, 0)
def why24CatalystSeedPath : depthOutputPath 1 1 :=
  fun _ => why24CatalystSeedPort
def why24CatalystSeedScheduleIndex : BH12PathScheduleIndex 1 where
  depth := 1
  path := why24CatalystSeedPath
noncomputable def why24CatalystSeedCost : Real :=
  bh12PathScheduleTypedSuccessfulOutputCost 1 why24CatalystSeedParameter
    why24CatalystSeedParameter_small why24CatalystSeedParameter_le_half
    why24CatalystSeedParameter_strong why24CatalystSeedScheduleIndex
noncomputable def why24CatalystSeedCostPerFreshOutput (batch : Nat) : Real :=
  why24CatalystSeedCost /
    ((2 * batch * why24OneRoundOutputCount batch : Nat) : Real)
end QEC.Distillation.Why24ConstantOverhead


