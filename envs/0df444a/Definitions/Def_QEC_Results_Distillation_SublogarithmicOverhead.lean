-- Prove2me | Definitions.Def_QEC_Results_Distillation_SublogarithmicOverhead
-- name    : QEC_Results_Distillation_SublogarithmicOverhead
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T23:00:09.784315+00:00
-- url     : https://prove2.me/theorems/c5bf52b8-659f-4816-b0ab-0787b46e2048
-- title:
--   Sublogarithmic Overhead
-- statement:
--   Definitions and structural lemmas for Sublogarithmic Overhead, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/SublogarithmicOverhead.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_SelectedCode
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Asymptotic
set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.HH18
open Coding
open Coding.PuncturedReedMuller
open Filter Topology
open Semantics
open Semantics.FiniteInstrument
open QEC.Distillation.HH18PuncturedReedMuller
open HH18SublogarithmicEntropy
open HH18Parameterized
end QEC.Distillation.HH18


