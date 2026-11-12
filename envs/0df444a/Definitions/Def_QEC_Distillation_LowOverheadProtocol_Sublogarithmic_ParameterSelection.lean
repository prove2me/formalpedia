-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
-- name    : QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:34:36.611377+00:00
-- url     : https://prove2.me/theorems/3a926a4b-e589-456f-9a46-382779af91ed
-- title:
--   Parameter Selection
-- statement:
--   Definitions and structural lemmas for Parameter Selection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/ParameterSelection.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
set_option autoImplicit false
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology
def parameterR (D j : Nat) : Nat := 2 * D * j
def parameterW (A j : Nat) : Nat := 6 * A * j
def parameterM (D j : Nat) : Nat := 6 * D * j + 1
def parameterLength (A D j : Nat) : Nat :=
  binomialTail (parameterM D j) (parameterW A j)
def parameterDimension (A D j : Nat) : Nat :=
  binomialUpTo (parameterM D j) (parameterW A j)
def parameterDistance (A D j : Nat) : Nat :=
  binomialTail (parameterR D j + 1) (parameterW A j)
noncomputable def parameterGamma (A D j : Nat) : ℝ :=
  Real.log ((parameterLength A D j : ℝ) / parameterDimension A D j) /
    Real.log (parameterDistance A D j : ℝ)
noncomputable def parameterLengthLimit (D : Nat) : ℝ :=
  6 * D * Real.log 2
noncomputable def entropyRay (s a : Nat) : ℝ :=
  s * Real.log s - a * Real.log a - (s - a) * Real.log (s - a)
noncomputable def parameterDimensionLimit (A D : Nat) : ℝ :=
  entropyRay (6 * D) (6 * A)
noncomputable def parameterDistanceLimit (A D : Nat) : ℝ :=
  entropyRay (2 * D) (6 * A)
end QEC.Distillation.HH18.HH18SublogarithmicEntropy


