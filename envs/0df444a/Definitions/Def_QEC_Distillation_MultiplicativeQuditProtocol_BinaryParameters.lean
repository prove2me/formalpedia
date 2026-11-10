-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryParameters
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_BinaryParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T11:42:32.791211+00:00
-- url     : https://prove2.me/theorems/8af36ca8-cac6-475c-aa09-edd29f4cb5e7
-- title:
--   Binary Parameters
-- statement:
--   Definitions and structural lemmas for Binary Parameters, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryParameters.lean

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter
open scoped BigOperators Topology
local instance _p2m_local_instance_6d70a6dbef_22 {A : Type} [Fintype A] : Fintype (Word F256 A) := Fintype.ofFinite _
def binaryLength (i : Nat) : Nat := 512 * f256QuditLength i
def binaryDistance (i : Nat) : Nat :=
  QuditSubsystem.finiteMeasurementDistance
    (fun _ : (f256SourceInput i).PivotComplement × Fin 512 => 2) (binaryEncodedCode i).code
end QEC.Distillation.Ngu24Binary


