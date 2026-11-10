-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T11:39:20.303964+00:00
-- url     : https://prove2.me/theorems/9ba3b060-4edf-400b-8260-de0cdb074fbf
-- title:
--   Binary Distance
-- statement:
--   Definitions and structural lemmas for Binary Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryDistance.lean

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
variable {J : Type} [DecidableEq J]
local instance _p2m_local_instance_9a39a2a69e_41 {A : Type} [Fintype A] : Fintype (Word F256 A) := Fintype.ofFinite _
end QEC.Distillation.Ngu24Binary


