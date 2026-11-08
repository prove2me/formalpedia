-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureDistance
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureDistance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T12:13:38.708033+00:00
-- url     : https://prove2.me/theorems/847497c4-c6ef-454e-a91f-5edc9bf8088d
-- title:
--   Normal Closure Distance
-- statement:
--   Definitions and structural lemmas for Normal Closure Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureDistance.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureInterpolation
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureInput
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CosetDetectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Semantics
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
local instance _p2m_local_instance_5d3c569749_91 {J : Type} [Fintype J] : Fintype (Word F256 J) := Fintype.ofFinite _
end QEC.Distillation.Ngu24MultiplicativeCSS


