-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTensorEncoding
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_BinaryTensorEncoding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T11:53:36.473204+00:00
-- url     : https://prove2.me/theorems/f6ebae4b-0942-4c48-acad-9458b2ff71e7
-- title:
--   Binary Tensor Encoding
-- statement:
--   Definitions and structural lemmas for Binary Tensor Encoding, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTensorEncoding.lean

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_TensorRegister
set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
end QEC.Distillation.Ngu24Binary


