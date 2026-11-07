-- Prove2me | Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
-- name    : QEC_Coding_FiniteFieldMultiplication_BinaryConversion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:11:19.862183+00:00
-- url     : https://prove2.me/theorems/e1246210-a202-4868-935c-937d064f4e98
-- title:
--   Binary Conversion
-- statement:
--   Definitions and structural lemmas for Binary Conversion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/BinaryConversion.lean

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
set_option autoImplicit false
noncomputable section
namespace QEC.Coding
open scoped BigOperators
def f256MFEFromSelfDual : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 512 → ZMod 2) :=
  f256MFESigma.comp f256SelfDualBasis.equivFun.symm.toLinearMap
end QEC.Coding


