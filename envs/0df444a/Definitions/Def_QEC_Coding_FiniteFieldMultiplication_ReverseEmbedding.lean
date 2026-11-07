-- Prove2me | Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
-- name    : QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:09:49.733212+00:00
-- url     : https://prove2.me/theorems/c85671bf-1477-4720-a9dc-f2f8417769ce
-- title:
--   Reverse Embedding
-- statement:
--   Definitions and structural lemmas for Reverse Embedding, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/ReverseEmbedding.lean

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
set_option autoImplicit false
namespace QEC.Coding
noncomputable def f256RMFEphi : ZMod 2 →ₗ[ZMod 2] F256 :=
  Algebra.linearMap (ZMod 2) F256
noncomputable def f256RMFEpsi : F256 →ₗ[ZMod 2] ZMod 2 :=
  (Algebra.trace (ZMod 2) F256).comp (LinearMap.mulLeft (ZMod 2) (f256Alpha ^ 3))
end QEC.Coding


