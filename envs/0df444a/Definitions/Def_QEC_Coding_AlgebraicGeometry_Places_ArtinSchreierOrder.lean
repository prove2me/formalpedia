-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
-- name    : QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:11:02.280241+00:00
-- url     : https://prove2.me/theorems/daa09f8e-6df8-43ae-96a9-8b3cabdb64ed
-- title:
--   Artin Schreier Order
-- statement:
--   Definitions and structural lemmas for Artin Schreier Order, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ArtinSchreierOrder.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L]
end QEC.Coding.AlgebraicGeometry.GlobalPlace


