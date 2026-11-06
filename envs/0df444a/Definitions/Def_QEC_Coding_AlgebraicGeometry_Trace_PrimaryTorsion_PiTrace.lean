-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PiTrace
-- name    : QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PiTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:34:41.030058+00:00
-- url     : https://prove2.me/theorems/2ab7243b-6636-4d1a-9746-3e76160921a2
-- title:
--   Pi Trace
-- statement:
--   Definitions and structural lemmas for Pi Trace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PiTrace.lean

import Mathlib.LinearAlgebra.Pi
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceFunctorial
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type w}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
def piDiagonalBlock (f : (∀ i, M i) →ₗ[R] ∀ i, M i) (i : ι) :
    M i →ₗ[R] M i :=
  (LinearMap.proj i).comp
    (f.comp (LinearMap.single R M i))
end QEC.Coding.AlgebraicGeometry


