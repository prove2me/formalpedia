-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_LocalRelNormCount
-- name    : QEC_Coding_AlgebraicGeometry_Divisors_LocalRelNormCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:42:28.576705+00:00
-- url     : https://prove2.me/theorems/f01638e2-8ba0-4d87-be9a-95848f774d75
-- title:
--   Local Rel Norm Count
-- statement:
--   Definitions and structural lemmas for Local Rel Norm Count, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/LocalRelNormCount.lean

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.LocalRelNormCount
open UniqueFactorizationMonoid
variable (R S : Type*)
variable [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsDedekindDomain R]
variable [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [IsDedekindDomain S]
variable [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
noncomputable def primeRelNormExponent (P : Ideal S) (p : Ideal R)
    [P.LiesOver p] [p.IsPrime] : Nat :=
  Nat.find (Ideal.exists_relNorm_eq_pow_of_isPrime P p)
end QEC.Coding.AlgebraicGeometry.LocalRelNormCount


