-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_GlobalResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Rational_GlobalResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:43:55.497316+00:00
-- url     : https://prove2.me/theorems/114fca8b-ba61-4899-b678-7312a06c9607
-- title:
--   Global Residue
-- statement:
--   Definitions and structural lemmas for Global Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/GlobalResidue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidueLinear
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SimpleFractionGlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SquarefreePartialFraction
set_option autoImplicit false
open scoped BigOperators Polynomial RatFunc
namespace QEC.Coding.AlgebraicGeometry
namespace Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
noncomputable def rationalPlaceOfIrreducible
    (q : k[X]) (hq : Irreducible q) :
    IsDedekindDomain.HeightOneSpectrum k[X] := by
  have hqPrime : Prime q :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hq
  have hspanIsPrime : (Ideal.span ({q} : Set k[X])).IsPrime :=
    (Ideal.span_singleton_prime hq.ne_zero).mpr hqPrime
  exact IsDedekindDomain.HeightOneSpectrum.ofPrime
    (Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr hq.ne_zero) hspanIsPrime)
end Differential
end QEC.Coding.AlgebraicGeometry


