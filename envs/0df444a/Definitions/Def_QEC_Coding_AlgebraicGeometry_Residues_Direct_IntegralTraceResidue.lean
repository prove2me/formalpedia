-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralTraceResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralTraceResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:03:23.134863+00:00
-- url     : https://prove2.me/theorems/3c2afb8e-e902-40e6-aa0b-e5305a7f6c0f
-- title:
--   Integral Trace Residue
-- statement:
--   Definitions and structural lemmas for Integral Trace Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralTraceResidue.lean

import Mathlib.RingTheory.Trace.Quotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_DedekindQuotientTrace
set_option autoImplicit false
namespace Ideal
open scoped nonZeroDivisors
open UniqueFactorizationMonoid
attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
namespace Factors
universe u v
variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable {S : Type v} [CommRing S] [IsDedekindDomain S] [Algebra R S]
variable [Module.IsTorsionFree R S] [Module.Finite R S]
noncomputable def quotientResidueEquiv
    {A : Type*} [CommRing A] (I : Ideal A) [I.IsMaximal] :
    (A ⧸ I) ≃+* I.ResidueField :=
  RingEquiv.ofBijective (algebraMap (A ⧸ I) I.ResidueField)
    I.bijective_algebraMap_quotient_residueField
noncomputable def factorResidueTrace
    (p : Ideal R) [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) :
    p.ResidueField := by
  letI : (P : Ideal S).IsMaximal :=
    (Factors.isPrime p P).isMaximal (Factors.ne_bot p P)
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime (P : Ideal S)) :=
    Localization.AtPrime.algebraOfLiesOver p (P : Ideal S)
  exact Algebra.trace p.ResidueField (P : Ideal S).ResidueField
    (algebraMap S (P : Ideal S).ResidueField x)
end Factors
end Ideal


