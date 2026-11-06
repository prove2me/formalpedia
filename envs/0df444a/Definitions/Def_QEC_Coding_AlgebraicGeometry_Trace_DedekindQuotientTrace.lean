-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_DedekindQuotientTrace
-- name    : QEC_Coding_AlgebraicGeometry_Trace_DedekindQuotientTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:02:59.724651+00:00
-- url     : https://prove2.me/theorems/ad266175-0dae-41ed-a020-19b93360fc3e
-- title:
--   Dedekind Quotient Trace
-- statement:
--   Definitions and structural lemmas for Dedekind Quotient Trace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/DedekindQuotientTrace.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimePowerQuotientTrace
set_option autoImplicit false
namespace Ideal
universe u v w w'
variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
namespace Factors
open UniqueFactorizationMonoid
variable [IsDedekindDomain S] [Module.Finite R S]
end Factors
end Ideal


