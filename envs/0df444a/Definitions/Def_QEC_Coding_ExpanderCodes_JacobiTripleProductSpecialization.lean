-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
-- name    : QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:20:08.984979+00:00
-- url     : https://prove2.me/theorems/ed7496b3-2009-4cc3-a206-419dad6ecff9
-- title:
--   Jacobi Triple Product Specialization
-- statement:
--   Definitions and structural lemmas for Jacobi Triple Product Specialization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductSpecialization.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
set_option linter.style.haveILetI false
noncomputable def jacobiLaurentEvalOne : LaurentPolynomial ℤ →+* ℚ :=
  LaurentPolynomial.eval₂ (Int.castRingHom ℚ) 1
noncomputable def jacobiPowerSeriesEvalOne :
    JacobiTripleProductCore.R →+* ℚ⟦X⟧ :=
  PowerSeries.map jacobiLaurentEvalOne
end QEC.Coding.TannerLiftedProduct


