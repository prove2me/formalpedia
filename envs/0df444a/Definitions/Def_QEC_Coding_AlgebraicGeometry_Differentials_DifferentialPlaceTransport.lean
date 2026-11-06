-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialPlaceTransport
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_DifferentialPlaceTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:41:18.240225+00:00
-- url     : https://prove2.me/theorems/70c42253-1ba9-47b7-a2cc-8f20d0dbe534
-- title:
--   Differential Place Transport
-- statement:
--   Definitions and structural lemmas for Differential Place Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialPlaceTransport.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralModelCentre
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
local instance placeTransportDVR (P : GlobalPlace k K) :
    IsDiscreteValuationRing P.valuationRing := P.valuationRing_isDiscreteValuationRing
namespace FunctionFieldDifferential
variable [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]
end FunctionFieldDifferential
end
end QEC.Coding.AlgebraicGeometry


