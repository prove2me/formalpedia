-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IntegralPSBserSubOne
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_IntegralPSBserSubOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:17.313648+00:00
-- url     : https://prove2.me/theorems/6cbf7cdb-b212-4df8-ba62-e1ced771f92d
-- title:
--   Integral PSBser Sub One
-- statement:
--   Definitions and structural lemmas for Integral PSBser Sub One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IntegralPSBserSubOne.lean

import Definitions.Def_Formalism_EllipticTorsion_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
namespace Formalism.ELL.PadicLogarithmSubstitution
open Formalism.G Formalism.ELL
section Integral
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
end Integral
section LogId
variable {K : Type*} [Field K] [CharZero K]
def geometricSignedSeries (K : Type*) [Field K] [CharZero K] : PowerSeries K :=
  mk fun n => algebraMap ℚ K ((-1 : ℚ) ^ n)
end LogId
section Binom
variable (p : ℕ) [Fact p.Prime] (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
def phi : ℤ_[p] →+* K := (algebraMap ℚ_[p] K).comp PadicInt.Coe.ringHom
def bser (b : ℤ_[p]) : PowerSeries K := mk fun n => phi p K (Ring.choose b n)
end Binom
end PadicLogarithmSubstitution
end Formalism.ELL


