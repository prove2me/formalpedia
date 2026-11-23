-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:18.416653+00:00
-- url     : https://prove2.me/theorems/88cf11d8-06de-4536-b9d5-17284e034b73
-- title:
--   Degree Le Of Mem Antidiagonal
-- statement:
--   Definitions and structural lemmas for Degree Le Of Mem Antidiagonal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/DegreeLeOfMemAntidiagonal.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
namespace Formalism.L2.Th1.C
namespace IntegralMvPolynomialLemmas
section Chain
variable {A : Type*} [CommRing A] {σ : Type*}
end Chain
section Integral
variable {K : Type} [Field K] {σ : Type} {R : Subring K}
end Integral
section Exp
variable {K : Type} [Field K] [CharZero K] {σ : Type}
end Exp
end IntegralMvPolynomialLemmas
open IntegralMvPolynomialLemmas
end Formalism.L2.Th1.C


