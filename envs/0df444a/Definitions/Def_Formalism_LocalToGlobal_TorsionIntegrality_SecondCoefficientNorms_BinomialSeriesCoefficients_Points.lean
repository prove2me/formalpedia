-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:50.483626+00:00
-- url     : https://prove2.me/theorems/b105ea52-4b4c-439f-8982-890a0b9d4801
-- title:
--   Points
-- statement:
--   Definitions and structural lemmas for Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.C
namespace Pts
open IntegralMvPolynomialLemmas
section Toolkit
variable {K : Type} [Field K] {σ : Type} {l linv : PowerSeries K}
end Toolkit
section Integral
variable {K : Type} [Field K] {σ : Type} {R : Subring K} {l linv : PowerSeries K}
end Integral
end Pts
end Formalism.L2.Th1.C


