-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:16.49539+00:00
-- url     : https://prove2.me/theorems/2a7be6ac-6dfb-4ecf-9d43-008bcfe04dcd
-- title:
--   Int PSDerivative Of LG
-- statement:
--   Definitions and structural lemmas for Int PSDerivative Of LG, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
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
open Finset
namespace Formalism.L2.Th1.C
namespace JetSubstitutionLemmas
section Field
variable {K : Type} [Field K]
variable {R : Subring K}
end Field
section CharZero
variable {K : Type} [Field K] [CharZero K] {R : Subring K}
end CharZero
end JetSubstitutionLemmas
open JetSubstitutionLemmas
namespace JetSubstitutionLemmas
section Norm
variable {K : Type} [Field K]
end Norm
end JetSubstitutionLemmas
namespace JetSubstitutionLemmas
section Adj
variable {K : Type} [Field K] {σ : Type}
def Q (l ψ : PowerSeries K) (α β : K) : MvPowerSeries (Fin 2) K :=
  PowerSeries.subst (MvPowerSeries.C α * PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) l +
    MvPowerSeries.C β * PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) l) ψ
end Adj
end JetSubstitutionLemmas
namespace JetSubstitutionLemmas
section Hurwitz
variable {K : Type} [Field K] {R : Subring K}
variable [CharZero K]
end Hurwitz
end JetSubstitutionLemmas
end Formalism.L2.Th1.C


