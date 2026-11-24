-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IntegralPartAtVariable
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IntegralPartAtVariable
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:59:42.46075+00:00
-- url     : https://prove2.me/theorems/c6292e61-3b82-42b8-a3e8-872448206e3b
-- title:
--   Integral Part At Variable
-- statement:
--   Definitions and structural lemmas for Integral Part At Variable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/IntegralPartAtVariable.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
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
namespace Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp frobVar)
open MvPowerSeries
namespace SubstitutionCoefficientLemmas
open Pair InverseCommuting
section Alg
variable {K : Type} [Field K]
end Alg
section Normed
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
def InS (l : ℕ) (σ : K →+* K) (be0 : MvPowerSeries (Fin 2) K) (α : K) : Prop :=
  ‖α‖ ≤ 1 ∧ σ (σ α) = α ∧
    Simeq (subst ![C α * at1 (0 : Fin 2) (lgF K l), at1 (1 : Fin 2) (lgF K l)] (addC l be0))
      (subst ![at1 (0 : Fin 2) (lgF K l), C (σ α) * at1 (1 : Fin 2) (lgF K l)] (addC l be0))
variable {l : ℕ} {σ : K →+* K} {F be0 : MvPowerSeries (Fin 2) K}
end Normed
end SubstitutionCoefficientLemmas
open SubstitutionCoefficientLemmas Pair
end Formalism.L2.Th1.D


