-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InvariantDerivationSubstLawThree
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InvariantDerivationSubstLawThree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:29.013602+00:00
-- url     : https://prove2.me/theorems/bc2ecf21-1647-4c81-bcae-d5ad8d83faa7
-- title:
--   Invariant Derivation Subst Law Three
-- statement:
--   Definitions and structural lemmas for Invariant Derivation Subst Law Three, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/InvariantDerivationSubstLawThree.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Th1.B.Jets
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3)
open Formalism.G.LogP (hs2 psubst_subst constantCoeff_subst_of_zero psubst_injective)
section Alg
variable {K : Type} [Field K] [CharZero K]
def Dj (l : PowerSeries K) (j : Fin 3) (g : MvPowerSeries (Fin 3) K) : MvPowerSeries (Fin 3) K :=
  at1 j (dz l)⁻¹ * pd j g
def U2 (F : MvPowerSeries (Fin 2) K) (a b : Fin 3) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![(MvPowerSeries.X a : MvPowerSeries (Fin 3) K), MvPowerSeries.X b] F
def U3 (F : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![U2 F 0 1, MvPowerSeries.X 2] F
section Steps
variable {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K}
end Steps
end Alg
section Norm
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
end Norm
end Formalism.L2.Th1.B.Jets


