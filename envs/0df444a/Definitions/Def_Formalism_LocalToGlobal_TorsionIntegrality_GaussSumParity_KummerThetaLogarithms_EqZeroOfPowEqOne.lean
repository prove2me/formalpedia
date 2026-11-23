-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:17.965961+00:00
-- url     : https://prove2.me/theorems/5684983d-5511-438e-8f12-8df6805d18a2
-- title:
--   Eq Zero Of Pow Eq One
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Pow Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/EqZeroOfPowEqOne.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand

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
open Formalism.DworkPowerSeriesWeights (Integral letterLog entLog)
open Formalism.InvariantFactorPaths.G7 (frobVar frobVar_eq_expand UnrOK)
namespace KernelCokernelKilling
open MvPowerSeries
section Gen
variable {K : Type} [Field K] {τ : Type} [DecidableEq τ] {l d : ℕ}
def gLog (K : Type) [Field K] (l : ℕ) (φ : ZMod d → τ) (s : ZMod d) : MvPowerSeries τ K :=
  fun n => ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0
end Gen
section Normed
variable {K : Type} [NormedField K] {τ : Type}
end Normed
end KernelCokernelKilling
end Formalism.L2.Th1.D


