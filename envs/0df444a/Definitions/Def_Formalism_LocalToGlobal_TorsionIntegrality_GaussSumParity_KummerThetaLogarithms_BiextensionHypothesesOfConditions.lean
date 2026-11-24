-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionHypothesesOfConditions
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionHypothesesOfConditions
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T10:17:24.653102+00:00
-- url     : https://prove2.me/theorems/d6d9ae56-8cf6-47b8-865b-6bd691f93d39
-- title:
--   Biextension Hypotheses Of Conditions
-- statement:
--   Definitions and structural lemmas for Biextension Hypotheses Of Conditions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionHypothesesOfConditions.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp NoLowBidegree letterLog de1 de2 s0 s1 s2 s1' s2' V2 degE)
open Formalism.InvariantFactorPaths.G7 (Simeq DivAB UnrOK IsLawOfLog)
open MvPowerSeries (subst HasSubst constantCoeff)
namespace B4
section Lin
variable {K : Type} [NormedField K] {τ : Type} {d : ℕ} [NeZero d]
end Lin
section Five
variable {K : Type} [Field K] {τ : Type} {d : ℕ} {a : V2 d → MvPowerSeries τ K}
end Five
section Sim
variable {K ι : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
end Sim
end B4
open B4
namespace B4
section Linear
variable {K : Type} [Field K] {τ τ' : Type}
variable {d : ℕ} [NeZero d]
end Linear
end B4
end Formalism.L2.Th1.D


