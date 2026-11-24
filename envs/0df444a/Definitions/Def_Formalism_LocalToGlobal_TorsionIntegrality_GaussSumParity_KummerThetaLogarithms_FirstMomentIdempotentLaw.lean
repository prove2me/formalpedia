-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T10:24:06.836411+00:00
-- url     : https://prove2.me/theorems/1b0792e5-51e4-4499-9603-fefc74e21315
-- title:
--   First Moment Idempotent Law
-- statement:
--   Definitions and structural lemmas for First Moment Idempotent Law, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FirstMomentIdempotentLaw.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog frobVar frobVar_eq_expand)
open MvPowerSeries
namespace TranslateJetMomentLawAnyIdempotentLevel
open Pair KernelCokernelKilling
section Alg
variable {K : Type} [Field K] {d : ℕ} [NeZero d]
variable {ι : Type}
def pXY (σ : K →+* K) (om oms : ι → K) (x : Bool × ι) (s : ZMod d) : K :=
  if s.val % 2 = 0 then (if x.1 = false then σ^[s.val] (oms x.2) else 0)
  else (if x.1 = true then σ^[s.val] (om x.2) else 0)
end Alg
end TranslateJetMomentLawAnyIdempotentLevel
open Pair TranslateJetMomentLawAnyIdempotentLevel
namespace TranslateJetMomentLawAnyIdempotentLevel
open Pair KernelCokernelKilling
section Gen
variable {K : Type} [Field K]
open Classical in

def keep {τ : Type} (P : τ → Prop) (f : MvPowerSeries τ K) : MvPowerSeries τ K :=
  rescale (fun x => if P x then (1 : K) else 0) f
open Classical in

def keepX {τ : Type} (P : τ → Prop) : τ → MvPowerSeries τ K :=
  (fun x => if P x then (1 : K) else 0) • X
end Gen
end TranslateJetMomentLawAnyIdempotentLevel
namespace TranslateJetMomentLawAnyIdempotentLevel
open Pair KernelCokernelKilling
section Shift
variable {K : Type} [Field K] {d : ℕ} [NeZero d] {ι : Type}
def sM (K : Type) [Field K] (d : ℕ) (s k : ZMod d) : K := if k = s - 2 then 1 else 0
end Shift
section Normed
variable {K : Type} [NormedField K] {d : ℕ} [NeZero d] {ι : Type}
end Normed
end TranslateJetMomentLawAnyIdempotentLevel
end Formalism.L2.Th1.D


