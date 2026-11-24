-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_InvAlgOfSteps
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_InvAlgOfSteps
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T12:57:53.790331+00:00
-- url     : https://prove2.me/theorems/34b10b01-f5d2-4c6f-bae6-64cd1f7c8e88
-- title:
--   Inv Alg Of Steps
-- statement:
--   Definitions and structural lemmas for Inv Alg Of Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantAlgebraComparison/InvAlgOfSteps.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.BridgeInvAlg
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
def Theta (I : AutInst) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E →+*
    (InfinitePlace I.F → ℂ) × (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :=
  RingHom.prod (Pi.ringHom fun v => thetaV I v) (tauF I)
def ThetaInj : Prop := ∀ I : AutInst, Function.Injective (Theta I)
def ThetaSurj : Prop := ∀ I : AutInst, Function.Surjective (Theta I)
def HomStep : Prop := ∀ I : AutInst, ∃ f : HAd I →* I.GA, PI.AdBridgeSteps.IsFormula I f
def InjStep : Prop := ∀ (I : AutInst) (f : HAd I →* I.GA), PI.AdBridgeSteps.IsFormula I f →
  Function.Injective f
def SurjStep : Prop := ∀ (I : AutInst) (f : HAd I →* I.GA), PI.AdBridgeSteps.IsFormula I f →
  Function.Surjective f
end PI.UnitaryGroupMassFormula.BridgeInvAlg


