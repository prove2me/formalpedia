-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousPsiVOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousPsiVOf
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T11:51:51.104609+00:00
-- url     : https://prove2.me/theorems/7ecf42a7-1f8a-40e7-816e-b4f3d2c9b1a8
-- title:
--   Continuous Psi VOf
-- statement:
--   Definitions and structural lemmas for Continuous Psi VOf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ContinuousPsiVOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousTrESymm
import Theorems.Thm_PI_VolStabSW_exists_unif_Fv
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabSW_secondCountable_Fv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
def piu : Fv F v := (PI.VolStabSW.exists_unif_Fv v).choose
variable (ψ : AddChar (AF F) ℂ)
def OpenKer : Prop :=
  ∃ k : ℕ, ∀ c ∈ v.adicCompletionIntegers F, psiV F ψ v (piu v ^ k * c) = 1
def ballK (k : ℕ) : Set (Fv F v) := {t | (piu v ^ k)⁻¹ * t ∈ v.adicCompletionIntegers F}
end PI.UnitaryGroupMassFormula.LocJacTyp.Sd


