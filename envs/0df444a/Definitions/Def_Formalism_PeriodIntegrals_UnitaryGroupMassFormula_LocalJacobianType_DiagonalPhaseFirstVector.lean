-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_DiagonalPhaseFirstVector
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_DiagonalPhaseFirstVector
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T12:51:25.101477+00:00
-- url     : https://prove2.me/theorems/5cb5c5f0-d2e7-5397-a2fa-57cc416ac4bd
-- title:
--   Diagonal Phase First Vector
-- statement:
--   Definitions and structural lemmas for Diagonal Phase First Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/DiagonalPhaseFirstVector.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ComponentsOfD1EqZero
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_psiV_add__9a67760e36c5
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_psiV_neg_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_psiV_zero
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
open PI.VolStabSW.SdUniqW
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)
theorem diagonal_phase_first_vector : (0 : Fv F v ⊗[F] E) ∈ D1 (E := E) v ψ := by
  intro x _; simp [psiV_zero]
theorem conductor_add_mem {y y' : Fv F v ⊗[F] E} (hy : y ∈ D1 (E := E) v ψ) (hy' : y' ∈ D1 (E := E) v ψ) :
    y + y' ∈ D1 (E := E) v ψ := by
  intro x hx
  rw [mul_add, map_add, psiV_add', hy x hx, hy' x hx, mul_one]
theorem conductor_neg_mem {y : Fv F v ⊗[F] E} (hy : y ∈ D1 (E := E) v ψ) : -y ∈ D1 (E := E) v ψ := by
  intro x hx
  have h := psiV_neg_mul v ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y))
  rw [hy x hx, mul_one] at h
  rwa [mul_neg, map_neg]
def D1sub : AddSubgroup (Fv F v ⊗[F] E) where
  carrier := D1 (E := E) v ψ
  add_mem' := conductor_add_mem v ψ
  zero_mem' := diagonal_phase_first_vector v ψ
  neg_mem' := conductor_neg_mem v ψ
variable (hK : OpenKer v ψ)
include hK
end PI.UnitaryGroupMassFormula.LocJacTyp.Sd


