-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_ExistsGalFixCyclotomicLayerCycloCharNeOne
-- name    : GroundTheory_PAdicHodge_ExistsGalFixCyclotomicLayerCycloCharNeOne
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T04:33:57.714831+00:00
-- url     : https://prove2.me/theorems/97c7bf73-ac1a-50da-947b-15cf5ea86d0d
-- title:
--   Exists Gal Fix Cyclotomic Layer Cyclo Char Ne One
-- statement:
--   Definitions and structural lemmas for Exists Gal Fix Cyclotomic Layer Cyclo Char Ne One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExistsGalFixCyclotomicLayerCycloCharNeOne.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Theorems.Thm_GroundTheory_PAdicHodge_cpTwistRep_apply
import Theorems.Thm_GroundTheory_PAdicHodge_cyclotomicLayer_le_cyclotomicLimit
import Theorems.Thm_GroundTheory_PAdicHodge_exists_eq_coe_of_forall_smul_eq
import Theorems.Thm_GroundTheory_PAdicHodge_le_cyclotomicLayer
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_GroundTheory_PAdicHodge_twistScalar_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.PAdicHodge
open IntermediateField UniformSpace
variable {p : ℕ} [hp : Fact p.Prime]
section Torsion
end Torsion
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))
section Character
variable [FiniteDimensional ℚ_[p] K]
end Character
section Invariants
noncomputable abbrev cyclotomicLimitGal : Subgroup Gal(PadicAlgCl p/K) :=
  (extendScalars ((le_cyclotomicLayer K 0).trans (cyclotomicLayer_le_cyclotomicLimit K 0))).fixingSubgroup
variable [FiniteDimensional ℚ_[p] K]
theorem cpTwistRep_invariants_zero :
    (cpTwistRep K 0).invariants = LinearMap.range (Algebra.linearMap K ℂ_[p]) := by
  ext x
  rw [ContRepresentation.mem_invariants, LinearMap.mem_range]
  simp only [cpTwistRep_apply, twistScalar_zero, one_mul, Algebra.linearMap_apply]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_eq_coe_of_forall_smul_eq (K := K) h
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩ σ
    exact gal_smul_algebraMap_intermediateField K σ k
noncomputable def continuousCohomologyZeroEquiv :
    continuousCohomology 0 (cpTwist K 0) ≃ₗ[K] K :=
  (ContinuousCohomology.zeroIso (cpTwist K 0)).toContinuousLinearEquiv.toLinearEquiv ≪≫ₗ
    LinearEquiv.ofEq _ _ (cpTwistRep_invariants_zero K) ≪≫ₗ
    (LinearEquiv.ofInjective (Algebra.linearMap K ℂ_[p])
      (FaithfulSMul.algebraMap_injective K ℂ_[p])).symm
end Invariants
end GroundTheory.PAdicHodge


