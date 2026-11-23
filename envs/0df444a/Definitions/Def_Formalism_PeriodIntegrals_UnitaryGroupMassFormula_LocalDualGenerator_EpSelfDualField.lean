-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualField
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:55:40.554804+00:00
-- url     : https://prove2.me/theorems/d39f9a1b-fa45-4470-925b-cea115bfb84e
-- title:
--   Ep Self Dual Field
-- statement:
--   Definitions and structural lemmas for Ep Self Dual Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualField.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open ValuativeRel IsDedekindDomain
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace PI.LocDualGen.EpF
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [CharZero K]
local notation "C" => integralClosure 𝒪[K] L
theorem tf : Module.IsTorsionFree 𝒪[K] L := by
  first
    | exact Module.IsTorsionFree.trans_faithfulSMul 𝒪[K] K L
    | (rw [Module.isTorsionFree_iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective,
        IsScalarTower.algebraMap_eq 𝒪[K] K L]
       exact (algebraMap K L).injective.comp Subtype.val_injective)
theorem dd : IsDedekindDomain C := integralClosure.isDedekindDomain 𝒪[K] K L
theorem fr : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension K L
theorem mf : Module.Finite 𝒪[K] C := IsIntegralClosure.finite 𝒪[K] K L C
theorem tfC : Module.IsTorsionFree 𝒪[K] C := by
  have hf : FaithfulSMul 𝒪[K] L := Module.isTorsionFree_iff_faithfulSMul.1 (tf K L)
  rw [Module.isTorsionFree_iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective]
  intro a b h
  have h' := congrArg (algebraMap C L) h
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h'
  exact (FaithfulSMul.algebraMap_injective 𝒪[K] L) h'
attribute [local instance] dd fr mf tfC
theorem sepFR : Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing C) := by
  first
    | infer_instance
    | exact Algebra.IsAlgebraic.isSeparable_of_perfectField
attribute [local instance] sepFR
end PI.LocDualGen.EpF


