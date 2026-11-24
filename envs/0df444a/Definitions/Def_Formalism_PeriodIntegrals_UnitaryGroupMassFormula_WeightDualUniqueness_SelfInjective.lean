-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightDualUniqueness_SelfInjective
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightDualUniqueness_SelfInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:50.281694+00:00
-- url     : https://prove2.me/theorems/4cc0df73-6433-4442-a16a-852f47a41287
-- title:
--   Self Injective
-- statement:
--   Definitions and structural lemmas for Self Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightDualUniqueness/SelfInjective.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.UnitaryGroupMassFormula.AlgWtDualUniq
open Module
variable {G : Type*} [Group G] {Va Vb : Type*} [AddCommGroup Va] [Module ℂ Va] [AddCommGroup Vb] [Module ℂ Vb]
  (ρa : Representation ℂ G Va) (ρb : Representation ℂ G Vb)
def Inv (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) : Prop := ∀ g x y, B (ρa g x) (ρb g y) = B x y
def rKer (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) : Subrepresentation ρb where
  toSubmodule := LinearMap.ker B.flip
  apply_mem_toSubmodule g y hy := by
    rw [LinearMap.mem_ker] at hy ⊢
    ext x
    have h1 := hB g (ρa g⁻¹ x) y
    rw [Representation.self_inv_apply] at h1
    rw [LinearMap.flip_apply, h1, ← LinearMap.flip_apply, hy]
    rfl
def lKer (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) : Subrepresentation ρa where
  toSubmodule := LinearMap.ker B
  apply_mem_toSubmodule g x hx := by
    rw [LinearMap.mem_ker] at hx ⊢
    ext y
    have h1 := hB g x (ρb g⁻¹ y)
    rw [Representation.self_inv_apply] at h1
    rw [h1, hx]
    rfl
variable {ρa ρb}
theorem flip_injective [ρb.IsIrreducible] (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) (h0 : B ≠ 0) :
    Function.Injective B.flip := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (rKer ρa ρb B hB) with h | h
  · have hk : LinearMap.ker B.flip = ⊥ := by
      exact (congrArg Subrepresentation.toSubmodule h).trans rfl
    exact LinearMap.ker_eq_bot.mp hk
  · exfalso
    apply h0
    have hk : LinearMap.ker B.flip = ⊤ := by
      exact (congrArg Subrepresentation.toSubmodule h).trans rfl
    ext x y
    have hy : y ∈ LinearMap.ker B.flip := by rw [hk]; trivial
    rw [LinearMap.mem_ker] at hy
    simpa using LinearMap.congr_fun hy x
theorem self_injective [ρa.IsIrreducible] (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) (h0 : B ≠ 0) :
    Function.Injective B := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (lKer ρa ρb B hB) with h | h
  · have hk : LinearMap.ker B = ⊥ := by
      exact (congrArg Subrepresentation.toSubmodule h).trans rfl
    exact LinearMap.ker_eq_bot.mp hk
  · exfalso
    apply h0
    have hk : LinearMap.ker B = ⊤ := by
      exact (congrArg Subrepresentation.toSubmodule h).trans rfl
    ext x y
    have hx : x ∈ LinearMap.ker B := by rw [hk]; trivial
    rw [LinearMap.mem_ker] at hx
    simpa using LinearMap.congr_fun hx y
theorem finrank_eq [FiniteDimensional ℂ Va] [FiniteDimensional ℂ Vb] [ρa.IsIrreducible] [ρb.IsIrreducible]
    (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) (h0 : B ≠ 0) :
    finrank ℂ Vb = finrank ℂ (Dual ℂ Va) := by
  have h1 := LinearMap.finrank_le_finrank_of_injective (flip_injective B hB h0)
  have h2 := LinearMap.finrank_le_finrank_of_injective (self_injective B hB h0)
  rw [Subspace.dual_finrank_eq] at h1 h2 ⊢
  omega
noncomputable def phi [FiniteDimensional ℂ Va] [FiniteDimensional ℂ Vb] [ρa.IsIrreducible] [ρb.IsIrreducible]
    (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) (h0 : B ≠ 0) : Vb ≃ₗ[ℂ] Dual ℂ Va :=
  LinearMap.linearEquivOfInjective B.flip (flip_injective B hB h0) (finrank_eq B hB h0)
end PI.UnitaryGroupMassFormula.AlgWtDualUniq


