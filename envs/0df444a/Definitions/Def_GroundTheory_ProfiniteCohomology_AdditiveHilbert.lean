-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_AdditiveHilbert
-- name    : GroundTheory_ProfiniteCohomology_AdditiveHilbert
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:46.119952+00:00
-- url     : https://prove2.me/theorems/4549f16d-6fdd-4340-b1cd-ef45ae7819bc
-- title:
--   Additive Hilbert
-- statement:
--   Definitions and structural lemmas for Additive Hilbert, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/AdditiveHilbert.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open CategoryTheory CategoryTheory.Limits
universe u
section NormalBasis
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
theorem normalBasis_repr_apply_smul (σ τ : Gal(L/K)) (y : L) :
    (IsGalois.normalBasis K L).repr (σ y) τ = (IsGalois.normalBasis K L).repr y (σ⁻¹ * τ) := by
  have hb (ρ : Gal(L/K)) :
      σ (IsGalois.normalBasis K L ρ) = IsGalois.normalBasis K L (σ * ρ) := by
    rw [IsGalois.normalBasis_apply (σ * ρ), IsGalois.normalBasis_apply ρ, AlgEquiv.mul_apply]
  have key : (Finsupp.lapply τ ∘ₗ (IsGalois.normalBasis K L).repr.toLinearMap ∘ₗ σ.toLinearMap :
      L →ₗ[K] K) = Finsupp.lapply (σ⁻¹ * τ) ∘ₗ (IsGalois.normalBasis K L).repr.toLinearMap := by
    refine (IsGalois.normalBasis K L).ext fun ρ => ?_
    change (IsGalois.normalBasis K L).repr (σ (IsGalois.normalBasis K L ρ)) τ =
      (IsGalois.normalBasis K L).repr (IsGalois.normalBasis K L ρ) (σ⁻¹ * τ)
    classical
    rw [hb, Module.Basis.repr_self, Module.Basis.repr_self]
    simp only [Finsupp.single_apply, eq_inv_mul_iff_mul_eq]
  exact LinearMap.congr_fun key y
end NormalBasis
section Coinduced
variable (k : Type u) (K L : Type u) [CommRing k] [Field K] [Field L] [Algebra K L]
  [Algebra k K] [Algebra k L] [IsScalarTower k K L] [FiniteDimensional K L] [IsGalois K L]
noncomputable def galoisCoindIso :
    Rep.ofDistribMulAction k Gal(L/K) L ≅
      Rep.coind (⊥ : Subgroup Gal(L/K)).subtype (Rep.trivial k (⊥ : Subgroup Gal(L/K)) K) := by
  have htop : (Representation.trivial k (⊥ : Subgroup Gal(L/K)) K).coindV
      (⊥ : Subgroup Gal(L/K)).subtype = ⊤ := by
    ext f
    simp only [Representation.mem_coindV, Submodule.mem_top, iff_true]
    rintro ⟨g, hg⟩ h
    rw [Subgroup.mem_bot] at hg
    subst hg
    simp
  let e : L ≃ₗ[k] _ :=
    ((IsGalois.normalBasis K L).equivFun.restrictScalars k).trans
      ((LinearEquiv.funCongrLeft k K (Equiv.inv Gal(L/K))).trans (LinearEquiv.ofTop _ htop).symm)
  refine Rep.mkIso (Representation.Equiv.mk e fun σ => ?_)
  refine LinearMap.ext fun y => Subtype.ext (funext fun h => ?_)
  change (IsGalois.normalBasis K L).repr (σ y) h⁻¹ =
    (IsGalois.normalBasis K L).repr y (h * σ)⁻¹
  rw [normalBasis_repr_apply_smul, mul_inv_rev]
end Coinduced
section Vanishing
open groupCohomology
variable (k : Type u) (K L : Type u) [CommRing k] [Field K] [Field L] [Algebra K L]
  [Algebra k K] [Algebra k L] [IsScalarTower k K L] [FiniteDimensional K L] [IsGalois K L]
end Vanishing
section Integral
variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
end Integral
end GroundTheory.ProfCoh


