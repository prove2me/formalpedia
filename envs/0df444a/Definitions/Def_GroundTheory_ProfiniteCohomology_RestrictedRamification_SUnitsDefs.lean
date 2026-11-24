-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_SUnitsDefs
-- name    : GroundTheory_ProfiniteCohomology_RestrictedRamification_SUnitsDefs
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T17:48:43.460968+00:00
-- url     : https://prove2.me/theorems/d184421e-ec93-4686-b83b-3e61bd121b13
-- title:
--   SUnits Defs
-- statement:
--   Definitions and structural lemmas for SUnits Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/SUnitsDefs.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisCohomology_UnitsInflationCochainsFHomApply
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_openNormalSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_openNormalSubgroupEquiv_apply
import Theorems.Thm_GroundTheory_ProfCoh_unitsInflationCochains_f_hom_apply
import Theorems.Thm_GroundTheory_ProfCoh_unitsRestrictHom_hom_apply
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
attribute [local simp] GroundTheory.ProfCoh.coe_openNormalSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer
attribute [local simp] GroundTheory.ProfCoh.openNormalSubgroupEquiv_apply
attribute [local simp] GroundTheory.ProfCoh.unitsInflationCochains_f_hom_apply
attribute [local simp] GroundTheory.ProfCoh.unitsRestrictHom_hom_apply
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
attribute [local simp] P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open NumberField IsDedekindDomain CategoryTheory
universe u
section SUnits
variable {F : Type u} [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F)))
variable (E : Type u) [Field E] [Algebra F E]
def sUnitsOf : Subgroup Eˣ where
  carrier := {x | IsIntegral (S.integer F) (x : E) ∧ IsIntegral (S.integer F) ((x⁻¹ : Eˣ) : E)}
  mul_mem' hx hy := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact hx.1.mul hy.1
    · rw [mul_inv, Units.val_mul]
      exact hx.2.mul hy.2
  one_mem' := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_one]
      exact isIntegral_one
    · rw [inv_one, Units.val_one]
      exact isIntegral_one
  inv_mem' {x} hx := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩
variable {S E}
theorem isIntegral_algEquiv_apply (σ : E ≃ₐ[F] E) {x : E} (hx : IsIntegral (S.integer F) x) :
    IsIntegral (S.integer F) (σ x) :=
  hx.map ((σ : E →ₐ[F] E).restrictScalars (S.integer F))
theorem mem_sUnitsOf_of_mem_rootsOfUnity {n : ℕ} (hn0 : n ≠ 0) {ζ : Eˣ}
    (hζ : ζ ∈ rootsOfUnity n E) : ζ ∈ sUnitsOf S E := by
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have h1 : ∀ y : Eˣ, y ^ n = 1 → IsIntegral (S.integer F) (y : E) := fun y hy =>
    ⟨Polynomial.X ^ n - 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one, ← Units.val_pow_eq_pow_val,
        hy, Units.val_one, sub_self]⟩
  have hζ' : ζ ^ n = 1 := (mem_rootsOfUnity n ζ).1 hζ
  exact ⟨h1 ζ hζ', h1 ζ⁻¹ (by rw [inv_pow, hζ', inv_one])⟩
theorem galUnitsHom_mem_sUnitsOf (σ : E ≃ₐ[F] E) {x : Eˣ} (hx : x ∈ sUnitsOf S E) :
    galUnitsHom F E σ x ∈ sUnitsOf S E := by
  refine ⟨isIntegral_algEquiv_apply σ hx.1, ?_⟩
  rw [← map_inv]
  exact isIntegral_algEquiv_apply σ hx.2
variable (S E)
def galSUnitsHom : Gal(E/F) →* Monoid.End (sUnitsOf S E) where
  toFun σ := ((galUnitsHom F E σ).comp (sUnitsOf S E).subtype).codRestrict (sUnitsOf S E)
    fun x => galUnitsHom_mem_sUnitsOf σ x.2
  map_one' := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl
@[simp]
theorem coe_galSUnitsHom_apply (σ : Gal(E/F)) (x : sUnitsOf S E) :
    (((galSUnitsHom S E σ x : Eˣ)) : E) = σ (x : Eˣ) :=
  rfl
abbrev galSUnits : Rep.{u} (ULift.{u} ℤ) Gal(E/F) :=
  Rep.of (intRepOfMonoidEnd.{u} (galSUnitsHom S E))
@[simp]
theorem galSUnits_ρ_apply (σ : Gal(E/F)) (x : Additive (sUnitsOf S E)) :
    (galSUnits S E).ρ σ x = Additive.ofMul (galSUnitsHom S E σ x.toMul) :=
  rfl
def sUnitsToUnits : galSUnits S E ⟶ galUnits.{u} F E :=
  Rep.ofHom ⟨uliftIntLinearMap (MonoidHom.toAdditive (sUnitsOf S E).subtype), fun σ => by
    ext x
    rfl⟩
@[simp]
theorem sUnitsToUnits_hom_apply (x : Additive (sUnitsOf S E)) :
    ((sUnitsToUnits S E).hom x : Additive Eˣ) =
      Additive.ofMul ((Additive.toMul x : sUnitsOf S E) : Eˣ) :=
  rfl
theorem sUnitsToUnits_injective : Function.Injective (sUnitsToUnits S E).hom := fun _ _ h =>
  Additive.toMul.injective (Subtype.ext (Additive.ofMul.symm.injective h))
instance isDiscreteRep_galSUnits [Algebra.IsIntegral F E] : IsDiscreteRep (galSUnits S E) :=
  IsDiscreteRep.of_injective (sUnitsToUnits S E) (sUnitsToUnits_injective S E)
variable (n : ℕ) [NeZero n]
def rootsOfUnityToSUnitsHom : rootsOfUnity n E →* sUnitsOf S E :=
  (rootsOfUnity n E).subtype.codRestrict (sUnitsOf S E) fun ζ =>
    mem_sUnitsOf_of_mem_rootsOfUnity (NeZero.ne n) ζ.2
def rootsOfUnityToSUnits : galRootsOfUnity.{u} F E n ⟶ galSUnits S E :=
  Rep.ofHom ⟨uliftIntLinearMap (MonoidHom.toAdditive (rootsOfUnityToSUnitsHom S E n)), fun σ => by
    ext x
    rfl⟩
@[simp]
theorem rootsOfUnityToSUnits_hom_apply (x : Additive (rootsOfUnity n E)) :
    ((((Additive.toMul ((rootsOfUnityToSUnits S E n).hom x) : sUnitsOf S E)) : Eˣ) : E) =
      (((Additive.toMul x : rootsOfUnity n E) : Eˣ) : E) :=
  rfl
noncomputable def sUnitsKummerSequence : ShortComplex (Rep.{u} (ULift.{u} ℤ) Gal(E/F)) :=
  ShortComplex.mk (rootsOfUnityToSUnits S E n) (n • 𝟙 (galSUnits S E)) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    change ((((Additive.toMul (α := rootsOfUnity n E) x : rootsOfUnity n E) : Eˣ) ^ n : Eˣ) : E) = 1
    rw [(mem_rootsOfUnity n _).1 (Additive.toMul (α := rootsOfUnity n E) x).2, Units.val_one])
end SUnits
section Max
variable (F : Type u) [Field F] [NumberField F] (Ω : Type u) [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))
noncomputable abbrev sUnitsMax : Subgroup (maxUnramifiedOutside F Ω S)ˣ :=
  sUnitsOf S (maxUnramifiedOutside F Ω S)
noncomputable abbrev galSUnitsMax : Rep.{u} (ULift.{u} ℤ) (galUnramifiedOutside F Ω S) :=
  galSUnits S (maxUnramifiedOutside F Ω S)
example [Algebra.IsIntegral F Ω] : IsDiscreteRep (galSUnitsMax F Ω S) := inferInstance
end Max
end GroundTheory.ProfCoh


