-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveInvariants
-- name    : GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveInvariants
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:12:13.556746+00:00
-- url     : https://prove2.me/theorems/658b643e-a2c1-4914-88d3-71da472eaaf5
-- title:
--   Additive Invariants
-- statement:
--   Definitions and structural lemmas for Additive Invariants, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveInvariants.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.coe_torsNRep_apply
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
universe u v w
open Representation TensorProduct
section Invariants
variable {k Γ : Type*} [Field k] [Group Γ] [Fintype Γ]
  {X₁ X₂ X₃ : Type*} [AddCommGroup X₁] [Module k X₁] [AddCommGroup X₂] [Module k X₂]
  [AddCommGroup X₃] [Module k X₃]
  {ρ₁ : Representation k Γ X₁} {ρ₂ : Representation k Γ X₂} {ρ₃ : Representation k Γ X₃}
omit [Fintype Γ] in

theorem mapsTo_invariants {f : X₁ →ₗ[k] X₂} (hf : ρ₁.IsIntertwiningMap ρ₂ f) (x : X₁)
    (hx : x ∈ ρ₁.invariants) : f x ∈ ρ₂.invariants := fun γ => by
  rw [← hf.isIntertwining, hx γ]
theorem exists_invariant_preimage (hΓ : (Fintype.card Γ : k) ≠ 0) {g : X₂ →ₗ[k] X₃}
    (hg : ρ₂.IsIntertwiningMap ρ₃ g) (hs : Function.Surjective g) (y : X₃)
    (hy : y ∈ ρ₃.invariants) : ∃ x ∈ ρ₂.invariants, g x = y := by
  obtain ⟨x, rfl⟩ := hs y
  refine ⟨(Fintype.card Γ : k)⁻¹ • ρ₂.norm x, fun γ => by rw [map_smul, self_norm_apply], ?_⟩
  have hnorm : g (ρ₂.norm x) = ρ₃.norm (g x) := by
    simp [Representation.norm, LinearMap.sum_apply, map_sum, hg.isIntertwining]
  have hinv : ρ₃.norm (g x) = (Fintype.card Γ : k) • g x := by
    have hy' : ∀ γ, ρ₃ γ (g x) = g x := hy
    simp only [Representation.norm, LinearMap.sum_apply, hy', Finset.sum_const, Finset.card_univ]
    exact (Nat.cast_smul_eq_nsmul k _ _).symm
  rw [map_smul, hnorm, hinv, smul_smul, inv_mul_cancel₀ hΓ, one_smul]
theorem finrank_invariants_additive [FiniteDimensional k X₂] (hΓ : (Fintype.card Γ : k) ≠ 0)
    (f : X₁ →ₗ[k] X₂) (g : X₂ →ₗ[k] X₃) (hf : ρ₁.IsIntertwiningMap ρ₂ f)
    (hg : ρ₂.IsIntertwiningMap ρ₃ g) (hinj : Function.Injective f) (hfg : Function.Exact f g)
    (hs : Function.Surjective g) :
    Module.finrank k ρ₂.invariants =
      Module.finrank k ρ₁.invariants + Module.finrank k ρ₃.invariants := by
  let f' : ρ₁.invariants →ₗ[k] ρ₂.invariants := f.restrict (mapsTo_invariants hf)
  let g' : ρ₂.invariants →ₗ[k] ρ₃.invariants := g.restrict (mapsTo_invariants hg)
  have hf' : Function.Injective f' := fun a b hab =>
    Subtype.ext (hinj (congrArg Subtype.val hab))
  have hg' : Function.Surjective g' := fun y => by
    obtain ⟨x, hx, hxy⟩ := exists_invariant_preimage hΓ hg hs y y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hker : LinearMap.ker g' = LinearMap.range f' := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := (hfg (x : X₂)).1 (congrArg Subtype.val hx)
      have ha' : a ∈ ρ₁.invariants := fun γ => hinj (by
        rw [hf.isIntertwining, ha, x.2 γ])
      exact ⟨⟨a, ha'⟩, Subtype.ext ha⟩
    · rintro ⟨a, rfl⟩
      exact Subtype.ext ((hfg _).2 ⟨a, rfl⟩)
  have h₁ := LinearMap.finrank_range_add_finrank_ker g'
  rw [LinearMap.range_eq_top.2 hg', finrank_top, hker, LinearMap.finrank_range_of_inj hf'] at h₁
  omega
end Invariants
theorem isIntertwiningMap_rTensor {k Γ X Y N : Type*} [CommRing k] [Monoid Γ] [AddCommGroup X]
    [Module k X] [AddCommGroup Y] [Module k Y] [AddCommGroup N] [Module k N]
    {ρ : Representation k Γ X} {ρ' : Representation k Γ Y} (σ : Representation k Γ N)
    {f : X →ₗ[k] Y} (hf : ρ.IsIntertwiningMap ρ' f) :
    (ρ.tprod σ).IsIntertwiningMap (ρ'.tprod σ) (f.rTensor N) :=
  ⟨fun γ v => by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x n => simp [hf.isIntertwining]
    | add v w hv hw => simp only [map_add, hv, hw]⟩
namespace AdditiveFunction
noncomputable def invariantsTensor (l : ℕ) [Fact l.Prime] (Γ : Type v) [Group Γ] [Finite Γ]
    (hΓ : Nat.Coprime (Nat.card Γ) l) {N : Type w} [AddCommGroup N] [Module (ZMod l) N]
    [Module.Finite (ZMod l) N] (σ : Representation (ZMod l) Γ N) : AdditiveFunction.{u} l Γ where
  toFun X _ _ _ ρ := Module.finrank (ZMod l) (ρ.tprod σ).invariants
  additive := by
    intro X₁ X₂ X₃ _ _ _ _ _ _ _ _ _ ρ₁ ρ₂ ρ₃ f g hf hg hinj hfg hs
    have := Fintype.ofFinite Γ
    have hΓ' : (Fintype.card Γ : ZMod l) ≠ 0 := by
      rw [← Nat.card_eq_fintype_card, Ne, ZMod.natCast_eq_zero_iff]
      exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).1 hΓ.symm
    have := Module.Finite.of_finite (R := ZMod l) (M := X₂)
    exact_mod_cast finrank_invariants_additive hΓ' (f.rTensor N) (g.rTensor N)
      (isIntertwiningMap_rTensor σ hf) (isIntertwiningMap_rTensor σ hg)
      (Module.Flat.rTensor_preserves_injective_linearMap f hinj) (rTensor_exact N hfg hs)
      (LinearMap.rTensor_surjective N hs)
end AdditiveFunction
end GroundTheory.ProfCoh


