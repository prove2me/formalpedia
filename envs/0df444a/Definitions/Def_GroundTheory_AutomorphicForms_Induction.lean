-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_Induction
-- name    : GroundTheory_AutomorphicForms_Induction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:18.120799+00:00
-- url     : https://prove2.me/theorems/9fce7e3b-2049-40fa-9e1f-186b4eb8cb43
-- title:
--   Induction
-- statement:
--   Definitions and structural lemmas for Induction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Induction.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open Set Filter Topology Pointwise
section RightTranslation
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
def rightTranslation : Representation ℂ G (G → W) where
  toFun g := LinearMap.funLeft ℂ W (· * g)
  map_one' := by
    ext f x
    simp [LinearMap.funLeft_apply]
  map_mul' g h := by
    ext f x
    simp [LinearMap.funLeft_apply, Module.End.mul_apply, mul_assoc]
@[simp]
theorem rightTranslation_apply (g : G) (f : G → W) (x : G) :
    rightTranslation g f x = f (x * g) := rfl
end RightTranslation
section Induced
variable {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G)
  {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W)
def indSpace : Submodule ℂ (G → W) where
  carrier := {f | (∀ h : H, ∀ g : G, f ((h : G) * g) = σ h (f g)) ∧
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ k ∈ K, ∀ g : G, f (g * k) = f g}
  add_mem' := by
    rintro f₁ f₂ ⟨h₁, K₁, hK₁, hf₁⟩ ⟨h₂, K₂, hK₂, hf₂⟩
    refine ⟨fun h g => by simp [h₁ h g, h₂ h g], K₁ ⊓ K₂, ?_, fun k hk g => ?_⟩
    · rw [Subgroup.coe_inf]
      exact hK₁.inter hK₂
    · simp [hf₁ k (Subgroup.mem_inf.1 hk).1 g, hf₂ k (Subgroup.mem_inf.1 hk).2 g]
  zero_mem' := ⟨fun h g => by simp, ⊤, by simp, fun k _ g => rfl⟩
  smul_mem' := by
    rintro c f ⟨h₁, K, hK, hf⟩
    exact ⟨fun h g => by simp [h₁ h g], K, hK, fun k hk g => by simp [hf k hk g]⟩
def cindSpace : Submodule ℂ (G → W) :=
  indSpace H σ ⊓
  { carrier := {f | ∃ C : Set G, IsCompact C ∧ ∀ g, f g ≠ 0 → g ∈ (H : Set G) * C}
    add_mem' := by
      rintro f₁ f₂ ⟨C₁, hC₁, hf₁⟩ ⟨C₂, hC₂, hf₂⟩
      refine ⟨C₁ ∪ C₂, hC₁.union hC₂, fun g hg => ?_⟩
      by_cases h : f₁ g = 0
      · have : f₂ g ≠ 0 := by simpa [h] using hg
        exact Set.mul_subset_mul_left Set.subset_union_right (hf₂ g this)
      · exact Set.mul_subset_mul_left Set.subset_union_left (hf₁ g h)
    zero_mem' := ⟨∅, isCompact_empty, fun g hg => (hg rfl).elim⟩
    smul_mem' := by
      rintro c f ⟨C, hC, hf⟩
      exact ⟨C, hC, fun g hg => hf g fun h0 => hg (by simp [h0])⟩ }
variable {H σ} in
theorem mem_cindSpace {f : G → W} :
    f ∈ cindSpace H σ ↔ f ∈ indSpace H σ ∧
      ∃ C : Set G, IsCompact C ∧ ∀ g, f g ≠ 0 → g ∈ (H : Set G) * C :=
  Iff.rfl
theorem cindSpace_le : cindSpace H σ ≤ indSpace H σ := inf_le_left
variable [IsTopologicalGroup G]
variable {H σ} in

theorem rightTranslation_mem_indSpace {f : G → W} (hf : f ∈ indSpace H σ) (g : G) :
    rightTranslation g f ∈ indSpace H σ := by
  obtain ⟨h₁, K, hK, hfK⟩ := hf
  refine ⟨fun h x => ?_, K.comap (MulAut.conj g⁻¹).toMonoidHom, ?_, fun k hk x => ?_⟩
  · show f ((h : G) * x * g) = σ h (f (x * g))
    rw [mul_assoc, h₁]
  · rw [Subgroup.coe_comap]
    have : ⇑(MulAut.conj g⁻¹).toMonoidHom = fun x : G => g⁻¹ * x * g⁻¹⁻¹ := by
      ext x
      simp
    rw [this]
    exact hK.preimage (by fun_prop)
  · have := hfK _ hk (x * g)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this
    simp only [rightTranslation_apply]
    rw [← this]
    congr 1
    group
variable {H σ} in

theorem rightTranslation_mem_cindSpace {f : G → W} (hf : f ∈ cindSpace H σ) (g : G) :
    rightTranslation g f ∈ cindSpace H σ := by
  obtain ⟨hf, C, hC, hfC⟩ := mem_cindSpace.1 hf
  refine mem_cindSpace.2 ⟨rightTranslation_mem_indSpace hf g, (· * g⁻¹) '' C,
    hC.image (continuous_mul_const g⁻¹), fun x hx => ?_⟩
  obtain ⟨h, hh, c, hc, hxc⟩ := Set.mem_mul.1 (hfC (x * g) hx)
  refine Set.mem_mul.2 ⟨h, hh, c * g⁻¹, ⟨c, hc, rfl⟩, ?_⟩
  rw [← mul_assoc, hxc, mul_inv_cancel_right]
def indRep : Representation ℂ G (indSpace H σ) :=
  (rightTranslation (W := W)).subrepresentation (indSpace H σ) fun g _ hf =>
    rightTranslation_mem_indSpace hf g
@[simp]
theorem coe_indRep_apply (g : G) (f : indSpace H σ) (x : G) :
    (indRep H σ g f : G → W) x = (f : G → W) (x * g) := rfl
def cindRep : Representation ℂ G (cindSpace H σ) :=
  (rightTranslation (W := W)).subrepresentation (cindSpace H σ) fun g _ hf =>
    rightTranslation_mem_cindSpace hf g
@[simp]
theorem coe_cindRep_apply (g : G) (f : cindSpace H σ) (x : G) :
    (cindRep H σ g f : G → W) x = (f : G → W) (x * g) := rfl
def cindToInd : Representation.IntertwiningMap (cindRep H σ) (indRep H σ) :=
  (Submodule.inclusion (cindSpace_le H σ)).intertwiningMap_of_isIntertwiningMap _ _
    fun _ _ => rfl
section Frobenius
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
def evalOne : indSpace H σ →ₗ[ℂ] W :=
  LinearMap.proj (R := ℂ) (φ := fun _ : G => W) 1 ∘ₗ (indSpace H σ).subtype
omit [IsTopologicalGroup G] in
@[simp]
theorem evalOne_apply (f : indSpace H σ) : evalOne H σ f = (f : G → W) 1 := rfl
theorem evalOne_indRep (h : H) (f : indSpace H σ) :
    evalOne H σ (indRep H σ h f) = σ h (evalOne H σ f) := by
  simpa using f.2.1 h 1
def frobeniusFun (Φ : Representation.IntertwiningMap π (indRep H σ)) :
    Representation.IntertwiningMap (π.comp H.subtype) σ where
  toLinearMap := evalOne H σ ∘ₗ Φ.toLinearMap
  isIntertwining' h := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp,
      Subgroup.coe_subtype, Representation.IntertwiningMap.toLinearMap_apply]
    rw [Representation.IntertwiningMap.isIntertwining _ _ Φ, evalOne_indRep]
variable {π}
def frobeniusInv (hπ : IsSmooth π) (φ : Representation.IntertwiningMap (π.comp H.subtype) σ) :
    Representation.IntertwiningMap π (indRep H σ) where
  toFun v := ⟨fun g => φ (π g v), fun h g => by
      simp only [map_mul, Module.End.mul_apply]
      exact Representation.IntertwiningMap.isIntertwining _ _ φ h (π g v),
    stabilizerOf π v, hπ v, fun k hk g => by
      simp [map_mul, Module.End.mul_apply, mem_stabilizerOf.1 hk]⟩
  map_add' v w := Subtype.ext (funext fun g => by simp)
  map_smul' c v := Subtype.ext (funext fun g => by simp)
  isIntertwining' g := LinearMap.ext fun v => Subtype.ext (funext fun x => by
    simp [map_mul, Module.End.mul_apply])
@[simp]
theorem frobeniusInv_apply (hπ : IsSmooth π)
    (φ : Representation.IntertwiningMap (π.comp H.subtype) σ) (v : V) (g : G) :
    (frobeniusInv H σ hπ φ v : G → W) g = φ (π g v) := rfl
def frobenius (hπ : IsSmooth π) :
    Representation.IntertwiningMap π (indRep H σ) ≃ₗ[ℂ]
      Representation.IntertwiningMap (π.comp H.subtype) σ where
  toFun := frobeniusFun H σ π
  map_add' Φ Ψ := Representation.IntertwiningMap.ext (LinearMap.ext fun v => by
    simp [frobeniusFun])
  map_smul' c Φ := Representation.IntertwiningMap.ext (LinearMap.ext fun v => by
    simp [frobeniusFun])
  invFun := frobeniusInv H σ hπ
  left_inv Φ := Representation.IntertwiningMap.ext (LinearMap.ext fun v =>
    Subtype.ext (funext fun x => by
      simp only [Representation.IntertwiningMap.toLinearMap_apply, frobeniusInv_apply]
      show (evalOne H σ) (Φ (π x v)) = _
      rw [Representation.IntertwiningMap.isIntertwining _ _ Φ, evalOne_apply, coe_indRep_apply, one_mul]))
  right_inv φ := Representation.IntertwiningMap.ext (LinearMap.ext fun v => by
    show (evalOne H σ) (frobeniusInv H σ hπ φ v) = φ v
    simp)
end Frobenius
end Induced
end GroundTheory.Automorphic


