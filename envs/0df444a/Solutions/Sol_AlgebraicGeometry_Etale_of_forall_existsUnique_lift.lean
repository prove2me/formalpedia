-- Prove2me | solution 1 for AlgebraicGeometry.Etale.of_forall_existsUnique_lift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/ec9f5ba5-5243-529a-8fdf-563278b61e78

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Etale_of_forall_existsUnique_lift

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace EtaleInfinitesimalEngine

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def LiftProp : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] (φ : R →+* S), Function.Surjective φ →
    RingHom.ker φ ^ 2 = ⊥ → ∀ (a : Spec (CommRingCat.of S) ⟶ X) (b : Spec (CommRingCat.of R) ⟶ Y),
      a ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ b →
      ∃! l : Spec (CommRingCat.of R) ⟶ X, Spec.map (CommRingCat.ofHom φ) ≫ l = a ∧ l ≫ f = b

variable {f}

theorem formallyUnramified (hlift : LiftProp f) : FormallyUnramified f := by
  refine FormallyUnramified.of_hom_ext f fun R S φ hφ hker g₁ g₂ h₁ h₂ => ?_
  obtain ⟨l, -, huniq⟩ := hlift R S φ.hom hφ hker (Spec.map φ ≫ g₁) (g₁ ≫ f)
    (by simp only [CommRingCat.ofHom_hom, Category.assoc])
  have e₁ : g₁ = l := huniq g₁ ⟨by simp only [CommRingCat.ofHom_hom], rfl⟩
  have e₂ : g₂ = l := huniq g₂ ⟨by simp only [CommRingCat.ofHom_hom, h₁], h₂.symm⟩
  exact e₁.trans e₂.symm

theorem range_subset_of_comp {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ ^ 2 = ⊥) (l : Spec (CommRingCat.of R) ⟶ X) (V : X.Opens)
    (h : Set.range (Spec.map (CommRingCat.ofHom φ) ≫ l) ⊆ (V : Set X)) :
    Set.range l ⊆ (V : Set X) := by
  rintro _ ⟨p, rfl⟩

  have hmem : (p : PrimeSpectrum R) ∈ PrimeSpectrum.zeroLocus ((RingHom.ker φ : Ideal R) : Set R) := by
    intro r hr
    have h2 : r ^ 2 ∈ RingHom.ker φ ^ 2 := Ideal.pow_mem_pow hr 2
    rw [hker, Ideal.mem_bot] at h2
    exact p.2.mem_of_pow_mem 2 (by rw [h2]; exact Ideal.zero_mem _)
  have hp : (p : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap φ) := by
    rw [range_comap_of_surjective _ φ hφ]
    exact hmem
  obtain ⟨q, hq⟩ := hp
  refine h ⟨q, ?_⟩
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply]
  congr 1

section Smooth

variable (hlift : LiftProp f)
include hlift

theorem formallySmooth_appLE {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) :
    letI := (f.appLE U V e).hom.toAlgebra
    Algebra.FormallySmooth Γ(Y, U) Γ(X, V) := by
  letI := (f.appLE U V e).hom.toAlgebra
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ I hI g => ?_

  let φ : B →+* B ⧸ I := Ideal.Quotient.mk I
  have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ ^ 2 = ⊥ := by simpa [φ, Ideal.mk_ker] using hI
  let a : Spec (CommRingCat.of (B ⧸ I)) ⟶ X := Spec.map (CommRingCat.ofHom g.toRingHom) ≫ hV.fromSpec
  let b : Spec (CommRingCat.of B) ⟶ Y := Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) B)) ≫ hU.fromSpec
  have hsq : a ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ b := by
    simp only [a, b, Category.assoc]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    rw [← CommRingCat.ofHom_comp]
    change f.appLE U V e ≫ CommRingCat.ofHom (g.toRingHom) = _
    have hg : g.toRingHom.comp (f.appLE U V e).hom = algebraMap Γ(Y, U) (B ⧸ I) := by
      have := g.comp_algebraMap
      simpa [RingHom.algebraMap_toAlgebra] using this
    ext x
    · change g.toRingHom ((f.appLE U V e).hom x) = φ (algebraMap Γ(Y, U) B x)
      rw [← RingHom.comp_apply, hg]
      rfl
  obtain ⟨l, ⟨hl₁, hl₂⟩, -⟩ := hlift B (B ⧸ I) φ hφ hker a b hsq

  have hrange : Set.range l ⊆ Set.range hV.fromSpec := by
    rw [IsAffineOpen.range_fromSpec]
    refine range_subset_of_comp φ hφ hker l V ?_
    rw [hl₁]
    rintro _ ⟨p, rfl⟩
    have : (a p) ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
    rwa [IsAffineOpen.range_fromSpec] at this
  let l' : Spec (CommRingCat.of B) ⟶ Spec Γ(X, V) := IsOpenImmersion.lift hV.fromSpec l hrange
  have hl' : l' ≫ hV.fromSpec = l := IsOpenImmersion.lift_fac _ _ _
  let ψ : Γ(X, V) ⟶ CommRingCat.of B := Spec.preimage l'
  have hψ : Spec.map ψ = l' := Spec.map_preimage l'

  have hcomm : ψ.hom.comp (f.appLE U V e).hom = algebraMap Γ(Y, U) B := by
    have h1 : Spec.map (f.appLE U V e ≫ ψ) ≫ hU.fromSpec = Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) B)) ≫
        hU.fromSpec := by
      rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e, hψ, ← Category.assoc, hl']
      exact hl₂
    rw [cancel_mono] at h1
    have h2 := Spec.map_injective h1
    exact congrArg (fun t => t.hom) h2

  have hliftg : φ.comp ψ.hom = g.toRingHom := by
    have h1 : Spec.map (ψ ≫ CommRingCat.ofHom φ) ≫ hV.fromSpec = Spec.map (CommRingCat.ofHom g.toRingHom) ≫ hV.fromSpec := by
      rw [Spec.map_comp, Category.assoc, hψ, hl']
      exact hl₁
    rw [cancel_mono] at h1
    have h2 := Spec.map_injective h1
    exact congrArg (fun t => t.hom) h2
  refine ⟨⟨ψ.hom, fun r => ?_⟩, ?_⟩
  · change ψ.hom ((f.appLE U V e).hom r) = algebraMap Γ(Y, U) B r
    rw [← RingHom.comp_apply, hcomm]
  · apply AlgHom.ext
    intro x
    change φ (ψ.hom x) = g x
    rw [← RingHom.comp_apply, hliftg]
    rfl

theorem etale [LocallyOfFinitePresentation f] : Etale f := by
  have hfu : FormallyUnramified f := formallyUnramified hlift
  refine ⟨fun {U} hU {V} hV e => ?_⟩
  have hfp := f.finitePresentation_appLE hU hV e
  have hur := f.formallyUnramified_appLE hU hV e
  have hsm := formallySmooth_appLE hlift hU hV e
  letI := (f.appLE U V e).hom.toAlgebra
  have : Algebra.FormallyUnramified Γ(Y, U) Γ(X, V) := hur
  have : Algebra.FormallySmooth Γ(Y, U) Γ(X, V) := hsm
  have : Algebra.FinitePresentation Γ(Y, U) Γ(X, V) := hfp
  have : Algebra.FormallyEtale Γ(Y, U) Γ(X, V) := Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth
  exact (⟨this, ‹_›⟩ : Algebra.Etale Γ(Y, U) Γ(X, V))

end Smooth

end EtaleInfinitesimalEngine

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (hlift : ∀ (R S : Type u) [CommRing R] [CommRing S] (φ : R →+* S), Function.Surjective φ →
      RingHom.ker φ ^ 2 = ⊥ → ∀ (a : Spec (CommRingCat.of S) ⟶ X) (b : Spec (CommRingCat.of R) ⟶ Y),
        a ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ b →
        ∃! l : Spec (CommRingCat.of R) ⟶ X, Spec.map (CommRingCat.ofHom φ) ≫ l = a ∧ l ≫ f = b) :
    Etale f :=
  EtaleInfinitesimalEngine.etale hlift

end S_AlgebraicGeometry_Etale_of_forall_existsUnique_lift
end P2MW
export P2MW.S_AlgebraicGeometry_Etale_of_forall_existsUnique_lift (solution)
